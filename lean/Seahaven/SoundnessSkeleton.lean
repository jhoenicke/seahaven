import Mathlib.Data.Nat.Bitwise
import Seahaven.SolvableBits

/-!
# Skeleton of the soundness proof for the body of `solverRecCheckSolvable`

Target: the part of `solverRecCheckSolvable` between the memo read and the memo
write (`Solver.lean:377-401`).  Soundness only — *if the expanded bit is set then
the position really is solvable*.  The converse (completeness) is not addressed.

The pile loop accumulates `solvable := solvable ||| movable''`.  The whole loop
therefore reduces to a **per-contribution** obligation, because the `subsetTable`
expansion turns out to be *additive* in the local bitmask (`subsetAt_or`, decided
over the tables below).  That is the one structural fact that makes this
tractable; it is proved here, along with the `BitSet` algebra it needs.

What is left is three semantic obligations, stated as named `Prop`s:
`SubsetSound`, `ComponentSound`, `MoveSimulated`.  The fourth piece — carrying
the recursion's query across a lone-king vacate — is **proved** here as
`kingStep_transport`, from `MoveSimulated`'s `KingVacates`/`FK` clause.

## What `subsetTable` is for

`closureInfos[f]` stores only the **maximal** king assignments — every free pile
carrying a king.  Real positions need not have a king on every free pile, and
`subsetTable` is what repairs that: it closes a local set downwards under
"put fewer kings on piles".  See `subsetAt_spec_*` below for the exact
characterization, decided against the tables.

Two consequences, and note they point in opposite directions:

* `MaskSub.mono` — *fewer* kings on piles stays covered.  Free.
* the *reverse* fails: a forced lone-king vacate puts one *more* king on a pile,
  landing in a different block, while the solver keeps querying the child
  expansion at the parent's configuration.  That is exactly why the child answer
  is intersected with `forcedKings` — the intersection deletes every child
  configuration lacking the vacated kings, and what survives covers the child's
  *actual* configuration too (`kingStep_transport`, engine `MaskSub_iff` /
  `MaskSub.clear_forced`).

Beware the twice-refuted shortcut "the intersection only shrinks the set, so
soundness is free": it silently instantiates the child's answer at the parent's
configuration, which the child state does *not* stand for after a vacate — see
the `SolvableBits` module docstring for the concrete counterexample.  The
solvability specs are stated over `StateMatchesKingConfig` (with the `no_pile`
clause) precisely to make that instantiation impossible.
-/

/-! ## `BitSet` algebra -/

theorem nat_and_shiftLeft_ne_zero (n k : Nat) :
    (n &&& (1 <<< k) ≠ 0) ↔ n.testBit k = true := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow]
  cases h : n.testBit k <;> simp

theorem uint16_mask_toNat (k : Fin 16) :
    ((1 : UInt16) <<< (UInt16.ofNat k.val)).toNat = 1 <<< k.val := by
  fin_cases k <;> decide

theorem BitSet_toNat (w : UInt16) (k : Fin 16) : BitSet w k ↔ w.toNat.testBit k.val := by
  unfold BitSet
  rw [← nat_and_shiftLeft_ne_zero, ← uint16_mask_toNat k, ← UInt16.toNat_and]
  constructor
  · intro h hz; exact h (UInt16.toNat_inj.1 (by simpa using hz))
  · intro h hz; exact h (by rw [hz]; rfl)

theorem BitSet_or (x y : UInt16) (k : Fin 16) :
    BitSet (x ||| y) k ↔ BitSet x k ∨ BitSet y k := by
  simp [BitSet_toNat, UInt16.toNat_or, Nat.testBit_or]

theorem BitSet_zero (k : Fin 16) : ¬ BitSet 0 k := by simp [BitSet_toNat]

theorem BitSet_and (x y : UInt16) (k : Fin 16) :
    BitSet (x &&& y) k ↔ BitSet x k ∧ BitSet y k := by
  simp [BitSet_toNat, UInt16.toNat_and, Nat.testBit_and]

/-! ## `forcedKings`, described through the vacated suits

`forcedKings` is a set of king **configurations** — bit `d` stands for grlex
index `d`, itself denoting a set of suits — but it is always built as the
intersection of `kingOnPileMap` rows for the suits whose lone king was vacated
(`Solver.lean:301`, starting from `0xffff`).  `KingVacates FK fk` captures that
by its membership condition: configuration `d` survives in `fk` exactly when it
piles *every* vacated suit.

The `.2` direction is the completeness-facing one: any configuration that piles
all of `FK`'s suits — in particular "`K` with `FK`'s bits cleared", for every
`K` — survives the `&&& forcedKings` intersection. -/

def KingVacates (FK : Finset Suit) (fk : UInt16) : Prop :=
  ∀ d : Fin 16, BitSet fk d ↔ ∀ su ∈ FK, ¬ CfgBitSet d su

/-- No vacate: `forcedKings` starts (and stays) at `0xffff`. -/
theorem KingVacates.empty : KingVacates ∅ 0xffff := by
  unfold KingVacates; decide

/-- One vacate contributes its `kingOnPileMap` row (cf. `kingOnPileMap_eq`). -/
theorem KingVacates.single (su : Suit) :
    KingVacates {su} (kingOnPileMap.get (finOfSuit su)) := by
  unfold KingVacates; revert su; decide

/-- Vacates accumulate: suit sets by union, masks by `&&&` — exactly the code's
`forcedKings := forcedKings &&& …` accumulators across cleanup calls and the
`busyAces` drain. -/
theorem KingVacates.inter {F₁ F₂ : Finset Suit} {fk₁ fk₂ : UInt16}
    (h₁ : KingVacates F₁ fk₁) (h₂ : KingVacates F₂ fk₂) :
    KingVacates (F₁ ∪ F₂) (fk₁ &&& fk₂) := by
  intro d
  rw [BitSet_and, h₁ d, h₂ d]
  constructor
  · rintro ⟨ha, hb⟩ su hsu
    rcases Finset.mem_union.1 hsu with h | h
    · exact ha su h
    · exact hb su h
  · exact fun h => ⟨fun su hsu => h su (Finset.mem_union_left _ hsu),
                    fun su hsu => h su (Finset.mem_union_right _ hsu)⟩

/-! ## `subsetTable` is additive in the local bitmask

`subsetAt (off + T)` is the set of global configurations from which some
configuration of the local set `T` is reachable, so it distributes over unions
of `T`.  Decided per block; the `freePiles = 2` block is 64×64 and takes a while. -/

theorem subsetAt_zero_block (f : Fin 11) :
    subsetAt (closureInfos.get f).offset.toNat = 0 := by
  fin_cases f <;> decide

theorem subsetAt_or_98 : ∀ a b : Fin 2,
    subsetAt (98 + (a.val ||| b.val)) = subsetAt (98 + a.val) ||| subsetAt (98 + b.val) := by
  decide

theorem subsetAt_or_96 : ∀ a b : Fin 2,
    subsetAt (96 + (a.val ||| b.val)) = subsetAt (96 + a.val) ||| subsetAt (96 + b.val) := by
  decide

theorem subsetAt_or_0 : ∀ a b : Fin 16,
    subsetAt (0 + (a.val ||| b.val)) = subsetAt (0 + a.val) ||| subsetAt (0 + b.val) := by
  decide

theorem subsetAt_or_80 : ∀ a b : Fin 16,
    subsetAt (80 + (a.val ||| b.val)) = subsetAt (80 + a.val) ||| subsetAt (80 + b.val) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem subsetAt_or_16 : ∀ a b : Fin 64,
    subsetAt (16 + (a.val ||| b.val)) = subsetAt (16 + a.val) ||| subsetAt (16 + b.val) := by
  decide

theorem subsetAt_or_block (f : Fin 11) (a b : Nat)
    (ha : a < 2 ^ (closureInfos.get f).numBits.toNat)
    (hb : b < 2 ^ (closureInfos.get f).numBits.toNat) :
    subsetAt ((closureInfos.get f).offset.toNat + (a ||| b))
      = subsetAt ((closureInfos.get f).offset.toNat + a)
        ||| subsetAt ((closureInfos.get f).offset.toNat + b) := by
  fin_cases f
  · exact subsetAt_or_98 ⟨a, ha⟩ ⟨b, hb⟩
  · exact subsetAt_or_0 ⟨a, ha⟩ ⟨b, hb⟩
  · exact subsetAt_or_16 ⟨a, ha⟩ ⟨b, hb⟩
  · exact subsetAt_or_80 ⟨a, ha⟩ ⟨b, hb⟩
  all_goals exact subsetAt_or_96 ⟨a, ha⟩ ⟨b, hb⟩

theorem subsetAt_or_pos (p : SolverPosType) {a b : UInt16}
    (ha : LocalMask p a) (hb : LocalMask p b) :
    subsetAt ((closureInfoOf p).offset.toNat + (a ||| b).toNat)
      = subsetAt ((closureInfoOf p).offset.toNat + a.toNat)
        ||| subsetAt ((closureInfoOf p).offset.toNat + b.toNat) := by
  rw [UInt16.toNat_or]
  exact subsetAt_or_block ⟨min p.freePiles.toInt.toNat 10, by omega⟩ _ _ ha hb

theorem subsetAt_zero_pos (p : SolverPosType) :
    subsetAt ((closureInfoOf p).offset.toNat + (0 : UInt16).toNat) = 0 :=
  subsetAt_zero_block ⟨min p.freePiles.toInt.toNat 10, by omega⟩

/-! ## One simulated step, and how steps chain

Each phase of a `SolverMove` — the flute move, each `SolverCleanupPile`, each
`SolverMoveAces` — produces the same four-part package, so it gets one name.
`Simulates` bundles them, and `Simulates.trans` is the whole chaining story:
`Reach` composes, the intermediate configuration is forgotten, the vacated suits
accumulate by `∪`, and the returned masks by `&&&` — exactly the code's
`forcedKings := forcedKings &&& (← …)` accumulator.

The `bound` field is what makes this compose at all.  It is an **upper** bound on
what the new configuration piles, so bounds chain by transitivity of `⊆`:

> `piled k'' ⊆ piled k' ∪ F₂ ⊆ (piled k ∪ F₁) ∪ F₂`

The reverse ("`k'` piles at least `piled k ∪ FK`") would compose into a *lower*
bound, which is useless both here and to `kingStep_transport`
(`kingStep_flipped_insufficient`).

Note what `bound` does **not** promise: that `k'` piles no *less* than `k`.  A
suit may legitimately stop being piled — but not arbitrarily, so do not plan on
a "shrink the configuration" step.  `StateMatchesKingConfig` is *anti*-monotone in
the piled set through `no_pile`: a suit with cards physically sitting on a
solver-empty column is *forced* to be piled.  The freedom exists exactly for
suits with nothing on such a column (nothing freed yet, or the whole suit already
on the foundation), which is why `RealizesKingConfig.mono` alone does not lift to
`StateMatchesKingConfig`.  In practice no phase needs to shrink: carrying `k`
with the vacated suits cleared already satisfies `bound`. -/

/-- One or more phases of a `SolverMove`, simulated: legal moves from `s` to `s'`,
the successor position `p'` matched at configuration `k'`, the vacated suits `FK`
with the `forcedKings` mask `fk` they force, and the guarantee that `k'` piles
nothing beyond `k`'s piles and `FK`. -/
structure Simulates (g : Globals) (s : State) (p : SolverPosType) (k : Fin 16)
    (s' : State) (p' : SolverPosType) (k' : Fin 16)
    (FK : Finset Suit) (fk : UInt16) : Prop where
  reach : Reach s s'
  cfg : StateMatchesKingConfig g s' p' k'
  vacates : KingVacates FK fk
  bound : ∀ su : Suit, ¬ CfgBitSet k' su → ¬ CfgBitSet k su ∨ su ∈ FK

/-- **Doing nothing simulates nothing**, and is the unit for `trans`. -/
theorem Simulates.refl {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (h : StateMatchesKingConfig g s p k) : Simulates g s p k s p k ∅ 0xffff where
  reach := Relation.ReflTransGen.refl
  cfg := h
  vacates := KingVacates.empty
  bound := fun _ hk => Or.inl hk

/-- **A phase that vacates no king**: the flute move, cleanup's merge and
extension, and the foundation drain all keep the configuration and contribute the
neutral `0xffff`. -/
theorem Simulates.ofReach {g : Globals} {s s' : State} {p p' : SolverPosType} {k : Fin 16}
    (hr : Reach s s') (h : StateMatchesKingConfig g s' p' k) :
    Simulates g s p k s' p' k ∅ 0xffff where
  reach := hr
  cfg := h
  vacates := KingVacates.empty
  bound := fun _ hk => Or.inl hk

/-- **A lone-king vacate** (`kingMove`): suit `su` joins the piled set, every
other suit keeps its bit, and the contributed mask is `su`'s `kingOnPileMap` row.
The `Reach` is usually `refl` — vacating moves no card — but it is taken as a
parameter so cleanup's extension can be folded in. -/
theorem Simulates.vacate {g : Globals} {s s' : State} {p p' : SolverPosType} {k k' : Fin 16}
    {su : Suit} (hr : Reach s s') (h : StateMatchesKingConfig g s' p' k')
    (hk' : ∀ su' : Suit, su' ≠ su → (CfgBitSet k' su' ↔ CfgBitSet k su')) :
    Simulates g s p k s' p' k' {su} (kingOnPileMap.get (finOfSuit su)) where
  reach := hr
  cfg := h
  vacates := KingVacates.single su
  bound := fun su' hk =>
    if hsu : su' = su then Or.inr (by simp [hsu])
    else Or.inl (fun hc => hk ((hk' su' hsu).2 hc))

/-- **Chaining.**  This is the only composition rule the phase lemmas need: run
one phase, then the next from wherever it left off. -/
theorem Simulates.trans {g : Globals} {s s' s'' : State} {p p' p'' : SolverPosType}
    {k k' k'' : Fin 16} {F₁ F₂ : Finset Suit} {fk₁ fk₂ : UInt16}
    (h₁ : Simulates g s p k s' p' k' F₁ fk₁) (h₂ : Simulates g s' p' k' s'' p'' k'' F₂ fk₂) :
    Simulates g s p k s'' p'' k'' (F₁ ∪ F₂) (fk₁ &&& fk₂) where
  reach := h₁.reach.trans h₂.reach
  cfg := h₂.cfg
  vacates := h₁.vacates.inter h₂.vacates
  bound := fun su hk => by
    rcases h₂.bound su hk with hk' | hF₂
    · rcases h₁.bound su hk' with hk0 | hF₁
      · exact Or.inl hk0
      · exact Or.inr (Finset.mem_union_left _ hF₁)
    · exact Or.inr (Finset.mem_union_right _ hF₂)

/-! ## The loop invariant -/

/-- The soundness half of `SolvableBits`: a set bit really does mean solvable.
Like `SolvableBits`, this must be stated over `StateMatchesKingConfig` — with
bare `RealizesKingConfig` an A-piled state masquerades as an A-in-cells
configuration and the statement is unsatisfiable (see the `SolvableBits` module
docstring). -/
def SoundBits (g : Globals) (p : SolverPosType) (v : UInt16) : Prop :=
  ∀ (s : State) (k : Fin 16), StateMatchesKingConfig g s p k →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) k → Solvable s

/-- **Base case** of the loop: the accumulator starts at `0`, whose expansion is
empty in every block, so the invariant holds vacuously. -/
theorem SoundBits.zero (g : Globals) (p : SolverPosType) : SoundBits g p 0 := by
  intro s _ _ hbit
  rw [subsetAt_zero_pos p] at hbit
  exact absurd hbit (BitSet_zero _)

/-- **Inductive step** of the loop: soundness is closed under union of local
masks.  This is what additivity buys — the whole loop reduces to establishing
`SoundBits g p movable''` for one contribution at a time. -/
theorem SoundBits.union {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b)
    (ha : SoundBits g p a) (hb : SoundBits g p b) : SoundBits g p (a ||| b) := by
  intro s k hs hbit
  rw [subsetAt_or_pos p hla hlb, BitSet_or] at hbit
  rcases hbit with h | h
  · exact ha s k hs h
  · exact hb s k hs h

/-- Soundness is monotone downwards: a subset of a sound mask is sound.  (This is
*not* enough to discharge the `&&& forcedKings` intersection — the parent queries
the child's expansion at its own configuration, which the child state does not
`StateMatchesKingConfig`-realize after a vacate; that transport is
`kingStep_transport` below.) -/
theorem SoundBits.of_sub {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b)
    (hsub : a ||| b = b) (hb : SoundBits g p b) : SoundBits g p a := by
  intro s k hs hbit
  refine hb s k hs ?_
  rw [← hsub, subsetAt_or_pos p hla hlb, BitSet_or]
  exact Or.inl hbit

/-! ## The remaining semantic obligations

Everything above is proved.  What follows are the four statements the rest of
the argument needs; each is independent of the others. -/

/-- `s` can be brought, by legal moves that change nothing the abstract position
records, to a state standing for the same `p` at king configuration `k`.
Reshuffling king stacks between the cells and empty piles changes neither
depths, flutes, nor foundations — which is exactly why the same `p` appears on
both sides. -/
def KingConfigReachable (g : Globals) (p : SolverPosType) (s : State) (k : Fin 16) : Prop :=
  ∃ s', Reach s s' ∧ StateMatchesKingConfig g s' p k

/-- The global grlex configuration of local bit `i` of block `ci`. -/
def globalCfg (ci : ClosureInfo) (i : Nat) : Fin 16 :=
  ⟨min (ci.shiftValue.toNat + i) 15, by omega⟩


/-- **(1) `subsetTable` soundness.**  Its expansion means what its name says: if
the expansion of a local set `T` contains a configuration reachable from `s`,
then some configuration *of `T` itself* is reachable from `s`.

Three hypotheses, and none is optional:

* `LocalMask p T` — `subsetTable` is a flat array of per-block regions, so an
  out-of-block `T` reads a *neighbouring* block's entry, whose expansion says
  nothing about this block's bits (`subsetAt_spec_pos` is where this is used).
* `WellFormedLayout`/`SolverInvMerged` — as for `ComponentSound`, the closure is
  realized by physically moving king runs from the cells onto empty columns, so
  the position's cell and column budget has to describe `s`.  No separate
  `StateMatchesSolverPos` clause is needed: `KingConfigReachable` already
  supplies a matching state.

(Proved: `subsetSound` in `KingMoveSim`, via `subsetSound_of` in
`KingReshuffle` — the closure is repeated *piling*, the direction of a king
reshuffle that has no cell-space side condition.) -/
def SubsetSound : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (T : UInt16) (c : Fin 16),
    LocalMask p T → WellFormedLayout g → SolverInvMerged g p →
    KingConfigReachable g p s c →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + T.toNat)) c →
    ∃ i : Nat, i < (closureInfoOf p).numBits.toNat ∧
      BitSet T ⟨min i 15, by omega⟩ ∧ KingConfigReachable g p s (globalCfg (closureInfoOf p) i)

/-- **(2) Component soundness.**  `computeComponentKingBits` returns a set of
mutually reachable configurations, which is what justifies
`movable'' := movable' ||| component` (`Solver.lean:398`) adding bits.

The invariants are hypotheses because the reachability is realized by physically
moving king runs between the cells and empty columns: the cell budget the
component is computed from (`usedSpace`, `kings`) has to describe `s`, and the
count of empty columns has to be `freePiles`.  Both are available at the call
site (`WellFormedLayout` globally, `IsCanonicalPos` for the position the
recursion is at).  No separate `StateMatchesSolverPos` clause is needed —
`KingConfigReachable` already supplies a matching state.  (Proved:
`componentSound_of` in `KingReshuffle`, from the two physical steps.) -/
def ComponentSound : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (comp : UInt8) (i j : Nat),
    WellFormedLayout g → SolverInvMerged g p →
    EStateM.run (computeComponentKingBits p) g = .ok comp g →
    i < (closureInfoOf p).numBits.toNat → j < (closureInfoOf p).numBits.toNat →
    BitSet comp.toUInt16 ⟨min i 15, by omega⟩ → BitSet comp.toUInt16 ⟨min j 15, by omega⟩ →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) i) →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) j)

/-! ## What `subsetTable` actually computes

The block `closureInfos[f]` stores only the **maximal** king assignments — every
free pile carrying a king.  A real position need not have a king on every free
pile, and *that* is what `subsetTable` repairs: it closes a local set downwards
under "put fewer kings on piles", because moving a king stack from the cells onto
an empty pile is always legal and never costs a cell.

Writing `mask k = grlex2bits[k]` (bit `su` set = suit `su` has no pile), the
table is exactly

> `c ∈ subsetAt (off_f + T)  ⟺  ∃ i ∈ T,  mask (shift_f + i) ⊆ mask c`

i.e. some stored configuration puts *at least* as many kings on piles as `c`
does.  Decided against the tables below, all five blocks, exactly. -/

/-- `d` puts (weakly) more kings on piles than `c`. -/
def MaskSub (d c : Fin 16) : Prop :=
  (grlex2bits.get d) &&& (grlex2bits.get c) = (grlex2bits.get d)

instance (d c : Fin 16) : Decidable (MaskSub d c) := inferInstanceAs (Decidable (_ = _))

theorem subsetAt_spec_98 : ∀ (T : Fin 2) (c : Fin 16),
    BitSet (subsetAt (98 + T.val)) c ↔
      ∃ i : Fin 1, T.val.testBit i.val = true ∧ MaskSub ⟨15 + i.val, by omega⟩ c := by
  decide

theorem subsetAt_spec_96 : ∀ (T : Fin 2) (c : Fin 16),
    BitSet (subsetAt (96 + T.val)) c ↔
      ∃ i : Fin 1, T.val.testBit i.val = true ∧ MaskSub ⟨0 + i.val, by omega⟩ c := by
  decide

theorem subsetAt_spec_0 : ∀ (T : Fin 16) (c : Fin 16),
    BitSet (subsetAt (0 + T.val)) c ↔
      ∃ i : Fin 4, T.val.testBit i.val = true ∧ MaskSub ⟨11 + i.val, by omega⟩ c := by
  decide

theorem subsetAt_spec_80 : ∀ (T : Fin 16) (c : Fin 16),
    BitSet (subsetAt (80 + T.val)) c ↔
      ∃ i : Fin 4, T.val.testBit i.val = true ∧ MaskSub ⟨1 + i.val, by omega⟩ c := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem subsetAt_spec_16 : ∀ (T : Fin 64) (c : Fin 16),
    BitSet (subsetAt (16 + T.val)) c ↔
      ∃ i : Fin 6, T.val.testBit i.val = true ∧ MaskSub ⟨5 + i.val, by omega⟩ c := by
  decide

/-! ### Consequences

Both are purely combinatorial once the characterization is in hand. -/

/-- **Fewer kings on piles is still covered.**  Membership survives enlarging the
queried mask, because the witness only has to be a sub-assignment. -/
theorem MaskSub.mono {d c c' : Fin 16} (h : MaskSub d c) (hcc : MaskSub c c') :
    MaskSub d c' := by
  revert h hcc; revert d c c'; decide

/-- **The `forcedKings` transport.**  This is why `childSolvable'` is intersected
with `forcedKings` at `Solver.lean:394`.

A lone-king vacate moves the concrete state to a configuration with *more* kings
on piles — a strictly smaller mask, in a different block — while the solver keeps
querying the child expansion at the *parent's* configuration.  That would be
unsound in general.  It is sound here because every surviving witness `d` already
has the forced suits on piles (`forcedKings ⊆ kingOnPileMap su`), so
`mask d ⊆ mask parent` and `mask d ∩ forced = ∅` together give
`mask d ⊆ mask parent \ forced = mask child`. -/
theorem MaskSub.clear_forced (d cp cc fm : Fin 16)
    (hd : (grlex2bits.get d).toNat &&& fm.val = 0)
    (hsub : MaskSub d cp)
    (hcc : ((grlex2bits.get cp).toNat &&& (15 - fm.val)) &&& (grlex2bits.get cc).toNat
           = (grlex2bits.get cp).toNat &&& (15 - fm.val)) :
    MaskSub d cc := by
  revert hd hsub hcc; revert d cp cc fm; decide

/-- Suit-level characterization of `MaskSub`: `d` piles more kings than `c` iff
every suit without a pile in `d` is without one in `c`. -/
theorem MaskSub_iff (d c : Fin 16) :
    MaskSub d c ↔ ∀ su : Suit, CfgBitSet d su → CfgBitSet c su := by
  revert d c; decide

/-! ## The `forcedKings` transport, assembled

`kingStep_transport` is what the per-contribution soundness argument uses: the
recursion queried the child's expansion at the *parent's* configuration `gi`
(`Solver.lean:449-452` shifts by the parent's `shiftValue`), but after a vacate
the child state only `StateMatchesKingConfig`-stands for configurations with the
vacated suits piled, such as the simulation's witness `k'`.  The `&&&
forcedKings` intersection is exactly what lets the bit travel from `gi` to `k'`:
every surviving witness configuration piles all vacated suits, so covering `gi`
(`MaskSub d gi`) upgrades to covering `k'` (`MaskSub d k'`, via `MaskSub_iff`).

First the `subsetAt_spec_*` characterization uniformly over the blocks. -/

/-- Blocks fit in 16 bits: `shiftValue + numBits ≤ 16`. -/
theorem closureInfo_shift_add_numBits (f : Fin 11) :
    (closureInfos.get f).shiftValue.toNat + (closureInfos.get f).numBits.toNat ≤ 16 := by
  fin_cases f <;> decide

theorem closureInfo_numBits_pos (f : Fin 11) :
    1 ≤ (closureInfos.get f).numBits.toNat := by
  fin_cases f <;> decide

theorem globalCfg_val (ci : ClosureInfo) (i : Nat) (h : ci.shiftValue.toNat + i ≤ 15) :
    (globalCfg ci i).val = ci.shiftValue.toNat + i := by
  simp only [globalCfg]
  omega

/-- Converts one block's `subsetAt_spec_*` (a `Fin`-indexed `∃` with an inlined
index proof) into the uniform `globalCfg` phrasing. -/
private theorem spec_exists_conv (sh n : Nat) (ci : ClosureInfo)
    (hsh : ci.shiftValue.toNat = sh) (hn : ci.numBits.toNat = n) (hle : sh + n ≤ 16)
    (T : Nat) (c : Fin 16) (hpf : ∀ i : Fin n, sh + i.val < 16) :
    (∃ i : Fin n, T.testBit i.val = true ∧ MaskSub ⟨sh + i.val, hpf i⟩ c) ↔
    (∃ i : Nat, i < ci.numBits.toNat ∧ T.testBit i = true ∧ MaskSub (globalCfg ci i) c) := by
  subst hsh; subst hn
  constructor
  · rintro ⟨i, hbit, hsub⟩
    refine ⟨i.val, i.isLt, hbit, ?_⟩
    have he : globalCfg ci i.val = ⟨ci.shiftValue.toNat + i.val, hpf i⟩ :=
      Fin.ext (by rw [globalCfg_val ci i.val (by omega)])
    rw [he]; exact hsub
  · rintro ⟨i, hi, hbit, hsub⟩
    refine ⟨⟨i, hi⟩, hbit, ?_⟩
    have he : globalCfg ci i = ⟨ci.shiftValue.toNat + i, hpf ⟨i, hi⟩⟩ :=
      Fin.ext (by rw [globalCfg_val ci i (by omega)])
    rw [← he]; exact hsub

/-- **Uniform `subsetAt` characterization**: over every block, a configuration is
covered iff some set bit of the local mask covers it. -/
theorem subsetAt_spec_block (f : Fin 11) (T : Nat)
    (hT : T < 2 ^ (closureInfos.get f).numBits.toNat) (c : Fin 16) :
    BitSet (subsetAt ((closureInfos.get f).offset.toNat + T)) c ↔
      ∃ i : Nat, i < (closureInfos.get f).numBits.toNat ∧ T.testBit i = true ∧
        MaskSub (globalCfg (closureInfos.get f) i) c := by
  fin_cases f
  · exact (subsetAt_spec_98 ⟨T, hT⟩ c).trans
      (spec_exists_conv 15 1 _ (by decide) (by decide) (by omega) T c (fun i => by omega))
  · exact (subsetAt_spec_0 ⟨T, hT⟩ c).trans
      (spec_exists_conv 11 4 _ (by decide) (by decide) (by omega) T c (fun i => by omega))
  · exact (subsetAt_spec_16 ⟨T, hT⟩ c).trans
      (spec_exists_conv 5 6 _ (by decide) (by decide) (by omega) T c (fun i => by omega))
  · exact (subsetAt_spec_80 ⟨T, hT⟩ c).trans
      (spec_exists_conv 1 4 _ (by decide) (by decide) (by omega) T c (fun i => by omega))
  all_goals
    exact (subsetAt_spec_96 ⟨T, hT⟩ c).trans
      (spec_exists_conv 0 1 _ (by decide) (by decide) (by omega) T c (fun i => by omega))

theorem subsetAt_spec_pos (p : SolverPosType) {T : UInt16} (hT : LocalMask p T) (c : Fin 16) :
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + T.toNat)) c ↔
      ∃ i : Nat, i < (closureInfoOf p).numBits.toNat ∧ T.toNat.testBit i = true ∧
        MaskSub (globalCfg (closureInfoOf p) i) c :=
  subsetAt_spec_block ⟨min p.freePiles.toInt.toNat 10, by omega⟩ T.toNat hT c

/-- **The transport.**  If the parent's configuration `gi` is covered by the
`forcedKings`-intersected child mask, then the simulation's witness `k'` — which
clears, relative to `gi`, only vacated suits — is covered by the full child mask.

This is why the recursion is sound despite querying the child at the parent's
configuration: the surviving witness `d` piles every vacated suit (`d ∈ fk`), so
`d`'s cell-bound suits avoid `FK`; they are cell-bound in `gi` too (`MaskSub d
gi`), hence — not being vacated — still cell-bound in `k'` (`hstep`). -/
theorem kingStep_transport (p' : SolverPosType) {T fk : UInt16} {FK : Finset Suit}
    {gi k' : Fin 16} (hT : LocalMask p' T) (hv : KingVacates FK fk)
    (hstep : ∀ su : Suit, ¬ CfgBitSet k' su → ¬ CfgBitSet gi su ∨ su ∈ FK)
    (hbit : BitSet (subsetAt ((closureInfoOf p').offset.toNat +
        (T &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat)) gi) :
    BitSet (subsetAt ((closureInfoOf p').offset.toNat + T.toNat)) k' := by
  have hble : (closureInfoOf p').shiftValue.toNat + (closureInfoOf p').numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p'.freePiles.toInt.toNat 10, by omega⟩
  have hbpos : 1 ≤ (closureInfoOf p').numBits.toNat :=
    closureInfo_numBits_pos ⟨min p'.freePiles.toInt.toNat 10, by omega⟩
  obtain ⟨i, hi, hbits, hsub⟩ :=
    (subsetAt_spec_pos p' (LocalMask.and_left _ hT) gi).1 hbit
  rw [UInt16.toNat_and, Nat.testBit_and, Bool.and_eq_true] at hbits
  obtain ⟨hbT, hbX⟩ := hbits
  -- bit `i` of `fk >>> shift` is bit `shift + i` of `fk`
  have hfkbit : fk.toNat.testBit ((closureInfoOf p').shiftValue.toNat + i) = true := by
    rwa [UInt16.toNat_shiftRight, UInt8.toNat_toUInt16,
         Nat.mod_eq_of_lt (by omega : (closureInfoOf p').shiftValue.toNat < 16),
         Nat.testBit_shiftRight] at hbX
  -- the witness configuration `d` survives `fk`, so it piles every vacated suit
  have hdfk : BitSet fk (globalCfg (closureInfoOf p') i) := by
    rw [BitSet_toNat, globalCfg_val _ _ (by omega)]
    exact hfkbit
  have hforced := (hv _).1 hdfk
  -- and therefore covers `k'` as well
  have hk' : MaskSub (globalCfg (closureInfoOf p') i) k' := by
    rw [MaskSub_iff]
    intro su hdsu
    by_contra hknot
    rcases hstep su hknot with hgi | hFK
    · exact hgi ((MaskSub_iff _ gi).1 hsub su hdsu)
    · exact hforced su hFK hdsu
  exact (subsetAt_spec_pos p' hT k').2 ⟨i, hi, hbT, hk'⟩

/-- **The transport, as the consumer sees it.**  A whole simulated move — however
many phases it was chained from — carries the recursion's query from the
configuration the move was affordable at to the one the successor state actually
stands for.  Together with `.cfg` this is everything the per-contribution
soundness step needs from the simulation:

```
exact childSound _ _ hsim.cfg (hsim.transport hT hbit)   -- ⊢ Solvable s'
exact (hsim.reach) ▸ …                                   -- ⊢ Solvable s
```
-/
theorem Simulates.transport {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k k' : Fin 16} {FK : Finset Suit} {fk T : UInt16}
    (hsim : Simulates g s p k s' p' k' FK fk) (hT : LocalMask p' T)
    (hbit : BitSet (subsetAt ((closureInfoOf p').offset.toNat +
        (T &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat)) k) :
    BitSet (subsetAt ((closureInfoOf p').offset.toNat + T.toNat)) k' :=
  kingStep_transport p' hT hsim.vacates hsim.bound hbit

/-- **The direction of the step clause is not negotiable.**  It is an *upper*
bound on what `k'` piles — "`k'` piles nothing beyond `gi`'s piles and the
vacated suits" — and the reverse inclusion ("`k'` piles at least `gi`'s piles and
the vacated suits") cannot replace it, even though the simulation's natural
witness satisfies both (it piles exactly `piled gi ∪ FK`).

Witness, in the `freePiles = 2` child block: the surviving configuration `d = 5`
piles `{hearts, spades}`; the parent `gi = 11` piles `{spades}`; the vacated suit
is `hearts`, and `d` does pile it, so `d` survives the `forcedKings`
intersection.  But `k' = 2` piles `{clubs, hearts, spades}` — it satisfies the
flipped clause and yet `d` does not cover it, because of the extra `clubs`.  That
is precisely the swap the intersection is meant to rule out: `d` claims
solvability with `clubs` in the cells, while `k'` has it on a pile. -/
theorem kingStep_flipped_insufficient :
    ∃ (d gi k' : Fin 16) (FK : Finset Suit),
      -- `d` survives the `forcedKings` intersection: it piles every vacated suit
      (∀ su ∈ FK, ¬ CfgBitSet d su) ∧
      -- `d` covers the parent's configuration
      MaskSub d gi ∧
      -- the *flipped* clause holds: `k'` piles everything `gi` piles, plus `FK`
      (∀ su : Suit, (su ∈ FK ∨ ¬ CfgBitSet gi su) → ¬ CfgBitSet k' su) ∧
      -- and yet `d` fails to cover `k'`, so the transport's goal is out of reach
      ¬ MaskSub d k' :=
  ⟨5, 11, 2, {Suit.hearts}, by decide, by decide, by decide, by decide⟩

/-! ## `componentTable` fits its blocks

Needed to thread `LocalMask` through `solverRecCheckSolvable`'s accumulator: the
`component` contribution is a `componentTable` entry, which never has bits above
its block's width. -/

private theorem compBound_98 : ∀ j : Fin 2,
    (componentTable.get ⟨98 + j.val, by omega⟩).toNat < 16 := by decide
private theorem compBound_0 : ∀ j : Fin 16,
    (componentTable.get ⟨0 + j.val, by omega⟩).toNat < 64 := by decide
private theorem compBound_16 : ∀ j : Fin 64,
    (componentTable.get ⟨16 + j.val, by omega⟩).toNat < 16 := by decide
private theorem compBound_80 : ∀ j : Fin 16,
    (componentTable.get ⟨80 + j.val, by omega⟩).toNat < 2 := by decide
private theorem compBound_96 : ∀ j : Fin 2,
    (componentTable.get ⟨96 + j.val, by omega⟩).toNat < 2 := by decide

/-- Note the off-by-one: `computeComponentKingBits` indexes `componentTable`
through `closureInfos[emptyPiles - 1]` — the loop enumerates the block one
*below* the position's — but the returned value is a local mask of the
position's own block.  So block `f`'s component entries are bounded by block
`f + 1`'s width; instantiate at `f := freePiles - 1` to get `LocalMask` for the
`component` contribution. -/
theorem componentTable_localBound (f : Fin 11) (hf : f.val < 10) (j : Nat)
    (hj : j < 2 ^ (closureInfos.get f).numBits.toNat)
    (hidx : (closureInfos.get f).offset.toNat + j < 100) :
    (componentTable.get ⟨(closureInfos.get f).offset.toNat + j, hidx⟩).toNat
      < 2 ^ (closureInfos.get ⟨f.val + 1, by omega⟩).numBits.toNat := by
  fin_cases f
  · exact compBound_98 ⟨j, hj⟩
  · exact compBound_0 ⟨j, hj⟩
  · exact compBound_16 ⟨j, hj⟩
  · exact compBound_80 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact compBound_96 ⟨j, hj⟩
  · exact absurd hf (by decide)

/-! ## King spaces -/

/-- **How many suits get a king pile**: as many as there are free piles, capped
at four.  This is the quantity `closureInfos` is really indexed by. -/
def numPiledKings (p : SolverPosType) : Nat := min p.freePiles.toInt.toNat 4

theorem numPiledKings_eq (p : SolverPosType) :
    min (min p.freePiles.toInt.toNat 10) 4 = numPiledKings p := by
  unfold numPiledKings; omega

/-- The block for `f` free piles has one bit per way of choosing which
`min f 4` suits get a pile. -/
theorem closureInfo_numBits (f : Fin 11) :
    (closureInfos.get f).numBits.toNat = Nat.choose 4 (min f.val 4) := by
  fin_cases f <;> decide

theorem closureInfoOf_numBits (p : SolverPosType) :
    (closureInfoOf p).numBits.toNat = Nat.choose 4 (numPiledKings p) := by
  unfold closureInfoOf
  rw [closureInfo_numBits ⟨min p.freePiles.toInt.toNat 10, by omega⟩]
  congr 1
  exact numPiledKings_eq p

/-- The refund `computeKingSpaces` grants configuration `k`: for every suit `k`
puts on a pile, its whole freed king stack stops being charged to the cells. -/
def kingRefund (p : SolverPosType) (k : Fin 16) : Int :=
  ((List.finRange 4).map (fun su =>
    if (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0
    then ((13 : Int) - (VALUE (p.kings.get su)).toNat) else 0)).sum

/-- Free extra cells under king configuration `k`. -/
def freeCellsOf (p : SolverPosType) (k : Fin 16) : Int :=
  4 - (p.usedSpace.toInt - kingRefund p k)

/-- **The king-space table is the right one for this position.**  Bit `i` of
`possibleKings[c]` says that local configuration `i` of `p`'s block leaves at
least `c` free cells — the whole content of `computeKingSpaces`, and the
precondition every reader of a `KingInfo` needs (`solverGetMovable` above all).

Stated on `(p, ki)` alone, deliberately: unlike the run equation
`computeKingSpaces … g = .ok ki g` it mentions no `Globals`, so it survives the
memo writes the pile loop performs without any transport lemma. -/
def KingInfoCorrect (p : SolverPosType) (ki : KingInfo) : Prop :=
  ∀ (c : Nat) (hc : c < 6) (i : Nat) (hi : i < (closureInfoOf p).numBits.toNat),
    BitSet (ki.possibleKings.get ⟨c, hc⟩).toUInt16 ⟨min i 15, by omega⟩
      ↔ (c : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i)

/-- **What `computeKingSpaces` computes**: `KingInfoCorrect`, plus the top entry.

`possibleKings[5] = 0` is *not* automatic — it needs every configuration in the
block to leave at most four free cells, i.e. `0 ≤ usedSpace - kingRefund`.  With
a negative effective `usedSpace` the loop would set bit 5 (and at `≤ -2` it runs
off the end of the vector, which is why the run succeeding is a hypothesis).
That entry exists so `solverGetMovable` can index `possibleKings` at `fluteLen`
for `fluteLen = 5` — a five-card flute can never go to `EXTRA`, nor to a king
pile that does not already exist — without a separate case.

`SolverInvBase` is needed for a narrow but real reason: the loop computes each
refund as `Int32.ofNat (13 - VALUE kings[su])` — a **`Nat`** subtraction, which
truncates at zero — while `kingRefund` subtracts in `Int`.  The two agree exactly
when `VALUE kings[su] ≤ 13`, which is `aces_kings_valid`.  (Proved:
`kingSpaces_spec` in `ComputeKingSpaces`.) -/
def KingSpacesSpec : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (ki : KingInfo),
    SolverInvBase g p →
    EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
                   (closureInfoOf p).numBits p) g = .ok ki g →
    KingInfoCorrect p ki
    ∧ ((∀ i : Nat, i < (closureInfoOf p).numBits.toNat →
          freeCellsOf p (globalCfg (closureInfoOf p) i) ≤ 4) →
        ki.possibleKings.get 5 = 0)

/-! ## (3) Move simulation

Stated here rather than beside `SubsetSound`/`ComponentSound` because it needs
`KingInfoCorrect`: the mask `solverGetMovable` returns is meaningless unless the
`KingInfo` it read really is this position's. -/

/-- **(3) Move simulation.**  One abstract `SolverMove` — flute move, cleanup,
and the `busyAces` drain — is realized by a sequence of legal `Rules` moves,
provided the move is affordable in `s`'s configuration (`solverGetMovable`).
The pieces are already built: `run_fluteMoves` / `run_fluteToCells` for the flute,
`CPStep` for the freed-predecessor absorption, `PlaysAll` for the drain.

Three hypotheses pin down what the solver actually asked for, and none of them is
optional:

* `KingInfoCorrect p kingInfo` — otherwise `BitSet mv` certifies nothing, since
  `kingInfo` would be an arbitrary table.
* `hpile`/`hdepth`/`hdest` — the destination is the one `solverGetDestination`
  computed for a **non-empty** pile.  `SolverMove` itself validates nothing: it
  writes the bookkeeping and succeeds for *any* `toPile < 14`, so its run alone
  admits a successor `p'` that no state matches, and the conclusion would be
  false.  `destValid_of_getDest` turns `hdest` into the `MoveValid`/`DestValid`
  that `Simulates.move` consumes.

The witness configuration `k'` is **existential** and must be: a `∀ k'` version
is false, because a suit whose run drains entirely to the foundation may or may
not be read as claiming a spare empty pile (`OwnsPile`'s second disjunct — the
pile carries no card, so even `no_pile` cannot exclude the claim).  The
simulation *chooses* `k'`: `k` with exactly the vacated suits `FK` cleared,
each newly owning its vacated pile.

The last clause is an **upper bound** on what `k'` piles:

> `piled k' ⊆ piled gi ∪ FK`

read off bit-wise, "a suit piled in `k'` was already piled in `gi` or was
vacated".  It is what `kingStep_transport` consumes, and the direction matters:
the surviving witness `d` is known to pile `piled gi` (it covers `gi`) and `FK`
(it survived the `forcedKings` intersection), so bounding `piled k'` by that
union is exactly what makes `d` cover `k'` too.  The reverse inclusion is *also*
true of the natural witness — which piles exactly `piled gi ∪ FK` — but is
useless here, and `kingStep_flipped_insufficient` exhibits a concrete `d`, `gi`,
`k'` refuting the flipped version.

Note the interplay with the ∃: the simulation is *obliged* to pile the vacated
suits (their runs are physically on piles, so `no_pile` forbids setting those
bits), and that obligation is what makes the `FK` escape hatch necessary in the
first place; the freedom the ∃ buys is only for suits that need not be read as
piled — which `RealizesKingConfig.mono` is there to shrink away.

`i` is a **local** bit index and must be bounded by the block width, as in
`SubsetSound`/`ComponentSound`: `globalCfg` clamps at 15, so without `hi` the
statement would silently be about configuration 15 instead of about `i`, and no
proof could recover `globalCfg … i = shiftValue + i` (`globalCfg_val`). -/
def MoveSimulated : Prop :=
  ∀ (g : Globals) (s : State) (p p' : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (fk mv : UInt16) (kingInfo : KingInfo) (i : Nat),
    i < (closureInfoOf p).numBits.toNat →
    WellFormedLayout g → IsCanonicalPos g p →
    StateMatchesKingConfig g s p (globalCfg (closureInfoOf p) i) →
    KingInfoCorrect p kingInfo →
    pile.toNat < 10 →
    0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat →
    EStateM.run (solverGetDestination p pile) g = .ok toPile g →
    EStateM.run (solverGetMovable kingInfo (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g →
    BitSet mv ⟨min i 15, by omega⟩ →
    EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p') →
    ∃ (s' : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g s p (globalCfg (closureInfoOf p) i) s' p' k' FK fk
