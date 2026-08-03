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

What is left is four semantic obligations, stated at the end as named `Prop`s:
`SubsetSound`, `ComponentSound`, `MoveSimulated`, `ForcedKingsTransport`.

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
  is intersected with `forcedKings`, and `MaskSub.clear_forced` is the lemma that
  makes it go through.
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

/-- A local bitmask is one that fits in its block. -/
def LocalMask (p : SolverPosType) (v : UInt16) : Prop :=
  v.toNat < 2 ^ (closureInfoOf p).numBits.toNat

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

/-! ## The loop invariant -/

/-- The soundness half of `SolvableBits`: a set bit really does mean solvable. -/
def SoundBits (g : Globals) (p : SolverPosType) (v : UInt16) : Prop :=
  ∀ (s : State) (k : Fin 16), StateMatchesSolverPos g s p → RealizesKingConfig s p k →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) k → Solvable s

/-- **Base case** of the loop: the accumulator starts at `0`, whose expansion is
empty in every block, so the invariant holds vacuously. -/
theorem SoundBits.zero (g : Globals) (p : SolverPosType) : SoundBits g p 0 := by
  intro s _ _ _ hbit
  rw [subsetAt_zero_pos p] at hbit
  exact absurd hbit (BitSet_zero _)

/-- **Inductive step** of the loop: soundness is closed under union of local
masks.  This is what additivity buys — the whole loop reduces to establishing
`SoundBits g p movable''` for one contribution at a time. -/
theorem SoundBits.union {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b)
    (ha : SoundBits g p a) (hb : SoundBits g p b) : SoundBits g p (a ||| b) := by
  intro s k hs hk hbit
  rw [subsetAt_or_pos p hla hlb, BitSet_or] at hbit
  rcases hbit with h | h
  · exact ha s k hs hk h
  · exact hb s k hs hk h

/-- Soundness is monotone downwards, which is why intersecting with `forcedKings`
(`Solver.lean:394`) is free for this direction: it only shrinks the set. -/
theorem SoundBits.of_sub {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b)
    (hsub : a ||| b = b) (hb : SoundBits g p b) : SoundBits g p a := by
  intro s k hs hk hbit
  refine hb s k hs hk ?_
  rw [← hsub, subsetAt_or_pos p hla hlb, BitSet_or]
  exact Or.inl hbit

/-! ## The remaining semantic obligations

Everything above is proved.  What follows are the four statements the rest of
the argument needs; each is independent of the others. -/

/-- `s` can be brought, by legal moves that change nothing the abstract position
records, to a state realizing king configuration `k`.  Reshuffling king stacks
between the cells and empty piles changes neither depths, flutes, nor
foundations — which is exactly why the same `p` appears on both sides. -/
def KingConfigReachable (g : Globals) (p : SolverPosType) (s : State) (k : Fin 16) : Prop :=
  ∃ s', Reach s s' ∧ StateMatchesSolverPos g s' p ∧ RealizesKingConfig s' p k

/-- The global grlex configuration of local bit `i` of block `ci`. -/
def globalCfg (ci : ClosureInfo) (i : Nat) : Fin 16 :=
  ⟨min (ci.shiftValue.toNat + i) 15, by omega⟩
/-- The suits `fk` forces onto a pile: those whose `kingOnPileMap` entry contains
all of `fk`, i.e. every configuration `fk` still allows has that suit on a pile. -/
def ForcedSuit (fk : UInt16) (su : Suit) : Prop :=
  fk ||| kingOnPileMap.get (finOfSuit su) = kingOnPileMap.get (finOfSuit su)


/-- **(1) `subsetTable` soundness.**  Its expansion means what its name says: if
the expansion of a local set `T` contains a configuration reachable from `s`,
then some configuration *of `T` itself* is reachable from `s`.  Discharging this
requires knowing which king reshuffles are legal at a given free-cell count —
the material in `KingClosure.lean`. -/
def SubsetSound : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (T : UInt16) (c : Fin 16),
    StateMatchesSolverPos g s p → KingConfigReachable g p s c →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + T.toNat)) c →
    ∃ i : Nat, i < (closureInfoOf p).numBits.toNat ∧
      BitSet T ⟨min i 15, by omega⟩ ∧ KingConfigReachable g p s (globalCfg (closureInfoOf p) i)

/-- **(2) Component soundness.**  `computeComponentKingBits` returns a set of
mutually reachable configurations, which is what justifies
`movable'' := movable' ||| component` (`Solver.lean:398`) adding bits. -/
def ComponentSound : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (comp : UInt8) (i j : Nat),
    StateMatchesSolverPos g s p →
    EStateM.run (computeComponentKingBits p) g = .ok comp g →
    i < (closureInfoOf p).numBits.toNat → j < (closureInfoOf p).numBits.toNat →
    BitSet comp.toUInt16 ⟨min i 15, by omega⟩ → BitSet comp.toUInt16 ⟨min j 15, by omega⟩ →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) i) →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) j)

/-- **(3) Move simulation.**  One abstract `SolverMove` — flute move, cleanup,
and the `busyAces` drain — is realized by a sequence of legal `Rules` moves,
provided the move is affordable in `s`'s configuration (`solverGetMovable`).
The pieces are already built: `run_fluteMoves` / `run_fluteToCells` for the flute,
`CPStep` for the freed-predecessor absorption, `PlaysAll` for the drain. -/
def MoveSimulated : Prop :=
  ∀ (g : Globals) (s : State) (p p' : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (fk mv : UInt16) (kingInfo : KingInfo) (i : Nat),
    WellFormedLayout g → IsCanonicalPos g p → StateMatchesSolverPos g s p →
    RealizesKingConfig s p (globalCfg (closureInfoOf p) i) →
    EStateM.run (solverGetMovable kingInfo (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g →
    BitSet mv ⟨min i 15, by omega⟩ →
    EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p') →
    ∃ s', Reach s s' ∧ StateMatchesSolverPos g s' p' ∧
      -- the king-pile bound: no suit gains a pile except the forced ones
      ∀ k' : Fin 16, RealizesKingConfig s' p' k' →
        ∀ su : Suit, ¬ CfgBitSet k' su →
          ¬ CfgBitSet (globalCfg (closureInfoOf p) i) su ∨ ForcedSuit fk su

/-- **(4) Forced-king transport** — the hurdle.  The child is evaluated at the
*parent's* global configuration index (`Solver.lean:396-397` shifts by the
*parent's* `shiftValue`), but a lone-king vacate moves the concrete state into a
different block.  `forcedKings` records exactly which suits were forced onto
piles.  This says the child's real configuration is still covered.

Note the shortcut refuted in the module docstring: this cannot be reduced to
"clearing a bit is harmless". -/
def ForcedKingsTransport : Prop :=
  ∀ (g : Globals) (s s' : State) (p p' : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (fk : UInt16) (T : UInt16) (i : Nat),
    StateMatchesSolverPos g s p → StateMatchesSolverPos g s' p' →
    Reach s s' →
    EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p') →
    RealizesKingConfig s p (globalCfg (closureInfoOf p) i) →
    BitSet (subsetAt ((closureInfoOf p').offset.toNat +
              (T &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat))
           (globalCfg (closureInfoOf p) i) →
    ∀ k' : Fin 16, RealizesKingConfig s' p' k' →
    BitSet (subsetAt ((closureInfoOf p').offset.toNat + T.toNat)) k'

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
    then ((13 : Int) - (VALUE (p.kings.get su).toUInt8).toNat) else 0)).sum

/-- Free extra cells under king configuration `k`. -/
def freeCellsOf (p : SolverPosType) (k : Fin 16) : Int :=
  4 - (p.usedSpace.toInt - kingRefund p k)

/-- **What `computeKingSpaces` computes.**  Bit `i` of `possibleKings[c]` says
that local configuration `i` of `p`'s block leaves at least `c` free cells.

`possibleKings[5] = 0` is *not* automatic — it needs every configuration in the
block to leave at most four free cells, i.e. `0 ≤ usedSpace - kingRefund`.  With
a negative effective `usedSpace` the loop would set bit 5 (and at `≤ -2` it runs
off the end of the vector, which is why the run succeeding is a hypothesis).
That entry exists so `solverGetMovable` can index `possibleKings` at `fluteLen`
for `fluteLen = 5` — a five-card flute can never go to `EXTRA`, nor to a king
pile that does not already exist — without a separate case. -/
def KingSpacesSpec : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (ki : KingInfo),
    EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
                   (closureInfoOf p).numBits p) g = .ok ki g →
    (∀ (c : Nat) (hc : c < 6) (i : Nat) (hi : i < (closureInfoOf p).numBits.toNat),
       BitSet (ki.possibleKings.get ⟨c, hc⟩).toUInt16 ⟨min i 15, by omega⟩
         ↔ (c : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i))
    ∧ ((∀ i : Nat, i < (closureInfoOf p).numBits.toNat →
          freeCellsOf p (globalCfg (closureInfoOf p) i) ≤ 4) →
        ki.possibleKings.get 5 = 0)
