import Seahaven.RecCheckSound
import Seahaven.DestComplete

/-!
# The completeness spec layer

`SolvableBits`/`HashmapCorrect`/`RecCheckSolvableSpec` (`SolvableBits.lean`) are
stated as *equivalences*.  `RecCheckSound` discharges the `←` half by mirroring
them with `SoundBits`/`HashmapSound`/`RecCheckSolvableSound`; this file sets up the
mirror image for the `→` half, so the two developments can proceed independently
and be recombined at the end (`solvableBits_iff`, `recCheckSolvableSpec_of`).

The shape of the two halves is deliberately different, and it pays to see why
before writing any of the recursion:

* **Soundness is additive.**  `SoundBits` is closed under `|||`
  (`SoundBits.union`), so the pile loop reduces to justifying one contribution at
  a time and the accumulator's history is irrelevant.
* **Completeness is a persistence property.**  There is one *particular* iteration
  — the one that examines the winning move — whose contribution carries the bit,
  and the invariant must carry that bit through every *later* iteration.  What
  makes that work is monotonicity: the loop only ever ORs into the accumulator, and
  `CompleteBits.or_left` says a bit already present survives an OR.  This is the
  completeness counterpart of `SoundBits.union`, and it is the reason the loop's
  early `break` and its `movable &&& ~~~solvable == 0` skip are harmless.

The memo direction is likewise one-sided: a cached read is only ever *used* in the
completeness direction, so `HashmapComplete` is self-maintaining — it never has to
be entangled with `HashmapSound`.
-/

/-! ## The two-sided statement, split -/

/-- `CompleteBits g p v` : the mask `v` **misses no solvable configuration**.  Every
state `p` stands for at configuration `k` which really is solvable has `k`'s bit set
in the `subsetTable` expansion of `v`.  The `→` half of `SolvableBits`. -/
def CompleteBits (g : Globals) (p : SolverPosType) (v : UInt16) : Prop :=
  ∀ (s : State) (k : Fin 16), StateMatchesKingConfig g s p k → Solvable s →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) k

/-- **The stated spec is exactly the two halves.**  Nothing else is needed to
recombine `RecCheckSound`'s result with a completeness development. -/
theorem solvableBits_iff (g : Globals) (p : SolverPosType) (v : UInt16) :
    SolvableBits g p v ↔ (SoundBits g p v ∧ CompleteBits g p v) := by
  constructor
  · intro h
    exact ⟨fun s k hk hbit => (h s k hk).2 hbit, fun s k hk hsol => (h s k hk).1 hsol⟩
  · rintro ⟨hs, hc⟩ s k hk
    exact ⟨fun hsol => hc s k hk hsol, fun hbit => hs s k hk hbit⟩

/-! ## Monotonicity: the persistence lemma the loop runs on -/

/-- **A bit already in the accumulator survives an `|||`.**  The completeness
counterpart of `SoundBits.union`: soundness needs *both* operands to be sound,
completeness needs only *one* of them to carry the bit. -/
theorem BitSet.or_left {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b) {k : Fin 16}
    (h : BitSet (subsetAt ((closureInfoOf p).offset.toNat + a.toNat)) k) :
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + (a ||| b).toNat)) k := by
  rw [subsetAt_or_pos p hla hlb, BitSet_or]
  exact Or.inl h

theorem BitSet.or_right {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b) {k : Fin 16}
    (h : BitSet (subsetAt ((closureInfoOf p).offset.toNat + b.toNat)) k) :
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + (a ||| b).toNat)) k := by
  rw [subsetAt_or_pos p hla hlb, BitSet_or]
  exact Or.inr h

/-- `CompleteBits` is monotone in the mask: once an accumulator is complete, so is
anything it grows into.  This is what makes the loop invariant survive the
iterations *after* the winning one. -/
theorem CompleteBits.or_left {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b) (h : CompleteBits g p a) :
    CompleteBits g p (a ||| b) :=
  fun s k hk hsol => BitSet.or_left hla hlb (h s k hk hsol)

theorem CompleteBits.or_right {g : Globals} {p : SolverPosType} {a b : UInt16}
    (hla : LocalMask p a) (hlb : LocalMask p b) (h : CompleteBits g p b) :
    CompleteBits g p (a ||| b) :=
  fun s k hk hsol => BitSet.or_right hla hlb (h s k hk hsol)

/-- The vacuous case: a position no state realizes is complete for any mask.  (Used
for the loop's `break`, where the remaining configurations are unrealizable.) -/
theorem CompleteBits.of_no_state {g : Globals} {p : SolverPosType} {v : UInt16}
    (h : ∀ (s : State) (k : Fin 16), ¬ StateMatchesKingConfig g s p k) :
    CompleteBits g p v :=
  fun s k hk _ => absurd hk (h s k)

/-- Matching never reads the memo table, so a memo write cannot break completeness
— the frame every write in `solverRecCheckSolvable` needs. -/
theorem CompleteBits.set_hashmap {g : Globals} {p : SolverPosType} {v : UInt16}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : CompleteBits g p v) :
    CompleteBits { g with hashmap := hm } p v :=
  fun s k hk hsol => h s k ((StateMatchesKingConfig.hashmap_iff hm).1 hk) hsol

/-! ## The component is all-or-nothing in the accumulator

The pile loop skips an iteration entirely when `movable &&& ~~~solvable == 0`, and then
the winning move's own bit is *already* in `solvable` — but the bit the caller asked
about need not be, since the two are related only through the component
(`cfg_eq_or_component_bits`).  What closes that hole is a second loop invariant:

> once `solvable` contains **one** bit of `component`, it contains **all** of them.

It holds because `component` is computed once per position, so every iteration's
contribution is either disjoint from it (and then adds no component bit at all) or is
widened to contain it outright — which is precisely what
`movable'' := if movable' &&& component ≠ 0 then movable' ||| component else movable'`
does.  Note the invariant survives the skip and the `break` for free: both leave
`solvable` untouched. -/

/-- Every component bit is in `v`, or none is. -/
def CompAllOrNothing (v comp : UInt16) : Prop :=
  ∀ b c : Fin 16, BitSet comp b → BitSet v b → BitSet comp c → BitSet v c

/-- The loop starts at `solvable = 0`, where it holds vacuously. -/
theorem CompAllOrNothing.zero (comp : UInt16) : CompAllOrNothing 0 comp :=
  fun b _ _ hb _ => absurd hb (BitSet_zero b)

/-- **The widening maintains it.**  Either the contribution meets the component — and is
then widened to contain all of it — or it misses the component entirely, so the only
component bits in the new accumulator are the old ones. -/
theorem CompAllOrNothing.step {v comp : UInt16} (h : CompAllOrNothing v comp) (m : UInt16) :
    CompAllOrNothing (v ||| (if m &&& comp != 0 then m ||| comp else m)) comp := by
  intro b c hcb hvb hcc
  by_cases hc : (m &&& comp != 0) = true
  · rw [if_pos hc]
    exact (BitSet_or _ _ c).2 (Or.inr ((BitSet_or _ _ c).2 (Or.inr hcc)))
  · rw [if_neg hc] at hvb ⊢
    rcases (BitSet_or _ _ b).1 hvb with hb | hb
    · exact (BitSet_or _ _ c).2 (Or.inl (h b c hcb hb hcc))
    · exfalso
      have hz : m &&& comp = 0 := by simpa using hc
      have hmc : BitSet (m &&& comp) b := (BitSet_and m comp b).2 ⟨hb, hcb⟩
      rw [hz] at hmc
      exact BitSet_zero b hmc

/-- **What it is for.**  The winning move's configuration is in `solvable` and shares the
component with the caller's, so the caller's is in `solvable` too — whether or not the
iteration that put it there was the one that ran the move. -/
theorem CompAllOrNothing.transfer {v comp : UInt16} (h : CompAllOrNothing v comp)
    {i j : Fin 16} (hj : BitSet v j) (hcj : BitSet comp j) (hci : BitSet comp i) :
    BitSet v i := h j i hcj hj hci

/-! ## What one iteration does to the accumulator

Both loop invariants the completeness side threads — "a bit already there stays there"
and `CompAllOrNothing` — depend on the body only through this: the iteration either
leaves the accumulator alone (the pile is empty, the mask adds nothing new) or ORs in
one `movableComp`.  Reading that off the code once (`recBody_complete_step`) serves
both. -/

/-- The accumulator's step: unchanged, or grown by one `movableComp`. -/
def AccumStep (comp v v' : UInt16) : Prop :=
  v' = v ∨ ∃ m : UInt16, v' = v ||| movableComp m comp

/-- `movableComp`-spelled `CompAllOrNothing.step`: the code's widening is the `ite`
that lemma is stated with (`movableComp_eq` reconciles the `Bool` guard with the
`Prop` one). -/
theorem CompAllOrNothing.step' {v comp : UInt16} (h : CompAllOrNothing v comp) (m : UInt16) :
    CompAllOrNothing (v ||| movableComp m comp) comp := by
  rw [← movableComp_eq]
  exact h.step m

/-- **The accumulator never loses a bit.** -/
theorem AccumStep.grows {comp v v' : UInt16} (h : AccumStep comp v v') {k : Fin 16}
    (hk : BitSet v k) : BitSet v' k := by
  rcases h with rfl | ⟨m, rfl⟩
  · exact hk
  · exact (BitSet_or _ _ k).2 (Or.inl hk)

/-- **And it keeps `CompAllOrNothing`.**  Either nothing happened, or the contribution
was widened to contain the whole component if it met it at all. -/
theorem AccumStep.allOrNothing {comp v v' : UInt16} (h : AccumStep comp v v')
    (hv : CompAllOrNothing v comp) : CompAllOrNothing v' comp := by
  rcases h with rfl | ⟨m, rfl⟩
  · exact hv
  · exact hv.step' m

/-! ## The contribution reaches the accumulator

Two one-liners that say the loop never *loses* a bit once an iteration has produced it:
the `component` widening only ever adds, and the accumulator only ever `|||`s. -/

/-- The `component` widening keeps every bit `movable'` had. -/
theorem bitSet_movableComp {mv' comp : UInt16} {k : Fin 16} (h : BitSet mv' k) :
    BitSet (movableComp mv' comp) k := by
  unfold movableComp
  split_ifs
  · exact (BitSet_or _ _ k).2 (Or.inl h)
  · exact h

/-- And the accumulator keeps it. -/
theorem bitSet_accum {v mv'' : UInt16} {k : Fin 16} (h : BitSet mv'' k) :
    BitSet (v ||| mv'') k := (BitSet_or _ _ k).2 (Or.inr h)

/-! ## The `hash = 0` leaf

`solverRecCheckSolvable` answers `1` when the hash is zero.  Soundness reads that
as "the position is already solved"; completeness has the easier job — the value `1`
selects the block's *maximal* configuration, whose expansion at `freePiles = 10`
covers every configuration, so no solvable state can be missed. -/

/-- **At ten free piles the mask `1` expands to everything.**  Decided against the
table: the `freePiles = 10` block holds the single configuration that piles all
four suits, and `MaskSub` from it is universally true. -/
theorem subsetAt_one_ten (c : Fin 16) :
    BitSet (subsetAt ((closureInfos.get 10).offset.toNat + 1)) c := by
  revert c; decide

/-- Hence the leaf value is complete for any position with ten free piles — which is
exactly the `hash = 0` case (`hash = 0 → every depth is 0 → freePiles = 10`). -/
theorem completeBits_one_of_freePiles_ten {g : Globals} {p : SolverPosType}
    (hfp : p.freePiles.toNat = 10) : CompleteBits g p 1 := by
  intro s k _ _
  have h : closureInfoOf p = closureInfos.get 10 := by
    unfold closureInfoOf
    congr 1
    exact Fin.ext (by simp [hfp])
  rw [h]
  exact subsetAt_one_ten k

/-! ## The memo invariant

Self-maintaining, and independent of `HashmapSound`: a slot is either free or its
value misses no solvable configuration. -/

def HashmapComplete (g : Globals) : Prop :=
  ∀ (p : SolverPosType), IsCanonicalPos g p →
    ∀ v : UInt8, EStateM.run (getSlot p.hash) g = .ok v g →
      v = UInt8.ofNat FREESLOT ∨ (CompleteBits g p v.toUInt16 ∧ LocalMask p v.toUInt16)

/-! ## The induction hypothesis, completeness side

Mirror of `RecCheckSound.ChildSpec`: what the recursive call is known to satisfy,
guarded by the measure `move_merged` makes drop.

The memo invariant is a parameter `H`, exactly as on the soundness side: the loop
never inspects a slot, it only hands `H` to the recursive call and hands back what
the call returns.  `H := HashmapComplete` gives the standalone completeness
recursion — the invariant is self-maintaining, so that version never has to be
entangled with its dual — and `H := HashmapCorrect` gives the two-sided recursion of
`RecCheckSpec`, where a *single* induction over the depth serves both halves. -/

def ChildSpecComplete (H : Globals → Prop) (p : SolverPosType) : Prop :=
  ∀ (child : SolverPosType) (g₁ g₂ : Globals) (w : UInt16),
    SolverSpec.DepthSum child < SolverSpec.DepthSum p → WellFormedLayout g₁ →
    IsCanonicalPos g₁ child → H g₁ →
    EStateM.run (solverRecCheckSolvable child) g₁ = .ok w g₂ →
    (CompleteBits g₁ child w ∧ LocalMask child w) ∧ H g₂ ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g₂ = { g₁ with hashmap := hm }

/-! ## The statements to discharge

Mirrors of `RecCheckSolvableSound` and of `SolveSpec`'s forward half.  Stated so
that `recCheckSolvableSpec_of` below assembles the two halves into the spec
`SolvableBits.lean` asks for. -/

/-- **What `solverRecCheckSolvable` must satisfy, completeness half.** -/
def RecCheckSolvableComplete : Prop :=
  ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
    WellFormedLayout g → HashmapComplete g → IsCanonicalPos g p →
    EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
    (CompleteBits g p v ∧ LocalMask p v) ∧ HashmapComplete g' ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }

/-! ## Recombination

`HashmapCorrect` is the conjunction of the two memo invariants, so recombining the
two developments is pure bookkeeping. -/

/-- The recombination at the level of one answer. -/
theorem recCheck_spec_of {g : Globals} {p : SolverPosType} {v : UInt16}
    (hs : SoundBits g p v) (hc : CompleteBits g p v) : SolvableBits g p v :=
  (solvableBits_iff g p v).2 ⟨hs, hc⟩

theorem hashmapCorrect_of {g : Globals} (hs : HashmapSound g) (hc : HashmapComplete g) :
    HashmapCorrect g := by
  intro p hcan v hget
  rcases hs p hcan v hget with h | ⟨hsb, hlm⟩
  · exact Or.inl h
  · rcases hc p hcan v hget with h | ⟨hcb, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨recCheck_spec_of hsb hcb, hlm⟩

/-- **The two halves give the specification, at a run.**  Superseded by
`RecCheckSpec.recCheck_spec`, which runs one merged induction instead — and which also
proves the call *returns*, something neither half supplies (both are conditional on
`hrun`).  So this assembles the `RecCheckSolvableSpec.apply` shape, not
`RecCheckSolvableSpec` itself. -/
theorem recCheckSolvableSpec_of (hsound : RecCheckSolvableSound)
    (hcomplete : RecCheckSolvableComplete) :
    ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
      WellFormedLayout g → IsCanonicalPos g p → HashmapCorrect g →
      EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
      (SolvableBits g p v ∧ LocalMask p v) ∧ HashmapCorrect g' ∧
        g'.pos2card = g.pos2card := by
  intro g g' p v hwf hcan hcorrect hrun
  have hs : HashmapSound g := by
    intro q hq w hget
    rcases hcorrect q hq w hget with h | ⟨hsb, hlm⟩
    · exact Or.inl h
    · exact Or.inr ⟨fun s k hk hbit => (hsb s k hk).2 hbit, hlm⟩
  have hc : HashmapComplete g := by
    intro q hq w hget
    rcases hcorrect q hq w hget with h | ⟨hsb, hlm⟩
    · exact Or.inl h
    · exact Or.inr ⟨fun s k hk hsol => (hsb s k hk).1 hsol, hlm⟩
  obtain ⟨⟨hsv, hlv⟩, hs', hframe⟩ := hsound g g' p v ⟨hwf, hs⟩ hcan hrun
  obtain ⟨⟨hcv, -⟩, hc', -⟩ := hcomplete g g' p v hwf hc hcan hrun
  obtain ⟨hm, rfl⟩ := hframe
  exact ⟨⟨recCheck_spec_of hsv hcv, hlv⟩, hashmapCorrect_of hs' hc', rfl⟩

/-! ## No semantic obligation is listed here

The soundness development was written against `SubsetSound` / `ComponentSound` /
`MoveSimulated` and only later discharged them.  Completeness needs **no** counterpart
of the first two, and it is worth recording why, since both mirror images look
plausible and both are wrong.

The tables are already characterized *bidirectionally* — `subsetAt_spec_pos` is an `↔`,
`KingVacates` is an `↔` by definition and the code's `forcedKings` is proved to satisfy
it, `component_run_eq` pins the component mask bit-by-bit — and the `←` directions are
pure arithmetic.  What `SubsetSound` and `ComponentSound` add is the *physical* half,
and completeness does not consume the tables in a direction that needs it.

**No `subsetTable` obligation.** *(refuted shortcut, recorded so it is not tried a third
time.)*  The obvious mirror — "if a configuration reachable from `s` lies in a local set
`T`, then `s`'s own configuration lies in `T`'s expansion" — is **false**.  By
`subsetAt_spec_pos` the expansion covers `c` exactly when some bit `i` of `T` has
`MaskSub (globalCfg ci i) c`, and reachability supplies no such `MaskSub`: at
`freePiles = 1` the block holds four configurations, one per piled suit, and a state
with one empty column and two suits' freed runs in the cells reaches two of them by a
single piling move each — yet neither covers the other (`subsetAt (0 + 1)` does not
cover `globalCfg (closureInfos.get 1) 1`).  Two configurations reachable from one state
say nothing about `MaskSub`; that relation is what the *component* mask records.

What the recursion actually has is stronger and needs no new obligation: the critical
iteration hands over the `MaskSub` witness itself (`CriticalIteration.CriticalBit`), so
the block step is `subsetAt_spec_pos.2` and nothing more.

**No component obligation** either.  The mirror image of `ComponentSound` — two
configurations *reachable from one state* lie in the same component mask — is not what
the recursion needs, and abstract reachability does not supply it: it hands over no
feasible one-suit-smaller configuration for the second of the two.  What the recursion
actually has is two *different* states, the caller's and the critical one, joined by the
winning play's prefix, and the play's own empty-column state is the witness.  That is
`ComponentComplete.cfg_eq_or_component_bits`, proved outright — via "every configuration
with a feasible subset that leaves a column spare is in the component"
(`inComponent_of_hasSpareSubset` + `component_bit_of_inComponent`).

So `RecCheckSpec.RecLoopComplete` assembles out of proved pieces only:

1. `MaximalCfg.exists_block_cfg_maskSub` — a block index `j` above the caller's
   configuration `k`;
2. `critical_loop_bitSet` — a block index `i` above the critical state's `k_t`, with
   `BitSet v ⟨min i 15⟩`, and `CompAllOrNothing v comp` alongside;
3. `cfg_eq_or_component_bits` — either `k = k_t`, and `i` already covers `k`, or both
   bits lie in `comp` and `CompAllOrNothing.transfer` moves the bit from `i` to `j`
   (the guard cases are `block_index_eq_of_freePiles_four` and
   `cfg_eq_of_freePiles_zero`, where `computeComponentKingBits` returns `0`);
4. `subsetAt_spec_pos.2` on the surviving index.

What is left is the plumbing that produces the critical state from the caller's —
`CriticalMove.exists_critical_state` — not a new fact about the tables. -/
