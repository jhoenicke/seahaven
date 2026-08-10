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

/-- **The two halves give `RecCheckSolvableSpec`.**  With `recCheck_sound_of_semantics`
already discharging the soundness half, this is the shape of the endgame: everything
that remains is `RecCheckSolvableComplete`. -/
theorem recCheckSolvableSpec_of (hsound : RecCheckSolvableSound)
    (hcomplete : RecCheckSolvableComplete) : RecCheckSolvableSpec := by
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

/-! ## The semantic hypotheses the recursion will be built against

The soundness development was written against `SubsetSound` / `ComponentSound` /
`MoveSimulated` and only later discharged them.  The same facts are needed in
the opposite direction; naming them here lets the recursion assembly proceed while
the physical arguments are still being written.

The tables themselves are already characterized *bidirectionally* — `subsetAt_spec_pos`
is an `↔`, `KingVacates` is an `↔` by definition and the code's `forcedKings` is proved
to satisfy it, and `component_run_eq` pins the component mask bit-by-bit — so what
these ask for is only the physical half.

**No component obligation is listed.**  The mirror image of `ComponentSound` — two
configurations *reachable from one state* lie in the same component mask — is not what
the recursion needs, and abstract reachability does not supply it: it hands over no
feasible one-suit-smaller configuration for the second of the two.  What the recursion
actually has is two *different* states, the caller's and the critical one, joined by the
winning play's prefix, and the play's own empty-column state is the witness.  That is
`ComponentComplete.cfg_eq_or_component_bits`, proved outright — via "every configuration
with a feasible subset that leaves a column spare is in the component"
(`inComponent_of_hasSpareSubset` + `component_bit_of_inComponent`). -/

/-- **(1) `subsetTable` completeness.**  If a configuration reachable from `s` lies
in a local set `T`, then `s`'s own configuration lies in `T`'s expansion.  The
converse of `SubsetSound`, and the step that lets the parent query the child at its
own configuration. -/
def SubsetComplete : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (T : UInt16) (c : Fin 16) (i : Nat),
    LocalMask p T → WellFormedLayout g → SolverInvMerged g p →
    i < (closureInfoOf p).numBits.toNat →
    BitSet T ⟨min i 15, by omega⟩ →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) i) →
    KingConfigReachable g p s c →
    BitSet (subsetAt ((closureInfoOf p).offset.toNat + T.toNat)) c
