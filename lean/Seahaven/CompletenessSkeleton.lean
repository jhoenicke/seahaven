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
`MoveSimulated` and only later discharged them.  The same three facts are needed in
the opposite direction; naming them here lets the recursion assembly proceed while
the physical arguments are still being written.

The tables themselves are already characterized *bidirectionally* — `subsetAt_spec_pos`
is an `↔`, `KingVacates` is an `↔` by definition and the code's `forcedKings` is proved
to satisfy it, and `component_run_eq` pins the component mask bit-by-bit — so what
these three ask for is only the physical half. -/

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

/-- **(2) Component completeness.**  Two configurations of the same state lie in the
same component mask.  The converse of `ComponentSound`, and what carries the bit
from the configuration the play realizes (`k_t`) back to the one the caller asked
about (`k`). -/
def ComponentComplete : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (comp : UInt8) (i j : Nat),
    WellFormedLayout g → SolverInvMerged g p →
    EStateM.run (computeComponentKingBits p) g = .ok comp g →
    i < (closureInfoOf p).numBits.toNat → j < (closureInfoOf p).numBits.toNat →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) i) →
    KingConfigReachable g p s (globalCfg (closureInfoOf p) j) →
    BitSet comp.toUInt16 ⟨min i 15, by omega⟩ →
    BitSet comp.toUInt16 ⟨min j 15, by omega⟩
