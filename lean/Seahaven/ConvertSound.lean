import Seahaven.ConvertInv

/-!
# `SolverConvertFromPilesKings` produces a canonical position

Assembling the three pieces:

* `convert_run_eq` — loops 1 and 2 hand the cleanup loop `convertPre g pk`;
* `convertPre_mergedUpTo_zero` — that position satisfies the cleanup loop's entry
  invariant, and `solverCleanupPile_step` carries it pile by pile to
  `MergedUpTo … 10 = SolverInvMerged`;
* `drain_canonical` — the `busyAces` drain then reaches `IsCanonicalPos`.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## Loop 3: the per-pile cleanup -/

theorem cvCleanupBody_run (i : Nat) (fk fk0 : UInt16) (g : Globals) (q q' : SolverPosType)
    (h : EStateM.run (_root_.SolverCleanupPile (UInt32.ofNat i)) (g, q) = .ok fk0 (g, q')) :
    cvCleanupBody i fk (g, q) = .ok (.yield (fk &&& fk0)) (g, q') := by
  have h' : _root_.SolverCleanupPile (UInt32.ofNat i) (g, q) = .ok fk0 (g, q') := h
  simp only [cvCleanupBody, bind, EStateM.bind, pure, EStateM.pure, h']

/-- **The cleanup loop reaches the merged layer.**  One `solverCleanupPile_step`
    per iteration, carrying `MergedUpTo`. -/
theorem cvCleanupLoop_run (g : Globals) (hwf : WellFormedLayout g) :
    ∀ (n k : Nat), k + n = 10 → ∀ (fk : UInt16) (q : SolverPosType), MergedUpTo g q k →
      ∃ (fk' : UInt16) (q' : SolverPosType),
        forIn (List.range' k n) fk cvCleanupBody (g, q) = .ok fk' (g, q') ∧
        MergedUpTo g q' 10 := by
  intro n
  induction n with
  | zero =>
    intro k hk fk q hq
    obtain rfl : k = 10 := by omega
    exact ⟨fk, q, rfl, hq⟩
  | succ n ih =>
    intro k hk fk q hq
    have hklt : k < 10 := by omega
    obtain ⟨fk0, q1, hrun1, hq1, -⟩ := solverCleanupPile_step g q k hklt hwf hq
    obtain ⟨fk', q', hrun', hq'⟩ := ih (k + 1) (by omega) (fk &&& fk0) q1 hq1
    refine ⟨fk', q', ?_, hq'⟩
    rw [List.range'_succ, List.forIn_cons]
    show (cvCleanupBody k fk >>= _) (g, q) = _
    simp only [bind, EStateM.bind, cvCleanupBody_run k fk fk0 g q q1 hrun1]
    exact hrun'

/-! ## The whole call -/

/-- **`SolverConvertFromPilesKings` produces a canonical state.**  Given a
    well-formed layout and a legal pile-depth vector, converting from any starting
    position (the function overwrites every field) succeeds, leaves `globals`
    untouched, and yields a canonical `SolverPosType`. -/
theorem convert_canonical (g : Globals) (p0 : SolverPosType) (pk : Vector UInt8 11)
    (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    ∃ fk p', EStateM.run (_root_.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  have hcount : CvCountBound g pk := cvCountBound g hwf pk hpk
  -- loop 3
  obtain ⟨fk1, q1, hrun1, hq1⟩ :=
    cvCleanupLoop_run g hwf 10 0 rfl 0xffff (convertPre g pk)
      (convertPre_mergedUpTo_zero g pk hwf hpk)
  have hmerged : SolverInvMerged g q1 := mergedUpTo_ten_iff.mp hq1
  -- loop 4
  obtain ⟨fk2, q2, hrun2, hcan, -⟩ := drain_canonical g q1 fk1 hwf hmerged
  refine ⟨fk2, q2, ?_, hcan⟩
  show _root_.SolverConvertFromPilesKings pk (g, p0) = _
  rw [convert_run_eq g hwf pk p0 hpk hcount]
  show (forIn (List.range 10) (0xffff : UInt16) cvCleanupBody >>= fun fk =>
      Loop.forIn Loop.mk fk drainBody >>= fun r => pure r) (g, convertPre g pk) = _
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    show List.range 10 = List.range' 0 10 from by rw [List.range_eq_range'], hrun1, hrun2]

end SolverSpec
