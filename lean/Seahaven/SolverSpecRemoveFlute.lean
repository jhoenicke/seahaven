import Seahaven.SolverSpecCleanupPile

/-!
# Spec for `removeFlute`

`removeFlute` is `cleanupPile`'s composed-flute-removal counterpart; this file
reduces its `PileBase`/`PileMerged` preservation facts to the `cleanupPile`
ones via the exact reduction `removeFlute_eq` (from `SolverRealSpec`).
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **`SolverRemoveFlute` preserves the base layer.**  Direct corollary of
    `cleanupPile_baseNF` via the exact reduction `removeFlute_eq`: the
    precondition is stated at the composed point — depth and hash already
    decremented (`removeFlutePre`), stale flute normalized (`fluteNorm`).  At
    exactly this state the `usedSpace` ledger balances and the caller-side
    anomalies vanish (a destination flute extended by `SolverMove` is valid once
    the source depth is decremented; an `aces` advanced by `SolverMoveAces` no
    longer conflicts with the normalized flute). -/
theorem removeFlute_base (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile (removeFlutePre pile hpile p))) :
    ∃ fk p', EStateM.run (_root_.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      SolverInvBase g p' := by
  rw [removeFlute_eq pile g p hpile]
  exact cleanupPile_base pile g (removeFlutePre pile hpile p) hpile hwf hnf

/-- **`SolverRemoveFlute` re-establishes the Merged layer** from the midpoint
    predicate at the composed point (see `removeFlute_baseNF` for why the
    composed state is the right place). -/
theorem removeFlute_merged (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hready : CleanupReady g (fluteNorm pile hpile (removeFlutePre pile hpile p)) pile) :
    ∃ fk p', EStateM.run (_root_.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' ∧ p'.aces = p.aces ∧
      (∀ mask : UInt8, p.busyAces &&& mask ≠ 0 → p'.busyAces &&& mask ≠ 0) := by
  rw [removeFlute_eq pile g p hpile]
  obtain ⟨fk, p', hrun, hinv', haces, hbusyMono⟩ :=
    cleanupPile_merged pile g (removeFlutePre pile hpile p) hpile hwf hready
  have hbusyEq : (removeFlutePre pile hpile p).busyAces = p.busyAces := by
    simp only [removeFlutePre]
  refine ⟨fk, p', hrun, hinv', haces, fun mask hmask => hbusyMono mask ?_⟩
  rwa [hbusyEq]

end SolverSpec
