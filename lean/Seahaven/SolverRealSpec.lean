import Seahaven.Solver
import Seahaven.EStateMTail

/-!
# Specs proved directly against the real solver (no fuel model)

On Lean 4.31 the real solver's `while` loops are no longer opaque (see
`Seahaven.EStateMTail`), so we can state and prove specifications directly about
`_root_.SolverCleanupPile` etc., instead of going through the `SolverModel` fuel
twin and a (fragile, fuel-dependent) `model = real` equality.

This file seeds that approach.  `cleanupPile_empty` is a *complete* proof (only
the standard `propext/Classical.choice/Quot.sound` axioms — no `sorry`) about the
real function: it is the base case of the convert cleanup loop.
-/

-- **Base case of `SolverCleanupPile`.**  Cleaning an already-empty pile
-- (`pileDepth[pile] = 0`) succeeds without running either `while` loop: it leaves
-- `globals` unchanged and returns `0xffff`.
set_option linter.unusedSimpArgs false in
theorem cleanupPile_empty (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hd : p.pileDepth[pile.toNat]'(by omega) = 0) :
    ∃ p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff (g, p') := by
  unfold SolverCleanupPile
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.set, EStateM.pure, Vector.getE, Vector.setE, getElem?_pos, hpile, hd, dif_pos]
  exact ⟨_, rfl⟩
