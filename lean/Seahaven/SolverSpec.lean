import Seahaven.SolverInvariant
import Seahaven.SolverModel

/-!
# Specs: the model canonicalization functions establish the invariant tower

Each theorem says: run the corresponding `SolverModel` function on a state
satisfying a precondition, and it succeeds (`.ok`, no `Error` thrown), leaving
`globals` unchanged and producing a `SolverPosType` satisfying the postcondition.

All proofs are `sorry` at this stage — they are Stage 2+ work (unfold the fuel
recursion, do induction, discharge the arithmetic).  The value here is the
*shape*: exactly which layer of the tower each function establishes.

Several preconditions (`CleanupPre`, `MoveValid`) are still approximate and
flagged `TODO refine` — the exact conditions will be pinned down against the
recursion during the proofs (as anticipated in `VerificationPlan.md`).
-/

namespace SolverSpec

open SolverModel

-- ---------------------------------------------------------------------------
-- Auxiliary preconditions (approximate; refined during the proofs)
-- ---------------------------------------------------------------------------

/-- All ten pile depths in the input vector are `≤ 5` (a legal deal). -/
def ValidDepths (pk : Vector UInt8 11) : Prop :=
  ∀ i : Fin 10, (pk.get ⟨i.val, by omega⟩).toNat ≤ 5

/-- **TODO refine.** Validity precondition for `SolverMove pile toPile`: the pile
    is non-empty, the destination is a legal target, and the move the solver is
    about to make is one it actually considers (flute length fits, etc.).  The
    exact conditions (mirroring `solverGetMovable`) will be pinned down during the
    soundness proof. -/
def MoveValid (_g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8) : Prop :=
  pile.toNat < 10 ∧ toPile.toNat ≤ 14 ∧ (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNatClampNeg > 0

-- ---------------------------------------------------------------------------
-- Specs
-- ---------------------------------------------------------------------------

/-- **`SolverCleanupPile` — one step of the convert cleanup loop.**  Given the
    loop invariant `MergedUpTo g p k` (base holds everywhere; piles below `k`
    already merged; pile `k` still raw), cleaning pile `k` succeeds, leaves
    `globals` and the other piles' depths untouched, and re-establishes the
    invariant with one more pile merged.

    TODO refine: the invariant may need strengthening to survive the way
    decreasing `pileDepth[k]` can free a predecessor card of an already-merged
    pile (`flute_maximal` of piles `< k` depends on cross-pile freeness). -/
theorem solverCleanupPile_step (g : Globals) (p : SolverPosType) (k : Nat) (hk : k < 10)
    (hwf : WellFormedLayout g) (hpre : MergedUpTo g p k) :
    ∃ fk p', EStateM.run (SolverModel.SolverCleanupPile (UInt32.ofNat k)) (g, p) = .ok fk (g, p') ∧
      MergedUpTo g p' (k + 1) ∧
      (∀ j : Fin 10, j.val ≠ k → p'.pileDepth.get j = p.pileDepth.get j) := by
  sorry

/-- **`SolverRemoveFlute` — remove the top flute of a merged pile, then clean it.**
    From a canonical-except-drain state, removing pile `pile`'s flute (the caller
    step of a solver move) and cleaning it yields a state that is again
    `SolverInvMerged` for that pile and preserves it elsewhere.

    TODO refine: precondition/postcondition to be stated in terms of the exact
    per-pile transition; here we assert only success and preservation of the base
    layer. -/
theorem solverRemoveFlute_merged (g : Globals) (p : SolverPosType) (pile : UInt32)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p) (hpile : pile.toNat < 10) :
    ∃ fk p', EStateM.run (SolverModel.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      SolverInvBase g p' := by
  sorry

/-- **`SolverMoveAces` — one foundation advance.**  From a merged state with a
    pending foundation move (`busyAces ≠ 0`), advancing one suit succeeds and
    returns to a merged state.  Iterating this (the `while busyAces ≠ 0` drain)
    reaches `IsCanonicalPos` — see `drain_canonical`. -/
theorem solverMoveAces_merged (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) (hbusy : p.busyAces ≠ 0) :
    ∃ fk p', EStateM.run SolverModel.SolverMoveAces (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' := by
  sorry

/-- **The drain loop reaches canonical form.**  From a merged state, draining
    `busyAces` (via `drainLoop`, with enough fuel) yields a fully canonical state. -/
theorem drain_canonical (g : Globals) (p : SolverPosType) (fk0 : UInt16)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) :
    ∃ fk p', EStateM.run (SolverModel.drainLoop 64 fk0) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

/-- **`SolverMove` preserves canonical form.**  From a canonical state, a valid
    solver move yields another canonical state (this is the per-node invariant
    maintenance behind the soundness proof). -/
theorem solverMove_canonical (g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p) (hvalid : MoveValid g p pile toPile) :
    ∃ fk p', EStateM.run (SolverModel.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

/-- **`SolverConvertFromPilesKings` produces a canonical state.**  Given a
    well-formed layout and a legal pile-depth vector, converting from the empty
    position yields a canonical `SolverPosType` (for any starting position — the
    function overwrites all fields). -/
theorem solverConvert_canonical (g : Globals) (p0 : SolverPosType) (pk : Vector UInt8 11)
    (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    ∃ fk p', EStateM.run (SolverModel.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

end SolverSpec
