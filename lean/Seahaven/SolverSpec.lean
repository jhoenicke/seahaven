import Seahaven.SolverSpecCommon
import Seahaven.SolverSpecKingMove
import Seahaven.SolverSpecPreCleanupPile
import Seahaven.SolverSpecCleanupPile
import Seahaven.SolverSpecRemoveFlute
import Seahaven.SolverSpecSolverCleanupPile
import Seahaven.SolverSpecMoveAces
import Seahaven.SolverSpecMove
import Seahaven.SolverSpecDrain
import Seahaven.SolverSpecSolverMove
import Seahaven.SolverSpecSolverConvert
import Seahaven.SolverSpecFreedBoundary

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

This file used to hold the entire `SolverSpec` namespace; it has been split
into one file per function under proof (plus a shared auxiliary file), and
now just re-exports them all:

* `SolverSpecCommon` — auxiliary preconditions/definitions and helper lemmas
  shared across the files below.
* `SolverSpecKingMove` — spec for `kingMove`.
* `SolverSpecPreCleanupPile` — spec for `preCleanupPile` (and the older
  `cleanupRunResult`).
* `SolverSpecCleanupPile` — spec for `cleanupPile`.
* `SolverSpecRemoveFlute` — spec for `removeFlute`.
* `SolverSpecSolverCleanupPile` — spec for the monadic `SolverCleanupPile`
  step.
* `SolverSpecMoveAces` — spec for `moveAcesLoop` / `SolverMoveAces`.
* `SolverSpecMove` — spec for the composed `move` step.
* `SolverSpecDrain` — spec for the `busyAces` drain loop.
* `SolverSpecSolverMove` — spec for the top-level `SolverMove` entry point.
* `SolverSpecSolverConvert` — spec for `SolverConvertFromPilesKings`.
* `SolverSpecFreedBoundary` — the freed-loop absorption-range boundary lemma.
-/
