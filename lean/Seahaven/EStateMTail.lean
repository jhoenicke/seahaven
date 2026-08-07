import Seahaven.Solver
import Seahaven.EStateMOrder

/-!
# `MonadTail` for `EStateM`, enabling `while`/`Loop.forIn` reasoning

The instances themselves are generic and now live in `Seahaven.EStateMOrder`, which
sits below `Seahaven.Solver` because `solverRecCheckSolvable` is defined by
`partial_fixpoint` and needs them at its definition site; the `Nonempty Error` /
`Inhabited Globals` witnesses live in `Solver.lean` next to those types.

This file is kept as the name the `Loop.forIn_eq_of_monadTail` clients import: it
pulls in both halves at once.
-/
