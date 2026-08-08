import Seahaven.SolverSpecDrain
import Seahaven.ConvertSound

/-!
# Spec for `SolverConvertFromPilesKings`

`solverConvert_canonical`: converting from a legal pile-depth vector (any
starting position — the function overwrites all fields) yields a canonical
`SolverPosType`.

The statement is against the **real** `_root_.SolverConvertFromPilesKings` (its
`while` loops are no longer opaque on Lean 4.31 — see `Seahaven.EStateMTail`);
the proof is `ConvertSound.convert_canonical`, which runs the prologue to the
closed form `convertPre`, carries `MergedUpTo` through the per-pile cleanup loop,
and finishes with the `busyAces` drain.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **`SolverConvertFromPilesKings` produces a canonical state.**  Given a
    well-formed layout and a legal pile-depth vector, converting from any starting
    position yields a canonical `SolverPosType`. -/
theorem solverConvert_canonical (g : Globals) (p0 : SolverPosType) (pk : Vector UInt8 11)
    (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    ∃ fk p', EStateM.run (_root_.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' :=
  convert_canonical g p0 pk hwf hpk

end SolverSpec
