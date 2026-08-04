import Seahaven.SolverSpecDrain

/-!
# Spec for `SolverConvertFromPilesKings`

`solverConvert_canonical`: converting from a legal pile-depth vector (any
starting position — the function overwrites all fields) yields a canonical
`SolverPosType`.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

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
