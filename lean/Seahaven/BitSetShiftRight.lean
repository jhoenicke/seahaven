import Seahaven.SoundnessSkeleton

open Rules
open Solver

/-!
# Reading a bit of a right-shifted mask

`movable'` intersects `movable` with a *global* configuration set shifted down by
the parent's `shiftValue`, so local bit `i` of the result is global bit
`shiftValue + i` — i.e. `globalCfg` — of the set.

Split out on its own (rather than living in `RecStepSound`, where it is also used)
because `GetMovableSpec` needs it too, and `GetMovableSpec` sits upstream of
`RecStepSound` in the import order (`RecStepSound` needs `Phase1Sim`, which needs
`GetMovableSpec`).
-/

/-- Local bit `i` of `w >>> ci.shiftValue` is `w`'s bit at global configuration
`globalCfg ci i`. -/
theorem BitSet_shiftRight_globalCfg (w : UInt16) (ci : ClosureInfo) (i : Nat)
    (hlt : ci.shiftValue.toNat + i < 16) :
    BitSet (w >>> ci.shiftValue.toUInt16) ⟨min i 15, by omega⟩ ↔ BitSet w (globalCfg ci i) := by
  rw [BitSet_toNat, BitSet_toNat, globalCfg_val ci i (by omega), UInt16.toNat_shiftRight,
    UInt8.toNat_toUInt16, Nat.mod_eq_of_lt (show ci.shiftValue.toNat < 16 by omega),
    Nat.testBit_shiftRight,
    show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega)]
