import Seahaven.Solver

/-!
# `UInt8` arithmetic lemmas

`Seahaven.Solver` only needs `UInt8.toInt32` (C's integer promotion) to state the
solver code itself.  The `Int`-valued view `UInt8.toInt` and the lemmas relating
it to `≤`, `<`, `+`, `-` and `toInt32` exist purely for the proofs, so they live
here and are imported by the files that reason about the solver.
-/

/-- The mathematical value of a `uint8_t`. -/
abbrev UInt8.toInt (x : UInt8) : Int := (x.toNat : Int)

@[simp] theorem UInt8.toInt_eq (x : UInt8) : x.toInt = (x.toNat : Int) := rfl
@[simp] theorem UInt8.toInt_toNat (x : UInt8) : x.toInt.toNat = x.toNat := rfl
@[simp] theorem UInt8.toInt_nonneg (x : UInt8) : 0 ≤ x.toInt := Int.natCast_nonneg _

@[simp] theorem UInt8.toInt_inj {a b : UInt8} : a.toInt = b.toInt ↔ a = b := by
  constructor
  · intro h
    have : a.toNat = b.toNat := by
      have := h; simp only [UInt8.toInt] at this; omega
    exact UInt8.toNat_inj.mp this
  · rintro rfl; rfl

theorem UInt8.le_iff_toInt_le {a b : UInt8} : a ≤ b ↔ a.toInt ≤ b.toInt := by
  simp [UInt8.toInt, UInt8.le_iff_toNat_le]

theorem UInt8.lt_iff_toInt_lt {a b : UInt8} : a < b ↔ a.toInt < b.toInt := by
  simp [UInt8.toInt, UInt8.lt_iff_toNat_lt]

@[simp] theorem UInt8.toInt_toInt32 (x : UInt8) : x.toInt32.toInt = x.toInt := by
  show (x.toUInt32.toInt32).toInt = _
  have hb : (x.toUInt32.toInt32).toInt = ((x.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
    show (x.toUInt32.toInt32).toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_bmod]; rfl
  have hlt : x.toNat < 256 := x.toNat_lt_size
  rw [hb, UInt8.toNat_toUInt32, Int.bmod_eq_of_le (by omega) (by omega)]

theorem UInt8.sub_sub (a b c : UInt8) : a - b - c = a - (b + c) := by
  apply UInt8.toBitVec_inj.mp; simp [BitVec.sub_sub]

@[simp] theorem UInt8.toInt_one : (1 : UInt8).toInt = 1 := rfl

theorem UInt8.toInt_add (a b : UInt8) : (a + b).toInt = (a.toInt + b.toInt) % 256 := by
  have h : (a + b).toNat = (a.toNat + b.toNat) % 256 := UInt8.toNat_add a b
  simp only [UInt8.toInt, h]
  omega

theorem UInt8.toInt_sub (a b : UInt8) : (a - b).toInt = (a.toInt - b.toInt) % 256 := by
  have h : (a - b).toNat = (2 ^ 8 - b.toNat + a.toNat) % 2 ^ 8 := UInt8.toNat_sub a b
  have hcast : ((2 ^ 8 - b.toNat + a.toNat) % 2 ^ 8 : Nat) =
      ((2 ^ 8 - b.toNat + a.toNat : Nat) : Int) % (2 ^ 8 : Int) := by
    exact_mod_cast rfl
  have hbnat : b.toNat < 256 := b.toNat_lt_size
  have hcast2 : ((2 ^ 8 - b.toNat + a.toNat : Nat) : Int) =
      256 - (b.toNat : Int) + (a.toNat : Int) := by omega
  simp only [UInt8.toInt, h, hcast, hcast2]
  omega
