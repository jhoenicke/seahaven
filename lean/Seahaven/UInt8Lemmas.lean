import Seahaven.Solver

/-!
# `UInt8` arithmetic lemmas

`Seahaven.Solver` only needs `UInt8.toInt32` (C's integer promotion) to state the
solver code itself.  The `Int`-valued view `UInt8.toInt` and the lemmas relating
it to `≤`, `<`, `+`, `-` and `toInt32` exist purely for the proofs, so they live
here and are imported by the files that reason about the solver.

The card codec's field accessors are here too, as plain `Nat` arithmetic: they are
what every reader of a card code starts from, and both the solver-side proofs and
the `Rules`-side encoding bridge (`LayoutProofs.encodeCard_SUIT`) need them.
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

/-! ## The card codec, as `Nat` arithmetic

A card code is `suit * 16 + value`.  These three turn the bit operations into the
`/`, `%` and `*` form `omega` can work with. -/

private theorem nat_and_15 (n : Nat) : n &&& 15 = n % 16 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod n 4

theorem VALUE_toNat (c : UInt8) : (VALUE c).toNat = c.toNat % 16 := by
  simp [VALUE, UInt8.toNat_and, nat_and_15]

theorem SUIT_toNat (c : UInt8) : (SUIT c).toNat = c.toNat / 16 := by
  simp [SUIT, Nat.shiftRight_eq_div_pow]

/-- `c` is a **real card**: suit in `0..3`, value in `1..13`.  (Consequently
    `c.toNat ≤ 3*16+13 = 61 < 64`, so it is a valid `card2*` index.)

    Here rather than beside the solver invariant because both sides of the codec
    need it: the solver-side proofs as the domain of `WellFormedLayout`, and the
    `Rules`-side bridge as the image of `encodeCard`. -/
def IsRealCard (c : UInt8) : Prop :=
  (SUIT c).toNat < 4 ∧ 1 ≤ (VALUE c).toNat ∧ (VALUE c).toNat ≤ 13

instance (c : UInt8) : Decidable (IsRealCard c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A real card's code is a valid `card2*` index. -/
theorem IsRealCard_lt64 {c : UInt8} (h : IsRealCard c) : c.toNat < 64 := by
  have h1 := h.1
  have h2 := h.2.2
  have h3 := SUIT_toNat c
  have h4 := VALUE_toNat c
  omega

/-- `CARD s v` as raw `Nat` arithmetic, wrap-free for `s<16, v<16`. -/
theorem CARD_toNat {s v : Nat} (hs : s < 16) (hv : v < 16) :
    (CARD (UInt8.ofNat s) (UInt8.ofNat v)).toNat = s * 16 + v := by
  unfold CARD
  rw [UInt8.toNat_add, UInt8.toNat_shiftLeft]
  have h1 : (UInt8.ofNat s).toNat = s := by rw [UInt8.toNat_ofNat']; omega
  have h2 : (UInt8.ofNat v).toNat = v := by rw [UInt8.toNat_ofNat']; omega
  rw [h1, h2, show ((4:UInt8).toNat % 8 = 4) from by decide, Nat.shiftLeft_eq]
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
