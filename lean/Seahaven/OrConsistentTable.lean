import Seahaven.SolvableBits

/-- The subset and component table are or consistent: for a bit mask the value of
    an entry can be computed by oring the entries for the individual bits. -/

def or_consistent {α : Type} [HOr α α α] [OfNat α 0] (n : Nat) (f : Nat → α) : Prop :=
  ∀ a : Fin (2 ^ n), f a = Nat.fold n (fun bit _ acc => acc |||
   if a.val.testBit bit then f (1 <<< bit) else 0) 0

/-- One fold step splits: the `a ||| b` contribution of a bit is the `|||` of the
individual contributions (idempotence of `|||` when the bit is set in both). -/
private theorem or_ite_split (A B c : Nat) (ta tb : Bool) :
    (A ||| B) ||| (if ta || tb then c else 0)
      = (A ||| (if ta then c else 0)) ||| (B ||| (if tb then c else 0)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases ta <;> cases tb <;>
    cases hA : A.testBit i <;> cases hB : B.testBit i <;> cases hc : c.testBit i <;>
    simp [Nat.testBit_or, hA, hB, hc]

private theorem fold_or_distrib (n : Nat) (g : Nat → Nat) (a b : Nat) :
    Nat.fold n (fun bit _ acc => acc ||| if (a ||| b).testBit bit then g bit else 0) 0
  = Nat.fold n (fun bit _ acc => acc ||| if a.testBit bit then g bit else 0) 0
    ||| Nat.fold n (fun bit _ acc => acc ||| if b.testBit bit then g bit else 0) 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Nat.fold_succ]
    rw [ih, Nat.testBit_or]
    exact or_ite_split _ _ _ _ _

/-- `UInt16.toNat` is a `|||`-and-`0` homomorphism, so it commutes with the
bit-decomposition fold. -/
private theorem toNat_fold (n : Nat) (g : Nat → UInt16) (a : Nat) :
    (Nat.fold n (fun bit _ acc => acc ||| if a.testBit bit then g (1 <<< bit) else 0) (0:UInt16)).toNat
  = Nat.fold n (fun bit _ acc => acc ||| if a.testBit bit then (g (1 <<< bit)).toNat else 0) 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [Nat.fold_succ, UInt16.toNat_or, ih, apply_ite UInt16.toNat,
               show ((0:UInt16)).toNat = 0 from rfl]

theorem or_consistent_toNat {n : Nat} {f : Nat → UInt16} (hor : or_consistent n f) :
    or_consistent n (fun a => (f a).toNat) := by
  intro a
  simp only
  rw [hor a]
  exact toNat_fold n f a.val

theorem or_consistent_distributes_or {n : Nat} {f : Nat → Nat} (hor : or_consistent n f) :
    ∀ a b : Fin (2 ^ n), f (a.val ||| b.val) = (f a.val) ||| (f b.val) := by
  intro a b
  have ha : a.val < 2 ^ n := by exact a.isLt
  have hb : b.val < 2 ^ n := by exact b.isLt
  have hab : a.val ||| b.val < 2 ^ n := by
    exact Nat.or_lt_two_pow ha hb
  have h1 := hor ⟨a.val ||| b.val, hab⟩
  simp only at h1
  rw [h1, hor a, hor b]
  exact fold_or_distrib n (fun bit => f (1 <<< bit)) a.val b.val

theorem or_consistent_distributes_or16 {n : Nat} {f : Nat → UInt16} (hor : or_consistent n f) :
    ∀ a b : Fin (2 ^ n), f (a.val ||| b.val) = (f a.val) ||| (f b.val) := by
  intro a b
  have h := or_consistent_distributes_or (or_consistent_toNat hor) a b
  apply UInt16.toNat_inj.mp
  rw [UInt16.toNat_or]
  exact h

/-- `testBit` of the bit-decomposition fold: exactly the set bits contribute. -/
private theorem testBit_fold (n : Nat) (g : Nat → Nat) (a c : Nat) :
    (Nat.fold n (fun bit _ acc => acc ||| if a.testBit bit then g (1 <<< bit) else 0) 0).testBit c
        = true
      ↔ ∃ i : Fin n, a.testBit i.val = true ∧ (g (1 <<< i.val)).testBit c = true := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Nat.fold_succ, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, ht, hb⟩ | h)
      · exact ⟨i.castSucc, ht, hb⟩
      · by_cases ht : a.testBit m
        · rw [if_pos ht] at h
          exact ⟨Fin.last m, ht, h⟩
        · rw [if_neg ht] at h
          simp at h
    · rintro ⟨i, ht, hb⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 i.isLt with hlt | heq
      · exact Or.inl ⟨⟨i.val, hlt⟩, ht, hb⟩
      · rw [heq] at ht hb
        right
        rw [if_pos ht]
        exact hb

/-- **The point of `or_consistent`**: one bit of one entry only ever depends on the
entries of the *single* index bits, so a table specification costs `n` cases per
queried bit instead of `2 ^ n`. -/
theorem or_consistent_testBit {n : Nat} {f : Nat → Nat} (hor : or_consistent n f)
    (T : Fin (2 ^ n)) (c : Nat) :
    (f T.val).testBit c = true ↔
      ∃ i : Fin n, T.val.testBit i.val = true ∧ (f (2 ^ i.val)).testBit c = true := by
  rw [hor T, testBit_fold]
  simp only [Nat.one_shiftLeft]

/-- **A width bound is per bit too.**  An entry is the `|||` of its single-bit
entries, and `|||` cannot leave a bit range — so bounding the `n` single-bit entries
bounds all `2 ^ n` of them.  (Note this does *not* follow from a table's
specification: a specification quantifies over the *in-range* bits, and says nothing
about the bits this rules out.) -/
theorem or_consistent_lt_two_pow {n m : Nat} {f : Nat → Nat} (hor : or_consistent n f)
    (h : ∀ i : Fin n, f (2 ^ i.val) < 2 ^ m) (T : Fin (2 ^ n)) : f T.val < 2 ^ m := by
  refine Nat.lt_pow_two_of_testBit _ (fun b hb => ?_)
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  obtain ⟨i, -, hbit⟩ := (or_consistent_testBit hor T b).1 hcon
  rw [Nat.testBit_lt_two_pow
    (lt_of_lt_of_le (h i) (Nat.pow_le_pow_right (by omega) hb))] at hbit
  exact absurd hbit (by simp)

theorem or_consistent_spec {n : Nat} {f : Nat → UInt16} (hor: or_consistent n f) :
  ∀ (T : Fin (2 ^ n)) (c : Fin 16),
    BitSet (f T.val) c ↔
      ∃ i : Fin n, T.val.testBit i.val = true ∧ BitSet (f (2 ^ i.val)) c := by
  intro T c
  simp only [BitSet_toNat]
  exact or_consistent_testBit (or_consistent_toNat hor) T c.val
