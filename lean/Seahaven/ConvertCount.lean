import Seahaven.ConvertPre

/-!
# The prologue's space accounting never underflows

`SolverConvertFromPilesKings` computes `usedSpace` by subtracting, from `52`, the
pile depths and then each suit's foundation top.  For the result to be the
`usedSpace_def` value (rather than a wrapped `UInt8`) those two families have to
fit inside the deck:

> `Σ depths + Σ aceVal ≤ 52`   (`CvCountBound`)

They do, because they are *disjoint*: a card still resident on a pile is not free
(`round_trip_inv`), while every card the foundation walk counts is free by
construction.  The proof is the same cardinality injection `usedSpace_bounded`
uses, restricted to two families (the third — flute interiors — is empty here,
every `pileFlute` being `1`).
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## Sums over `Fin n`, as the prefix folds spell them -/

theorem finRange_foldl_eq_sum {n : Nat} (f : Fin n → Nat) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i : Fin n, f i := by
  rw [show (List.finRange n).foldl (fun acc i => acc + f i) 0
        = ((List.finRange n).map f).foldl (·+·) 0 from (List.foldl_map ..).symm,
    list_foldl_add_eq_sum, ← List.ofFn_eq_map, List.sum_ofFn]

theorem cvDepthPrefix_ten (pk : Vector UInt8 11) :
    cvDepthPrefix pk 10 = ∑ i : Fin 10, ((cvDepths pk).get i).toNat := by
  unfold cvDepthPrefix
  rw [List.take_of_length_le (by simp : (List.finRange 10).length ≤ 10)]
  exact finRange_foldl_eq_sum _

theorem cvAcePrefix_four (g : Globals) (d : Vector UInt8 10) :
    cvAcePrefix g d 4 = ∑ s : Fin 4, cvAceVal g d s.val := by
  unfold cvAcePrefix
  rw [List.take_of_length_le (by simp : (List.finRange 4).length ≤ 4)]
  exact finRange_foldl_eq_sum _

/-! ## The two families are disjoint -/

/-- A card still resident on its pile is not free.  (Same argument as
    `depth_card_not_free`, restated over a bare depth vector — the prologue has
    no `SolverInvBase` yet, and that hypothesis is unused there anyway.) -/
theorem depthSlot_not_free (g : Globals) (hwf : WellFormedLayout g) (d : Vector UInt8 10)
    (i : Fin 10) (j : Fin 5) (hj : j.val < (d.get i).toNat) :
    ¬ freeAt g d ((g.pos2card.get i).get j) := by
  have hreal : IsRealCard ((g.pos2card.get i).get j) := hwf.pos2card_real i j
  have h64 : ((g.pos2card.get i).get j).toNat < 64 := by
    have hsn := SUIT_toNat ((g.pos2card.get i).get j)
    have h1 := hreal.1
    omega
  obtain ⟨hpileEq, hdepthEq⟩ := hwf.round_trip_inv i j
  unfold freeAt
  simp only [dif_pos h64]
  have hpileEq' : g.card2pile.get ⟨((g.pos2card.get i).get j).toNat, h64⟩
      = cardPile g ((g.pos2card.get i).get j) := by unfold cardPile; simp [h64]
  have hpile64 : (cardPile g ((g.pos2card.get i).get j)).toNat < 10 :=
    hpileEq' ▸ hwf.card2pile_lt _ h64
  simp only [hpileEq', dif_pos hpile64]
  have hdepthEq' : g.card2depth.get ⟨((g.pos2card.get i).get j).toNat, h64⟩
      = cardDepth g ((g.pos2card.get i).get j) := by unfold cardDepth; simp [h64]
  rw [hdepthEq']
  have hpileI : (⟨(cardPile g ((g.pos2card.get i).get j)).toNat, hpile64⟩ : Fin 10) = i :=
    Fin.ext hpileEq
  rw [show d.get ⟨(cardPile g ((g.pos2card.get i).get j)).toNat, hpile64⟩ = d.get i from
    congrArg d.get hpileI]
  show ¬ (cardDepth g ((g.pos2card.get i).get j)).toNat ≥ (d.get i).toNat
  omega

/-- Every card the foundation walk counts is free. -/
theorem aceSlot_free (g : Globals) (d : Vector UInt8 10) (s : Fin 4) (v : Nat)
    (hv : v < cvAceVal g d s.val) :
    freeAt g d (CARD (UInt8.ofNat s.val) (UInt8.ofNat (v + 1))) :=
  runLen_holds (aceFree g d s.val) 13 v hv

/-! ## The counting injection -/

private def CountDom (g : Globals) (d : Vector UInt8 10) : Type :=
  (Σ _i : Fin 10, Fin (d.get _i).toNat) ⊕ (Σ _s : Fin 4, Fin (cvAceVal g d _s.val))

private instance (g : Globals) (d : Vector UInt8 10) : Fintype (CountDom g d) := by
  unfold CountDom; infer_instance

private def cardOfDom (g : Globals) (d : Vector UInt8 10) : CountDom g d → UInt8
  | .inl ⟨i, j⟩ => if h : j.val < 5 then (g.pos2card.get i).get ⟨j.val, h⟩ else 0
  | .inr ⟨s, v⟩ => CARD (UInt8.ofNat s.val) (UInt8.ofNat (v.val + 1))

set_option maxHeartbeats 1000000 in
private theorem cardOfDom_real (g : Globals) (hwf : WellFormedLayout g) (d : Vector UInt8 10)
    (hd5 : ∀ i : Fin 10, (d.get i).toNat ≤ 5) :
    ∀ x : CountDom g d, IsRealCard (cardOfDom g d x) := by
  intro x
  match x with
  | .inl ⟨i, j⟩ =>
    have hj5 : j.val < 5 := by have := hd5 i; have := j.isLt; omega
    simp only [cardOfDom, dif_pos hj5]
    exact hwf.pos2card_real i ⟨j.val, hj5⟩
  | .inr ⟨s, v⟩ =>
    have hv13 : v.val + 1 ≤ 13 := by
      have := runLen_le (aceFree g d s.val) 13
      have := v.isLt
      have hcv : cvAceVal g d s.val = runLen (aceFree g d s.val) 13 := rfl
      omega
    simp only [cardOfDom]
    refine ⟨?_, ?_, ?_⟩
    · rw [cv_card_suit s.isLt (by omega), UInt8.toNat_ofNat']; omega
    · rw [cv_card_value s.isLt (by omega), UInt8.toNat_ofNat']; omega
    · rw [cv_card_value s.isLt (by omega), UInt8.toNat_ofNat']; omega

set_option maxHeartbeats 1000000 in
private theorem cardOfDom_inj (g : Globals) (hwf : WellFormedLayout g) (d : Vector UInt8 10)
    (hd5 : ∀ i : Fin 10, (d.get i).toNat ≤ 5) :
    Function.Injective (cardOfDom g d) := by
  intro x y hxy
  rcases x with ⟨i, j⟩ | ⟨s, v⟩ <;> rcases y with ⟨i', j'⟩ | ⟨s', v'⟩
  · -- pile slot vs pile slot: `pos2card` is injective across the whole layout
    have hj5 : j.val < 5 := by have := hd5 i; have := j.isLt; omega
    have hj5' : j'.val < 5 := by have := hd5 i'; have := j'.isLt; omega
    simp only [cardOfDom, dif_pos hj5, dif_pos hj5'] at hxy
    obtain ⟨hi, hjv⟩ := hwf.pos2card_inj i i' ⟨j.val, hj5⟩ ⟨j'.val, hj5'⟩ hxy
    subst hi
    have : j = j' := Fin.ext (congrArg Fin.val hjv : (⟨j.val, hj5⟩ : Fin 5).val = _)
    subst this
    rfl
  · -- pile slot vs foundation card: the first is not free, the second is
    exfalso
    have hj5 : j.val < 5 := by have := hd5 i; have := j.isLt; omega
    have hnf := depthSlot_not_free g hwf d i ⟨j.val, hj5⟩ j.isLt
    have hf := aceSlot_free g d s' v'.val v'.isLt
    simp only [cardOfDom, dif_pos hj5] at hxy
    rw [hxy] at hnf
    exact hnf hf
  · exfalso
    have hj5' : j'.val < 5 := by have := hd5 i'; have := j'.isLt; omega
    have hnf := depthSlot_not_free g hwf d i' ⟨j'.val, hj5'⟩ j'.isLt
    have hf := aceSlot_free g d s v.val v.isLt
    simp only [cardOfDom, dif_pos hj5'] at hxy
    rw [← hxy] at hnf
    exact hnf hf
  · -- two foundation cards: `CARD` is injective on the relevant range
    have hb : ∀ (t : Fin 4) (w : Fin (cvAceVal g d t.val)), w.val + 1 ≤ 13 := by
      intro t w
      have := runLen_le (aceFree g d t.val) 13
      have hcv : cvAceVal g d t.val = runLen (aceFree g d t.val) 13 := rfl
      have := w.isLt
      omega
    have h1 : (CARD (UInt8.ofNat s.val) (UInt8.ofNat (v.val + 1))).toNat
        = s.val * 16 + (v.val + 1) := cv_card_toNat s.isLt (by have := hb s v; omega)
    have h2 : (CARD (UInt8.ofNat s'.val) (UInt8.ofNat (v'.val + 1))).toNat
        = s'.val * 16 + (v'.val + 1) := cv_card_toNat s'.isLt (by have := hb s' v'; omega)
    simp only [cardOfDom] at hxy
    have heq := congrArg UInt8.toNat hxy
    rw [h1, h2] at heq
    have hss : s.val = s'.val := by have := hb s v; have := hb s' v'; omega
    have hs : s = s' := Fin.ext hss
    subst hs
    have hvv : v.val = v'.val := by omega
    have : v = v' := Fin.ext hvv
    subst this
    rfl

/-- **The counting bound.** -/
theorem cvCountBound (g : Globals) (hwf : WellFormedLayout g) (pk : Vector UInt8 11)
    (hpk : ValidDepths pk) : CvCountBound g pk := by
  set d := cvDepths pk with hd
  have hd5 : ∀ i : Fin 10, (d.get i).toNat ≤ 5 := by
    intro i; rw [hd, cvDepths_get]; exact hpk i
  have hinj' : Function.Injective (fun x : CountDom g d =>
      (⟨cardOfDom g d x, cardOfDom_real g hwf d hd5 x⟩ : {c : UInt8 // IsRealCard c})) := by
    intro a b hab
    exact cardOfDom_inj g hwf d hd5 (congrArg Subtype.val hab)
  have hle : Fintype.card (CountDom g d) ≤ Fintype.card {c : UInt8 // IsRealCard c} :=
    Fintype.card_le_of_injective _ hinj'
  have hcard52 : Fintype.card {c : UInt8 // IsRealCard c} = 52 :=
    (Fintype.card_subtype IsRealCard).trans RealCardsFinset.card_eq
  have hcardDom : Fintype.card (CountDom g d) =
      (∑ i : Fin 10, (d.get i).toNat) + (∑ s : Fin 4, cvAceVal g d s.val) := by
    have heq : Fintype.card (CountDom g d) = Fintype.card
        ((Σ _i : Fin 10, Fin (d.get _i).toNat) ⊕ (Σ _s : Fin 4, Fin (cvAceVal g d _s.val))) :=
      Fintype.card_congr (Equiv.cast rfl)
    rw [heq]
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rw [hcardDom, hcard52] at hle
  unfold CvCountBound
  rw [cvDepthPrefix_ten pk, cvAcePrefix_four g (cvDepths pk), ← hd]
  exact hle

end SolverSpec
