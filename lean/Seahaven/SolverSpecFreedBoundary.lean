import Seahaven.SolverSpecCommon

/-!
# Freed-loop absorption-range boundary lemma

`freed_below_other_boundary`: a pile's freed-loop absorption range lies
strictly above any other pile's current boundary that sits below the merge
boundary.  Used by `SolverInvariant.lean`.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **A pile's freed-loop absorption range lies strictly above any other
    pile's current boundary that sits below the merge boundary.**  If pile
    `j`'s boundary `Bj` has smaller raw value than `B` (the boundary the
    freed loop walks down from) and pile `j` is non-empty, then `Bj` lies
    strictly below the *entire* range `[B-f, B-1]` the freed loop absorbs:
    if it were inside, it would equal one of the `f` consecutive walked
    values, and the freed guard at that step would assert it free —
    contradicting `boundary_not_free`. -/
theorem freed_below_other_boundary (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hnf : SolverInvBase g p)
    (suit B : UInt8) (hBreal : IsRealCard B) (f : Nat)
    (hfg : ∀ k, k < f → freedGuard g suit
      (freedIter k (⟨(1 : UInt8), p, B - 1⟩ : FreedAcc)))
    (j : Fin 10) (hdj : (p.pileDepth.get j).toNat > 0)
    (hBjlt : ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hnf.pileDepth_bound j; omega⟩ : UInt8).toNat < B.toNat) :
    ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hnf.pileDepth_bound j; omega⟩ : UInt8).toNat < B.toNat - f := by
  have hB64 : B.toNat < 64 := by
    have hsn := SUIT_toNat B; have h1 := hBreal.1; omega
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1,
    by have := hnf.pileDepth_bound j; omega⟩ : Fin 5) with hBjdef
  by_contra hge
  push Not at hge
  have hkf : B.toNat - 1 - Bj.toNat < f := by omega
  have hg := hfg (B.toNat - 1 - Bj.toNat) hkf
  obtain ⟨_, hg2⟩ := hg
  simp only [freedIter_eq] at hg2
  have h1B : (1 : UInt8) ≤ B := by rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have h1nat : ((1 : UInt8)).toNat = 1 := rfl
  have hkof : (UInt8.ofNat (B.toNat - 1 - Bj.toNat)).toNat = B.toNat - 1 - Bj.toNat := by
    rw [UInt8.toNat_ofNat']; omega
  have hkle : UInt8.ofNat (B.toNat - 1 - Bj.toNat) ≤ B - 1 := by
    rw [UInt8.le_iff_toNat_le, hkof, UInt8.toNat_sub_of_le _ _ h1B, h1nat]; omega
  have hBjB : B - 1 - UInt8.ofNat (B.toNat - 1 - Bj.toNat) = Bj := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hkle, UInt8.toNat_sub_of_le _ _ h1B, hkof, h1nat]
    omega
  simp only [hBjB] at hg2
  have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
  have hBj64 : Bj.toNat < 64 := by
    have hsn := SUIT_toNat Bj; have h1 := hBjreal.1; omega
  have hBj64u : Bj.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hBj64
  have hg2' := hg2 hBj64u
    (by rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt Bj.toNat hBj64)
  have hfree : isFreeCard g p Bj := by
    unfold isFreeCard
    simp only [dif_pos hBj64]
    have hpileEq' : g.card2pile.get ⟨Bj.toNat, hBj64⟩ = cardPile g Bj := by
      unfold cardPile; simp [hBj64]
    have hpile64 : (cardPile g Bj).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt Bj.toNat hBj64
    simp only [hpileEq', dif_pos hpile64]
    have hpileEqGE : (g.card2pile[Bj.toUInt32.toNat]'hBj64u).toUInt32.toNat =
        (cardPile g Bj).toNat := by
      have : g.card2pile[Bj.toUInt32.toNat]'hBj64u = g.card2pile.get ⟨Bj.toNat, hBj64⟩ := rfl
      rw [this, hpileEq', UInt8.toNat_toUInt32]
    have hdepthEqGE : (g.card2depth[Bj.toUInt32.toNat]'hBj64u).toNat =
        (g.card2depth.get ⟨Bj.toNat, hBj64⟩).toNat := by
      have : g.card2depth[Bj.toUInt32.toNat]'hBj64u = g.card2depth.get ⟨Bj.toNat, hBj64⟩ := rfl
      rw [this]
    have keyEq : (p.pileDepth[(g.card2pile[Bj.toUInt32.toNat]'hBj64u).toUInt32.toNat]'
        (by rw [hpileEqGE]; exact hpile64)).toNat =
      (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toNat := by
      congr 2
    show (g.card2depth.get ⟨Bj.toNat, hBj64⟩).toNat ≥
      (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toNat
    rw [← hdepthEqGE, ← keyEq]
    exact hg2'
  exact free_card_ne_boundary hwf hnf j hdj Bj hfree rfl


end SolverSpec
