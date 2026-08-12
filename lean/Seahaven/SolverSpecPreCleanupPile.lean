import Seahaven.SolverSpecCommon

/-!
# Spec for `preCleanupPile` (and the older `cleanupRunResult`)

Field-projection and monotonicity facts about `preCleanupPile`, plus the
`PileBase`/`PileMerged`/`PileClean`/`SuitClean` preservation theorems it
establishes.  Also carries the two `cleanupRunResult` lemmas (the
predecessor of the `kingMove`/`preCleanupPile` split) that this file's
theorems' doc comments still cross-reference.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **`cleanupRunResult` only ever decreases `pileDepth`**, pointwise across all
    ten piles.  Piles other than `pile` are literally untouched (the function
    only ever writes `pileDepth[pile]`, in either branch); `pile`'s own depth
    either drops to `0` (lone-king branch) or to `d0 - m` (`m ≥ 0`, still within
    `UInt8` range given `hd5`/`hm`, so no wraparound).  This is the building
    block for showing `PileBase`/`PileMerged` survive cleanup at every OTHER
    pile via `isFreeCard_mono`. -/
theorem cleanupRunResult_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat) (i : Fin 10) :
    ((cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get i).toNat ≤
      (p.pileDepth.get i).toNat := by
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m := depth_sub_ofNat_eq hd5 hm
  show (((cleanupRunResult pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).2).pileDepth[i.val]'i.isLt).toNat ≤
    (p.pileDepth[i.val]'i.isLt).toNat
  simp only [cleanupRunResult]
  -- `pileDepth` doesn't depend on the `busyAces` branch at all, but that
  -- (unresolved) inner `if` still blocks `reduceIte` from reducing the OUTER
  -- (king) `if` unless it too is split — mirrors the `hk`/`hba` double split
  -- already used to discharge `cleanupPile_base` itself (its "Lone-king
  -- branch"/"No lone king" cases).
  by_cases hk : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1
      && VALUE (B + UInt8.ofNat m) == 13) = true
  · by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true
    · simp only [hk, hba, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [show (((0 : UInt8)).toNat = 0) from rfl]
        exact Nat.zero_le _
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [show (((0 : UInt8)).toNat = 0) from rfl]
        exact Nat.zero_le _
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
  · rw [Bool.not_eq_true] at hk
    by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true
    · simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [hdepth1I]
        omega
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [hdepth1I]
        omega
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]

/-- Specialization of `cleanupRunResult_pileDepth_le` to piles `j ≠ pile`:
    `pileDepth[j]` is literally unchanged (not merely `≤`). -/
theorem cleanupRunResult_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get j =
      p.pileDepth.get j := by
  show ((cleanupRunResult pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).2).pileDepth[j.val]'j.isLt =
    p.pileDepth[j.val]'j.isLt
  simp only [cleanupRunResult]
  by_cases hk : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1
      && VALUE (B + UInt8.ofNat m) == 13) = true
  · by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true
    · simp only [hk, hba, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
  · rw [Bool.not_eq_true] at hk
    by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true
    · simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `preCleanupPile`'s output `pileDepth` is pointwise `≤` the input, for every
    pile — same fact as `cleanupRunResult_pileDepth_le`, but for the simpler
    no-king write (a single `busyAces`-branch `if`, not a nested one, so no
    `hk` split is needed). -/
theorem preCleanupPile_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat) (i : Fin 10) :
    ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get i).toNat ≤
      (p.pileDepth.get i).toNat := by
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m := depth_sub_ofNat_eq hd5 hm
  show (((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth[i.val]'i.isLt).toNat ≤
    (p.pileDepth[i.val]'i.isLt).toNat
  simp only [preCleanupPile]
  by_cases hip : pile.toNat = i.val
  · simp only [← hip, Vector.getElem_set_self]
    show (((p.pileDepth[pile.toNat]'hpile)
             - UInt8.ofNat m)).toNat ≤
      (p.pileDepth[pile.toNat]'hpile).toNat
    rw [hdepth1I]
    omega
  · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]

/-- Specialization to `j ≠ pile`: `pileDepth[j]` is literally unchanged. -/
theorem preCleanupPile_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j =
      p.pileDepth.get j := by
  show ((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth[j.val]'j.isLt =
    p.pileDepth[j.val]'j.isLt
  simp only [preCleanupPile]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- Specialization to `j ≠ pile`: `pileFlute[j]` is literally unchanged. -/
theorem preCleanupPile_pileFlute_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.get j =
      p.pileFlute.get j := by
  show ((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p)).pileFlute[j.val]'j.isLt =
    p.pileFlute[j.val]'j.isLt
  simp only [preCleanupPile]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `preCleanupPile` never touches `aces` (only `hash`/`usedSpace`/`busyAces`/
    `pileDepth`/`pileFlute`) — true in both `busyAces`-branches, so needs the
    same `hba` split as the field-projection lemmas above (the `if` on
    `busyAces` doesn't block `rfl` here — `aces` isn't in the goal's
    `simp only [preCleanupPile]`-unfolded form at all, but the two branches
    are still distinct terms until the `if` is resolved). -/
theorem preCleanupPile_aces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).aces = p.aces := by
  simp only [preCleanupPile]

/-- `preCleanupPile` never touches `kings`. -/
theorem preCleanupPile_kings_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).kings = p.kings := by
  simp only [preCleanupPile]

/-- **`PileBase` survives `preCleanupPile` at every OTHER pile `j ≠ pile`.**
    `j`'s own depth/flute are literally unchanged
    (`preCleanupPile_pileDepth_eq_of_ne`/`_pileFlute_eq_of_ne`), so the
    "shape" clauses transfer directly; the freeness clause
    (`flute_cards_free`) transfers via `isFreeCard_mono` using
    `preCleanupPile_pileDepth_le` (depths only ever decrease, so anything free
    before stays free); `flute_not_aces` doesn't even mention freeness (`aces`
    is untouched by `preCleanupPile_aces_eq`), so it transfers verbatim. -/
theorem preCleanupPile_pileBase_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) (hb : PileBase g p j) :
    PileBase g (preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile) m f p) j := by
  have hdeq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj
  have hfeq := preCleanupPile_pileFlute_eq_of_ne pile hpile B ph hs4 p m f j hj
  have haeq := preCleanupPile_aces_eq pile hpile B ph hs4 p m f
  have hdmono := preCleanupPile_pileDepth_le pile hpile B ph hs4 p m f hd5 hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeq]; exact hb.pileDepth_bound
  · rw [hfeq]; exact hb.flute_pos
  · intro h0
    rw [hfeq]
    apply hb.flute_empty
    rwa [hdeq] at h0
  · intro k hdpos hk0 hklt
    have hdpos' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdpos
    have hklt' : k.toNat < (p.pileFlute.get j).toNat := by rw [← hfeq]; exact hklt
    have hidxEq : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      have hidxEq' : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
          (p.pileDepth.get j).toNat - 1 := hidxEq
      exact Fin.ext hidxEq'
    rw [hXeq]
    exact isFreeCard_mono hdmono (hb.flute_cards_free k hdpos' hk0 hklt')
  · intro hdpos
    have hdpos' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdpos
    have hidxEq : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      have hidxEq' : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
          (p.pileDepth.get j).toNat - 1 := hidxEq
      exact Fin.ext hidxEq'
    -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `preCleanupPile`
    -- terms first (so the `let boundary` in the field's own statement gets
    -- expanded concretely, rather than staying an opaque `intro`-introduced
    -- local), THEN reduce those wrappers uniformly.
    show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat < 4,
      ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).aces.get
        ⟨(SUIT ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
            by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat, hs⟩).toNat +
        ((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.get j).toNat ≤
      UInt8.toNat ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)
    rw [hXeq, hfeq, haeq]
    intro hs
    exact hb.flute_not_aces hdpos' hs

/-- **A real card strictly below the merged-away range keeps its freeness
    status across `preCleanupPile`.**  The merge-absorbed slots hold exactly
    `B, …, B+m-1` (`hmcards`); a real card `C < B` can't be any of those, so
    if `C`'s own home pile isn't `pile`, cleanup doesn't touch it at all, and
    if it *is* `pile`, `round_trip` forces its home depth to be strictly below
    the new (shrunk) depth too — so `¬isFreeCard` transfers either way.  This
    is the "wrong direction" of `isFreeCard_mono` (needed for `flute_maximal`'s
    `¬isFreeCard` disjunct, not just its `isFreeCard` one), which only holds
    because `C` is provably outside the range cleanup could have freed. -/
private theorem preCleanupPile_not_free_of_lt_boundary
    (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (hBrange : B.toNat ≤ 61)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (C : UInt8) (hCreal : IsRealCard C) (hClt : C.toNat < B.toNat)
    (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  by_cases hcp : (cardPile g C).toNat = pile.toNat
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat - m :=
      depth_sub_ofNat_eq hd5 (by omega)
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    have hnfreeLt : (cardDepth g C).toNat <
        (p.pileDepth[(cardPile g C).toNat]'hp64).toNat := by
      by_contra hge
      push Not at hge
      exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)
    have hpdEq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[(cardPile g C).toNat]'hp64
        = (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
      have hstep : (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64
          = (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hstep]
      simp only [preCleanupPile]
      rw [Vector.getElem_set_self]
    rw [hpdEq, hdI8] at hfreeGe
    have hpEq : (p.pileDepth[(cardPile g C).toNat]'hp64).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat := by
      have h : (p.pileDepth[(cardPile g C).toNat]'hp64) = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [h]
    rw [hpEq] at hnfreeLt
    set cd := (cardDepth g C).toNat with hcddef
    have hmNat : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat - 1 := by omega
    have hcd5 : cd < 5 := by omega
    obtain ⟨k, hkm, hkeq⟩ : ∃ k, k < m ∧
        ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat k - 1).toUInt32.toNat = cd := by
      refine ⟨(p.pileDepth[pile.toNat]'hpile).toNat - 1 - cd, by omega, ?_⟩
      rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega)]
      omega
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hcd_lt5 : (cardDepth g C).toNat < 5 := hcd5
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) = (⟨cd, hcd5⟩ : Fin 5) := Fin.ext rfl
    rw [hcpEq, hcdEq] at hround
    have hgetEq : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get (⟨cd, hcd5⟩ : Fin 5) =
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'hidxk := by
      congr 1
      exact Fin.ext hkeq.symm
    rw [hgetEq, heqk] at hround
    have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
    have hlt : B.toNat + k < 256 := by omega
    have hBkB : (B + UInt8.ofNat k).toNat = B.toNat + k := by
      rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hlt]
    have hCeq := congrArg UInt8.toNat hround
    rw [hBkB] at hCeq
    omega
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hj : (⟨(cardPile g C).toNat, hp64⟩ : Fin 10).val ≠ pile.toNat := hcp
    have hpdEq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f
      ⟨(cardPile g C).toNat, hp64⟩ hj
    have hpdEq' : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[(cardPile g C).toNat]'hp64
        = p.pileDepth[(cardPile g C).toNat]'hp64 := hpdEq
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    rw [hpdEq'] at hfreeGe
    exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hfreeGe)

/-- **Generalized form of `preCleanupPile_not_free_of_lt_boundary`**: instead of
    requiring `C < B` (which only rules out `C` being one of `B, …, B+m-1` when
    `C` is numerically below the whole merge-absorbed run), takes the direct
    hypothesis that `C` isn't literally any of `B, …, B+m-1`.  This covers both
    the old numeric case (`C.toNat < B.toNat`) and the new "different suit"
    case needed by `SuitClean` (`SUIT C ≠ SUIT B` rules out `C = B+k` for every
    `k ≤ m`, since `merge_real_chain'` shows every such card has suit `SUIT B`,
    even when `C` is numerically *above* `B+m-1`, which can happen for a higher
    suit). -/
private theorem preCleanupPile_not_free_of_ne_absorbed
    (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (_hBrange : B.toNat ≤ 61)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (C : UInt8) (hCreal : IsRealCard C) (hne : ∀ k, k ≤ m → C ≠ B + UInt8.ofNat k)
    (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  by_cases hcp : (cardPile g C).toNat = pile.toNat
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat - m :=
      depth_sub_ofNat_eq hd5 (by omega)
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    have hnfreeLt : (cardDepth g C).toNat <
        (p.pileDepth[(cardPile g C).toNat]'hp64).toNat := by
      by_contra hge
      push Not at hge
      exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)
    have hpdEq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[(cardPile g C).toNat]'hp64
        = (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
      have hstep : (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64
          = (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hstep]
      simp only [preCleanupPile]
      rw [Vector.getElem_set_self]
    rw [hpdEq, hdI8] at hfreeGe
    have hpEq : (p.pileDepth[(cardPile g C).toNat]'hp64).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat := by
      have h : (p.pileDepth[(cardPile g C).toNat]'hp64) = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [h]
    rw [hpEq] at hnfreeLt
    set cd := (cardDepth g C).toNat with hcddef
    have hmNat : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat - 1 := by omega
    have hcd5 : cd < 5 := by omega
    obtain ⟨k, hkm, hkeq⟩ : ∃ k, k < m ∧
        ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat k - 1).toUInt32.toNat = cd := by
      refine ⟨(p.pileDepth[pile.toNat]'hpile).toNat - 1 - cd, by omega, ?_⟩
      rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega)]
      omega
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hcd_lt5 : (cardDepth g C).toNat < 5 := hcd5
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) = (⟨cd, hcd5⟩ : Fin 5) := Fin.ext rfl
    rw [hcpEq, hcdEq] at hround
    have hgetEq : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get (⟨cd, hcd5⟩ : Fin 5) =
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'hidxk := by
      congr 1
      exact Fin.ext hkeq.symm
    rw [hgetEq, heqk] at hround
    -- `hround : B + UInt8.ofNat k = C`; directly contradicts `hne`.
    exact hne k (by omega) hround.symm
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hj : (⟨(cardPile g C).toNat, hp64⟩ : Fin 10).val ≠ pile.toNat := hcp
    have hpdEq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f
      ⟨(cardPile g C).toNat, hp64⟩ hj
    have hpdEq' : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[(cardPile g C).toNat]'hp64
        = p.pileDepth[(cardPile g C).toNat]'hp64 := hpdEq
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    rw [hpdEq'] at hfreeGe
    exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hfreeGe)

/-- **`PileBase` holds for `pile` itself after `preCleanupPile`.**  Takes
    the boundary card `B` and semantic facts about the merge/freed runs
    directly — not the raw `mergeGuard`/`freedGuard` machinery — matching the
    user's simplified interface: for `m`, the `m` successive ascending cards
    starting at `B` (`hmcards`); for `f`, that the `f` predecessor cards are
    all free *and* above the foundation ace (`hffree`).  `ph` is always just
    `pileHashes.get pile`, so it's no longer a separate parameter either.
    This is a restatement of the "No lone king" branch's own-pile reasoning
    out of the (structurally stale) monolithic `cleanupPile_base`, purely in
    terms of `preCleanupPile`. -/
theorem preCleanupPile_pileBase_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hf_le : f ≤ B.toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l)) :
    PileBase g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) ⟨pile.toNat, hpile⟩ := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1
    have h2 := hreal.2.1
    have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have h1le : (1 : UInt8) ≤ (p.pileDepth[pile.toNat]'hpile) := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile) - 1).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - 1 :=
    UInt8.toNat_sub_of_le _ _ h1le
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B := by
    by_contra hge
    rw [UInt8.lt_iff_toNat_lt, not_lt] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat := hge
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4)) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4))).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      hnf.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toNat
          rw [UInt8.toNat_toUInt32, hsubd]
          omega)
    exact hnfB hfree
  have hmof8 : (UInt8.ofNat m).toNat = m := by
    rw [UInt8.toNat_ofNat']; omega
  have hfof8 : (UInt8.ofNat f).toNat = f := by
    rw [UInt8.toNat_ofNat']; omega
  have hfl8 : (1 + UInt8.ofNat m + UInt8.ofNat f).toNat = 1 + m + f := by
    rw [UInt8.toNat_add, UInt8.toNat_add, hmof8, hfof8,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
      (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile =
      (1 + UInt8.ofNat m + UInt8.ofNat f) := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  -- Merge-absorbed cards `B+k` (`k < m`) sit past the shrunk depth, hence free.
  have hfree_interior : ∀ k, k < m → isFreeCard g
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p)
      (B + UInt8.ofNat k) := by
    intro k hkm
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hreal_k : IsRealCard (B + UInt8.ofNat k) := heqk ▸ hwf.pos2card_real _ _
    have hc64 : (B + UInt8.ofNat k).toNat < 64 := by
      have hsn := SUIT_toNat (B + UInt8.ofNat k); have h1 := hreal_k.1; omega
    have heqk' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        (⟨((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat k - 1).toUInt32.toNat,
          hidxk⟩ : Fin 5) = B + UInt8.ofNat k := heqk
    have hrt := hwf.round_trip_inv ⟨pile.toNat, hpile⟩ ⟨((p.pileDepth[pile.toNat
        ]'hpile) - UInt8.ofNat k - 1).toUInt32.toNat, hidxk⟩
    rw [heqk'] at hrt
    have hp64 : (cardPile g (B + UInt8.ofNat k)).toNat < 10 := by
      rw [hrt.1]; exact hpile
    apply isFree_of_cardDepth_ge g _ hwf _ hc64 hp64
    have hgoal2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p
        ).pileDepth[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
        = (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
      have hstep : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
          = (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
        exact hrt.1
      rw [hstep, hpd]
    rw [hrt.2, hgoal2]
    show ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat k - 1).toUInt32.toNat ≥
      ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat
    rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega), hdI8]
    omega
  -- Freed-predecessor cards `B-l` (`1 ≤ l ≤ f`) were already free in `p`
  -- (`hffree`), and freeness is monotone under the pile's depth decrease.
  have hfree_freed : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p)
      (B - UInt8.ofNat l) := fun l hl1 hlf =>
    isFreeCard_mono
      (preCleanupPile_pileDepth_le pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f hd5
        (by omega))
      (hffree l hl1 hlf).1
  -- `aces[suit] < B` extends forward to `aces[suit] < B+k` for `k ≤ m` (the
  -- merge-absorbed range never crosses the foundation, since it only grows).
  have haces_lt_Bk : ∀ k, k ≤ m →
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B + UInt8.ofNat k) := by
    intro k hkm
    have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
    have hadd : (B + UInt8.ofNat k).toNat = B.toNat + k := by
      rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt (by omega)]
    have htiBk : (B + UInt8.ofNat k).toInt = (B.toNat + k : Int) := by
      rw [uint8_toInt8_toInt_of_lt128 (by omega), hadd]
      push_cast
      ring
    have htiB : B.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
    have hlt := UInt8.lt_iff_toInt_lt.mp haces_lt_B
    rw [htiB] at hlt
    rw [UInt8.lt_iff_toInt_lt, htiBk]
    omega
  -- Shared by `flute_cards_free`/`flute_not_aces`: the cleaned pile's new
  -- boundary slot's index (`hbidx`) and its card value `B + m` (`hcardEq`,
  -- via `hmcards` at `k := m`), plus the same facts restated about
  -- `preCleanupPile`'s own (already-written) `pileDepth` field (`hboundOut`/
  -- `hcardEqOut`) so both clauses can `rw` them directly instead of
  -- re-deriving the `Vector.set`-vs-raw bridge twice.
  have hbidx : (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
      ).toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat := by
    rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega), hdI8]
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile
      ).toNat - 1 < 5 := by
    rw [hpd, hdI8]
    omega
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
      ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
        ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  -- `SUIT(B+m) = SUIT B`: the merge-absorbed range never crosses a suit
  -- boundary (`merge_real_chain'` gives the `VALUE` progression from
  -- `hmcards` directly, no loop-guard unfolding needed).
  have hrcm := merge_real_chain' g pile hpile hwf B
    (p.pileDepth[pile.toNat]'hpile) m hreal hmcards m (le_refl m)
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := by
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat m)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat m)
    have hb4 := VALUE_toNat B
    have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + m < 256 := by omega
    have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
    have hvm := hrcm.2
    omega
  exact {
    pileDepth_bound := by
      show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile
          ).toNat ≤ 5
      rw [hpd, hdI8]
      omega
    flute_pos := by
      show 1 ≤ ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile).toNat
      rw [hpf, hfl8]
      omega
    flute_empty := by
      intro hdep
      exfalso
      have hdep' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile = 0 := hdep
      rw [hpd] at hdep'
      have hz := congrArg UInt8.toNat hdep'
      rw [hdI8, show ((0 : UInt8).toNat = 0) from rfl] at hz
      omega
    flute_cards_free := by
      intro j hdi hj0 hjlt
      have hjlt' : j.toNat < ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile).toNat :=
        hjlt
      rw [hpf, hfl8] at hjlt'
      show isFreeCard g _
        ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut - j)
      rw [hcardEqOut]
      rcases flute_offset_split B m f hBrange.2 (by omega) hf_le j hj0 (by omega)
        with ⟨k, hkm, hval⟩ | ⟨l, hl1, hlf, hval⟩
      · rw [hval]; exact hfree_interior k hkm
      · rw [hval]; exact hfree_freed l hl1 hlf
    flute_not_aces := by
      intro hdi _
      -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `preCleanupPile`
      -- terms first, THEN reduce those wrappers uniformly, BEFORE `intro`-ing the
      -- dependent `hs` binder — mirrors the recipe from
      -- `preCleanupPile_pileBase_ne`'s own `flute_not_aces` (rewriting `boundary`
      -- AFTER `hs` is fixed hits "motive is not type correct", since `hs`'s own
      -- type embeds the pre-rewrite `boundary` expression).
      show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut)).toNat < 4,
        ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).aces.get
            ⟨(SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
                (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
                ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut)).toNat, hs⟩).toNat +
          ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile).toNat ≤
          UInt8.toNat ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
              ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut)
      rw [preCleanupPile_aces_eq, hcardEqOut, hpf, hfl8]
      intro hs
      have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
      have hidxEq : (⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ : Fin 4) =
          ⟨(SUIT B).toNat, hs4'⟩ := Fin.ext (congrArg UInt8.toNat hSm)
      have hEq2 : p.aces.get ⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
        rw [hidxEq]; congr 1
      rw [hEq2]
      -- New Nat-based bound: `aces[SUIT B].toUInt8.toNat + f < B.toNat`, tightest
      -- at the largest valid offset (`f = 0` falls back to `haces_lt_B`; `f > 0`
      -- uses the freed-predecessor bound at its largest index `l = f`).
      have hAB_lt : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat + f < B.toNat := by
        rcases Nat.eq_zero_or_pos f with hf0 | hfpos
        · subst hf0
          simp only [Nat.add_zero]
          exact UInt8.lt_iff_toNat_lt.mp haces_lt_B
        · have hf' := (hffree f hfpos (le_refl f)).2
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hfBle : UInt8.ofNat f ≤ B := by rw [UInt8.le_iff_toNat_le, hfof]; omega
          have hBf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
            rw [UInt8.toNat_sub_of_le _ _ hfBle, hfof]
          have hlt := UInt8.lt_iff_toNat_lt.mp hf'
          rw [hBf] at hlt
          omega
      have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
      have hBmAdd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
        rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt (by omega)]
      rw [hBmAdd]
      omega }

set_option maxHeartbeats 1000000 in
/-- **`PileMerged` holds for `pile` itself after `preCleanupPile`.**  Genuinely
    new content (never proved anywhere before, unlike `preCleanupPile_pileBase_self`
    which ports the old monolithic proof): `merge_complete`/`flute_maximal` each
    need one more semantic "stopping" fact beyond `hmcards`/`hffree` — `hmstop`
    (either the pile ends at depth `≤ 1`, or the card two below the new boundary
    doesn't continue the ascending run) and `hfstop` (either the ace has already
    reached `B-1-f`, or that card is genuinely not free — this is the "why the
    freed loop actually stopped" fact, the counterpart to `hffree`'s "why it kept
    going"). `busyAces_complete`'s antecedent turns out to be *exactly*
    `preCleanupPile`'s own `busyAces`-setting condition, so it's essentially
    definitional once unfolded. -/
theorem preCleanupPile_pileMerged_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hmstop : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1 ∨
      (m + 1 < (p.pileDepth[pile.toNat]'hpile).toNat ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
            UInt8.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l))
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f) ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
    (hbound : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get ⟨pile.toNat, hpile⟩
        ).toNat ≤ 5) :
    PileMerged g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) ⟨pile.toNat, hpile⟩ hbound := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1; have h2 := hreal.2.1; have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have h1le : (1 : UInt8) ≤ (p.pileDepth[pile.toNat]'hpile) := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile) - 1).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - 1 :=
    UInt8.toNat_sub_of_le _ _ h1le
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B := by
    by_contra hge
    rw [UInt8.lt_iff_toNat_lt, not_lt] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat := hge
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4)) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4))).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      hnf.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toNat
          rw [UInt8.toNat_toUInt32, hsubd]
          omega)
    exact hnfB hfree
  have hmof8 : (UInt8.ofNat m).toNat = m := by
    rw [UInt8.toNat_ofNat']; omega
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
      (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile =
      (1 + UInt8.ofNat m + UInt8.ofNat f) := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hfof8 : (UInt8.ofNat f).toNat = f := by
    rw [UInt8.toNat_ofNat']; omega
  have hfl8 : (1 + UInt8.ofNat m + UInt8.ofNat f).toNat = 1 + m + f := by
    rw [UInt8.toNat_add, UInt8.toNat_add, hmof8, hfof8,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile
      ).toNat - 1 < 5 := by
    rw [hpd, hdI8]
    omega
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hbidx : (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
      ).toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat := by
    rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega), hdI8]
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
      ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
        ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m)).toNat - 1]'(by
            show (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
              ).toNat - 1 < 5
            omega) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  have hrcm := merge_real_chain' g pile hpile hwf B
    (p.pileDepth[pile.toNat]'hpile) m hreal hmcards m (le_refl m)
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := by
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat m)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat m)
    have hb4 := VALUE_toNat B
    have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + m < 256 := by omega
    have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
    have hvm := hrcm.2
    omega
  -- `prevCard` (`flute_maximal`'s own `boundary - flute2`) is exactly
  -- `B - 1 - f` — a UInt8 group identity, no range condition needed.
  have hprevEq : (B + UInt8.ofNat m) - (1 + UInt8.ofNat m + UInt8.ofNat f)
      = B - 1 - UInt8.ofNat f := by
    have hfl8' : (1 + UInt8.ofNat m + UInt8.ofNat f) = UInt8.ofNat (1 + m + f) := by
      apply UInt8.toNat_inj.mp
      rw [hfl8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [hfl8']
    apply UInt8.toNat_inj.mp
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
    have hsumof : (UInt8.ofNat (1 + m + f)).toNat = 1 + m + f := by
      rw [UInt8.toNat_ofNat']; omega
    have hlt1 : B.toNat + m < 256 := by omega
    have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof, Nat.mod_eq_of_lt hlt1]
    have hle1 : UInt8.ofNat (1 + m + f) ≤ B + UInt8.ofNat m := by
      rw [UInt8.le_iff_toNat_le, hsumof, hBmB]; omega
    have hle2 : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hle3 : UInt8.ofNat f ≤ B - 1 := by
      rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2, show ((1 : UInt8).toNat = 1) from rfl]
      omega
    rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ hle2, hBmB, hsumof, hfof, show ((1 : UInt8).toNat = 1) from rfl]
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete
    show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile ≤ 1 ∨
      (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile).toNat - 2]'(by
            rw [hpd, hdI8]
            omega) ≠
        (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut + 1
    rcases hmstop with hmA | ⟨hgt2, hidx2, hmB⟩
    · left
      rw [hpd, UInt8.le_iff_toNat_le, hdI8]
      have h1 : (1 : UInt8).toNat = 1 := rfl
      omega
    · right
      have hidxEq : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile
          ).toNat - 2 =
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat := by
        rw [hpd, UInt8.toNat_toUInt32, depth_sub_ofNat_sub_two_eq hd5 (by omega), hdI8]
      intro heq
      apply hmB
      have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile).toNat - 2]'(by
            rw [hpd, hdI8]
            omega)
          = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
            UInt8.ofNat m - 2).toUInt32.toNat]'hidx2 := by
        congr 1
      rw [hstep] at heq
      rw [heq, hcardEqOut]
      have hstepB : B + UInt8.ofNat m + 1 = B + UInt8.ofNat (m + 1) := by
        rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
      rw [hstepB]
  · -- (3b) flute_maximal
    show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile = 0 ∨
      let boundary := (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut
      let prevCard := boundary - (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile)
          hs4 (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile
      (∃ hs : (SUIT boundary).toUInt32.toNat < 4,
        p.aces[(SUIT boundary).toUInt32.toNat]'hs = prevCard) ∨
      ¬ isFreeCard g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p) prevCard
    right
    simp only [hcardEqOut, hSm, hpf, hprevEq]
    rcases hfstop with hge | hnfree
    · left
      exact ⟨hs4, hge⟩
    · -- `hf_le_tight` only guarantees `f ≤ VALUE(B) - 1`: the residual case
      -- `f = VALUE(B) - 1` makes `prevCard = B - 1 - f` the suit's own
      -- value-0 sentinel, which isn't a real card, so the general
      -- not-free-preserved argument (needing `IsRealCard`) below doesn't
      -- apply there.  Handle it directly instead: the sentinel value is
      -- pinned between `aces[suit]`'s suit-block lower bound
      -- (`aces_kings_valid`) and the freed-loop's own upper bound at the
      -- last step, forcing `aces[suit] = prevCard` exactly (the *other*
      -- disjunct) rather than needing to transport `hnfree`.
      have hle2 : (1 : UInt8) ≤ B := by
        rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
      have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
      have hle3 : UInt8.ofNat f ≤ B - 1 := by
        rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2, show ((1 : UInt8).toNat = 1) from rfl]
        omega
      have hprevNat : (B - 1 - UInt8.ofNat f).toNat = B.toNat - 1 - f := by
        rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ hle2, show ((1 : UInt8).toNat = 1) from rfl, hfof]
      have hsn := SUIT_toNat B
      have hvn := VALUE_toNat B
      have hs1 : (SUIT B).toNat < 4 := hreal.1
      have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
      have hv2 : (VALUE B).toNat ≤ 13 := hreal.2.2
      have hBdecomp : B.toNat = 16 * (SUIT B).toNat + (VALUE B).toNat := by omega
      by_cases hfeq : f = (VALUE B).toNat - 1
      · left
        refine ⟨hs4, ?_⟩
        have hprevlt128 : (B - 1 - UInt8.ofNat f).toNat < 128 := by omega
        have hacesLt : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat f) := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · rw [hf0, show UInt8.ofNat 0 = 0 from rfl, UInt8.sub_zero]
            exact haces_lt_B
          · exact (hffree f hfpos (le_refl f)).2
        have hbf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
          have hlef : UInt8.ofNat f ≤ B := by
            rw [UInt8.le_iff_toNat_le, hfof]; omega
          rw [UInt8.toNat_sub_of_le _ _ hlef, hfof]
        have hbflt128 : (B - UInt8.ofNat f).toNat < 128 := by omega
        have hacesLeNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat ≤
            (B - 1 - UInt8.ofNat f).toNat := by
          have hlt := UInt8.lt_iff_toNat_lt.mp hacesLt
          rw [hprevNat]
          omega
        have hacesGeNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat ≥
            16 * (SUIT B).toNat := by
          have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
          have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
          have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
              p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
          have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
          have hSAeq : (SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4)).toNat =
              (SUIT B).toUInt32.toNat := by
            rw [← hgetEq, hak.1]
            show (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat
            rw [UInt8.toNat_ofNat']
            omega
          have hAdecomp : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat =
              16 * (SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4)).toNat +
                (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4)).toNat := by
            have h1 := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
            have h2 := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
            omega
          omega
        have hprevSentinelNat : (B - 1 - UInt8.ofNat f).toNat = 16 * (SUIT B).toNat := by
          rw [hprevNat, hBdecomp, hfeq]; omega
        have hEqNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat =
            (B - 1 - UInt8.ofNat f).toNat := by omega
        apply UInt8.toNat_inj.mp
        omega
      · right
        exact preCleanupPile_not_free_of_lt_boundary g pile hpile hwf B
          (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
          (B - 1 - UInt8.ofNat f) (by
            have hsn' := SUIT_toNat (B - 1 - UInt8.ofNat f)
            have hvn' := VALUE_toNat (B - 1 - UInt8.ofNat f)
            have hprevVal : (VALUE (B - 1 - UInt8.ofNat f)).toNat = (VALUE B).toNat - 1 - f := by
              rw [hvn', hprevNat, hBdecomp]
              omega
            have hprevSuit : (SUIT (B - 1 - UInt8.ofNat f)).toNat = (SUIT B).toNat := by
              rw [hsn', hprevNat, hBdecomp]
              omega
            refine ⟨?_, ?_, ?_⟩
            · omega
            · omega
            · omega)
          (by omega) hnfree
  · -- (6) busyAces_complete
    intro hdi
    show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
        ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut)).toUInt32.toNat < 4,
      (p.aces[(SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut)).toUInt32.toNat]'hs
        ) =
        (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut -
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile →
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).busyAces &&&
        ((1 : UInt8) <<< (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut))) ≠ 0
    rw [hcardEqOut, hSm, hpf, hprevEq]
    intro hs heq
    have hbusy : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).busyAces =
        if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f) then
          p.busyAces ||| (1 : UInt8) <<< SUIT B
        else p.busyAces := by
      simp only [preCleanupPile]
    have hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true := by
      rw [heq]; exact beq_self_eq_true _
    rw [hbusy, hcond]
    simp only [reduceIte]
    have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
    exact uint8_and_ne_zero_of_or_right (uint8_shift_self_ne_zero (SUIT B) hs4')

/-- **`PileMerged` survives `preCleanupPile` at every OTHER pile `j ≠ pile`.**
    Counterpart of `preCleanupPile_pileBase_ne` for the merged layer.
    `merge_complete` transfers verbatim (only reads `pos2card`/`pileDepth[j]`,
    both untouched). `busyAces_complete` transfers because `preCleanupPile`'s
    `busyAces` write only ever ORs in one more bit
    (`uint8_and_ne_zero_of_or_left`). `flute_maximal` is the hard clause: its
    `¬isFreeCard` disjunct needs `prevCard` (pile `j`'s own flute predecessor)
    to never coincide with one of the `m` merge-absorbed cards `B, …, B+m-1`
    (which the cleanup step reveals as newly free) — proved via
    `hb.flute_cards_free`/`WellFormedLayout.round_trip_inv` case analysis on
    `p.pileFlute.get j`, then `preCleanupPile_not_free_of_ne_absorbed` carries
    the rest across. -/
theorem preCleanupPile_pileMerged_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hak : ∀ s : Fin 4, SUIT (p.aces.get s) = s.val.toUInt8)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hb : PileBase g p j) (hpm : PileMerged g p j hb.pileDepth_bound) :
    PileMerged g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) j
      (by rw [preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj]
          exact hb.pileDepth_bound) := by
  have hdeq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj
  have hfeq := preCleanupPile_pileFlute_eq_of_ne pile hpile B ph hs4 p m f j hj
  have haeq := preCleanupPile_aces_eq pile hpile B ph hs4 p m f
  have hm : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat := by omega
  have hdmono := preCleanupPile_pileDepth_le pile hpile B ph hs4 p m f hd5 hm
  -- `B` is real, from `hmcards` at `k = 0` (its own boundary slot).
  obtain ⟨hidx0, heq0⟩ := hmcards 0 (Nat.zero_le _)
  have hBcard : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
      UInt8.ofNat 0 - 1).toUInt32.toNat]'hidx0 = B := by
    rw [heq0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
  have hreal : IsRealCard B :=
    hBcard ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat 0 - 1).toUInt32.toNat, hidx0⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1; have h2 := hreal.2.1; have h3 := hreal.2.2
    omega
  -- The shrunk depth, as a plain integer fact, reused by both the `hkeqm`
  -- direct argument in `flute_maximal` and (implicitly) by the private lemma
  -- calls below.
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete: transfers verbatim (only reads `pos2card`/`pileDepth[j]`).
    have hidxEq2 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 2 =
        (p.pileDepth.get j).toNat - 2 := by rw [hdeq]
    have hidxEq1 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hX2 : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq2
    have hX1 : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq1
    rw [hX2, hX1, hdeq]
    exact hpm.merge_complete
  · -- (3b) flute_maximal: the hard clause.
    by_cases hd0 : p.pileDepth.get j = 0
    · left
      rw [hdeq]
      exact hd0
    · have hdj : (p.pileDepth.get j).toNat > 0 :=
        Nat.pos_of_ne_zero (fun h => hd0 (UInt8.toNat_inj.mp h))
      right
      set boundaryNew := (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew_def
      set prevCardNew := boundaryNew - (preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.get j with hprevCardNew_def
      show (∃ hs : (SUIT boundaryNew).toNat < 4,
          (preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).aces.get ⟨(SUIT boundaryNew).toNat, hs⟩ = prevCardNew) ∨
        ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p) prevCardNew
      set boundary := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
          by have := hb.pileDepth_bound; omega⟩ with hboundary_def
      set prevCard := boundary - p.pileFlute.get j with hprevCard_def
      have hidxEqB : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
          (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
      have hboundEq : boundaryNew = boundary := by
        rw [hboundaryNew_def, hboundary_def]
        congr 1
        exact Fin.ext hidxEqB
      have hprevEq : prevCardNew = prevCard := by
        rw [hprevCardNew_def, hprevCard_def, hboundEq, hfeq]
      rw [hboundEq, hprevEq, haeq]
      have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
      have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
      have hBDrange : boundary.toNat ≤ 61 := by
        have hsn := SUIT_toNat boundary
        have hvn := VALUE_toNat boundary
        have h1 := hrealBd.1; have h2 := hrealBd.2.1; have h3 := hrealBd.2.2
        omega
      have hflv : (p.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
        hb.flute_le_value hwf hak hdj
      have hVsn_bd := VALUE_toNat boundary
      have hSsn_bd := SUIT_toNat boundary
      have hfleB : p.pileFlute.get j ≤ boundary := by
        rw [UInt8.le_iff_toNat_le]
        have := Nat.mod_le boundary.toNat 16
        omega
      have hprevNat : prevCard.toNat = boundary.toNat - (p.pileFlute.get j).toNat :=
        UInt8.toNat_sub_of_le _ _ hfleB
      have hSUITeq : SUIT prevCard = SUIT boundary := by
        apply UInt8.toNat_inj.mp
        rw [SUIT_toNat, SUIT_toNat, hprevNat]
        omega
      have hVALeq : (VALUE prevCard).toNat =
          (VALUE boundary).toNat - (p.pileFlute.get j).toNat := by
        rw [VALUE_toNat, hprevNat]
        omega
      have hsuiteq : SUIT boundary = (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 := by
        show SUIT boundary = ((SUIT boundary).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      rcases hpm.flute_maximal.resolve_left hd0 with hOldA | hOldNF
      · left
        exact hOldA
      · by_cases hV0 : (VALUE prevCard).toNat = 0
        · -- `prevCard` is the suit's own zero-value sentinel: the NEW
          -- unconditional Nat-based `flute_not_aces` upper bound (`hb`, no
          -- offset/case-split needed), combined with the suit-block lower
          -- bound, pins `aces = prevCard` exactly (no old `≥`/inequality
          -- special-casing needed anymore).
          left
          refine ⟨hs4', ?_⟩
          have hSuitAcesEq :
              SUIT ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩)) = SUIT boundary := by
            rw [hak ⟨(SUIT boundary).toNat, hs4'⟩, ← hsuiteq]
          have hVBnat := VALUE_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSBnat := SUIT_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSeq := congrArg UInt8.toNat hSuitAcesEq
          have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
          have hacesGeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat ≥ prevCard.toNat := by
            rw [hprevNat0]; omega
          have hboundUpper : (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat +
              (p.pileFlute.get j).toNat ≤ boundary.toNat := hb.flute_not_aces hdj hs4'
          have hacesLeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat ≤ prevCard.toNat := by
            rw [hprevNat]; omega
          have hacesEqNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat = prevCard.toNat :=
            le_antisymm hacesLeNat hacesGeNat
          exact UInt8.toNat_inj.mp hacesEqNat
        · -- `prevCard` is a genuine real card: transfer `¬isFreeCard` across
          -- cleanup via `preCleanupPile_not_free_of_ne_absorbed`, once we've
          -- ruled out `prevCard = B + k` for every `k ≤ m`.
          right
          have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
          have hVle : (VALUE prevCard).toNat ≤ 13 := by
            have := hrealBd.2.2
            omega
          have hCrealPrev : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
          by_cases hkeqm : prevCard = B + UInt8.ofNat m
          · -- `prevCard` is exactly pile `pile`'s NEW boundary card: it stays
            -- resident (not free) directly, no need to rule out any `k`.
            rw [hkeqm]
            obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
            have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
              ⟨((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat,
                hidxm⟩
            have heqm' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                (⟨((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat,
                  hidxm⟩ : Fin 5) = B + UInt8.ofNat m := heqm
            rw [heqm'] at hrt
            have hrealBm : IsRealCard (B + UInt8.ofNat m) := heqm ▸ hwf.pos2card_real _ _
            have hc64 : (B + UInt8.ofNat m).toNat < 64 := by
              have := hrealBm.1
              have hsn := SUIT_toNat (B + UInt8.ofNat m)
              omega
            have hp64 : (cardPile g (B + UInt8.ofNat m)).toNat < 10 := by
              rw [hrt.1]; exact hpile
            intro hfree
            have hge := isFree_to_cardDepth_ge g (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile) m f p) hwf
              (B + UInt8.ofNat m) hc64 hp64 hfree
            have hstepD : (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile) m f p
                ).pileDepth[(cardPile g (B + UInt8.ofNat m)).toNat]'hp64 =
                (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile := by
              congr 1
              exact hrt.1
            rw [hstepD] at hge
            have hpdNew : (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
                (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
              simp only [preCleanupPile]
              rw [Vector.getElem_set_self]
            have hcdEqIdxM : (cardDepth g (B + UInt8.ofNat m)).toNat =
                ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat :=
              hrt.2
            rw [hpdNew, hcdEqIdxM] at hge
            have hidxmNat : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m -
                1).toUInt32.toNat = (p.pileDepth[pile.toNat]'hpile).toNat - m - 1 := by
              rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega)]
            rw [hidxmNat, hdI8] at hge
            omega
          · -- `prevCard ≠ B + m`; combined with the shift-argument for `k < m`,
            -- rule out `prevCard = B + k` for the FULL range `k ≤ m`.
            have hne : ∀ k, k ≤ m → prevCard ≠ B + UInt8.ofNat k := by
              intro k hkm heq
              rcases Nat.lt_or_eq_of_le hkm with hklt | hkeq
              · -- `k < m`: shift by one, landing on a card known to sit
                -- strictly inside pile `pile`'s (still fully occupied) OLD
                -- range, contradicting either `flute_cards_free` (pileFlute
                -- ≥ 2) or the cross-pile clash `j = pile` (pileFlute = 1).
                obtain ⟨hidxk1, heqk1⟩ := hmcards (k + 1) (by omega)
                set C := B + UInt8.ofNat (k + 1) with hCdef
                have hrealC : IsRealCard C := heqk1 ▸ hwf.pos2card_real _ _
                have hc64C : C.toNat < 64 := by
                  have := hrealC.1
                  have hsn := SUIT_toNat C
                  omega
                have hrtC := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
                  ⟨((p.pileDepth[pile.toNat]'hpile) -
                    UInt8.ofNat (k + 1) - 1).toUInt32.toNat, hidxk1⟩
                have heqk1' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                    (⟨((p.pileDepth[pile.toNat]'hpile) -
                      UInt8.ofNat (k + 1) - 1).toUInt32.toNat, hidxk1⟩ : Fin 5) = C := heqk1
                rw [heqk1'] at hrtC
                have hp64C : (cardPile g C).toNat < 10 := by rw [hrtC.1]; exact hpile
                have hCnotfree : ¬ isFreeCard g p C := by
                  intro hfreeC
                  have hgeC := isFree_to_cardDepth_ge g p hwf C hc64C hp64C hfreeC
                  have hstepDC : p.pileDepth[(cardPile g C).toNat]'hp64C =
                      p.pileDepth[pile.toNat]'hpile := by
                    congr 1; exact hrtC.1
                  have hcdEqIdx : (cardDepth g C).toNat =
                      ((p.pileDepth[pile.toNat]'hpile) -
                        UInt8.ofNat (k + 1) - 1).toUInt32.toNat := hrtC.2
                  rw [hstepDC, hcdEqIdx] at hgeC
                  have hidxk1Nat : ((p.pileDepth[pile.toNat]'hpile) -
                      UInt8.ofNat (k + 1) - 1).toUInt32.toNat =
                      (p.pileDepth[pile.toNat]'hpile).toNat - (k + 1) - 1 := by
                    rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega)]
                  rw [hidxk1Nat] at hgeC
                  omega
                have hCeqPrevSucc : C = prevCard + 1 := by
                  rw [hCdef, heq]
                  have hstepB : B + UInt8.ofNat k + 1 = B + UInt8.ofNat (k + 1) := by
                    rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
                  rw [← hstepB]
                by_cases hflj : (2 : UInt8) ≤ p.pileFlute.get j
                · -- pileFlute[j] ≥ 2: `boundary - (pileFlute - 1) = prevCard + 1`
                  -- is a flute-interior card, hence free — contradicting
                  -- `hCnotfree` (`C = prevCard + 1`).
                  have h1le : (1 : UInt8) ≤ p.pileFlute.get j := by
                    rw [UInt8.le_iff_toNat_le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (1 : UInt8).toNat = 1 := rfl
                    have h4 : (2 : UInt8).toNat = 2 := rfl
                    omega
                  have hoffLt : (p.pileFlute.get j - 1).toNat < (p.pileFlute.get j).toNat := by
                    rw [UInt8.toNat_sub_of_le _ _ h1le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (2 : UInt8).toNat = 2 := rfl
                    have h4 : (1 : UInt8).toNat = 1 := rfl
                    omega
                  have hoffPos : 0 < (p.pileFlute.get j - 1).toNat := by
                    rw [UInt8.toNat_sub_of_le _ _ h1le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (2 : UInt8).toNat = 2 := rfl
                    have h4 : (1 : UInt8).toNat = 1 := rfl
                    omega
                  have hfreeInterior :
                      isFreeCard g p (boundary - (p.pileFlute.get j - 1)) :=
                    hb.flute_cards_free (p.pileFlute.get j - 1) hdj hoffPos hoffLt
                  have hcardEq : boundary - (p.pileFlute.get j - 1) = prevCard + 1 := by
                    rw [hprevCard_def]
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    have hfleBNat : (p.pileFlute.get j).toNat ≤ boundary.toNat :=
                      UInt8.le_iff_toNat_le.mp hfleB
                    have hfm1le : p.pileFlute.get j - 1 ≤ boundary := by
                      rw [UInt8.le_iff_toNat_le, UInt8.toNat_sub_of_le _ _ h1le, h1]
                      omega
                    apply UInt8.toNat_inj.mp
                    rw [UInt8.toNat_sub_of_le _ _ hfm1le, UInt8.toNat_sub_of_le _ _ h1le, h1]
                    have hlt256 : boundary.toNat - (p.pileFlute.get j).toNat + 1 < 2 ^ 8 := by omega
                    rw [UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hfleB, h1, Nat.mod_eq_of_lt hlt256]
                    omega
                  rw [hcardEq] at hfreeInterior
                  exact hCnotfree (hCeqPrevSucc ▸ hfreeInterior)
                · -- pileFlute[j] = 1 (`flute_pos` rules out 0): `prevCard + 1 =
                  -- boundary` exactly, so `C = boundary` — but `boundary`'s own
                  -- pile is `j`, while `C`'s is `pile`, forcing `j = pile`.
                  have hfl1 : p.pileFlute.get j = 1 := by
                    have hpos := hb.flute_pos
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    have h2 : (2 : UInt8).toNat = 2 := rfl
                    have hlt2 : (p.pileFlute.get j).toNat < 2 := by
                      by_contra hge
                      apply hflj
                      rw [UInt8.le_iff_toNat_le, h2]
                      omega
                    apply UInt8.toNat_inj.mp
                    omega
                  have hCeqBoundary : C = boundary := by
                    have hle1 : (1 : UInt8) ≤ boundary := by
                      rw [UInt8.le_iff_toNat_le]
                      have h1' : (1 : UInt8).toNat = 1 := rfl
                      have := hrealBd.2.1
                      omega
                    rw [hCeqPrevSucc, hprevCard_def, hfl1]
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    apply UInt8.toNat_inj.mp
                    rw [UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle1, h1]
                    have hlt256 : boundary.toNat - 1 + 1 < 2 ^ 8 := by omega
                    rw [Nat.mod_eq_of_lt hlt256]
                    omega
                  have hrtBd := hwf.round_trip_inv j ⟨(p.pileDepth.get j).toNat - 1,
                    by have := hb.pileDepth_bound; omega⟩
                  have hjEqPile : j.val = pile.toNat := by
                    rw [hCeqBoundary, hboundary_def] at hrtC
                    rw [hrtBd.1] at hrtC
                    exact hrtC.1
                  exact hj hjEqPile
              · rw [hkeq] at heq; exact hkeqm heq
            exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B ph hs4 hBrange.2
              p m f hd5 hm_le hmcards prevCard hCrealPrev hne hOldNF
  · -- (6) busyAces_complete
    intro hdi
    have hdi' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdi
    set boundaryNew2 := (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew2_def
    show ∀ hs : (SUIT boundaryNew2).toNat < 4,
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).aces.get ⟨(SUIT boundaryNew2).toNat, hs⟩) =
          boundaryNew2 - (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.get j →
        (preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).busyAces &&& ((1 : UInt8) <<< SUIT boundaryNew2) ≠ 0
    set boundaryOld2 := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ with hboundaryOld2_def
    have hidxEqB2 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hboundEq2 : boundaryNew2 = boundaryOld2 := by
      rw [hboundaryNew2_def, hboundaryOld2_def]
      congr 1
      exact Fin.ext hidxEqB2
    rw [hboundEq2, hfeq, haeq]
    intro hs heq
    have hbusy_eq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).busyAces =
        if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f) then
          p.busyAces ||| (1 : UInt8) <<< SUIT B
        else p.busyAces := by
      simp only [preCleanupPile]
    rw [hbusy_eq]
    split
    · exact uint8_and_ne_zero_of_or_left (hpm.busyAces_complete hdi' hs heq)
    · exact hpm.busyAces_complete hdi' hs heq

/-- **`preCleanupPile` leaves the pile it just wrote `PileClean`.**  Combines
    `preCleanupPile_pileBase_self` and `preCleanupPile_pileMerged_self` into the
    full per-pile bundle. -/
theorem preCleanupPile_pileClean_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hmstop : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1 ∨
      (m + 1 < (p.pileDepth[pile.toNat]'hpile).toNat ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
            UInt8.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l))
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f) ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f)) :
    PileClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) ⟨pile.toNat, hpile⟩ := by
  have hb := preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hf_le hffree
  have hm := preCleanupPile_pileMerged_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hmstop hf_le hf_le_tight hffree hfstop hb.pileDepth_bound
  exact { hb, hm with }

/-- **`preCleanupPile`'s output has bounded depth everywhere**, not just at
    `pile` itself — the parameter `SuitClean` needs (its `king_frontier`/
    `foundation_maximal_weak` clauses index into whichever pile happens to
    witness a flute-top, which may be any pile, not just `pile`).  At `pile`
    itself this is `preCleanupPile_pileBase_self`'s own `pileDepth_bound`
    field; everywhere else the depth is untouched
    (`preCleanupPile_pileDepth_eq_of_ne`), so it's just `hnf`'s own bound. -/
theorem preCleanupPile_pileDepth_bound_all (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hf_le : f ≤ B.toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l)) :
    ∀ i : Fin 10, ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get i).toNat ≤ 5 := by
  intro i
  by_cases hip : i.val = pile.toNat
  · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip
    subst hii
    exact (preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
      m f hm_le hmcards hf_le hffree).pileDepth_bound
  · rw [preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
      i hip]
    exact hnf.pileDepth_bound i

set_option maxHeartbeats 1000000 in
/-- **`SuitClean` holds for every suit `s` after `preCleanupPile`.**  The
    hardest part of the per-pile/per-suit tower split: unlike `PileBase`/
    `PileMerged` (which only ever look at `pile` itself), `SuitClean`'s
    `foundation_maximal_weak`/`king_frontier` clauses quantify over an
    arbitrary suit `s` and reference a `¬isFreeCard` fact about the
    foundation-successor / king-frontier card, which `preCleanupPile` can
    only possibly disturb if that card happens to be one of the `m`
    merge-absorbed cards `B, …, B+m-1` — all of suit `SUIT B`
    (`merge_real_chain'`).  So for `s ≠ SUIT B` the witness card provably
    isn't in the revealed range (different suit ⟹ can't equal `B+k`) and
    `preCleanupPile_not_free_of_ne_absorbed` transfers `¬isFreeCard` directly;
    for `s = SUIT B` a delicate case analysis (ported from the old monolithic
    `cleanupPile_baseNF`'s non-king branch) pins the witness down to exactly
    `B` itself when it IS in the revealed range, forcing `f = 0`
    (`hAeqB_implies_f0`) and landing the argument in the "flute-top witness is
    `pile` itself" disjunct instead. -/
theorem preCleanupPile_suitClean (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (_hmstop : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1 ∨
      (m + 1 < (p.pileDepth[pile.toNat]'hpile).toNat ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
            UInt8.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l))
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f) ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
    (s : Fin 4) :
    SuitClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p) s
        (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
          m f hm_le hmcards hf_le hffree) := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1
    have h2 := hreal.2.1
    have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have h1le : (1 : UInt8) ≤ (p.pileDepth[pile.toNat]'hpile) := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile) - 1).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - 1 :=
    UInt8.toNat_sub_of_le _ _ h1le
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B := by
    by_contra hge
    rw [UInt8.lt_iff_toNat_lt, not_lt] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat := hge
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).aces_kings_valid
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4)) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4))).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).foundation_cards_free B hsuiteq hreal.2.1
        hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toNat
          rw [UInt8.toNat_toUInt32, hsubd]
          omega)
    exact hnfB hfree
  -- Arithmetic facts (identical to `preCleanupPile_pileMerged_self`'s preamble).
  have hmof8 : (UInt8.ofNat m).toNat = m := by
    rw [UInt8.toNat_ofNat']; omega
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  have hfof8 : (UInt8.ofNat f).toNat = f := by
    rw [UInt8.toNat_ofNat']; omega
  have hfl8 : (1 + UInt8.ofNat m + UInt8.ofNat f).toNat = 1 + m + f := by
    rw [UInt8.toNat_add, UInt8.toNat_add, hmof8, hfof8,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
      (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile =
      (1 + UInt8.ofNat m + UInt8.ofNat f) := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile
      ).toNat - 1 < 5 := by
    rw [hpd, hdI8]
    omega
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hbidx : (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
      ).toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat := by
    rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega), hdI8]
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ) - UInt8.ofNat m)).toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
      ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
        ).pileDepth[pile.toNat]'hpile).toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat m)).toNat - 1]'(by
            show (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
              ).toNat - 1 < 5
            omega) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  have hprevEq : (B + UInt8.ofNat m) - (1 + UInt8.ofNat m + UInt8.ofNat f)
      = B - 1 - UInt8.ofNat f := by
    have hfl8' : (1 + UInt8.ofNat m + UInt8.ofNat f) =
        UInt8.ofNat (1 + m + f) := by
      apply UInt8.toNat_inj.mp
      rw [hfl8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [hfl8']
    apply UInt8.toNat_inj.mp
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
    have hsumof : (UInt8.ofNat (1 + m + f)).toNat = 1 + m + f := by
      rw [UInt8.toNat_ofNat']; omega
    have hlt1 : B.toNat + m < 256 := by omega
    have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof, Nat.mod_eq_of_lt hlt1]
    have hle1 : UInt8.ofNat (1 + m + f) ≤ B + UInt8.ofNat m := by
      rw [UInt8.le_iff_toNat_le, hsumof, hBmB]; omega
    have hle2 : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hle3 : UInt8.ofNat f ≤ B - 1 := by
      rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2, show ((1 : UInt8).toNat = 1) from rfl]
      omega
    rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ hle2, hBmB, hsumof, hfof, show ((1 : UInt8).toNat = 1) from rfl]
    omega
  -- Depth-monotonicity bridge (`fluteNorm p` → the cleaned position), used by
  -- `isFreeCard_mono` everywhere below (mirrors `preCleanupPile_pileBase_ne`'s
  -- own `hdmono`).
  have hdec : ∀ i : Fin 10, ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get i).toNat ≤
      ((fluteNorm pile hpile p).pileDepth.get i).toNat :=
    preCleanupPile_pileDepth_le pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f hd5
      (by omega)
  -- `aces`/`kings` are entirely untouched by `preCleanupPile`.
  have haeq := preCleanupPile_aces_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
  have hkeqV := preCleanupPile_kings_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
  -- `SUIT(B+j) = SUIT B`/`VALUE(B+j) = VALUE B + j` for every `j ≤ m` (not just
  -- `j = m`): the merge-absorbed run never crosses a suit boundary.
  have hRCgen : ∀ j : Nat, j ≤ m →
      (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
    (merge_real_chain' g pile hpile hwf B (p.pileDepth[pile.toNat]'hpile) m hreal
      hmcards j hjm).2
  have hSjEq : ∀ j : Nat, j ≤ m → SUIT (B + UInt8.ofNat j) = SUIT B := by
    intro j hjm
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat j)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat j)
    have hb4 := VALUE_toNat B
    have hjB : (UInt8.ofNat j).toNat = j := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + j < 256 := by omega
    have hadd : (B + UInt8.ofNat j).toNat = B.toNat + j := by
      rw [UInt8.toNat_add, hjB, Nat.mod_eq_of_lt hlt256]
    have hvj := hRCgen j hjm
    omega
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := hSjEq m (le_refl m)
  -- `f = 0` whenever the ace-successor witness pins `A = B` exactly (else the
  -- freed loop's own `l = 1` fact would force the strict inequality
  -- `aces[SUIT B] < B - 1`, contradicting `aces[SUIT B] = B - 1`).
  -- Pure UInt8 group arithmetic: `A + 1 = B ⟹ A = B - 1`, via `toNat`
  -- injection (needs `A.toNat < 255`, from the suit/value bound).
  have hAeqBm1_of : (p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1 = B →
      (p.aces[(SUIT B).toUInt32.toNat]'hs4) = B - 1 := by
    intro hAB
    have hak1 : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4) =
        ((SUIT B).toUInt32.toNat).toUInt8 :=
      (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).aces_kings_valid.1
    have hb1 := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
    have hb2 := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
    have hb3 := congrArg UInt8.toNat hak1
    have hb4 : ((SUIT B).toUInt32.toNat).toUInt8.toNat = (SUIT B).toUInt32.toNat := by
      rw [UInt8.toNat_ofNat']; omega
    have hacesLt255 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat < 255 := by omega
    have htoNatSucc : ((p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1).toNat =
        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat + 1 :=
      toNat_succ _ hacesLt255
    have hABn := congrArg UInt8.toNat hAB
    rw [htoNatSucc] at hABn
    have hBm1 : (B - 1).toNat = B.toNat - 1 := UInt8.toNat_sub_of_le _ _ h1B
    apply UInt8.toNat_inj.mp
    rw [hBm1]; omega
  have hAeqB_implies_f0 : (p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1 = B →
      f = 0 := by
    intro hAB
    by_contra hfne
    have hf1 : 1 ≤ f := by omega
    have hg := (hffree 1 (le_refl 1) hf1).2
    have h1eq : (UInt8.ofNat 1 : UInt8) = 1 := rfl
    rw [h1eq] at hg
    have hUeq := hAeqBm1_of hAB
    rw [hUeq] at hg
    have hlt := UInt8.lt_iff_toInt_lt.mp hg
    omega
  -- `busyAces` monotonicity: `preCleanupPile` either leaves it alone or ORs in
  -- one more bit, so an already-set bit stays set (mirrors `nf_setBusyAces`).
  have hbusyMono : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).busyAces &&& mask ≠ 0 := by
    intro mask hmask
    show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f) then
        p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&& mask ≠ 0
    by_cases hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f)) = true
    · simp only [hcond, reduceIte]
      exact uint8_and_ne_zero_of_or_left hmask
    · rw [Bool.not_eq_true] at hcond
      simp only [hcond, Bool.false_eq_true, reduceIte]
      exact hmask
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) aces_kings_valid: `aces`/`kings` untouched.
    rw [haeq, hkeqV]
    exact (hnf.suitClean s).aces_kings_valid
  · -- (4a) foundation_cards_free: aces unchanged, freeness monotone.
    intro c h1 h2 h3
    rw [haeq] at h3
    exact isFreeCard_mono hdec ((hnf.suitClean s).foundation_cards_free c h1 h2 h3)
  · -- (4b-weak) foundation_maximal_weak: `aces` untouched, so only the
    -- `¬isFreeCard`/busy disjuncts need real work, and only for `s = SUIT B`
    -- (any other suit's witness can't be a merge-absorbed card).
    rw [haeq]
    by_cases hAV13 : (VALUE (p.aces.get s)).toNat = 13
    · exact Or.inl hAV13
    · have hvalid : SUIT (p.aces.get s) = s.val.toUInt8 ∧
          (VALUE (p.aces.get s)).toNat ≤ 13 ∧
          SUIT (p.kings.get s) = s.val.toUInt8 ∧
          (VALUE (p.kings.get s)).toNat ≤ 13 ∧
          p.aces.get s ≤ p.kings.get s := (hnf.suitClean s).aces_kings_valid
      have hAV12 : (VALUE (p.aces.get s)).toNat ≤ 12 := by
        have := hvalid.2.1; omega
      have hVlt15 : (VALUE (p.aces.get s)).toNat < 15 := by omega
      have hSA : SUIT ((p.aces.get s) + 1) = SUIT (p.aces.get s) :=
        SUIT_succ _ hVlt15
      have hVA : (VALUE ((p.aces.get s) + 1)).toNat =
          (VALUE (p.aces.get s)).toNat + 1 := VALUE_succ _ hVlt15
      have hSAeqSval : SUIT ((p.aces.get s) + 1) = s.val.toUInt8 :=
        hSA.trans hvalid.1
      rcases (hnf.suitClean s).foundation_maximal_weak with h13 | hnfreeA | hbusy
      · exact absurd h13 hAV13
      · -- disjunct 2: the successor was already not free.
        by_cases hexists : ∃ k, k ≤ m ∧ (p.aces.get s) + 1 = B + UInt8.ofNat k
        · obtain ⟨k, hkm, hkeqA⟩ := hexists
          have hSAeqBk : SUIT ((p.aces.get s) + 1) = SUIT B := by
            rw [hkeqA]; exact hSjEq k hkm
          have hSBeqSval : SUIT B = s.val.toUInt8 := hSAeqBk.symm.trans hSAeqSval
          have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
            have hb1 := congrArg UInt8.toNat hSBeqSval
            have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
            have hb3 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
          subst hseq
          have hAB' : (p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1 = B + UInt8.ofNat k :=
            hkeqA
          by_cases hk0 : k = 0
          · have hAB : (p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1 = B := by
              rw [hk0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero] at hAB'
              exact hAB'
            have hf0 := hAeqB_implies_f0 hAB
            subst hf0
            -- The successor sits exactly at the fresh boundary `B`, i.e.
            -- `aces = B - 1 - f` with `f = 0`: exactly `preCleanupPile`'s own
            -- busy-write condition, so the busy bit for `SUIT B` is set.
            refine Or.inr (Or.inr ?_)
            rw [← hsuiteq]
            show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                (B - 1 - UInt8.ofNat 0) then
                p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&&
              (1 <<< SUIT B) ≠ 0
            have hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                (B - 1 - UInt8.ofNat 0)) = true := by
              rw [show UInt8.ofNat 0 = 0 from rfl, UInt8.sub_zero, beq_iff_eq]
              exact (hAeqBm1_of hAB)
            rw [hcond]
            simp only [reduceIte]
            have hSBlt4 : (SUIT B).toNat < 4 := by
              have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
              omega
            exact uint8_and_ne_zero_of_or_right (uint8_shift_self_ne_zero (SUIT B) hSBlt4)
          · exfalso
            have hb1 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1)
            have hb0v := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
            have hb0s := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4)
            have hb4 := SUIT_toNat B
            have hb5' := VALUE_toNat B
            have hSA' : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1) =
                SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4) := hSA
            have hSAeqAces : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4) = SUIT B :=
              hSA'.symm.trans hSAeqBk
            have hb3' := congrArg UInt8.toNat hSAeqAces
            have hlt := UInt8.lt_iff_toNat_lt.mp haces_lt_B
            have hVeqCard := congrArg (fun x : UInt8 => (VALUE x).toNat) hAB'
            have hVeq2 := hRCgen k hkm
            have hVA' : (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4) + 1)).toNat =
                (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4)).toNat + 1 := hVA
            omega
        · refine Or.inr (Or.inl ?_)
          have hne : ∀ k, k ≤ m → (p.aces.get s) + 1 ≠ B + UInt8.ofNat k := by
            intro k hkm heq
            exact hexists ⟨k, hkm, heq⟩
          have hrealA : IsRealCard ((p.aces.get s) + 1) := by
            refine ⟨?_, by omega, by omega⟩
            have hSct := congrArg UInt8.toNat hSAeqSval
            have hb9 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B
            (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
            ((p.aces.get s) + 1) hrealA hne hnfreeA
      · -- busy bit already set before cleanup; `preCleanupPile` only ORs in
        -- more bits (`hbusyMono`), so it stays set.
        exact Or.inr (Or.inr (hbusyMono _ hbusy))
  · -- (9) king_frontier: `kings`/`aces` untouched; `busyAces` only gains bits
    -- (`hbusyMono`); the frontier witness `kings[s]` can only lose its
    -- not-free status if it happens to be one of the `m` merge-absorbed cards
    -- `B, …, B+m-1`, ruled out via suit/value matching against the entry's
    -- own `king_frontier` (`hVKge`) — except `kings[s]` could BE the
    -- still-boundary card `B+m` itself, handled directly as an ordinary
    -- "current pile boundary is never free" fact.
    rw [haeq, hkeqV]
    obtain ⟨hidxbm, heqbm⟩ := hmcards m (le_refl m)
    have hnfreeBm : ¬ isFreeCard g (fluteNorm pile hpile p) (B + UInt8.ofNat m) := by
      rw [← heqbm]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩ (by
        show ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat <
          (p.pileDepth[pile.toNat]'hpile).toNat
        rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega)]
        omega)
    have hrealBm : IsRealCard (B + UInt8.ofNat m) := by
      rw [← heqbm]; exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩
    have hVKge : (VALUE (p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4))).toNat ≥
        (VALUE (B + UInt8.ofNat m)).toNat := by
      by_contra hlt
      push Not at hlt
      apply hnfreeBm
      have hall := (hnf.suitClean (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).king_frontier.2
      exact hall _ ((hSjEq m (le_refl m)).trans hsuiteq) hlt hrealBm.2.2
    refine ⟨?_, ?_⟩
    · rcases (hnf.suitClean s).king_frontier.1 with ⟨hkeqA, hcase⟩ | ⟨hv1, hnfree⟩
      · exact Or.inl ⟨hkeqA, hcase.imp id (fun hb => hbusyMono _ hb)⟩
      · refine Or.inr ⟨hv1, ?_⟩
        by_cases hkm_eq : (p.kings.get s) = B + UInt8.ofNat m
        · -- `kings[s]` is exactly the still-boundary card `B+m`: forces
          -- `s = SUIT B`; the freshly-written boundary is never free.
          have hSKeqB : SUIT (p.kings.get s) = SUIT B := by
            rw [hkm_eq]; exact hSjEq m (le_refl m)
          have hSKeqSval : SUIT (p.kings.get s) = s.val.toUInt8 :=
            (hnf.suitClean s).aces_kings_valid.2.2.1
          have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
            have hb1 := congrArg UInt8.toNat (hSKeqB.symm.trans hSKeqSval)
            have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
            have hb3 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
          subst hseq
          have hkm_eq' : (p.kings[(SUIT B).toUInt32.toNat]'hs4) = B + UInt8.ofNat m :=
            hkm_eq
          intro hfree
          have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10) ⟨_, hidxbm⟩
          have heqbm' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
              ⟨((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat,
                hidxbm⟩ = B + UInt8.ofNat m := heqbm
          rw [heqbm', ← hkm_eq'] at hrt
          have hc64 : (p.kings[(SUIT B).toUInt32.toNat]'hs4).toNat < 64 := by
            have hreal' := hrealBm
            rw [← hkm_eq'] at hreal'
            have h1 := hreal'.1
            have h2 := hreal'.2.1
            have h3 := hreal'.2.2
            have hsn := SUIT_toNat (p.kings[(SUIT B).toUInt32.toNat]'hs4)
            omega
          have hp64 : (cardPile g (p.kings[(SUIT B).toUInt32.toNat]'hs4)).toNat < 10 := by
            rw [hrt.1]; exact hpile
          have hge := isFree_to_cardDepth_ge g _ hwf _ hc64 hp64 hfree
          have hgoal2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p
              ).pileDepth[(cardPile g (p.kings[(SUIT B).toUInt32.toNat]'hs4)).toNat]'hp64
              = (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
            have hstep : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p
                ).pileDepth[(cardPile g
                  (p.kings[(SUIT B).toUInt32.toNat]'hs4)).toNat]'hp64
                = (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile := by
              congr 1
              exact hrt.1
            rw [hstep, hpd]
          rw [hrt.2, hgoal2] at hge
          have hge' : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat ≥
              ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat := hge
          rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_one_eq hd5 (by omega), hdI8] at hge'
          omega
        · -- `kings[s]` is genuinely NOT the still-boundary card: either a
          -- different suit entirely, or (same suit) provably below `B+m` in
          -- value — either way it's not one of the `m` absorbed cards.
          have hne : ∀ k, k ≤ m → (p.kings.get s) ≠ B + UInt8.ofNat k := by
            intro k hkm heq
            by_cases hkeqm : k = m
            · exact hkm_eq (hkeqm ▸ heq)
            · have hklm : k < m := by omega
              by_cases hSK : SUIT (p.kings.get s) = SUIT B
              · have hSKeqSval : SUIT (p.kings.get s) = s.val.toUInt8 :=
                  (hnf.suitClean s).aces_kings_valid.2.2.1
                have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
                  have hb1 := congrArg UInt8.toNat (hSK.symm.trans hSKeqSval)
                  have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                    UInt8.toNat_toUInt32 (SUIT B)
                  have hb3 : s.val.toUInt8.toNat = s.val := by
                    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
                  omega
                have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
                subst hseq
                have hVeq := congrArg (fun x : UInt8 => (VALUE x).toNat) heq
                have hVeqk := hRCgen k hkm
                have hVeqm := hRCgen m (le_refl m)
                omega
              · exact hSK (heq ▸ hSjEq k hkm)
          have hrealK : IsRealCard (p.kings.get s) := by
            have hSAs : SUIT (p.aces.get s) = s.val.toUInt8 :=
              (hnf.suitClean s).aces_kings_valid.1
            have hSs : SUIT (p.kings.get s) = s.val.toUInt8 :=
              (hnf.suitClean s).aces_kings_valid.2.2.1
            have hAKlt : (p.aces.get s).toNat < (p.kings.get s).toNat :=
              UInt8.lt_iff_toNat_lt.mp (show p.aces.get s < p.kings.get s from hv1)
            have hb1 := VALUE_toNat (p.aces.get s)
            have hb2 := SUIT_toNat (p.aces.get s)
            have hb3 := congrArg UInt8.toNat hSAs
            have hb4 := VALUE_toNat (p.kings.get s)
            have hb5 := SUIT_toNat (p.kings.get s)
            have hb6 := congrArg UInt8.toNat hSs
            have hb7 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hsval := s.isLt
            have hVKge1 : 1 ≤ (VALUE (p.kings.get s)).toNat := by omega
            have hs4' : (SUIT (p.kings.get s)).toNat < 4 := by omega
            exact ⟨hs4', hVKge1, (hnf.suitClean s).aces_kings_valid.2.2.2.1⟩
          exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B
            (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
            (p.kings.get s) hrealK hne hnfree
    · intro c hSc hgt hle
      exact isFreeCard_mono hdec ((hnf.suitClean s).king_frontier.2 c hSc hgt hle)

/-- **`preCleanupPile` preserves the `hash_def` field of `SolverInvBase`.**  The
    hash only depends on `pileDepth` (via the fixed `pileHashes` dot product),
    so only the depth-shrink arithmetic (`hd5`/`hm_le` ⇒ `hdI8`) is needed: the
    merge loop subtracted `m·ph` from `p.hash`, matching the depth decrease of
    exactly `m` at `pile` in the dot product (`hash_foldl_set` isolates that
    one term, then `UInt32.ofNat_add`/`mul_add` splits off the `m` part to
    match `preCleanupPile`'s own `hash := p.hash - UInt32.ofNat m * ph` field). -/
theorem preCleanupPile_hash_def (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat) :
    (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).hash =
      (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
        ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get i
          ).toNat.toUInt32) 0 := by
  show p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) =
    (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
      (((p.pileDepth.set pile.toNat
        ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile).get i)
        ).toNat.toUInt32) 0
  have hhd : p.hash = (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
      (p.pileDepth.get i).toNat.toUInt32) 0 := hnf.hash_def
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  have hclamp : (p.pileDepth[pile.toNat]'hpile).toNat =
      (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
        ).toNat + m := by
    rw [hdI8]
    omega
  have hadd := hash_foldl_set p.pileDepth pile.toNat hpile
    (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
  rw [hclamp,
    show ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
        ).toNat + m).toUInt32 =
      UInt32.ofNat ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
        ).toNat + m) from rfl,
    UInt32.ofNat_add, UInt32.mul_add] at hadd
  have h2 := congrArg
    (· - ((pileHashes[pile.toNat]'hpile) *
      UInt32.ofNat ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
        ).toNat) +
      (pileHashes[pile.toNat]'hpile) * UInt32.ofNat m)) hadd
  rw [UInt32.add_sub_cancel, uint32_sub_add, UInt32.add_sub_cancel] at h2
  have hfoldEq : (List.finRange 10).foldl (fun acc i =>
        acc + pileHashes.get i * (p.pileDepth.get i).toNat.toUInt32) 0 =
      (List.finRange 10).foldl (fun acc i =>
        acc + pileHashes.get i * (p.pileDepth.get i).toNat.toUInt32) 0 := rfl
  rw [hfoldEq] at h2
  rw [hhd, UInt32.mul_comm (UInt32.ofNat m) (pileHashes[pile.toNat]'hpile), ← h2]

set_option maxHeartbeats 1000000 in
/-- **`preCleanupPile` preserves the `usedSpace_def` field of `SolverInvBase`.**
    Both `pileDepth` and `pileFlute` change at `pile`: depth shrinks by `m`
    (`depth_sum_foldl_set`), and the flute-term goes from `0` (normalized
    entry: depth `d0 > 0`, flute `1`) to `m+f` (depth `d0-m > 0` — still
    nonzero since `hd5`/`hm_le` bound `m ≤ d0-1` — flute `1+m+f`,
    `usedSpace_term_foldl_set`); combined with the `f` lost from `usedSpace`
    itself (`preCleanupPile`'s own `usedSpace := p.usedSpace - UInt8.ofNat f`
    field), the ledger balances exactly.  The final `UInt8` arithmetic
    (`usedSpace - f`) doesn't wrap because `usedSpace_bounded` bounds
    `p.usedSpace.toInt ∈ [0,52]` and `f ≤ B.toNat - 1 ≤ 60`. -/
theorem preCleanupPile_usedSpace_def (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8))
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < B - UInt8.ofNat l)
    (hBrange2 : B.toNat ≤ 61) :
    (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile) m f p).usedSpace.toInt =
      (52 : Int)
      - ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
      - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - ((List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.toList
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.toList
          |>.foldl (·+·) 0 : Nat)) := by
  have hfl8 : (1 + UInt8.ofNat m + UInt8.ofNat f).toNat = 1 + m + f := by
    have hmof8 : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hfof8 : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
    rw [UInt8.toNat_add, UInt8.toNat_add, hmof8, hfof8,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  have hdI8 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m :=
    depth_sub_ofNat_eq hd5 (by omega)
  show (p.usedSpace - UInt8.ofNat f).toInt =
    (52 : Int)
    - ((p.pileDepth.set pile.toNat
        ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile
        ).toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
    - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
    - ((List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        (p.pileDepth.set pile.toNat
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile).toList
        (p.pileFlute.set pile.toNat
          ((1 + UInt8.ofNat m + UInt8.ofNat f)) hpile).toList
        |>.foldl (·+·) 0 : Nat))
  have hud : p.usedSpace.toInt = (52 : Int)
      - (p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
      - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          p.pileDepth.toList (p.pileFlute.set pile.toNat 1 hpile).toList
          |>.foldl (·+·) 0 : Nat) :=
    hnf.usedSpace_def
  have hds := depth_sum_foldl_set p.pileDepth pile.toNat hpile
    (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
  have hft_norm : (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList (p.pileFlute.set pile.toNat 1 hpile).toList
        |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) then
          (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) then
          (1 : UInt8).toNat - 1 else 0) := by
    have h := usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
      (p.pileDepth[pile.toNat]'hpile) (1 : UInt8)
    rwa [Vector.set_getElem_self hpile] at h
  have hft_new : (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        (p.pileDepth.set pile.toNat
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile).toList
        (p.pileFlute.set pile.toNat
          ((1 + UInt8.ofNat m + UInt8.ofNat f)) hpile).toList
        |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) then
          (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (·+·) 0 : Nat)
      + (if (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
          ≠ (0 : UInt8) then
          ((1 + UInt8.ofNat m + UInt8.ofNat f)).toNat - 1 else 0) :=
    usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
      (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
      ((1 + UInt8.ofNat m + UInt8.ofNat f))
  have hd' : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) := hd
  have ho : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) then
      (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (p.pileFlute[pile.toNat]'hpile).toNat - 1 := if_pos hd'
  have hn : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) then
      (1 : UInt8).toNat - 1 else 0) = 0 := if_pos hd'
  have hne1 : (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
      ≠ (0 : UInt8) := by
    intro heq
    have hz0 := congrArg UInt8.toNat heq
    rw [hdI8, show ((0 : UInt8).toNat = 0) from rfl] at hz0
    omega
  have hz : (if (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m))
      ≠ (0 : UInt8) then
      ((1 + UInt8.ofNat m + UInt8.ofNat f)).toNat - 1 else 0) = m + f := by
    rw [if_pos hne1, hfl8]
    omega
  simp only [ho, hn] at hft_norm
  simp only [ho, hz] at hft_new
  have hXNat : ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
      )).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m := hdI8
  have hpdNat : (p.pileDepth[pile.toNat]'hpile).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat := rfl
  have hXNat' : ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m)
      )).toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - m := hXNat
  have hspace_bound : p.usedSpace.toInt ≤ 52 := by
    have h := usedSpace_bounded hwf hnf
    rwa [show (fluteNorm pile hpile p).usedSpace = p.usedSpace from rfl] at h
  have hud2 : p.usedSpace.toInt = (52 : Int)
      - ((p.pileDepth.set pile.toNat
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile
        ).toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
      - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - ((List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          (p.pileDepth.set pile.toNat
            ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile).toList
          (p.pileFlute.set pile.toNat
            ((1 + UInt8.ofNat m + UInt8.ofNat f)) hpile).toList
          |>.foldl (·+·) 0 : Nat)) + f := by
    rw [hud]
    simp only [UInt8.toInt_eq] at *
    omega
  have hfInt : (UInt8.ofNat f).toInt = (f : Int) := by
    show ((UInt8.ofNat f).toNat : Int) = _
    rw [UInt8.toNat_ofNat']
    congr 1
    omega
  -- Bridge `hidx`/`hBdef`'s Int32-cast index to the plain `.toNat - 1` form
  -- used by `usedSpace_ge_freed_run`/`depth_card_not_free`/`pos2card_inj`.
  have hidxEq : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat =
      (p.pileDepth[pile.toNat]'hpile).toNat - 1 := by
    rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _
      (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]
    rfl
  -- `B` is a real card (it's `g.pos2card`'s own entry).
  have hBreal : IsRealCard B := by
    rw [← hBdef]
    exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ ⟨_, hidx⟩
  -- `B` is still physically in pile `pile` (it's `fluteNorm`'s own boundary card).
  have hBnotfreeQ : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
    rw [← hBdef]
    refine depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩ ⟨_, hidx⟩ ?_
    show ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat <
      (p.pileDepth[pile.toNat]'hpile).toNat
    rw [hidxEq]
    omega
  -- `isFreeCard`/`aces` only depend on `pileDepth`, which `fluteNorm` never
  -- touches, so `hffree` (about `p`) transfers to `fluteNorm pile hpile p`
  -- verbatim.
  have hffreeQ : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g (fluteNorm pile hpile p) (B - UInt8.ofNat l) ∧
      (fluteNorm pile hpile p).aces[(SUIT B).toUInt32.toNat]'hs4 < B - UInt8.ofNat l :=
    hffree
  -- `B` cannot ALSO be a different pile `j`'s boundary card (`pos2card_inj`),
  -- and it IS `pile`'s own boundary with `fluteNorm`'s freshly-set flute `1`.
  have hBflute1Q : ∀ (j : Fin 10)
      (hdj : ((fluteNorm pile hpile p).pileDepth.get j).toNat > 0),
      (g.pos2card.get j).get ⟨((fluteNorm pile hpile p).pileDepth.get j).toNat - 1,
          by have := hnf.pileDepth_bound j; omega⟩ = B →
      (fluteNorm pile hpile p).pileFlute.get j = 1 := by
    intro j hdj heq
    by_cases hjp : j.val = pile.toNat
    · have hjeq : j = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hjp
      subst hjeq
      show (fluteNorm pile hpile p).pileFlute[pile.toNat]'hpile = 1
      simp only [fluteNorm]
      rw [Vector.getElem_set_self]
    · exfalso
      have hjq : (fluteNorm pile hpile p).pileDepth.get j = p.pileDepth.get j := rfl
      have hidxj : (p.pileDepth.get j).toNat - 1 < 5 := by
        have hb := hnf.pileDepth_bound j
        rw [hjq] at hb
        omega
      have heq' : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩ = B := heq
      have hcontra := hwf.pos2card_inj j ⟨pile.toNat, hpile⟩
        ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩ ⟨_, hidx⟩ (heq'.trans hBdef.symm)
      exact hjp (congrArg Fin.val hcontra.1)
  -- The counting argument (`usedSpace_ge_freed_run`, extracted from
  -- `usedSpace_bounded`'s disjointness proof): the `f` cards the freed loop
  -- absorbed are all distinct from every card the layout is currently
  -- charging for, so `usedSpace` must already have room for them.
  have hfBound : (f : Int) ≤ p.usedSpace.toInt := by
    have hUsedEq : (fluteNorm pile hpile p).usedSpace = p.usedSpace := rfl
    rw [← hUsedEq]
    exact usedSpace_ge_freed_run hwf hnf B hBreal hBnotfreeQ hs4 f hf_le_tight hffreeQ hBflute1Q
  have hsub : (p.usedSpace - UInt8.ofNat f).toInt = p.usedSpace.toInt - f := by
    rw [UInt8.toInt_sub, hfInt]
    omega
  rw [hsub, hud]
  simp only [UInt8.toInt_eq] at *
  omega

-- `cleanupPile_baseNF`'s discharge has grown large enough (12 clauses × 2
-- branches, each needing its own index/arithmetic bookkeeping) that the
-- default 200000-heartbeat budget is exceeded on unrelated later bullets
-- purely from the theorem's overall size — confirmed by reproducing the
-- timeout even with the newest clause `sorry`'d out (so it isn't a specific
-- broken `rfl`/`exact` looping forever; it's cumulative elaboration cost).
-- Same remedy already used elsewhere in this file's `rfl`-twin proofs.

end SolverSpec
