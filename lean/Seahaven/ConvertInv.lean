import Seahaven.ConvertCount

/-!
# The prologue establishes the base invariant

`convertPre g pk` — the position `SolverConvertFromPilesKings`'s first two loops
produce — satisfies `MergedUpTo g · 0`, the entry condition of the per-pile
cleanup loop: `SolverInvBase` globally, `freePiles` counting the (empty) processed
prefix, and every pile still carrying the default `pileFlute = 1`.

The per-pile clauses are cheap (a flute of length `1` has no interior), and the
per-suit clauses are exactly what the two walks were written to establish:

* `foundation_cards_free` / `king_frontier`'s upper run — `runLen_holds`;
* `foundation_maximal_weak` / `king_frontier`'s frontier — `runLen_stop`;
* `flute_not_aces` — a pile's boundary card is not free, so the foundation walk,
  which only ever counts free cards, stopped strictly below it.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## Card decomposition -/

theorem cv_card_decomp (c : UInt8) :
    CARD (UInt8.ofNat (SUIT c).toNat) (UInt8.ofNat (VALUE c).toNat) = c := by
  have hs : (SUIT c).toNat < 16 := by
    rw [SUIT_toNat]; have := c.toNat_lt; omega
  have hv : (VALUE c).toNat < 16 := by rw [VALUE_toNat]; omega
  apply UInt8.toNat_inj.mp
  rw [CARD_toNat hs hv, SUIT_toNat, VALUE_toNat]
  omega

theorem cv_suit_lt16 (c : UInt8) : (SUIT c).toNat < 16 := by
  rw [SUIT_toNat]; have := c.toNat_lt; omega

theorem cv_value_lt16 (c : UInt8) : (VALUE c).toNat < 16 := by
  rw [VALUE_toNat]; omega

/-! ## Reading `convertPre`'s fields -/

variable (g : Globals) (pk : Vector UInt8 11)

@[simp] theorem convertPre_pileDepth : (convertPre g pk).pileDepth = cvDepths pk := rfl
@[simp] theorem convertPre_freePiles : (convertPre g pk).freePiles = 0 := rfl
@[simp] theorem convertPre_busyAces : (convertPre g pk).busyAces = 0 := rfl
@[simp] theorem convertPre_hash : (convertPre g pk).hash = cvHash pk := rfl

@[simp] theorem convertPre_pileFlute (i : Fin 10) : (convertPre g pk).pileFlute.get i = 1 := by
  show (Vector.ofFn (fun _ : Fin 10 => (1 : UInt8)))[i.val]'i.isLt = 1
  rw [Vector.getElem_ofFn]

@[simp] theorem convertPre_aces (s : Fin 4) : (convertPre g pk).aces.get s =
    CARD (UInt8.ofNat s.val) (UInt8.ofNat (cvAceVal g (cvDepths pk) s.val)) := by
  show (Vector.ofFn (fun i : Fin 4 =>
    CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvAceVal g (cvDepths pk) i.val))))[s.val]'s.isLt = _
  rw [Vector.getElem_ofFn]

@[simp] theorem convertPre_kings (s : Fin 4) : (convertPre g pk).kings.get s =
    CARD (UInt8.ofNat s.val) (UInt8.ofNat (cvKingVal g (cvDepths pk) s.val)) := by
  show (Vector.ofFn (fun i : Fin 4 =>
    CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvKingVal g (cvDepths pk) i.val))))[s.val]'s.isLt = _
  rw [Vector.getElem_ofFn]

/-- Freeness at `convertPre` is freeness at the installed depths. -/
theorem convertPre_free (c : UInt8) :
    isFreeCard g (convertPre g pk) c = freeAt g (cvDepths pk) c := rfl

/-! ## Elementary facts about the two walk values -/

theorem cvAceVal_le (d : Vector UInt8 10) (su : Nat) : cvAceVal g d su ≤ 13 :=
  runLen_le _ _

theorem cvKingVal_le (d : Vector UInt8 10) (su : Nat) : cvKingVal g d su ≤ 13 := by
  unfold cvKingVal
  split
  · omega
  · omega

/-- Cards `1 … cvAceVal` of a suit are free. -/
theorem cvAceVal_free (d : Vector UInt8 10) (su w : Nat) (h1 : 1 ≤ w)
    (hw : w ≤ cvAceVal g d su) : freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat w)) := by
  have h2 : freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (w - 1 + 1))) :=
    runLen_holds (aceFree g d su) 13 (w - 1) (by
      have : cvAceVal g d su = runLen (aceFree g d su) 13 := rfl
      omega)
  rwa [show w - 1 + 1 = w from by omega] at h2

/-- The card just above the foundation top is not free (unless the suit is done). -/
theorem cvAceVal_stop (d : Vector UInt8 10) (su : Nat) (h : cvAceVal g d su < 13) :
    ¬ freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (cvAceVal g d su + 1))) :=
  runLen_stop (aceFree g d su) 13 h

/-- The king frontier is at least the foundation top. -/
theorem cvAceVal_le_cvKingVal (d : Vector UInt8 10) (su : Nat) :
    cvAceVal g d su ≤ cvKingVal g d su := by
  unfold cvKingVal
  split
  · omega
  · rename_i hne
    have hA : cvAceVal g d su < 13 := by have := cvAceVal_le g d su; omega
    have hT : cvKingRun g d su ≤ 12 := cvKingRun_le g d su hA
    have hTdef : runLen (kingFree g d su) 13 = cvKingRun g d su := rfl
    by_contra hc
    -- if the king run reached past the foundation top, card `A+1` would be free
    have h2 : freeAt g d
        (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - (12 - cvAceVal g d su)))) :=
      runLen_holds (kingFree g d su) 13 (12 - cvAceVal g d su) (by omega)
    rw [show 13 - (12 - cvAceVal g d su) = cvAceVal g d su + 1 from by omega] at h2
    exact cvAceVal_stop g d su hA h2

/-- Cards strictly above the king frontier are free. -/
theorem cvKingVal_free (d : Vector UInt8 10) (su w : Nat)
    (hw : cvKingVal g d su < w) (hw13 : w ≤ 13) :
    freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat w)) := by
  have hA : cvAceVal g d su < 13 := by
    by_contra hc
    have hA13 : cvAceVal g d su = 13 := by have := cvAceVal_le g d su; omega
    unfold cvKingVal at hw
    rw [if_pos hA13] at hw
    omega
  have hT : cvKingRun g d su ≤ 12 := cvKingRun_le g d su hA
  have hKV : cvKingVal g d su = 13 - cvKingRun g d su := by
    unfold cvKingVal; rw [if_neg (by omega)]
  have hTdef : runLen (kingFree g d su) 13 = cvKingRun g d su := rfl
  have h2 : freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - (13 - w)))) :=
    runLen_holds (kingFree g d su) 13 (13 - w) (by omega)
  rwa [show 13 - (13 - w) = w from by omega] at h2

/-- The king frontier itself is not free (when the suit is not entirely freed). -/
theorem cvKingVal_stop (d : Vector UInt8 10) (su : Nat) (hA : cvAceVal g d su < 13) :
    ¬ freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (cvKingVal g d su))) := by
  have hT : cvKingRun g d su ≤ 12 := cvKingRun_le g d su hA
  have hKV : cvKingVal g d su = 13 - cvKingRun g d su := by
    unfold cvKingVal; rw [if_neg (by omega)]
  have hTdef : runLen (kingFree g d su) 13 = cvKingRun g d su := rfl
  rw [hKV]
  exact runLen_stop (kingFree g d su) 13 (by omega)

/-! ## Sum bridges for `usedSpace_def` -/

theorem vec_foldl_add_eq_sum {n : Nat} {α : Type} (v : Vector α n) (f : α → Nat) :
    v.toList.foldl (fun acc x => acc + f x) 0 = ∑ i : Fin n, f (v.get i) := by
  have h1 : v.toList = List.ofFn v.get := by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp only [List.getElem_ofFn, Vector.getElem_toList]
      rfl
  rw [h1,
    show (List.ofFn v.get).foldl (fun acc x => acc + f x) 0
      = ((List.ofFn v.get).map f).foldl (·+·) 0 from (List.foldl_map ..).symm,
    List.map_ofFn]
  rw [show ((List.ofFn (f ∘ v.get)).foldl (·+·) 0) = (List.ofFn (f ∘ v.get)).sum from
    (by induction (List.ofFn (f ∘ v.get)) with
        | nil => simp
        | cons a l ih =>
          rw [List.foldl_cons, Nat.zero_add]
          have h := @List.foldl_assoc Nat (·+·) _ l a 0
          simp only [Nat.add_zero] at h
          rw [h, ih, List.sum_cons]), List.sum_ofFn]
  rfl

theorem zipWith_flute_one_zero (dv fv : Vector UInt8 10) (hf : ∀ i : Fin 10, fv.get i = 1) :
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
      dv.toList fv.toList).foldl (·+·) 0 = 0 := by
  have hrep : List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
      dv.toList fv.toList = List.replicate 10 0 := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi10 : i < 10 := by
        have := h1
        rw [List.length_zipWith, Vector.length_toList, Vector.length_toList] at this
        omega
      rw [List.getElem_zipWith, List.getElem_replicate, Vector.getElem_toList,
        Vector.getElem_toList]
      have : fv.get ⟨i, hi10⟩ = 1 := hf ⟨i, hi10⟩
      show (if dv[i]'hi10 ≠ (0 : UInt8) then (fv[i]'hi10).toNat - 1 else 0) = 0
      rw [show (fv[i]'hi10) = fv.get ⟨i, hi10⟩ from rfl, this]
      split <;> rfl
  rw [hrep]
  decide

/-! ## The base invariant -/

set_option maxHeartbeats 1000000 in
theorem convertPre_pileBase (hwf : WellFormedLayout g) (hpk : ValidDepths pk) (i : Fin 10) :
    PileBase g (convertPre g pk) i := by
  have hd5 : ((cvDepths pk).get i).toNat ≤ 5 := by rw [cvDepths_get]; exact hpk i
  have hdepi : (convertPre g pk).pileDepth.get i = (cvDepths pk).get i := rfl
  refine ⟨by rw [hdepi]; exact hd5, ?_, ?_, ?_, ?_⟩
  · rw [convertPre_pileFlute]; decide
  · intro _; rw [convertPre_pileFlute]
  · intro j _ hj0 hjlt
    rw [convertPre_pileFlute] at hjlt
    exfalso
    have h1 : ((1 : UInt8).toNat) = 1 := rfl
    omega
  · intro hdpos
    have hdpos' : ((cvDepths pk).get i).toNat > 0 := hdpos
    have hidx : ((cvDepths pk).get i).toNat - 1 < 5 := by omega
    intro B hs
    -- `B` is the let-bound boundary card; it is not free, so the foundation walk
    -- stopped strictly below it
    have hBdef : B = (g.pos2card.get i).get
        ⟨((cvDepths pk).get i).toNat - 1, hidx⟩ := rfl
    have hBnf : ¬ freeAt g (cvDepths pk) B := by
      rw [hBdef]
      exact depthSlot_not_free g hwf (cvDepths pk) i
        ⟨((cvDepths pk).get i).toNat - 1, hidx⟩
        (show ((cvDepths pk).get i).toNat - 1 < ((cvDepths pk).get i).toNat from by omega)
    have hBreal : IsRealCard B := hBdef ▸ hwf.pos2card_real i ⟨_, hidx⟩
    obtain ⟨A, hAdef⟩ : ∃ A, cvAceVal g (cvDepths pk) (SUIT B).toNat = A := ⟨_, rfl⟩
    have hA13 : A ≤ 13 := by rw [← hAdef]; exact cvAceVal_le g _ _
    have hlt : A < (VALUE B).toNat := by
      by_contra hc
      refine hBnf ?_
      have hfr := cvAceVal_free g (cvDepths pk) (SUIT B).toNat (VALUE B).toNat hBreal.2.1
        (by rw [hAdef]; omega)
      rwa [cv_card_decomp B] at hfr
    show ((convertPre g pk).aces.get ⟨(SUIT B).toNat, hs⟩).toNat
      + ((convertPre g pk).pileFlute.get i).toNat ≤ B.toNat
    rw [convertPre_pileFlute, convertPre_aces]
    show (CARD (UInt8.ofNat (SUIT B).toNat)
      (UInt8.ofNat (cvAceVal g (cvDepths pk) (SUIT B).toNat))).toNat
        + (1 : UInt8).toNat ≤ B.toNat
    rw [hAdef, cv_card_toNat hs (by omega), show ((1 : UInt8).toNat = 1) from rfl]
    have hbd : B.toNat = (SUIT B).toNat * 16 + (VALUE B).toNat := by
      rw [SUIT_toNat, VALUE_toNat]; omega
    omega

set_option maxHeartbeats 1000000 in
theorem convertPre_suitClean (s : Fin 4)
    (hb : ∀ i : Fin 10, ((convertPre g pk).pileDepth.get i).toNat ≤ 5) :
    SuitClean g (convertPre g pk) s hb := by
  have hsu : s.val < 4 := s.isLt
  obtain ⟨A, hAdef⟩ : ∃ A, cvAceVal g (cvDepths pk) s.val = A := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, cvKingVal g (cvDepths pk) s.val = K := ⟨_, rfl⟩
  have hA13 : A ≤ 13 := by rw [← hAdef]; exact cvAceVal_le g _ _
  have hK13 : K ≤ 13 := by rw [← hKdef]; exact cvKingVal_le g _ _
  have hAK : A ≤ K := by rw [← hAdef, ← hKdef]; exact cvAceVal_le_cvKingVal g _ _
  have hacesEq : (convertPre g pk).aces.get s = CARD (UInt8.ofNat s.val) (UInt8.ofNat A) := by
    rw [convertPre_aces, hAdef]
  have hkingsEq : (convertPre g pk).kings.get s = CARD (UInt8.ofNat s.val) (UInt8.ofNat K) := by
    rw [convertPre_kings, hKdef]
  have hfree : ∀ c : UInt8, isFreeCard g (convertPre g pk) c = freeAt g (cvDepths pk) c :=
    fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [hacesEq, cv_card_suit hsu (by omega)]
  · rw [hacesEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat']; omega
  · rw [hkingsEq, cv_card_suit hsu (by omega)]
  · rw [hkingsEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat']; omega
  · rw [hacesEq, hkingsEq, cv_card_le hsu (by omega) (by omega)]; omega
  · -- foundation cards are free
    intro c hcs hc1 hcA
    rw [hacesEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat'] at hcA
    have hcsu : (SUIT c).toNat = s.val := by rw [hcs, UInt8.toNat_ofNat']; omega
    have hv16 : (VALUE c).toNat < 16 := cv_value_lt16 c
    have hfr := cvAceVal_free g (cvDepths pk) s.val (VALUE c).toNat hc1 (by rw [hAdef]; omega)
    rw [← hcsu, cv_card_decomp c] at hfr
    rw [hfree]
    exact hfr
  · -- foundation maximal (weak)
    rw [hacesEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat']
    by_cases h13 : A = 13
    · left; omega
    · right; left
      rw [hfree, cv_card_succ hsu (by omega)]
      have := cvAceVal_stop g (cvDepths pk) s.val (by rw [hAdef]; omega)
      rw [hAdef] at this
      exact this
  · -- king frontier
    by_cases h13 : A = 13
    · left
      refine ⟨?_, ?_⟩
      · rw [hacesEq, hkingsEq]
        have hKeq : K = 13 := by
          rw [← hKdef]; unfold cvKingVal; rw [if_pos (by rw [hAdef]; exact h13)]
        rw [hKeq, h13]
      · left; rw [hacesEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat']; omega
    · right
      have hA : A < 13 := by omega
      have hAlt : A < K := by
        rw [← hAdef, ← hKdef]
        have hstop := cvAceVal_stop g (cvDepths pk) s.val (by rw [hAdef]; omega)
        by_contra hc
        have hT : cvKingRun g (cvDepths pk) s.val ≤ 12 :=
          cvKingRun_le g (cvDepths pk) s.val (by rw [hAdef]; omega)
        have hKV : cvKingVal g (cvDepths pk) s.val = 13 - cvKingRun g (cvDepths pk) s.val := by
          unfold cvKingVal; rw [if_neg (by rw [hAdef]; omega)]
        have hTdef : runLen (kingFree g (cvDepths pk) s.val) 13
            = cvKingRun g (cvDepths pk) s.val := rfl
        rw [hAdef, hKdef] at *
        have h2 : freeAt g (cvDepths pk)
            (CARD (UInt8.ofNat s.val) (UInt8.ofNat (13 - (12 - A)))) :=
          runLen_holds (kingFree g (cvDepths pk) s.val) 13 (12 - A) (by omega)
        rw [show 13 - (12 - A) = A + 1 from by omega] at h2
        exact hstop h2
      refine ⟨?_, ?_⟩
      · rw [hacesEq, hkingsEq, cv_card_lt hsu (by omega) (by omega)]; exact hAlt
      · rw [hfree, hkingsEq, ← hKdef]
        exact cvKingVal_stop g (cvDepths pk) s.val (by rw [hAdef]; omega)
  · -- cards above the king frontier are free
    intro c hcs hcK hc13
    rw [hkingsEq, cv_card_value hsu (by omega), UInt8.toNat_ofNat'] at hcK
    have hcsu : (SUIT c).toNat = s.val := by rw [hcs, UInt8.toNat_ofNat']; omega
    have hfr := cvKingVal_free g (cvDepths pk) s.val (VALUE c).toNat
      (by rw [hKdef]; omega) hc13
    rw [← hcsu, cv_card_decomp c] at hfr
    rw [hfree]
    exact hfr

set_option maxHeartbeats 1000000 in
theorem convertPre_usedSpace_def (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    (convertPre g pk).usedSpace.toInt =
      (52 : Int)
      - ((convertPre g pk).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
      - ((convertPre g pk).aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          (convertPre g pk).pileDepth.toList (convertPre g pk).pileFlute.toList
            |>.foldl (· + ·) 0 : Nat) := by
  have hcount : CvCountBound g pk := cvCountBound g hwf pk hpk
  obtain ⟨DS, hDS⟩ : ∃ DS, cvDepthPrefix pk 10 = DS := ⟨_, rfl⟩
  obtain ⟨AS, hAS⟩ : ∃ AS, cvAcePrefix g (cvDepths pk) 4 = AS := ⟨_, rfl⟩
  have hbound : DS + AS ≤ 52 := by unfold CvCountBound at hcount; omega
  have hdsum : (convertPre g pk).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 = DS := by
    show (cvDepths pk).toList.foldl (fun acc d => acc + d.toNat) 0 = DS
    rw [vec_foldl_add_eq_sum, ← cvDepthPrefix_ten pk, hDS]
  have hasum : (convertPre g pk).aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0
      = AS := by
    rw [vec_foldl_add_eq_sum, ← hAS, cvAcePrefix_four g (cvDepths pk)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [convertPre_aces, cv_card_value s.isLt
      (by have := cvAceVal_le g (cvDepths pk) s.val; omega), UInt8.toNat_ofNat']
    have := cvAceVal_le g (cvDepths pk) s.val
    omega
  have hzsum : (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
      (convertPre g pk).pileDepth.toList (convertPre g pk).pileFlute.toList).foldl (· + ·) 0
      = 0 := zipWith_flute_one_zero _ _ (convertPre_pileFlute g pk)
  rw [hdsum, hasum, hzsum]
  show ((UInt8.ofNat (52 - cvDepthPrefix pk 10 - cvAcePrefix g (cvDepths pk) 4)).toNat : Int) = _
  rw [hDS, hAS, UInt8.toNat_ofNat']
  omega

/-- **The prologue establishes the cleanup loop's entry invariant.** -/
theorem convertPre_mergedUpTo_zero (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    MergedUpTo g (convertPre g pk) 0 := by
  have hbase : SolverInvBase g (convertPre g pk) :=
    ⟨convertPre_pileBase g pk hwf hpk,
     fun s => convertPre_suitClean g pk s _,
     rfl,
     convertPre_usedSpace_def g pk hwf hpk,
     show (0 : UInt8) < 16 from by decide⟩
  refine ⟨hbase, ?_, by intro i hi; omega, fun i _ => convertPre_pileFlute g pk i⟩
  show (0 : UInt8).toInt = ((freePilesUpTo (convertPre g pk) 0 : Nat) : Int)
  unfold freePilesUpTo
  simp

end SolverSpec
