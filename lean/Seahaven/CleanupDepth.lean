import Seahaven.MoveAcesSim
import Seahaven.DepthMatch

/-!
# `SolverCleanupPile` at the depth-vector layer

The completeness step reaches the cleanup with only a **depth match** in hand — the
play's post-critical-move state has its flutes parked in cells, so it does not satisfy
`flute_match` and none of `CleanupSim`'s full-match lemmas apply to it.  What it needs
is exactly the depth-vector half of `SimulatesNorm.ofCleanupPile`:

> a state matching the entry position's depths matches the *result* position's depths.

Both ways the cleanup lowers a depth are already isolated, and neither moves a card:

* the **merge** re-reads consecutive dealt cards as flute cards — `PileMatches_lower`,
  fed with the chain `chain_of_mcards` extracts from the loop's own test;
* the **lone-king vacate** drops the last dealt card to depth `0`, which is legitimate
  because that card is a king — `PileMatches_vacate`.

The extension (the freed-predecessor drops) is the only card-moving part, and it
changes `pileFlute` only, so the depth vector does not see it at all.

The run is decomposed by `SolverSpec.cleanupPile_eq`, which is matching-independent, so
this file needs no new semantic input — only the index bookkeeping between the solver's
`UInt8` depth arithmetic and `PileMatches`' `Fin 6` index.
-/

/-- Two `Fin 6` depths with the same value give the same match. -/
theorem PileMatches_of_val_eq {g : Globals} {col : Column} {a : Fin 10} {n n' : Fin 6}
    (h : PileMatches g col a n) (hv : n'.val = n.val) : PileMatches g col a n' := by
  rw [(Fin.ext hv : n' = n)]
  exact h

/-- **The depth-vector half of a `SolverCleanupPile` call.**  Every pile but the one
being cleaned keeps its depth; the cleaned pile's drops by the merge count, or all the
way to `0` when its last dealt card is a king. -/
theorem cleanupPile_depth {g : Globals} {w : State} {q0 : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile q0))
    (hdm : ∀ (i : Fin 10) (h : (q0.pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i ⟨(q0.pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun' : EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p'))
    (i : Fin 10) :
    (p'.pileDepth.get i).toNat ≤ (q0.pileDepth.get i).toNat ∧
      ∀ h6 : (p'.pileDepth.get i).toNat < 6,
        PileMatches g (w.tableau i) i ⟨(p'.pileDepth.get i).toNat, h6⟩ := by
  rcases SolverSpec.cleanupPile_eq pile g q0 hpile hwf hb with
    ⟨hd0, hsd, hrunE⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- **Empty pile**: the depth vector is literally unchanged.
    injection hrun'.symm.trans hrunE with h1 h2
    injection h2 with _hg hp'eq
    have hdep : p'.pileDepth = q0.pileDepth := by
      rw [hp'eq]
      exact hsd
    have hval : (p'.pileDepth.get i).toNat = (q0.pileDepth.get i).toNat := by rw [hdep]
    exact ⟨le_of_eq hval, fun _ => PileMatches_of_val_eq (hdm i (by omega)) hval⟩
  · -- **Loop-bearing**: the result is the solver's own `cleanupRunResult`.
    have hdNat : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        = (q0.pileDepth[pile.toNat]'hpile).toNat := rfl
    have hres : cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0 = (fk, p') := by
      rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0]
      rcases hbranch with ⟨hnk, -, -, -, -, -, hrunE⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, -, -, -, -, -, hrunE⟩
      · rw [hnk]
        simp only [Bool.false_eq_true, reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
      · have hbr : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
            VALUE (B + UInt8.ofNat m) == 13) = true := by
          have hpdEq : (_root_.preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (q0.pileDepth[pile.toNat]'hpile) m f q0).pileDepth[pile.toNat]'hpile =
              ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) := by
            simp only [_root_.preCleanupPile]
            rw [Vector.getElem_set_self]
          have hdm' : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) = 1 := by
            rw [← hpdEq]; exact hd1'
          have hVK : VALUE (B + UInt8.ofNat m) = 13 := by
            apply UInt8.toNat_inj.mp
            rw [← hKeq, hVK13]; decide
          rw [Bool.and_eq_true]
          exact ⟨beq_iff_eq.mpr hdm', beq_iff_eq.mpr hVK⟩
        rw [hbr]
        simp only [reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
    have hp'snd : (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0).2 = p' := congrArg Prod.snd hres
    -- the merge chain, over `q0`'s own depths
    have hd1N : 1 ≤ (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by omega
    have hd5N : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 := hd5
    have hmN : m < (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by omega
    have hchain := chain_of_mcards (p := SolverSpec.fluteNorm pile hpile q0) hpile
      hd1N hd5N hmN hmcards
    -- `fluteNorm` only rewrites `pileFlute`, so its depths are `q0`'s (needed by `omega`,
    -- which sees the two spellings as different atoms)
    have hfn : ((SolverSpec.fluteNorm pile hpile q0).pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        = (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := rfl
    by_cases hi : i.val = pile.toNat
    · -- the cleaned pile
      have hfin : i = ⟨pile.toNat, hpile⟩ := Fin.ext hi
      subst hfin
      have hmatch0 := hdm ⟨pile.toNat, hpile⟩ (by omega)
      by_cases hk : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
          VALUE (B + UInt8.ofNat m) == 13) = true
      · -- **lone king**: merge down to one dealt card, then read it as the king pile
        obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_king pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0 hk
        rw [hp'snd] at hqd
        have hdmEq : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) = 1 :=
          beq_iff_eq.mp (Bool.and_eq_true .. ▸ hk |>.1)
        have hdmEq' : (q0.pileDepth.get ⟨pile.toNat, hpile⟩ - UInt8.ofNat m) = 1 := hdmEq
        have hmv : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m = 1 := by
          have h := depth1_toNat (d := q0.pileDepth.get ⟨pile.toNat, hpile⟩) (m := m) hd5N
            (by omega)
          rw [hdmEq'] at h
          rw [← h]; rfl
        -- merge to depth one
        have hone : PileMatches g (w.tableau ⟨pile.toNat, hpile⟩) ⟨pile.toNat, hpile⟩
            (⟨1, by omega⟩ : Fin 6) :=
          PileMatches_lower hwf hmatch0 (le_refl 1) hd1N
            (fun j hj1 hj2 hja hjb => hchain j (by simp only at hj1; omega)
              hj2 hja hjb)
        -- the remaining dealt card is a king
        have hzero : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat = 0 := by
          rw [hdmEq]; rfl
        obtain ⟨h5, hcard⟩ := hmcards m le_rfl
        have hVK : VALUE (B + UInt8.ofNat m) = 13 := beq_iff_eq.mp (Bool.and_eq_true .. ▸ hk |>.2)
        have hking : (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨0, by omega⟩)).toNat = 13 := by
          have hidx0 : (⟨((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat,
              h5⟩ : Fin 5) = ⟨0, by omega⟩ := Fin.ext hzero
          have hc : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨0, by omega⟩ = B + UInt8.ofNat m := by
            rw [← hidx0]; exact hcard
          rw [hc, hVK]
          rfl
        have hval : (p'.pileDepth.get ⟨pile.toNat, hpile⟩).toNat = 0 := by
          rw [hqd]
          show ((q0.pileDepth.set pile.toNat (0 : UInt8) hpile)[pile.toNat]'hpile).toNat = 0
          rw [Vector.getElem_set_self]
          rfl
        exact ⟨by omega, fun _ => PileMatches_of_val_eq (PileMatches_vacate hone hking) hval⟩
      · -- **ordinary**: the merge lowers the depth by `m`
        obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_ordinary pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0
          (by simpa using hk)
        rw [hp'snd] at hqd
        have hval : (p'.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
            = (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m := by
          rw [hqd]
          show ((q0.pileDepth.set pile.toNat
            ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) hpile)[pile.toNat]'hpile).toNat = _
          rw [Vector.getElem_set_self]
          exact depth1_toNat (d := q0.pileDepth.get ⟨pile.toNat, hpile⟩) (m := m) hd5N (by omega)
        refine ⟨by omega, fun _ => PileMatches_of_val_eq
          (n := ⟨(q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m, by omega⟩) ?_ hval⟩
        exact PileMatches_lower hwf hmatch0 (by simp only; omega)
          (by simp only; omega)
          (fun j hj1 hj2 hja hjb => hchain j (by simp only at hj1; omega) hj2 hja hjb)
    · -- every other pile keeps its depth
      have hval : (p'.pileDepth.get i).toNat = (q0.pileDepth.get i).toNat := by
        by_cases hk : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
            VALUE (B + UInt8.ofNat m) == 13) = true
        · obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_king pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0 hk
          rw [hp'snd] at hqd
          rw [hqd]
          show ((q0.pileDepth.set pile.toNat (0 : UInt8) hpile)[i.val]'i.isLt).toNat = _
          rw [Vector.getElem_set_ne hpile i.isLt (fun hc => hi hc.symm)]
          rfl
        · obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_ordinary pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0
            (by simpa using hk)
          rw [hp'snd] at hqd
          rw [hqd]
          show ((q0.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt).toNat = _
          rw [Vector.getElem_set_ne hpile i.isLt (fun hc => hi hc.symm)]
          rfl
      exact ⟨le_of_eq hval, fun _ => PileMatches_of_val_eq (hdm i (by omega)) hval⟩

/-- The depth match half. -/
theorem pileMatches_cleanupPile {g : Globals} {w : State} {q0 : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile q0))
    (hdm : ∀ (i : Fin 10) (h : (q0.pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i ⟨(q0.pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun' : EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p'))
    (i : Fin 10) (h6 : (p'.pileDepth.get i).toNat < 6) :
    PileMatches g (w.tableau i) i ⟨(p'.pileDepth.get i).toNat, h6⟩ :=
  (cleanupPile_depth hwf hpile hb hdm hrun' i).2 h6

/-- **The cleanup never raises a depth** — so a solver-empty column stays solver-empty,
which is what carries `PiledSuit` across the call. -/
theorem cleanupPile_depth_le {g : Globals} {w : State} {q0 : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile q0))
    (hdm : ∀ (i : Fin 10) (h : (q0.pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i ⟨(q0.pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun' : EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p'))
    (i : Fin 10) : (p'.pileDepth.get i).toNat ≤ (q0.pileDepth.get i).toNat :=
  (cleanupPile_depth hwf hpile hb hdm hrun' i).1

/-! ## The vacated suits are physically piled

`SimulatesNorm.drainFrom` may be entered with the mask `SolverRemoveFlute` returned only
if the configuration already piles every suit that mask forces.  At the depth layer that
is a *physical* statement about the state, and it is free: the lone-king branch fires
exactly when one dealt card is left and it is a king, so that card — the column's
deepest — is the vacated suit's king.

The suit bookkeeping is the only fiddly part.  The remaining dealt card is
`pos2card[pile][0] = B + m`, and `SUIT (B + m) = SUIT B` because `VALUE (B + m) = 13`
forces `VALUE B + m ≤ 15`: a carry would need `VALUE B + m = 29`, and `m < depth ≤ 5`. -/

/-- The merge never carries out of the value nibble, so it stays inside its suit. -/
private theorem suit_add_of_value_13 {B : UInt8} {m : Nat} (hreal : IsRealCard B)
    (hm : m ≤ 5) (hB61 : B.toNat ≤ 61) (hV : (VALUE (B + UInt8.ofNat m)).toNat = 13) :
    (SUIT (B + UInt8.ofNat m)).toNat = (SUIT B).toNat := by
  have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
  have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
    rw [UInt8.toNat_add, hmof, Nat.mod_eq_of_lt (by omega)]
  have hSB := SUIT_toNat B
  have hVB := VALUE_toNat B
  have hS := SUIT_toNat (B + UInt8.ofNat m)
  have hV' := VALUE_toNat (B + UInt8.ofNat m)
  have hVBle := hreal.2.2
  omega

/-- **The cleanup's `forcedKings` is met by the state itself.**  Its vacated suit — if
any — has its king physically on the freed column. -/
theorem kingVacates_cleanupPile {g : Globals} {w : State} {q0 : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile q0))
    (hdm : ∀ (i : Fin 10) (h : (q0.pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i ⟨(q0.pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun' : EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p')) :
    ∃ FK : Finset Suit, KingVacates FK fk ∧ (∀ su ∈ FK, PiledSuit w p' su) ∧
      VacateSites q0 p' FK := by
  have hle := cleanupPile_depth_le hwf hpile hb hdm hrun'
  rcases SolverSpec.cleanupPile_eq pile g q0 hpile hwf hb with
    ⟨hd0, hsd, hrunE⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- **Empty pile**: nothing is vacated.
    injection hrun'.symm.trans hrunE with h1 h2
    subst h1
    exact ⟨∅, KingVacates.empty, fun su hsu => absurd hsu (Finset.notMem_empty su),
      VacateSites.of_depth_le hle⟩
  · have hdNat : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        = (q0.pileDepth[pile.toNat]'hpile).toNat := rfl
    have hres : cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0 = (fk, p') := by
      rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0]
      rcases hbranch with ⟨hnk, -, -, -, -, -, hrunE⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, -, -, -, -, -, hrunE⟩
      · rw [hnk]
        simp only [Bool.false_eq_true, reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
      · have hbr : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
            VALUE (B + UInt8.ofNat m) == 13) = true := by
          have hpdEq : (_root_.preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (q0.pileDepth[pile.toNat]'hpile) m f q0).pileDepth[pile.toNat]'hpile =
              ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) := by
            simp only [_root_.preCleanupPile]
            rw [Vector.getElem_set_self]
          have hdm' : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) = 1 := by
            rw [← hpdEq]; exact hd1'
          have hVK : VALUE (B + UInt8.ofNat m) = 13 := by
            apply UInt8.toNat_inj.mp
            rw [← hKeq, hVK13]; decide
          rw [Bool.and_eq_true]
          exact ⟨beq_iff_eq.mpr hdm', beq_iff_eq.mpr hVK⟩
        rw [hbr]
        simp only [reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
    have hfkeq : (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0).1 = fk := congrArg Prod.fst hres
    have hp'snd : (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0).2 = p' := congrArg Prod.snd hres
    refine ⟨_, hfkeq ▸ cleanupRunResult_kingVacates pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0, ?_, ?_⟩
    swap
    · -- the vacate freed the pile it was called on
      by_cases hk : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
          VALUE (B + UInt8.ofNat m) == 13) = true
      · rw [if_pos hk]
        obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_king pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0 hk
        rw [hp'snd] at hqd
        refine VacateSites.single (a := ⟨pile.toNat, hpile⟩) hle hd1 ?_
        rw [hqd]
        show ((q0.pileDepth.set pile.toNat (0 : UInt8) hpile)[pile.toNat]'hpile).toNat = 0
        rw [Vector.getElem_set_self]
        rfl
      · rw [if_neg hk]
        exact VacateSites.of_depth_le hle
    intro su hsu
    by_cases hk : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
        VALUE (B + UInt8.ofNat m) == 13) = true
    · -- the vacated suit's king is the column's deepest card
      rw [if_pos hk, Finset.mem_singleton] at hsu
      subst hsu
      obtain ⟨hqd, -, -, -⟩ := cleanupRunResult_fields_king pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0 hk
      rw [hp'snd] at hqd
      have hd1N : 1 ≤ (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hd1
      have hmatch0 := hdm ⟨pile.toNat, hpile⟩ (by omega)
      obtain ⟨hlen, hbot, -⟩ := hmatch0
      simp only at hlen
      have hrev0 : 0 < (w.tableau ⟨pile.toNat, hpile⟩).reverse.length := by
        simp only [List.length_reverse]; omega
      have hb0 : encodeCard ((w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0)
          = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨0, by omega⟩ := by
        have hk0 := hbot ⟨0, by simp only; omega⟩
        rw [List.getElem?_eq_getElem hrev0, Option.map_some, Option.some.injEq] at hk0
        exact hk0
      -- the remaining dealt card is `B + m`
      have hdmEq : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) = 1 :=
        beq_iff_eq.mp (Bool.and_eq_true .. ▸ hk |>.1)
      have hzero : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat = 0 := by
        rw [hdmEq]; rfl
      obtain ⟨h5, hcard⟩ := hmcards m le_rfl
      have hc0 : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨0, by omega⟩ = B + UInt8.ofNat m := by
        rw [← (Fin.ext hzero :
          (⟨((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1).toUInt32.toNat, h5⟩ : Fin 5)
            = ⟨0, by omega⟩)]
        exact hcard
      -- so its suit is `B`'s
      have hVK : VALUE (B + UInt8.ofNat m) = 13 := beq_iff_eq.mp (Bool.and_eq_true .. ▸ hk |>.2)
      have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
      have hsuiteq : (SUIT (B + UInt8.ofNat m)).toNat = (SUIT B).toNat :=
        suit_add_of_value_13 hBreal (by omega) hBrange.2 (by rw [hVK]; rfl)
      refine ⟨⟨pile.toNat, hpile⟩, ?_, (w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0, ?_, ?_⟩
      · rw [hqd]
        show ((q0.pileDepth.set pile.toNat (0 : UInt8) hpile)[pile.toNat]'hpile).toNat = 0
        rw [Vector.getElem_set_self]
        rfl
      · rw [Option.mem_def, ← List.head?_reverse]
        exact List.head?_eq_getElem? .. ▸ (List.getElem?_eq_getElem hrev0)
      · refine suitToNat_inj ?_
        have hsu' := encodeCard_SUIT ((w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0)
        have hlt := suitToNat_lt ((w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0).suit
        have hsc : suitToNat (suitOfCode (SUIT B) hs4) = (SUIT B).toUInt32.toNat :=
          suitToNat_natToSuit _
        have h1 : (SUIT (encodeCard ((w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0))).toNat
            = suitToNat ((w.tableau ⟨pile.toNat, hpile⟩).reverse[0]'hrev0).suit := by
          rw [hsu', UInt8.toNat_ofNat']
          omega
        rw [hb0, hc0] at h1
        rw [hsc, UInt8.toNat_toUInt32]
        omega
    · rw [if_neg hk] at hsu
      exact absurd hsu (Finset.notMem_empty su)

/-! ## The whole `SolverRemoveFlute` call

`SolverRemoveFlute` is the depth/hash decrement and the flute reset — exactly the
`movePre` bookkeeping the state already reflects — followed by `SolverCleanupPile`
(`removeFlute_eq`).  Since `fluteNorm` rewrites only `pileFlute`, the depth vector the
cleanup is entered at *is* `movePre`'s. -/

theorem pileMatches_removeFlute {g : Globals} {w : State} {gameA : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile
      (removeFlutePre pile hpile gameA)))
    (hdm : ∀ (i : Fin 10)
        (h : ((removeFlutePre pile hpile gameA).pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i
        ⟨((removeFlutePre pile hpile gameA).pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun : _root_.SolverRemoveFlute pile (g, gameA) = .ok fk (g, p'))
    (i : Fin 10) (h6 : (p'.pileDepth.get i).toNat < 6) :
    PileMatches g (w.tableau i) i ⟨(p'.pileDepth.get i).toNat, h6⟩ := by
  have hrun' : EStateM.run (_root_.SolverRemoveFlute pile) (g, gameA) = .ok fk (g, p') := hrun
  rw [removeFlute_eq pile g gameA hpile] at hrun'
  exact pileMatches_cleanupPile hwf hpile hb hdm hrun' i h6

/-- **The depth match survives a whole `SolverRemoveFlute`**, in `DepthMatchesV` form —
stated at `movePre`, which is where `MovePreMatch.critical_depthMatchesV_movePre` leaves
the play's post-critical-move state. -/
theorem depthMatchesV_removeFlute {g : Globals} {w : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10) (toPile : UInt8)
    (hb : SolverInvBase g (SolverSpec.movePre pile toPile hpile p))
    (hd6 : ∀ i : Fin 10, ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat < 6)
    (hdm : DepthMatchesV g w (depthVec (SolverSpec.movePre pile toPile hpile p) hd6))
    {fk : UInt16} {p' : SolverPosType}
    (hrun : _root_.SolverRemoveFlute pile (g, SolverSpec.moveDestPre pile toPile hpile p)
      = .ok fk (g, p'))
    (hd6' : ∀ i : Fin 10, (p'.pileDepth.get i).toNat < 6) :
    DepthMatchesV g w (depthVec p' hd6') :=
  fun i => pileMatches_removeFlute hwf hpile hb
    (fun j _ => PileMatches_of_val_eq (hdm j) rfl) hrun i (hd6' i)

/-- A suit physically piled is piled by any configuration the state matches — the
`PiledSuit` form of `StateMatchesKingConfig.clear_of_column`. -/
theorem cfgBitSet_clear_of_piled {g : Globals} {u : State} {p : SolverPosType} {k : Fin 16}
    (h : StateMatchesKingConfig g u p k) {su : Suit} (hp : PiledSuit u p su) :
    ¬ CfgBitSet k su := by
  obtain ⟨i, hd0, d, hd, hsuit⟩ := hp
  exact fun hbit => h.no_pile su hbit i hd0 d hd hsuit

/-- **The `forcedKings` of a whole `SolverRemoveFlute` is met by the state.**  Together
with `depthMatchesV_removeFlute` this is everything `SimulatesNorm.drainFrom` asks for. -/
theorem kingVacates_removeFlute {g : Globals} {w : State} {gameA : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile
      (removeFlutePre pile hpile gameA)))
    (hdm : ∀ (i : Fin 10) (h : ((removeFlutePre pile hpile gameA).pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i
        ⟨((removeFlutePre pile hpile gameA).pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun : _root_.SolverRemoveFlute pile (g, gameA) = .ok fk (g, p')) :
    ∃ FK : Finset Suit, KingVacates FK fk ∧ (∀ su ∈ FK, PiledSuit w p' su) ∧
      VacateSites (removeFlutePre pile hpile gameA) p' FK := by
  have hrun' : EStateM.run (_root_.SolverRemoveFlute pile) (g, gameA) = .ok fk (g, p') := hrun
  rw [removeFlute_eq pile g gameA hpile] at hrun'
  exact kingVacates_cleanupPile hwf hpile hb hdm hrun'

/-- The depth bound across a whole `SolverRemoveFlute`. -/
theorem removeFlute_depth_le {g : Globals} {w : State} {gameA : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (SolverSpec.fluteNorm pile hpile
      (removeFlutePre pile hpile gameA)))
    (hdm : ∀ (i : Fin 10) (h : ((removeFlutePre pile hpile gameA).pileDepth.get i).toNat < 6),
      PileMatches g (w.tableau i) i
        ⟨((removeFlutePre pile hpile gameA).pileDepth.get i).toNat, h⟩)
    {fk : UInt16} {p' : SolverPosType}
    (hrun : _root_.SolverRemoveFlute pile (g, gameA) = .ok fk (g, p'))
    (i : Fin 10) :
    (p'.pileDepth.get i).toNat ≤ ((removeFlutePre pile hpile gameA).pileDepth.get i).toNat := by
  have hrun' : EStateM.run (_root_.SolverRemoveFlute pile) (g, gameA) = .ok fk (g, p') := hrun
  rw [removeFlute_eq pile g gameA hpile] at hrun'
  exact cleanupPile_depth_le hwf hpile hb hdm hrun' i
