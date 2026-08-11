import Seahaven.SolverSpecKingMove
import Seahaven.SolverSpecPreCleanupPile

/-!
# Spec for `cleanupPile`

`cleanupPile` dispatches to either `kingMove` or `preCleanupPile` depending on
whether the pile's cleanup exposes a lone king; this file establishes the
exact-run equations (`cleanupPile_eq`) and the resulting `PileBase`/
`PileMerged` preservation facts by case-splitting into the two spec files
above.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

-- `cleanupPile_baseNF`'s discharge has grown large enough (12 clauses × 2
-- branches, each needing its own index/arithmetic bookkeeping) that the
-- default 200000-heartbeat budget is exceeded on unrelated later bullets
-- purely from the theorem's overall size — confirmed by reproducing the
-- timeout even with the newest clause `sorry`'d out (so it isn't a specific
-- broken `rfl`/`exact` looping forever; it's cumulative elaboration cost).
-- Same remedy already used elsewhere in this file's `rfl`-twin proofs.
set_option maxHeartbeats 4000000 in
/-- **Shared guard-derivation preamble for `SolverCleanupPile`**, factored out of
    `cleanupPile_base`/`solverCleanupPile_step` (which used to duplicate an
    identical ~400-line derivation, differing only by a `pile ↦ UInt32.ofNat k`
    substitution).  Given the flute-normalized `SolverInvBase` precondition, this
    produces the exact symbolic run of `SolverCleanupPile pile` together with
    every fact its two callers need to reassemble their own (stronger) tower
    layer: the empty-pile case is a plain `freePiles += 1` no-op; the
    loop-bearing case exposes the boundary card `B`, the merge/freed loop
    counts `m`/`f`, and (for each of the non-king/king sub-branches) the
    resulting position's `PileClean`/`SuitClean`/`hash_def`/`usedSpace_def`
    facts and the "other piles' depths are untouched" frame condition. -/
theorem cleanupPile_eq (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p)) :
    (∃ (_hd : p.pileDepth[pile.toNat]'hpile = 0)
       (_hsd : p.pileDepth.set pile.toNat 0 hpile = p.pileDepth),
       EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff
         (g, { p with
               freePiles := p.freePiles + 1,
               pileDepth := p.pileDepth.set pile.toNat 0 hpile,
               pileFlute := p.pileFlute.set pile.toNat 1 hpile }))
    ∨
    (∃ (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
       (hd : p.pileDepth[pile.toNat]'hpile ≠ 0)
       (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
       (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
       (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
       (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
           ).toUInt32.toNat]'hidx = B)
       (hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61)
       (hnfp : ∀ i : Fin 10, i.val ≠ pile.toNat → PileBase g p i)
       (m f : Nat)
       (hm_le : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat)
       (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
             UInt8.ofNat k - 1).toUInt32.toNat < 5,
         (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
             UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
       (hmstop : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1 ∨
         (m + 1 < (p.pileDepth[pile.toNat]'hpile).toNat ∧
           ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2
             ).toUInt32.toNat < 5,
             (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
               UInt8.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
       (hf_le : f ≤ B.toNat - 1)
       (hf_le_tight : f ≤ (VALUE B).toNat - 1)
       (hffree : ∀ l, 1 ≤ l → l ≤ f →
         isFreeCard g p (B - UInt8.ofNat l) ∧
         p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l))
       (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f) ∨
         ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
       (hak : ∀ t : Fin 4, SUIT (p.aces.get t) = t.val.toUInt8),
       (∃ (hnk : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
             VALUE (B + UInt8.ofNat m) == 13) = false)
          (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat →
             (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
               (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get j = p.pileDepth.get j)
          (hpc : PileClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p) ⟨pile.toNat, hpile⟩)
          (hsuit : ∀ s : Fin 4, SuitClean g (preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p) s
              (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
                m f hm_le hmcards hf_le hffree))
          (hhash : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).hash =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get i
                ).toNat.toUInt32) 0)
          (_hused : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).usedSpace.toInt =
            (52 : Int)
            - ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p
                ).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
            - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.toList
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.toList
                |>.foldl (·+·) 0 : Nat)),
          EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff
            (g, preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p))
       ∨
       (∃ (hd1' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
             (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile = 1)
          (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
          (hVK13 : (VALUE K).toNat = 13)
          (hsuiteq : SUIT B = SUIT K)
          (hKeq : K = B + UInt8.ofNat m)
          (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat →
            (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.get j = p.pileDepth.get j)
          (hpc : PileClean g (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)) ⟨pile.toNat, hpile⟩)
          (hsuit : ∀ s : Fin 4, SuitClean g (kingMove pile hpile (SUIT B) hs4
              (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)) s
              (fun i => le_trans (kingMove_pileDepth_le pile hpile (SUIT B) hs4
                  (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile) m f p) i)
                (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
                  m f hm_le hmcards hf_le hffree i)))
          (hhash : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).hash =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.get i
                ).toNat.toUInt32) 0)
          (_hused : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).usedSpace.toInt =
            (52 : Int)
            - ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p)
                ).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
            - ((List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
                (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.toList
                (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile) m f p)).pileFlute.toList
                |>.foldl (·+·) 0 : Nat))),
          EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok
            (0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4)
            (g, kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile) m f p)))) := by
  by_cases hd : p.pileDepth[pile.toNat]'hpile = 0
  · -- Empty pile: transplanted verbatim from `cleanupPile_base`'s old empty case.
    left
    have hrun := cleanupPile_empty_eq pile g p hpile hd
    have hsd : p.pileDepth.set pile.toNat 0 hpile = p.pileDepth := by
      conv_lhs => rw [← hd]
      exact Vector.set_getElem_self hpile
    exact ⟨hd, hsd, hrun⟩
  · -- Loop-bearing case: `pileDepth[pile] > 0`.
    -- (`fluteNorm` only changes `pileFlute`, so all depth/aces facts of `hnf`
    -- transfer to `p` definitionally.)
    right
    have hnn : (0 : UInt8) ≤ p.pileDepth[pile.toNat]'hpile :=
      hnf.pileDepth_nonneg ⟨pile.toNat, hpile⟩
    have hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat := by
      have hne : (p.pileDepth[pile.toNat]'hpile).toNat ≠ 0 :=
        fun h => hd (UInt8.toNat_inj.mp h)
      omega
    have hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5 :=
      hnf.pileDepth_bound ⟨pile.toNat, hpile⟩
    have h1le : (1 : UInt8) ≤ (p.pileDepth[pile.toNat]'hpile) := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
    have hsubd : ((p.pileDepth[pile.toNat]'hpile) - 1).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat - 1 :=
      UInt8.toNat_sub_of_le _ _ h1le
    have hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5 := by
      rw [UInt8.toNat_toUInt32, hsubd]
      omega
    -- The boundary card is a real card (WellFormedLayout).
    have hreal : IsRealCard ((g.pos2card[pile.toNat]'hpile)[
        ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat]'hidx) :=
      hwf.pos2card_real ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩
    set B := (g.pos2card[pile.toNat]'hpile)[
      ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat]'hidx with hBdef
    have hs4 : (SUIT B).toUInt32.toNat < 4 := by
      rw [UInt8.toNat_toUInt32]; exact hreal.1
    have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
      have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
      have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
      have h1 := hreal.1
      have h2 := hreal.2.1
      have h3 := hreal.2.2
      omega
    have h1B : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hprev64 : (B - 1).toNat < 64 := by
      rw [UInt8.toNat_sub_of_le _ _ h1B]; omega
    have haces0 : (0 : UInt8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 :=
      int8_nonneg_of_suit
        (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
    -- The boundary card is still physically in the pile (`boundary_not_free`,
    -- via `depth_card_not_free`), so `foundation_cards_free`'s contrapositive
    -- forces `aces[SUIT B] < B`: if `aces[SUIT B]` had already reached `B`,
    -- `B` itself would satisfy `foundation_cards_free`'s hypotheses and hence
    -- be free, contradicting `boundary_not_free`.
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
        rw [hBdef]
        exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
          ⟨((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat, hidx⟩ (by
            show ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat <
              (p.pileDepth[pile.toNat]'hpile).toNat
            rw [UInt8.toNat_toUInt32, hsubd]
            omega)
      exact hnfB hfree
    -- Every same-suit card `aces[SUIT B]` represents lies within `SUIT B`'s
    -- own 16-wide code block (never below it) — the counterpart lower bound
    -- to `foundation_cards_free`'s implicit upper range, needed to rule out
    -- the freed loop crossing into a different suit's card block.
    have haces_ge : (16 : Nat) * (SUIT B).toUInt32.toNat ≤
        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat := by
      have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
      have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
      have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
      have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4)) = SUIT B := by
        rw [← hgetEq, hak.1, ← hsuiteq]
      have hb1 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4))
      have hsEq := congrArg UInt8.toNat hSuitAces
      have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      omega
    -- `fluteNorm` only ever changes `pileFlute[pile]`, so `hnf`'s `PileBase`
    -- facts about any OTHER pile transfer to `p` (not `fluteNorm pile hpile p`)
    -- verbatim — needed since `preCleanupPile_pileBase_ne`/`kingMove_pileBase_ne`
    -- are stated about `p` directly (they don't take the full `SolverInvBase`
    -- and re-derive the bridge themselves).
    have hnfp : ∀ i : Fin 10, i.val ≠ pile.toNat → PileBase g p i := by
      intro i hij
      have hfeq : (fluteNorm pile hpile p).pileFlute.get i = p.pileFlute.get i := by
        show (fluteNorm pile hpile p).pileFlute[i.val]'i.isLt = p.pileFlute[i.val]'i.isLt
        simp only [fluteNorm]
        exact Vector.getElem_set_ne hpile i.isLt (Ne.symm hij)
      have hb := hnf.pileBase i
      refine ⟨hb.pileDepth_bound, hb.pileDepth_nonneg, ?_, ?_, ?_, ?_⟩
      · rw [← hfeq]; exact hb.flute_pos
      · intro h0; rw [← hfeq]; exact hb.flute_empty h0
      · intro j hdi hj0 hjlt
        rw [← hfeq] at hjlt
        exact hb.flute_cards_free j hdi hj0 hjlt
      · exact fun hdi hs => by
          have h2 := hb.flute_not_aces hdi hs
          rwa [hfeq] at h2
    obtain ⟨m, f, hmg, hmx, hfg, hfx, hrun⟩ :=
      cleanupPile_nonempty_eq pile g p B (pileHashes[pile.toNat]'hpile) hpile rfl
        hd1 hd5 hidx hBdef.symm hs4 hprev64 hwf.card2pile_lt haces0
    -- ------------------------------------------------------------------
    -- Guard-derived arithmetic: bounds on the iteration counts (no wraps).
    -- ------------------------------------------------------------------
    -- The merge loop runs at most depth−1 times: the guard at step
    -- `depth.toNat − 1` would need `1 < depth − (depth−1) = 1`.
    have hm_le : m ≤ (p.pileDepth[pile.toNat]'hpile).toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hg := (hmg ((p.pileDepth[pile.toNat]'hpile).toNat - 1) (by omega)).1
      simp only [mergeIter_eq] at hg
      rw [UInt8.lt_iff_toNat_lt] at hg
      have hofk : (UInt8.ofNat ((p.pileDepth[pile.toNat]'hpile).toNat - 1)).toNat =
          (p.pileDepth[pile.toNat]'hpile).toNat - 1 := by
        rw [UInt8.toNat_ofNat']; omega
      rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hofk]; omega), hofk,
        show ((1 : UInt8).toNat = 1) from rfl] at hg
      omega
    have hpdCast : (p.pileDepth[pile.toNat]'hpile).toInt =
        ((p.pileDepth[pile.toNat]'hpile).toNat : Int) := rfl
    have hm4 : m ≤ 4 := by omega
    -- The freed loop runs at most B.toNat−1 times: at step B.toNat−1 the
    -- walked card would be 0, contradicting `0 ≤ aces < prevCard`.
    have hf_le : f ≤ B.toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hof : (UInt8.ofNat (B.toNat - 1)).toNat = B.toNat - 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hprev0 : B - 1 - UInt8.ofNat (B.toNat - 1) = 0 := by
        have hle : UInt8.ofNat (B.toNat - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hof, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_sub_of_le _ _ h1B, hof, show ((1 : UInt8).toNat = 1) from rfl, show ((0 : UInt8).toNat = 0) from rfl]
        omega
      have hg := (hfg (B.toNat - 1) (by omega)).1 hs4
      simp only [freedIter_eq, hprev0] at hg
      rw [UInt8.lt_iff_toNat_lt, show ((0 : UInt8).toNat = 0) from rfl] at hg
      omega
    -- Weaker form (mirrors the old monolithic proof exactly): the freed loop
    -- never crosses into a lower suit's card block either — at step
    -- `VALUE(B)−1` the walked card would be exactly the value-0 sentinel of
    -- `SUIT B`, contradicting `haces_ge`.
    have hf_le_tight : f ≤ (VALUE B).toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hvB := VALUE_toNat B
      have hsB := SUIT_toNat B
      have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
      have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      have hof : (UInt8.ofNat ((VALUE B).toNat - 1)).toNat = (VALUE B).toNat - 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hprevEq : B - 1 - UInt8.ofNat ((VALUE B).toNat - 1) =
          UInt8.ofNat (16 * (SUIT B).toUInt32.toNat) := by
        apply UInt8.toNat_inj.mp
        have hle : UInt8.ofNat ((VALUE B).toNat - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hof, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
          omega
        have h16x : 16 * (SUIT B).toUInt32.toNat < 256 := by omega
        rw [UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_sub_of_le _ _ h1B, hof, show ((1 : UInt8).toNat = 1) from rfl, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h16x]
        omega
      have hg := (hfg ((VALUE B).toNat - 1) (by omega)).1 hs4
      simp only [freedIter_eq, hprevEq] at hg
      have h16x : 16 * (SUIT B).toUInt32.toNat < 256 := by omega
      have hcardnat : (UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toNat =
          16 * (SUIT B).toUInt32.toNat := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h16x]
      have hlt := UInt8.lt_iff_toNat_lt.mp hg
      rw [hcardnat] at hlt
      omega
    -- ------------------------------------------------------------------
    -- Semantic bridges: raw `mergeGuard`/`freedGuard` facts (`hmg`/`hmx`/
    -- `hfg`/`hfx`) restated in the shape the modular `preCleanupPile_*`
    -- lemmas expect (`hmcards`/`hffree`/`hmstop`/`hfstop`).
    -- ------------------------------------------------------------------
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m).toNat =
        (p.pileDepth[pile.toNat]'hpile).toNat - m :=
      depth_sub_ofNat_eq hd5 (by omega)
    have hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat < 5,
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
          UInt8.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k := by
      intro k hkm
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        refine ⟨by simpa using hidx, ?_⟩
        simp only [UInt8.sub_zero, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
        exact hBdef.symm
      · exact merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
          (p.pileDepth[pile.toNat]'hpile) m p hd5 (by omega) hmg k hkpos hkm
    -- The freed-loop guard held for every step below `f`: unfold each into the
    -- semantic per-`l` fact `hffree` needs.
    have hffree : ∀ l, 1 ≤ l → l ≤ f →
        isFreeCard g p (B - UInt8.ofNat l) ∧
        p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l) := by
      intro l hl1 hlf
      have hg1 := (hfg (l - 1) (by omega)).1 hs4
      have hg2 := (hfg (l - 1) (by omega)).2
      simp only [freedIter_eq] at hg1 hg2
      simp only [UInt8.toNat_toUInt32] at hg2
      have hstepId : B - 1 - UInt8.ofNat (l - 1) = B - UInt8.ofNat l := by
        apply UInt8.toNat_inj.mp
        have hl1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by rw [UInt8.toNat_ofNat']; omega
        have hlof : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
        have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hl1of, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
          omega
        have hleB' : UInt8.ofNat l ≤ B := by
          rw [UInt8.le_iff_toNat_le, hlof]; omega
        rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B, hl1of, show ((1 : UInt8).toNat = 1) from rfl, UInt8.toNat_sub_of_le _ _ hleB', hlof]
        omega
      rw [← hstepId]
      have hl1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by rw [UInt8.toNat_ofNat']; omega
      have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
        rw [UInt8.le_iff_toNat_le, hl1of, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
        omega
      have hBl64 : (B - 1 - UInt8.ofNat (l - 1)).toNat < 64 := by
        rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
        omega
      exact ⟨isFree_of_card2depth_ge g p hwf (B - 1 - UInt8.ofNat (l - 1)) hBl64
        (hg2 hBl64 (hwf.card2pile_lt _ hBl64)), hg1⟩
    -- The merge loop stopped either because depth (after `m` steps) reached
    -- `≤ 1`, or because the card two below the new boundary doesn't continue
    -- the ascending run.
    have hmstop : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1 ∨
        (m + 1 < (p.pileDepth[pile.toNat]'hpile).toNat ∧
          ∃ h5 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2
            ).toUInt32.toNat < 5,
            (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) -
              UInt8.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)) := by
      by_cases hle1 : (p.pileDepth[pile.toNat]'hpile).toNat - m ≤ 1
      · exact Or.inl hle1
      · push Not at hle1
        right
        have h1lt : (1 : UInt8) < (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m := by
          rw [UInt8.lt_iff_toNat_lt, hdepth1I, show ((1 : UInt8).toNat = 1) from rfl]; omega
        have hidx2 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2
            ).toUInt32.toNat < 5 := by
          rw [UInt8.toNat_toUInt32, depth_sub_ofNat_sub_two_eq hd5 (by omega)]
          omega
        refine ⟨by omega, hidx2, ?_⟩
        intro heq
        apply hmx
        rw [mergeIter_eq]
        refine ⟨h1lt, fun h10 h5 => ?_⟩
        have hSame : (g.pos2card[pile.toNat]'hpile)[
            ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat]'h5 =
            (g.pos2card[pile.toNat]'hpile)[
            ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 2).toUInt32.toNat]'hidx2 := by
          congr 1
        have hstepB : B + UInt8.ofNat m + 1 = B + UInt8.ofNat (m + 1) := by
          rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
        rw [hSame, heq, hstepB]
    -- The freed loop stopped either because `aces` had already reached the
    -- stopping card exactly, or that card genuinely isn't free.
    have hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f) ∨
        ¬ isFreeCard g p (B - 1 - UInt8.ofNat f) := by
      have hg := hfx
      simp only [freedIter_eq] at hg
      by_cases hcase : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1 - UInt8.ofNat f)
      · right
        intro hfree
        apply hg
        refine ⟨fun _ => hcase, fun h64 h10 => ?_⟩
        simp only [UInt8.toNat_toUInt32]
        have hXnat64 : (B - 1 - UInt8.ofNat f).toNat < 64 := by
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hle3 : UInt8.ofNat f ≤ B - 1 := by
            rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
            omega
          rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ h1B, hfof, show ((1 : UInt8).toNat = 1) from rfl]
          omega
        exact isFree_to_card2depth_ge g p hwf (B - 1 - UInt8.ofNat f) hXnat64 hfree
      · left
        have hcase : (B - 1 - UInt8.ofNat f) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
          rw [UInt8.le_iff_toNat_le]
          have h := ‹¬ p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1 - UInt8.ofNat f)›
          rw [UInt8.lt_iff_toNat_lt] at h
          omega
        have h1B : (1 : UInt8) ≤ B := by
          rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
        have hfle : f ≤ B.toNat - 1 := hf_le
        have hXnat : (B - 1 - UInt8.ofNat f).toNat = B.toNat - 1 - f := by
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hle3 : UInt8.ofNat f ≤ B - 1 := by
            rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
            omega
          rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ h1B, hfof, show ((1 : UInt8).toNat = 1) from rfl]
        have haces_le : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat ≤
            (B - 1 - UInt8.ofNat f).toNat := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · subst hf0
            have hacesB : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat < B.toNat :=
              UInt8.lt_iff_toNat_lt.mp haces_lt_B
            rw [hXnat]
            omega
          · have hf' := (hffree f hfpos (le_refl f)).2
            have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
            have hfBle : UInt8.ofNat f ≤ B := by rw [UInt8.le_iff_toNat_le, hfof]; omega
            have hBf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
              rw [UInt8.toNat_sub_of_le _ _ hfBle, hfof]
            have hlt := UInt8.lt_iff_toNat_lt.mp hf'
            rw [hBf] at hlt
            rw [hXnat]
            omega
        have hgeNat : (B - 1 - UInt8.ofNat f).toNat ≤
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNat :=
          UInt8.le_iff_toNat_le.mp hcase
        apply UInt8.toNat_inj.mp
        omega
    have hmf128 : (1 + (m : Int) + f) < 128 := by
      have h1 := hm4
      have h2 := hf_le
      have h3 := hBrange.2
      omega
    -- ------------------------------------------------------------------
    -- Package the shared preamble facts (`hpc`/`hpdb_all`/`hak` don't depend
    -- on the non-king/king split, so they're computed once here and reused
    -- by both sub-branches below).
    -- ------------------------------------------------------------------
    have hm_le_int : m + 1 ≤ (p.pileDepth[pile.toNat]'hpile).toNat := by omega
    have hak : ∀ t : Fin 4, SUIT (p.aces.get t) = t.val.toUInt8 :=
      fun t => (hnf.suitClean t).aces_kings_valid.1
    have hpc := preCleanupPile_pileClean_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx
      hBdef.symm m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop
    have hpdb_all := preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5
      hidx hBdef.symm m f hm_le_int hmcards hf_le hffree
    refine ⟨B, hs4, hd, hd1, hd5, hidx, hBdef.symm, hBrange, hnfp, m, f, hm_le_int, hmcards,
      hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, ?_⟩
    -- ------------------------------------------------------------------
    -- Reconnect to the real run via `cleanupRunResult_eq`, then case-split
    -- on the lone-king condition.
    -- ------------------------------------------------------------------
    rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile) m f p] at hrun
    cases hk : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
        VALUE (B + UInt8.ofNat m) == 13) with
    | false =>
      simp only [hk, Bool.false_eq_true, reduceIte] at hrun
      left
      exact ⟨rfl, fun j hj => preCleanupPile_pileDepth_eq_of_ne pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 p m f j hj,
        hpc,
        preCleanupPile_suitClean pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef.symm
          m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop,
        preCleanupPile_hash_def pile g p hpile hnf B hs4 hd5 m f hm_le_int,
        preCleanupPile_usedSpace_def pile g p hpile hwf hnf B hs4 hd hd1 hd5 hidx hBdef.symm
          m f hm_le_int hf_le hf_le_tight hffree hBrange.2,
        hrun⟩
    | true =>
      simp only [hk, reduceIte] at hrun
      right
      rw [Bool.and_eq_true] at hk
      have hk1 := hk.1
      have hk2 := hk.2
      have hpdEq : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hpfEq : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile =
          (1 + UInt8.ofNat m + UInt8.ofNat f) := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hd1' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile = 1 := by
        rw [hpdEq, eq_of_beq hk1]
      have hVK13 : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by
        rw [eq_of_beq hk2]; decide
      have hrcm := merge_real_chain' g pile hpile hwf B (p.pileDepth[pile.toNat]'hpile) m
        hreal hmcards m (le_refl m)
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
      have hidx0 : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m - 1
          ).toUInt32.toNat = 0 := by
        have he1 := eq_of_beq hk1
        rw [he1]
        decide
      obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
      have hKeq : B + UInt8.ofNat m = (g.pos2card[pile.toNat]'hpile)[0]'(by omega) := by
        rw [← heqm]
        congr 1
      refine ⟨hd1', B + UInt8.ofNat m, hKeq, hVK13, hSm.symm, rfl, ?_, ?_, ?_, ?_, ?_, hrun⟩
      · intro j hj
        rw [kingMove_pileDepth_eq_of_ne pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p) j hj,
          preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
            j hj]
      · exact kingMove_pileClean_self pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)
      · exact fun s => kingMove_suitClean pile g hpile hwf (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)
          hpdb_all hd1' (B + UInt8.ofNat m) hKeq hVK13 hSm.symm hak hpc s
          (preCleanupPile_suitClean pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef.symm
            m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop s)
      · -- hash_def for the king branch: compose `preCleanupPile_hash_def` with
        -- `kingMove`'s own simple `hash -= ph` write, isolating `pile`'s own
        -- term (now `0`) via `hash_foldl_set`.
        have hqhash := preCleanupPile_hash_def pile g p hpile hnf B hs4 hd5 m f hm_le_int
        show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).hash -
            (pileHashes[pile.toNat]'hpile) =
          (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
            ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.get i
              ).toNat.toUInt32) 0
        have hpdeq : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth =
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.set
              pile.toNat (0 : UInt8) hpile := by
          simp only [kingMove]
        rw [hpdeq, hqhash]
        have hadd := hash_foldl_set (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile)
          hs4 (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth pile.toNat hpile (0 : UInt8)
        rw [hd1'] at hadd
        simp only [show ((1 : UInt8).toNat = 1) from rfl,
          show ((0 : UInt8).toNat = 0) from rfl,
          show (Nat.toUInt32 0 = 0) from rfl, show (Nat.toUInt32 1 = 1) from rfl,
          UInt32.mul_one, UInt32.mul_zero, UInt32.add_zero] at hadd
        rw [← hadd, UInt32.add_sub_cancel]
      · -- usedSpace_def for the king branch: compose `preCleanupPile_usedSpace_def`
        -- with `kingMove`'s own `usedSpace += pileFlute[pile]` write, isolating
        -- `pile`'s own depth/flute terms (now `0`/`1`) the same way.
        have hqused := preCleanupPile_usedSpace_def pile g p hpile hwf hnf B hs4 hd hd1 hd5
          hidx hBdef.symm m f hm_le_int hf_le hf_le_tight hffree hBrange.2
        have hfl8 : (1 + UInt8.ofNat m + UInt8.ofNat f).toNat = 1 + m + f := by
          have hmof8 : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
          have hfof8 : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          rw [UInt8.toNat_add, UInt8.toNat_add, hmof8, hfof8,
            show ((1 : UInt8).toNat = 1) from rfl]
          omega
        have hds := depth_sum_foldl_set (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
          ).pileDepth pile.toNat hpile (0 : UInt8)
        rw [hd1'] at hds
        simp only [show ((1 : UInt8).toNat = 1) from rfl,
          show ((0 : UInt8).toNat = 0) from rfl] at hds
        have hft := usedSpace_term_foldl_set (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p
            ).pileDepth
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute
          pile.toNat hpile (0 : UInt8) (1 : UInt8)
        rw [hd1', hpfEq] at hft
        simp only [show ((0 : UInt8) ≠ (0 : UInt8)) = False from by simp,
          show ((1 : UInt8) ≠ (0 : UInt8)) = True from by simp, reduceIte] at hft
        rw [hfl8] at hft
        show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).usedSpace +
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile
              )).toInt =
          (52 : Int)
          - ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)
              ).pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
          - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
          - ((List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
              (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.toList
              (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile) m f p)).pileFlute.toList
              |>.foldl (·+·) 0 : Nat))
        have hpdeqL : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.toList =
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.set
              pile.toNat (0 : UInt8) hpile).toList := by
          simp only [kingMove]
        have hpfeqL : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile) m f p)).pileFlute.toList =
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute.set
              pile.toNat (1 : UInt8) hpile).toList := by
          simp only [kingMove]
        rw [hpdeqL, hpfeqL]
        have hfl8Int : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileFlute[pile.toNat]'hpile
            ).toInt = (1 + (m : Int) + f) := by
          rw [hpfEq]
          show (((1 + UInt8.ofNat m + UInt8.ofNat f).toNat : Nat) : Int) = _
          rw [hfl8]
          push_cast
          ring
        rw [UInt8.toInt_add, hfl8Int]
        have hxcast : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).usedSpace.toInt =
            (((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).usedSpace.toNat : Int)) := rfl
        omega

/-- `1 <<< x < 16` whenever the shift amount `x.toNat < 4` (the bit set sits
    among the low 4 positions) — finite check via `native_decide`. -/
private theorem uint8_one_shl_lt16_nat :
    ∀ n : Nat, n < 256 → n < 4 → ((1 : UInt8) <<< UInt8.ofNat n).toNat < 16 := by
  native_decide

private theorem uint8_one_shl_lt16_of_lt4 (x : UInt8) (hx : x.toNat < 4) :
    ((1 : UInt8) <<< x) < 16 := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have h := uint8_one_shl_lt16_nat x.toNat h256 hx
  rw [UInt8.ofNat_toNat] at h
  rwa [UInt8.lt_iff_toNat_lt, show (16 : UInt8).toNat = 16 from by decide]

/-- `preCleanupPile`'s only `busyAces` write ORs in `1 <<< SUIT B`, a bit
    position `< 4` (`hs4`) — so the result stays `< 16` whenever the input
    did. -/
theorem preCleanupPile_busyAces_lt16 (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d : UInt8) (m f : Nat) (p : SolverPosType) (hp16 : p.busyAces < 16) :
    (preCleanupPile pile hpile B ph hs4 d m f p).busyAces < 16 := by
  have hs4' : (SUIT B).toNat < 4 := by rwa [UInt8.toNat_toUInt32] at hs4
  simp only [preCleanupPile]
  split
  · exact uint8_or_lt16_of_lt16 hp16 (uint8_one_shl_lt16_of_lt4 (SUIT B) hs4')
  · exact hp16

set_option maxHeartbeats 4000000 in
/-- **`SolverCleanupPile` preserves the base invariant layer** (up to the
    `freePiles` field, which `SolverInvBase` deliberately omits).

    The precondition is stated about the *flute-normalized* entry position
    `{ p with pileFlute[pile] := 1 }` rather than `p` itself: the callers
    (convert's cleanup loop, `SolverRemoveFlute`) leave a stale `pileFlute[pile]`
    behind — the function never reads it and overwrites it at the end — and the
    invariant's `usedSpace`/flute clauses are only true of the normalized
    position.  (The freed loop re-frees the old flute interiors; with a stale
    flute in the formula, `usedSpace_def` would double-count them.)

    No further hypotheses are needed: `aces_kings_valid` now allows the value-0
    `kings` sentinel (see its docstring), so the lone-king branch is fine — the
    freed-loop exit gives `aces[s] ≤ kings'[s]` directly, and the `busyAces` bit
    set in that case pends the foundation drain that restores `VALUE ≥ 1`.

    Proof status: complete.  The empty-pile case is direct; the loop-bearing case
    runs `cleanupPile_nonempty_eq` (the exact symbolic run) and discharges its
    clauses one by one. -/
theorem cleanupPile_base (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p)) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok fk (g, p') ∧
      SolverInvBase g p' := by
  rcases cleanupPile_eq pile g p hpile hwf hnf with
    ⟨hd, hsd, hrun⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- Empty pile: the depth write is a no-op; the base layer ignores `freePiles`.
    exact ⟨0xffff, _, hrun, by simp only [hsd]; exact nf_setFreePiles hnf _⟩
  · -- Loop-bearing case: reassemble `SolverInvBase` from `cleanupPile_eq`'s
    -- non-king/king bundle — `hsuit`/`hhash`/`hused` are already in exactly the
    -- shape `SolverInvBase`'s fields need; only `pileBase` (for `pile` itself
    -- via `hpc.toPileBase`, for other piles via the modular `_ne` lemmas
    -- chained through `hnfp`) and `busyAces_lt16` need assembling here.
    have hp16 : p.busyAces < 16 := hnf.busyAces_lt16
    rcases hbranch with
      ⟨-, hframe, hpc, hsuit, hhash, hused, hrun⟩ |
      ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
    · refine ⟨0xffff, _, hrun, fun i => ?_, hsuit, hhash, hused,
        preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p hp16⟩
      by_cases hij : i.val = pile.toNat
      · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
        subst hii
        exact hpc.toPileBase
      · exact preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p
          m f hd5 (by omega) i hij (hnfp i hij)
    · refine ⟨_, _, hrun, fun i => ?_, hsuit, hhash, hused, ?_⟩
      · by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact kingMove_pileBase_ne pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile) _ i
            hij (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
              hd5 (by omega) i hij (hnfp i hij))
      · rw [kingMove_busyAces_eq]
        exact preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p hp16

/-- Pure combinatorics: splitting a `List.finRange n`-indexed count at one
    excluded index `k` into the filtered count (over `j ≠ k`) plus the
    indicator of `k` itself.  Proved by induction on `n`, peeling the front
    element via `List.finRange_succ` and case-splitting on whether `k` is that
    front element (`k = 0`) or lies in the tail (`k = k' + 1`). -/
private theorem finRange_countP_ite_split : ∀ (n k : Nat) (hk : k < n) (f : Fin n → Bool),
    (List.finRange n).countP (fun j => (j.val != k) && f j) +
      (if f ⟨k, hk⟩ then 1 else 0) = (List.finRange n).countP f
  | 0, k, hk, _f => absurd hk (by omega)
  | (n+1), k, hk, f => by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [List.finRange_succ, List.countP_cons_of_neg (by simp), List.countP_cons, List.countP_map, List.countP_map, Function.comp_def, Function.comp_def]
        have h3 : (List.finRange n).countP (fun j : Fin n => (Fin.succ j).val != 0 &&
            f (Fin.succ j)) = (List.finRange n).countP (fun j : Fin n => f (Fin.succ j)) := by
          apply List.countP_congr
          intro j' _
          simp
        have h0eq : f ⟨0, hk⟩ = f (0 : Fin (n+1)) := by congr 1
        rw [h0eq]
        omega
      · obtain ⟨k', hkval⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        have hkeq1 : k = k' + 1 := by omega
        subst hkeq1
        have hk' : k' < n := by omega
        rw [List.finRange_succ, List.countP_cons, List.countP_cons, List.countP_map, List.countP_map, Function.comp_def, Function.comp_def]
        have hpred0 : ((0:Fin (n+1)).val != k'+1 && f 0) = f 0 := by simp
        rw [hpred0]
        have hkeq : (⟨k'+1, hk⟩ : Fin (n+1)) = Fin.succ ⟨k', hk'⟩ := by
          apply Fin.ext; simp
        rw [hkeq]
        have hcomp : (List.finRange n).countP (fun j : Fin n => (Fin.succ j).val != k'+1 &&
            f (Fin.succ j)) =
            (List.finRange n).countP (fun j : Fin n => j.val != k' && f (Fin.succ j)) := by
          apply List.countP_congr
          intro j' _
          have heqv : ((Fin.succ j').val != k' + 1) = (j'.val != k') := by
            simp only [Fin.val_succ]
            by_cases h : j'.val = k'
            · simp [h]
            · simp
          rw [heqv]
        rw [hcomp]
        have hstep := finRange_countP_ite_split n k' hk' (fun j => f (Fin.succ j))
        omega

/-- `CleanupReady`'s `freePiles` formula (which excludes `pile`) plus the
    indicator of `pile`'s own current emptiness equals `SolverInvMerged`'s
    formula (over all 10 piles) — the arithmetic bridge the plan calls for.
    Combines `finRange_countP_ite_split` with the fact that `Vector.toList`'s
    `countP` agrees with the `List.finRange`-indexed `countP` via `Vector.get`. -/
theorem cleanupReady_freePiles_split (pile : UInt32) (hpile : pile.toNat < 10)
    (q : SolverPosType) (fpCount : Nat)
    (hcount : fpCount = ((List.finRange 10).countP
        (fun j => j.val != pile.toNat && (q.pileDepth.get j == 0)) : Nat)) :
    q.pileDepth.toList.countP (· == 0) =
      fpCount + (if q.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) == 0 then 1 else 0) := by
  have hlistEq : q.pileDepth.toList = (List.finRange 10).map (fun j => q.pileDepth.get j) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [Vector.getElem_toList, List.getElem_map, List.getElem_finRange]
      rfl
  rw [hlistEq, List.countP_map, Function.comp_def, hcount]
  have hsplit := finRange_countP_ite_split 10 pile.toNat hpile
    (fun j => q.pileDepth.get j == 0)
  omega

/-- The `j ≠ pile` part of `CleanupReady`'s `freePiles` formula only reads
    `q.pileDepth.get j` for `j ≠ pile` (the `&&` short-circuits to `false` at
    `j = pile` regardless), so it transfers unchanged across any frame
    condition agreeing with a reference position outside `pile`. -/
theorem cleanupReady_freePiles_frame_eq (pile : UInt32) (p q : SolverPosType)
    (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileDepth.get j = p.pileDepth.get j) :
    (List.finRange 10).countP (fun j => j.val != pile.toNat && (q.pileDepth.get j == 0)) =
    (List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) := by
  apply List.countP_congr
  intro j _
  by_cases hij : j.val = pile.toNat
  · simp [hij]
  · rw [hframe j hij]

/-- **`SolverCleanupPile` re-establishes the Merged layer** from the midpoint
    predicate.  On top of `cleanupPile_baseNF`'s clause discharge this adds, at
    the same discharge site:

    * `PileMerged` for `pile` itself, from `cleanupRunResult`'s loop exit facts
      (`¬mergeGuard` ⇒ merge_complete, `¬freedGuard` ⇒ flute_maximal) and the
      busyAces branch condition (⇒ busyAces_complete);
    * preservation of the other piles' `PileMerged` — the nontrivial part is
      `flute_maximal[j]`: if pile `j`'s extension card were among the freshly
      freed cards `T..T+m−1`, `j`'s interiors would have to include the
      *non-free* new boundary `T+m`, contradicting `flute_cards_free[j]`;
    * `freePiles_def`, restored by cleanup itself (the empty and lone-king
      branches do `+1` and leave depth 0; otherwise the pile keeps depth ≥ 1). -/
theorem cleanupPile_merged (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hready : CleanupReady g (fluteNorm pile hpile p) pile) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' ∧ p'.aces = p.aces ∧
      (∀ mask : UInt8, p.busyAces &&& mask ≠ 0 → p'.busyAces &&& mask ≠ 0) := by
  obtain ⟨hnf, hpmOther, hfpCount⟩ := hready
  -- Restate `hfpCount` in terms of `p` directly (rather than
  -- `fluteNorm pile hpile p`): a `have`-with-explicit-type cast needing only
  -- the two sides' *defeq* (fluteNorm doesn't touch `pileDepth`/`freePiles`),
  -- not syntactic equality — needed because plain `rw`/`omega` match atoms
  -- syntactically and would otherwise treat the two spellings as unrelated.
  have hfpCount' : p.freePiles.toInt = ((List.finRange 10).countP
      (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) : Nat) := hfpCount
  -- Reusable overflow-safety bound: `CleanupReady`'s prefix count is a `countP`
  -- over the 10-element `List.finRange 10`, hence trivially ≤ 10 — enough
  -- headroom for the `UInt8` `+1` arithmetic in the empty/king branches below.
  have hfp_le' : ((List.finRange 10).countP
      (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) : Nat) ≤ 10 :=
    le_trans List.countP_le_length (by simp)
  -- Bridge `hpmOther` (about `fluteNorm pile hpile p`) down to a fact about
  -- `p` itself — exactly the same idea as `cleanupPile_eq`'s own `hnfp`
  -- bridges `PileBase`, needed because `preCleanupPile_pileMerged_ne`/
  -- `kingMove_pileMerged_ne` are stated about `p` directly.
  have hpmOtherP : ∀ j : Fin 10, j.val ≠ pile.toNat →
      PileMerged g p j (hnf.pileDepth_bound j) := by
    intro j hij
    have hfeq : (fluteNorm pile hpile p).pileFlute.get j = p.pileFlute.get j := by
      show (fluteNorm pile hpile p).pileFlute[j.val]'j.isLt = p.pileFlute[j.val]'j.isLt
      simp only [fluteNorm]
      exact Vector.getElem_set_ne hpile j.isLt (Ne.symm hij)
    have hb := hpmOther j hij
    refine ⟨hb.merge_complete, ?_, ?_⟩
    · have h2 := hb.flute_maximal
      rwa [hfeq] at h2
    · -- `busyAces_complete`'s field type has a `let boundary := …` before the
      -- real `∀ hs, …` binder; `intro` consumes one name PER binder including
      -- that `let`, so naming just `hpos hs heq` would bind `hs` to the *let*
      -- (a card, not a proof) and shift everything else — avoid the whole
      -- naming hazard by rewriting the goal (via `hfeq`) down to `hb`'s own
      -- shape instead of introducing further.
      intro hpos
      rw [show p.pileFlute.get j = (fluteNorm pile hpile p).pileFlute.get j from hfeq.symm]
      exact hb.busyAces_complete hpos
  have hp16 : p.busyAces < 16 := hnf.busyAces_lt16
  rcases cleanupPile_eq pile g p hpile hwf hnf with
    ⟨hd, hsd, hrun⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- Empty pile.
    refine ⟨0xffff, _, hrun, ?_, rfl, fun mask hmask => hmask⟩
    have hbase' : SolverInvBase g { p with freePiles := p.freePiles + 1, pileDepth := p.pileDepth.set pile.toNat 0 hpile, pileFlute := p.pileFlute.set pile.toNat 1 hpile } := by
      simp only [hsd]; exact nf_setFreePiles hnf _
    refine SolverInvMerged.of_base hbase' (fun i => ?_) ?_
    · -- (2)/(3b)/(6) `PileMerged` for every pile.
      by_cases hij : i.val = pile.toNat
      · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
        subst hii
        have hp'd0 : (p.pileDepth.set pile.toNat 0 hpile).get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := by
          rw [hsd]; exact hd
        exact ⟨Or.inl (by rw [hp'd0]; decide), Or.inl hp'd0,
          fun h => absurd h (by rw [hp'd0]; decide)⟩
      · simp only [hsd]
        exact pm_setFreePiles (hpmOther i hij) _
    · -- (9) `freePiles_def`: `pileDepth` is unchanged (`hsd`), and `pile` itself
      -- (already empty, `hd`) newly contributes to the count, matching the `+1`.
      show (p.freePiles + 1).toInt =
        ((p.pileDepth.set pile.toNat 0 hpile).toList.countP (· == 0) : Nat)
      rw [hsd]
      have hsplit := cleanupReady_freePiles_split pile hpile p
        ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
        rfl
      have hd' : p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := hd
      have hind : (if p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : UInt8) then
          (1 : Nat) else 0) = 1 := by simp [hd']
      rw [hind] at hsplit
      have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
        rw [UInt8.toInt_add, UInt8.toInt_one]
        omega
      omega
  · -- Loop-bearing case: reassemble `SolverInvMerged` from `cleanupPile_eq`'s
    -- non-king/king bundle — `hsuit`/`hhash`/`hused` are already the shape
    -- `SolverInvBase` needs; `pileBase`/`pileMerged` come from `hpc` (for
    -- `pile` itself) chained with the modular `_ne` lemmas through `hnfp`/
    -- `hpmOtherP` (for the others); `freePiles_def` from the two helper
    -- lemmas above plus the branch's own frame/depth facts.
    rcases hbranch with
      ⟨-, hframe, hpc, hsuit, hhash, hused, hrun⟩ |
      ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
    · -- NON-KING sub-branch.
      have hbase' : SolverInvBase g (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p) := by
        refine ⟨fun i => ?_, hsuit, hhash, hused,
          preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p hp16⟩
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p
            m f hd5 (by omega) i hij (hnfp i hij)
      have hpmAll : ∀ i : Fin 10, PileMerged g (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p) i
          (hbase'.pileDepth_bound i) := by
        intro i
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileMerged
        · exact preCleanupPile_pileMerged_ne pile g hpile hwf B (pileHashes[pile.toNat]'hpile) hs4
            p m f hd5 hm_le hmcards hak i hij (hnfp i hij) (hpmOtherP i hij)
      have hpdEqNK : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile =
          ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hpdNeNK : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) ≠ 0 := by
        show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth[pile.toNat]'hpile ≠ 0
        rw [hpdEqNK]
        intro heq
        have h' := congrArg UInt8.toNat heq
        rw [depth_sub_ofNat_eq hd5 (by omega),
          show ((0 : UInt8).toNat = 0) from rfl] at h'
        omega
      have hfp : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile) m f p).freePiles.toInt =
          ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.toList.countP (· == 0) :
            Nat) := by
        have hfeq2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).freePiles = p.freePiles := by
          simp only [preCleanupPile]
        have hframeEq := cleanupReady_freePiles_frame_eq pile p
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p) hframe
        have hsplit := cleanupReady_freePiles_split pile hpile
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)
          ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
          hframeEq.symm
        have hind : (if (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : UInt8) then (1 : Nat) else 0) = 0 := by
          simp [beq_eq_false_iff_ne.mpr hpdNeNK]
        rw [hind] at hsplit
        rw [hfeq2]
        omega
      -- `busyAces` monotonicity: `preCleanupPile` either leaves it alone or
      -- ORs in one more bit, so an already-set bit stays set.
      have hbusyMonoNK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
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
      exact ⟨0xffff, _, hrun, SolverInvMerged.of_base hbase' hpmAll hfp, rfl, hbusyMonoNK⟩
    · -- KING sub-branch.
      have hbase' : SolverInvBase g (kingMove pile hpile (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile) (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p)) := by
        refine ⟨fun i => ?_, hsuit, hhash, hused, ?_⟩
        swap
        · rw [kingMove_busyAces_eq]
          exact preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p hp16
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact kingMove_pileBase_ne pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile) _ i
            hij (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
              hd5 (by omega) i hij (hnfp i hij))
      have hpmAll : ∀ i : Fin 10, PileMerged g (kingMove pile hpile (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile) (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile) m f p)) i
          (hbase'.pileDepth_bound i) := by
        intro i
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileMerged
        · exact kingMove_pileMerged_ne pile g hpile hwf (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              _ hd1' K hKdef hVK13 hak i hij
              (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
                hd5 (by omega) i hij (hnfp i hij))
              (preCleanupPile_pileMerged_ne pile g hpile hwf B (pileHashes[pile.toNat]'hpile) hs4
                p m f hd5 hm_le hmcards hak i hij (hnfp i hij) (hpmOtherP i hij))
      have hkmfp : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)).freePiles = p.freePiles + 1 := by
        simp only [kingMove, preCleanupPile]
      have hkd0 : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) = 0 :=
        kingMove_pileDepth_self pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)
      have hfp : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile) m f p)).freePiles.toInt =
          ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.toList.countP (· == 0) :
            Nat) := by
        have hframeEq := cleanupReady_freePiles_frame_eq pile p
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p)) hframe
        have hsplit := cleanupReady_freePiles_split pile hpile
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p))
          ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
          hframeEq.symm
        have hind : (if (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p)).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : UInt8) then (1 : Nat) else 0) = 1 := by
          simp [hkd0]
        rw [hind] at hsplit
        rw [hkmfp]
        have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
          rw [UInt8.toInt_add, UInt8.toInt_one]
          omega
        omega
      have hbusyMonoNK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
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
      have hbusyMonoK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile) m f p)).busyAces &&& mask ≠ 0 := by
        intro mask hmask
        rw [kingMove_busyAces_eq]
        exact hbusyMonoNK mask hmask
      exact ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4, _, hrun,
        SolverInvMerged.of_base hbase' hpmAll hfp, rfl, hbusyMonoK⟩

end SolverSpec
