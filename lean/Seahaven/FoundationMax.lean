import Seahaven.CleanupLax
import Seahaven.ReachableMatch

/-!
# Maximizing the foundations

The first half of `CvPrologueSim` (`ConvertMatch`): loop 2 writes
`aces[su] = cvAceVal`, the highest foundation the *depth vector* allows, and the state has
to catch up by playing cards to its foundations.

The play is available: the cards `A … cvAceVal` of a suit are all free, so none of them is
a resident dealt card, and a free card is either in a cell or — since the cards above it in
a column are same-suit *lower* ranks, which the ascending play has already banked —
exposed on top of its column.  So the suit can be played one card at a time, and the walk
stops exactly at `cvAceVal`: the next card is not free, i.e. it is some pile's resident.

Everything here is read off the **depth match** alone; no position invariant is available
at the intermediate states (`foundation_maximal_weak` is exactly what fails while the
foundations are still climbing).
-/

namespace SolverSpec

/-! ## A card is in one place -/

/-- A card its foundation already covers is not lying in a column. -/
theorem not_mem_column_of_covered {u : State} (hcount : ∀ c : Card, countState u c = 1)
    {c : Card} (hcov : rankToNat c.rank ≤ optRankToNat (u.foundations c.suit)) {j : Fin 10}
    (hmem : c ∈ u.tableau j) : False := by
  have h1 : countFoundation u.foundations c = 1 := by
    unfold countFoundation
    rw [if_neg (by omega)]
  have h2 : 1 ≤ countColumn (u.tableau j) c := one_le_countColumn hmem
  have h3 : countColumn (u.tableau j) c ≤ countTableau u.tableau c :=
    le_sum_ofFn (fun k : Fin 10 => countColumn (u.tableau k) c) j
  have h := hcount c
  unfold countState at h
  omega

/-- **A card that is not free sits in its own dealt slot**, hence in that column: the
depth match puts the bottom `pileDepth` cards of every column where the layout says. -/
theorem mem_column_of_not_free {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (c : Card) (hnf : ¬ isFreeCard g p (encodeCard c)) : ∃ j : Fin 10, c ∈ u.tableau j := by
  have hreal : IsRealCard (encodeCard c) := encodeCard_real c
  have hc64 : (encodeCard c).toNat < 64 := IsRealCard_lt64 hreal
  have hp10 : (cardPile g (encodeCard c)).toNat < 10 := hwf.pile_lt _ hreal
  set P : Fin 10 := ⟨(cardPile g (encodeCard c)).toNat, hp10⟩ with hPdef
  have hlt : (cardDepth g (encodeCard c)).toNat < (p.pileDepth.get P).toNat := by
    by_contra hge
    refine hnf (isFree_of_cardDepth_ge g p hwf _ hc64 hp10 ?_)
    show (cardDepth g (encodeCard c)).toNat ≥ (p.pileDepth.get P).toNat
    omega
  have hd5 : (cardDepth g (encodeCard c)).toNat < 5 := by have := hd6 P; omega
  have hnL : (p.pileDepth.get P).toNat ≤ (u.tableau P).length := (hdm P).1
  have hrevP : (cardDepth g (encodeCard c)).toNat < (u.tableau P).reverse.length := by
    simp only [List.length_reverse]; omega
  have hcode := (hdm P).resident_code hlt hrevP
  have hround := hwf.round_trip (encodeCard c) hreal hd5
  refine ⟨P, ?_⟩
  have hdP : (u.tableau P).reverse[(cardDepth g (encodeCard c)).toNat]'hrevP = c := by
    refine encodeCard_inj ?_
    rw [hcode]
    exact hround
  rw [← hdP]
  exact List.mem_reverse.mp (List.getElem_mem ..)

/-! ## Reading the run above a boundary -/

/-- A rank exists for every value in range. -/
theorem exists_rank_of_le {n : Nat} (h1 : 1 ≤ n) (h13 : n ≤ 13) : ∃ r : Rank, rankToNat r = n := by
  interval_cases n
  exacts [⟨Rank.ace, rfl⟩, ⟨Rank.two, rfl⟩, ⟨Rank.three, rfl⟩, ⟨Rank.four, rfl⟩,
    ⟨Rank.five, rfl⟩, ⟨Rank.six, rfl⟩, ⟨Rank.seven, rfl⟩, ⟨Rank.eight, rfl⟩,
    ⟨Rank.nine, rfl⟩, ⟨Rank.ten, rfl⟩, ⟨Rank.jack, rfl⟩, ⟨Rank.queen, rfl⟩,
    ⟨Rank.king, rfl⟩]

/-- **A free card in a column sits above the boundary.**  The depth-match-only reading of
`free_above_boundary`: `depth_card_not_free_wf` needs no position invariant. -/
theorem free_reverse_index_ge {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (i : Fin 10) {r : Nat} (hrl : r < (u.tableau i).reverse.length)
    (hfree : isFreeCard g p (encodeCard ((u.tableau i).reverse[r]'hrl))) :
    (p.pileDepth.get i).toNat ≤ r := by
  by_contra hlt
  have hr5 : r < 5 := by have := hd6 i; omega
  refine depth_card_not_free_wf hwf i ⟨r, hr5⟩
    (show r < (p.pileDepth.get i).toNat from by omega) ?_
  rw [← (hdm i).resident_code (show r < (p.pileDepth.get i).toNat from by omega) hrl]
  exact hfree

/-- **Above a free card in a column sits its predecessor.**  Both cards are in the run
above the boundary, where the value climbs by one per card downwards. -/
theorem column_above_of_free {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (i : Fin 10) {r : Nat} (hr1 : r + 1 < (u.tableau i).reverse.length)
    (hrl : r < (u.tableau i).reverse.length)
    (hfree : isFreeCard g p (encodeCard ((u.tableau i).reverse[r]'hrl))) :
    ((u.tableau i).reverse[r + 1]'hr1).suit = ((u.tableau i).reverse[r]'hrl).suit ∧
      rankToNat ((u.tableau i).reverse[r + 1]'hr1).rank + 1
        = rankToNat ((u.tableau i).reverse[r]'hrl).rank := by
  have hge := free_reverse_index_ge hwf hd6 hdm i hrl hfree
  have hpos1 := rankToNat_pos ((u.tableau i).reverse[r]'hrl).rank
  have hpos2 := rankToNat_pos ((u.tableau i).reverse[r + 1]'hr1).rank
  have hv1 := encodeCard_VALUE ((u.tableau i).reverse[r]'hrl)
  have hv2 := encodeCard_VALUE ((u.tableau i).reverse[r + 1]'hr1)
  -- the two cards' codes, from the run structure
  obtain ⟨hs, hvals⟩ : SUIT (encodeCard ((u.tableau i).reverse[r + 1]'hr1))
        = SUIT (encodeCard ((u.tableau i).reverse[r]'hrl)) ∧
      (VALUE (encodeCard ((u.tableau i).reverse[r + 1]'hr1))).toNat + 1
        = (VALUE (encodeCard ((u.tableau i).reverse[r]'hrl))).toNat := by
    by_cases hn0 : (p.pileDepth.get i).toNat = 0
    · obtain ⟨su, hrun⟩ := (hdm i).king_run (show (⟨_, hd6 i⟩ : Fin 6).val = 0 from hn0)
      obtain ⟨hs1, hv1'⟩ := hrun r hrl
      obtain ⟨hs2, hv2'⟩ := hrun (r + 1) hr1
      exact ⟨by rw [hs1, hs2], by omega⟩
    · obtain ⟨hs1, hv1'⟩ := (hdm i).above_code
        (show 0 < (p.pileDepth.get i).toNat from by omega)
        (show (p.pileDepth.get i).toNat ≤ r from hge) hrl
      obtain ⟨hs2, hv2'⟩ := (hdm i).above_code
        (show 0 < (p.pileDepth.get i).toNat from by omega)
        (show (p.pileDepth.get i).toNat ≤ r + 1 from by omega) hr1
      have hnval : (⟨(p.pileDepth.get i).toNat, hd6 i⟩ : Fin 6).val
          = (p.pileDepth.get i).toNat := rfl
      exact ⟨by rw [hs1, hs2], by omega⟩
  refine ⟨?_, by omega⟩
  refine suitToNat_inj ?_
  have h1 := congrArg UInt8.toNat hs
  rw [encodeCard_SUIT, encodeCard_SUIT, UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h1
  have := suitToNat_lt ((u.tableau i).reverse[r + 1]'hr1).suit
  have := suitToNat_lt ((u.tableau i).reverse[r]'hrl).suit
  omega

/-! ## The next foundation card, when free, is accessible -/

/-- **A free card whose predecessors are all banked is exposed.**  It is not on a
foundation (its rank is above the top), and in a column the card above it is its own
predecessor — which the foundation already holds. -/
theorem accessible_of_free {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) {c : Card}
    (hrank : rankToNat c.rank = optRankToNat (u.foundations c.suit) + 1)
    (hfree : isFreeCard g p (encodeCard c)) : Accessible u c := by
  rcases NoDupState.location hcount c with hf | hcell | ⟨j, hmem⟩
  · -- not on a foundation: its rank is one above the top
    exfalso
    unfold countFoundation at hf
    rw [if_pos (by omega)] at hf
    exact absurd hf (by decide)
  · exact Or.inl hcell
  · -- in a column: it must be the head, else its predecessor is there too
    refine Or.inr ⟨j, ?_⟩
    obtain ⟨idx, hidx, hval⟩ := List.getElem_of_mem hmem
    -- read it at its reverse index
    have hlen : (u.tableau j).reverse.length = (u.tableau j).length := by simp
    have hrl : (u.tableau j).length - 1 - idx < (u.tableau j).reverse.length := by
      rw [hlen]; omega
    have hrev : (u.tableau j).reverse[(u.tableau j).length - 1 - idx]'hrl = c := by
      rw [List.getElem_reverse hrl, ← hval]
      congr 1
      omega
    by_cases hidx0 : idx = 0
    · subst hidx0
      rw [List.head?_eq_getElem? , List.getElem?_eq_getElem hidx, hval]
    · -- the card above `c` is its predecessor, which the foundation already covers
      exfalso
      have hr1 : ((u.tableau j).length - 1 - idx) + 1 < (u.tableau j).reverse.length := by
        rw [hlen]; omega
      obtain ⟨hsuit, hrk⟩ := column_above_of_free hwf hd6 hdm j hr1 hrl (by rw [hrev]; exact hfree)
      rw [hrev] at hsuit hrk
      refine not_mem_column_of_covered hcount (c := (u.tableau j).reverse[_]'hr1) ?_
        (j := j) (List.mem_reverse.mp (List.getElem_mem ..))
      rw [hsuit]
      omega

/-! ## The foundations start below the free run -/

/-- **A foundation never runs past the free prefix.**  Its top card is on the foundation,
hence not at its dealt slot, hence free — and the free prefix is exactly `cvAceVal`. -/
theorem foundation_le_aceVal {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) (su : Suit) :
    optRankToNat (u.foundations su) ≤ cvAceVal g p.pileDepth (suitToNat su) := by
  by_contra hlt
  have h13 : optRankToNat (u.foundations su) ≤ 13 := by
    cases hf : u.foundations su with
    | none => simp [optRankToNat]
    | some r => simpa [optRankToNat, hf] using rankBounded r
  -- the run stopped at a card the foundation covers
  have hcv : cvAceVal g p.pileDepth (suitToNat su)
      = runLen (aceFree g p.pileDepth (suitToNat su)) 13 := rfl
  have hstop : ¬ aceFree g p.pileDepth (suitToNat su) (cvAceVal g p.pileDepth (suitToNat su)) :=
    runLen_stop (aceFree g p.pileDepth (suitToNat su)) 13 (by omega)
  obtain ⟨r, hr⟩ := exists_rank_of_le (n := cvAceVal g p.pileDepth (suitToNat su) + 1)
    (by omega) (by omega)
  refine hstop ?_
  show freeAt g p.pileDepth (CARD (UInt8.ofNat (suitToNat su))
    (UInt8.ofNat (cvAceVal g p.pileDepth (suitToNat su) + 1)))
  rw [← show encodeCard ⟨su, r⟩ = CARD (UInt8.ofNat (suitToNat su))
      (UInt8.ofNat (cvAceVal g p.pileDepth (suitToNat su) + 1)) from by
    show CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (rankToNat r)) = _
    rw [hr]]
  rw [← isFreeCard_eq_freeAt]
  by_contra hnf
  obtain ⟨j, hmem⟩ := mem_column_of_not_free hwf hd6 hdm ⟨su, r⟩ hnf
  exact not_mem_column_of_covered hcount
    (show rankToNat (⟨su, r⟩ : Card).rank ≤ optRankToNat (u.foundations su) from by
      show rankToNat r ≤ optRankToNat (u.foundations su)
      omega) hmem

/-! ## Playing one suit up to the run the depths free -/

/-- **A column's bottom card survives, unless the column empties.**  Composed along a run
of plays: each play removes a column *head*. -/
theorem botFrame_trans {s t v : State}
    (h1 : ∀ q : Fin 10, (t.tableau q).getLast? = (s.tableau q).getLast? ∨ t.tableau q = [])
    (h2 : ∀ q : Fin 10, (v.tableau q).getLast? = (t.tableau q).getLast? ∨ v.tableau q = []) :
    ∀ q : Fin 10, (v.tableau q).getLast? = (s.tableau q).getLast? ∨ v.tableau q = [] := by
  intro q
  rcases h2 q with h2' | h2'
  · rcases h1 q with h1' | h1'
    · exact Or.inl (h2'.trans h1')
    · rw [h1'] at h2'
      simp only [List.getLast?_nil] at h2'
      exact Or.inr (List.getLast?_eq_none_iff.1 h2')
  · exact Or.inr h2'

private theorem reverse_getElem_head {col : Column} {c : Card} {rest : Column}
    (hcol : col = c :: rest) (h : rest.length < col.reverse.length) :
    col.reverse[rest.length]'h = c := by
  subst hcol
  rw [List.getElem_reverse h]
  simp

/-- **A free card on top of a column leaves the boundary behind**, so taking it keeps the
depth match (`PileMatches_tail_same`). -/
theorem depth_le_of_free_head {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (q : Fin 10) {c : Card} {rest : Column} (hcol : u.tableau q = c :: rest)
    (hfree : isFreeCard g p (encodeCard c)) : (p.pileDepth.get q).toNat ≤ rest.length := by
  have hrl : rest.length < (u.tableau q).reverse.length := by rw [hcol]; simp
  have hrev := reverse_getElem_head hcol hrl
  exact free_reverse_index_ge hwf hd6 hdm q hrl (by rw [hrev]; exact hfree)

/-- **One suit, played up to `cvAceVal`.**  `n` is a budget: any bound on how far the
foundation still has to climb will do. -/
theorem exists_plays_suit {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6) (su : Suit) :
    ∀ (n : Nat) (u : State), (∀ c : Card, countState u c = 1) →
      (∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩) →
      cvAceVal g p.pileDepth (suitToNat su) ≤ optRankToNat (u.foundations su) + n →
      ∃ t : State, FMReach u t ∧ (∀ c : Card, countState t c = 1) ∧
        (∀ i : Fin 10, PileMatches g (t.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩) ∧
        optRankToNat (t.foundations su) = cvAceVal g p.pileDepth (suitToNat su) ∧
        (∀ su' : Suit, su' ≠ su → t.foundations su' = u.foundations su') ∧
        (∀ (i : Fin 4) (x : Card), t.cells i = some x → u.cells i = some x) ∧
        (∀ q : Fin 10, (t.tableau q).getLast? = (u.tableau q).getLast? ∨ t.tableau q = []) := by
  intro n
  induction n with
  | zero =>
    intro u hcount hdm hle
    exact ⟨u, Relation.ReflTransGen.refl, hcount, hdm,
      le_antisymm (foundation_le_aceVal hwf hd6 hdm hcount su) (by omega), fun _ _ => rfl,
      fun _ _ h => h, fun _ => Or.inl rfl⟩
  | succ n ih =>
    intro u hcount hdm hle
    by_cases htop : optRankToNat (u.foundations su) = cvAceVal g p.pileDepth (suitToNat su)
    · exact ⟨u, Relation.ReflTransGen.refl, hcount, hdm, htop, fun _ _ => rfl, fun _ _ h => h,
        fun _ => Or.inl rfl⟩
    have hup := foundation_le_aceVal hwf hd6 hdm hcount su
    have hlt : optRankToNat (u.foundations su) < cvAceVal g p.pileDepth (suitToNat su) := by omega
    have hcv13 : cvAceVal g p.pileDepth (suitToNat su) ≤ 13 :=
      runLen_le (aceFree g p.pileDepth (suitToNat su)) 13
    have hcvdef : cvAceVal g p.pileDepth (suitToNat su)
        = runLen (aceFree g p.pileDepth (suitToNat su)) 13 := rfl
    -- the suit's next card
    obtain ⟨r, hr⟩ := exists_rank_of_le (n := optRankToNat (u.foundations su) + 1)
      (by omega) (by omega)
    have hready : some (⟨su, r⟩ : Card).rank = nextRank (u.foundations (⟨su, r⟩ : Card).suit) := by
      show some r = nextRank (u.foundations su)
      unfold nextRank
      rw [show optRankToNat (u.foundations su) + 1 = rankToNat r from hr.symm]
      exact (rankToNatToRank (some r)).symm
    have hcodeEq : encodeCard (⟨su, r⟩ : Card)
        = CARD (UInt8.ofNat (suitToNat su))
          (UInt8.ofNat (optRankToNat (u.foundations su) + 1)) := by
      show CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (rankToNat r)) = _
      rw [hr]
    have hfree : isFreeCard g p (encodeCard (⟨su, r⟩ : Card)) := by
      rw [isFreeCard_eq_freeAt]
      show freeAt g p.pileDepth (encodeCard (⟨su, r⟩ : Card))
      rw [hcodeEq]
      exact runLen_holds (aceFree g p.pileDepth (suitToNat su)) 13
        (optRankToNat (u.foundations su)) (by omega)
    obtain ⟨t1, hplay⟩ := PlaysTo.of_accessible
      (accessible_of_free hwf hd6 hdm hcount
        (show rankToNat (⟨su, r⟩ : Card).rank
            = optRankToNat (u.foundations (⟨su, r⟩ : Card).suit) + 1 from by
          show rankToNat r = optRankToNat (u.foundations su) + 1
          exact hr) hfree) hready
    -- what the play does
    obtain ⟨pos, hap⟩ := hplay.toFMStep
    have hcount1 : ∀ c : Card, countState t1 c = 1 := by
      intro c
      rw [← congrFun (movePreservesCards u _ t1 hap) c]
      exact hcount c
    have hfnd1 : t1.foundations = update u.foundations su r := by
      have h := hplay.foundations
      simpa using h
    have htop1 : optRankToNat (t1.foundations su) = optRankToNat (u.foundations su) + 1 := by
      rw [hfnd1, update_same]
      show rankToNat r = _
      exact hr
    have hoth1 : ∀ su' : Suit, su' ≠ su → t1.foundations su' = u.foundations su' := by
      intro su' hne
      rw [hfnd1, update_diff _ _ _ _ (Ne.symm hne)]
    have hdm1 : ∀ i : Fin 10,
        PileMatches g (t1.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩ := by
      rcases hplay.cases with ⟨i, hc, rfl⟩ | ⟨q, rest, hcol, rfl⟩
      · simpa using hdm
      · intro j
        by_cases hjq : j = q
        · subst hjq
          have hle' : (p.pileDepth.get j).toNat ≤ rest.length :=
            depth_le_of_free_head hwf hd6 hdm j hcol hfree
          have hm : PileMatches g ((⟨su, r⟩ : Card) :: rest) j
              ⟨(p.pileDepth.get j).toNat, hd6 j⟩ := by rw [← hcol]; exact hdm j
          have hres := PileMatches_tail_same hm (show (⟨(p.pileDepth.get j).toNat, hd6 j⟩
            : Fin 6).val ≤ rest.length from hle')
          simpa using hres
        · have : (updateFoundation (updateColumn u q rest) (⟨su, r⟩ : Card)).tableau j
              = u.tableau j := by
            simp only [updateFoundation_tableau, updateColumn_tableau]
            exact update_diff _ _ _ _ (Ne.symm hjq)
          rw [this]
          exact hdm j
    -- the cells only ever lose a card
    have hcells1 : ∀ (i : Fin 4) (x : Card), t1.cells i = some x → u.cells i = some x := by
      rcases hplay.cases with ⟨i, hc, rfl⟩ | ⟨q, rest, hcol, rfl⟩
      · intro i' x hx
        simp only [updateFoundation_cells, updateCell_cells, update] at hx
        by_cases hii : i = i'
        · rw [if_pos hii] at hx; exact absurd hx (by simp)
        · rw [if_neg hii] at hx; exact hx
      · intro i' x hx
        simpa using hx
    -- and a column's bottom card only disappears with the column
    have hbot1 : ∀ q : Fin 10,
        (t1.tableau q).getLast? = (u.tableau q).getLast? ∨ t1.tableau q = [] := by
      rcases hplay.cases with ⟨i, hc, rfl⟩ | ⟨q, rest, hcol, rfl⟩
      · intro q'
        exact Or.inl (by simp)
      · intro q'
        by_cases hqq : q' = q
        · subst hqq
          have hcolnew : (updateFoundation (updateColumn u q' rest)
              (⟨su, r⟩ : Card)).tableau q' = rest := by
            simp only [updateFoundation_tableau, updateColumn_tableau]
            exact update_same _ _ _
          rw [hcolnew, hcol]
          cases hrest : rest with
          | nil => exact Or.inr rfl
          | cons y ys => exact Or.inl (by simp)
        · refine Or.inl ?_
          have : (updateFoundation (updateColumn u q rest) (⟨su, r⟩ : Card)).tableau q'
              = u.tableau q' := by
            simp only [updateFoundation_tableau, updateColumn_tableau]
            exact update_diff _ _ _ _ (Ne.symm hqq)
          rw [this]
    obtain ⟨t, hreach, hct, hdmt, htopt, hotht, hcellst, hbott⟩ :=
      ih t1 hcount1 hdm1 (by omega)
    exact ⟨t, Relation.ReflTransGen.head ⟨pos, hap⟩ hreach, hct, hdmt, htopt,
      fun su' hne => (hotht su' hne).trans (hoth1 su' hne),
      fun i x hx => hcells1 i x (hcellst i x hx), botFrame_trans hbot1 hbott⟩

/-! ## All four suits

The four plays do not interfere: each advances only its own foundation, and freeness — the
only thing the accessibility argument reads — depends on the depth vector, which no
foundation play touches. -/

theorem cvAceVal_le_13 (g : Globals) (d : Vector UInt8 10) (su : Nat) :
    cvAceVal g d su ≤ 13 := runLen_le (aceFree g d su) 13

/-- **The foundations, maximized.**  Only foundation plays, and the depth match survives:
every card played was free, hence above its column's boundary. -/
theorem exists_maximal_foundations {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6) (u : State)
    (hcount : ∀ c : Card, countState u c = 1)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩) :
    ∃ t : State, FMReach u t ∧ (∀ c : Card, countState t c = 1) ∧
      (∀ i : Fin 10, PileMatches g (t.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩) ∧
      (∀ (i : Fin 4) (x : Card), t.cells i = some x → u.cells i = some x) ∧
      (∀ q : Fin 10, (t.tableau q).getLast? = (u.tableau q).getLast? ∨ t.tableau q = []) ∧
      ∀ su : Suit, optRankToNat (t.foundations su) = cvAceVal g p.pileDepth (suitToNat su) := by
  obtain ⟨t1, hr1, hc1, hd1, hf1, ho1, hx1, hb1⟩ := exists_plays_suit hwf hd6 Suit.clubs 13 u hcount hdm
    (by have := cvAceVal_le_13 g p.pileDepth (suitToNat Suit.clubs); omega)
  obtain ⟨t2, hr2, hc2, hd2, hf2, ho2, hx2, hb2⟩ := exists_plays_suit hwf hd6 Suit.diamonds 13 t1 hc1 hd1
    (by have := cvAceVal_le_13 g p.pileDepth (suitToNat Suit.diamonds); omega)
  obtain ⟨t3, hr3, hc3, hd3, hf3, ho3, hx3, hb3⟩ := exists_plays_suit hwf hd6 Suit.hearts 13 t2 hc2 hd2
    (by have := cvAceVal_le_13 g p.pileDepth (suitToNat Suit.hearts); omega)
  obtain ⟨t4, hr4, hc4, hd4, hf4, ho4, hx4, hb4⟩ := exists_plays_suit hwf hd6 Suit.spades 13 t3 hc3 hd3
    (by have := cvAceVal_le_13 g p.pileDepth (suitToNat Suit.spades); omega)
  refine ⟨t4, ((hr1.trans hr2).trans hr3).trans hr4, hc4, hd4,
    fun i x hx => hx1 i x (hx2 i x (hx3 i x (hx4 i x hx))),
    botFrame_trans (botFrame_trans (botFrame_trans hb1 hb2) hb3) hb4, fun su => ?_⟩
  cases su with
  | clubs =>
    rw [ho4 _ (by decide), ho3 _ (by decide), ho2 _ (by decide)]
    exact hf1
  | diamonds =>
    rw [ho4 _ (by decide), ho3 _ (by decide)]
    exact hf2
  | hearts =>
    rw [ho4 _ (by decide)]
    exact hf3
  | spades => exact hf4

end SolverSpec
