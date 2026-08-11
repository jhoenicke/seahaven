import Seahaven.FoundationMax

/-!
# Completing the king piles

The second half of `CvPrologueSim` (`ConvertMatch`): loop 2 writes
`kings[su] = cvKingVal`, and `king_pile` pins a solver-empty column's *length* to
`13 - VALUE kings[su]` — so the freed king-run cards that are still in cells have to be
dropped onto that column.

The moves are already there: `KingMoveSim.reach_pile_run` drops a run onto a column card by
card, from *any* starting length (`kingPileEquiv` uses it from the empty column).  What
this file adds is the two facts it needs about the state:

* the column already is a king run (`eq_kingRun_of_pileMatches`) — so `reach_pile_run`'s
  precondition on the column holds with `V + 1 + n = 14 - |col|`;
* the cards between `cvKingVal + 1` and that run are in the cells — they are free
  (`kingFree`), above the foundation (`cvAceVal ≤ cvKingVal`), and in no column: above a
  live boundary they would force that boundary to be free, and a *solver-empty* column
  carrying them would have to carry the suit's king, which the queried configuration
  already puts on this pile.
-/

namespace SolverSpec

/-! ## A solver-empty column is a king run -/

private theorem reverse_getElem_col {col : Column} {idx : Nat} (h : idx < col.length)
    (hr : col.length - 1 - idx < col.reverse.length) :
    col.reverse[col.length - 1 - idx]'hr = col[idx]'h := by
  rw [List.getElem_reverse hr]
  congr 1
  omega

/-- **A column the solver treats as empty is its suit's king run.**  Its cards descend from
the king at the bottom, and `kingRun` is exactly that list. -/
theorem eq_kingRun_of_pileMatches {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (hm : PileMatches g col a n) (hn : n.val = 0) (h13 : col.length ≤ 13) {su : Suit}
    (hsu : ∀ d ∈ col.getLast?, d.suit = su) :
    col = kingRun su (14 - col.length) := by
  obtain ⟨su', hrun⟩ := hm.king_run hn
  have hlenrev : col.reverse.length = col.length := by simp
  -- every card of the column carries the bottom card's suit and the value its depth says
  have helem : ∀ (idx : Nat) (h : idx < col.length),
      (SUIT (encodeCard (col[idx]'h)) = su' ∧
        (VALUE (encodeCard (col[idx]'h))).toNat = 14 - col.length + idx) := by
    intro idx h
    have hr : col.length - 1 - idx < col.reverse.length := by rw [hlenrev]; omega
    obtain ⟨hs, hv⟩ := hrun (col.length - 1 - idx) hr
    rw [reverse_getElem_col h hr] at hs hv
    exact ⟨hs, by omega⟩
  -- the bottom card pins the suit code
  have hsucode : ∀ (idx : Nat) (h : idx < col.length), (col[idx]'h).suit = su := by
    intro idx h
    have hL : 0 < col.length := by omega
    have hlast : col.getLast? = some (col[col.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    have hbot : (col[col.length - 1]'(by omega)).suit = su := hsu _ hlast
    refine suitToNat_inj ?_
    have h1 := congrArg UInt8.toNat (helem idx h).1
    have h2 := congrArg UInt8.toNat (helem (col.length - 1) (by omega)).1
    rw [encodeCard_SUIT, UInt8.toNat_ofNat'] at h1 h2
    have := suitToNat_lt (col[idx]'h).suit
    have := suitToNat_lt (col[col.length - 1]'(by omega)).suit
    rw [← hbot]
    omega
  refine List.ext_getElem (by rw [kingRun_length]; omega) (fun idx h1 h2 => ?_)
  simp only [kingRun, List.getElem_map, List.getElem_range]
  refine Card.ext (hsucode idx h1) (rankInj _ _ ?_)
  rw [rankToNat_cardOf su (by omega) (by omega), ← encodeCard_VALUE]
  exact (helem idx h1).2

/-! ## The freed king run

`cvAceVal_le_cvKingVal` (`ConvertInv`) already says the two runs of a suit do not meet. -/

/-- The king-run cards are free. -/
theorem kingRun_card_free (g : Globals) (d : Vector UInt8 10) (su : Nat) {v : Nat}
    (hv1 : cvKingVal g d su < v) (hv13 : v ≤ 13) (hA : cvAceVal g d su < 13) :
    freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat v)) := by
  have hT : cvKingRun g d su ≤ 12 := cvKingRun_le g d su hA
  have hKR : cvKingRun g d su = runLen (kingFree g d su) 13 := rfl
  have hKV : cvKingVal g d su = 13 - cvKingRun g d su := by
    unfold cvKingVal; rw [if_neg (by omega)]
  have hfree : freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - (13 - v)))) :=
    runLen_holds (kingFree g d su) 13 (13 - v) (by omega)
  rw [show 13 - (13 - v) = v from by omega] at hfree
  exact hfree

/-! ## The freed run's missing cards are in the cells

The one semantic step of the piling direction, and the reason `CvEntry.kingPiled` is there:
a card of the freed king run that the pile does not carry is in a cell.  It is free, it is
past the foundation (`cvAceVal ≤ cvKingVal`), and no column can hold it — above a live
boundary that boundary would be a *higher* card of the same suit, hence itself in the freed
run and free, which a resident is not; and a solver-empty column holding it would have to
carry this suit's king, which sits on the pile already. -/

theorem kingRun_card_in_cell {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (hfnd : ∀ su : Suit, optRankToNat (u.foundations su)
      = cvAceVal g p.pileDepth (suitToNat su))
    {su : Suit} {j : Fin 10}
    (hjking : (u.tableau j).getLast? = some ⟨su, Rank.king⟩)
    {v : Nat} (hv1 : cvKingVal g p.pileDepth (suitToNat su) < v)
    (hv2 : v < 14 - (u.tableau j).length) :
    ∃ c : Fin 4, u.cells c = some (cardOf su v) := by
  have hv13 : v ≤ 13 := by omega
  have hv0 : 1 ≤ v := by omega
  have hA : cvAceVal g p.pileDepth (suitToNat su) < 13 := by
    by_contra hA13
    have h13 : cvKingVal g p.pileDepth (suitToNat su) = 13 := by
      unfold cvKingVal
      rw [if_pos (by have := cvAceVal_le_13 g p.pileDepth (suitToNat su); omega)]
    omega
  have hAK : cvAceVal g p.pileDepth (suitToNat su) ≤ cvKingVal g p.pileDepth (suitToNat su) :=
    cvAceVal_le_cvKingVal g p.pileDepth (suitToNat su)
  -- the card, and its code
  have hesuit : (cardOf su v).suit = su := rfl
  have herank : rankToNat (cardOf su v).rank = v := rankToNat_cardOf su hv0 hv13
  have hecode : encodeCard (cardOf su v) = CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat v) := by
    show CARD (UInt8.ofNat (suitToNat (cardOf su v).suit))
      (UInt8.ofNat (rankToNat (cardOf su v).rank)) = _
    rw [hesuit, herank]
  have hefree : isFreeCard g p (encodeCard (cardOf su v)) := by
    rw [isFreeCard_eq_freeAt, hecode]
    exact kingRun_card_free g p.pileDepth (suitToNat su) hv1 hv13 hA
  have heV : (VALUE (encodeCard (cardOf su v))).toNat = v := by
    rw [encodeCard_VALUE, herank]
  rcases NoDupState.location hcount (cardOf su v) with hf | hcell | ⟨q, hmem⟩
  · -- past the foundation
    exfalso
    unfold countFoundation at hf
    rw [if_pos (show optRankToNat (u.foundations (cardOf su v).suit)
        < rankToNat (cardOf su v).rank from by
      rw [hesuit, herank, hfnd su]; omega)] at hf
    exact absurd hf (by decide)
  · exact hcell
  · -- and in no column
    exfalso
    obtain ⟨idx, hidx, hval⟩ := List.getElem_of_mem hmem
    have hlenq : (u.tableau q).reverse.length = (u.tableau q).length := by simp
    have hrl : (u.tableau q).length - 1 - idx < (u.tableau q).reverse.length := by
      rw [hlenq]; omega
    have hrev : (u.tableau q).reverse[(u.tableau q).length - 1 - idx]'hrl = cardOf su v := by
      rw [reverse_getElem_col hidx hrl]
      exact hval
    by_cases hq0 : (p.pileDepth.get q).toNat = 0
    · -- a solver-empty column: its bottom card is this suit's king, so it *is* `j`
      obtain ⟨su', hrun⟩ := (hdm q).king_run (show (⟨_, hd6 q⟩ : Fin 6).val = 0 from hq0)
      obtain ⟨hsq, hvq⟩ := hrun ((u.tableau q).length - 1 - idx) hrl
      rw [hrev] at hsq hvq
      -- the bottom card
      have h0r : 0 < (u.tableau q).reverse.length := by rw [hlenq]; omega
      obtain ⟨hs0, hv0'⟩ := hrun 0 h0r
      have hbotking : (u.tableau q).reverse[0]'h0r = (⟨su, Rank.king⟩ : Card) := by
        refine Card.ext ?_ (rankInj _ _ ?_)
        · refine suitToNat_inj ?_
          have h1 := congrArg UInt8.toNat (hs0.trans hsq.symm)
          rw [encodeCard_SUIT, encodeCard_SUIT, UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h1
          have h2 := suitToNat_lt ((u.tableau q).reverse[0]'h0r).suit
          have h3 := suitToNat_lt (cardOf su v).suit
          have h4 : suitToNat (cardOf su v).suit = suitToNat su := by rw [hesuit]
          show suitToNat ((u.tableau q).reverse[0]'h0r).suit = suitToNat su
          omega
        · rw [← encodeCard_VALUE, hv0']
          rfl
      -- so `q = j`, and the run's values start above `v`
      have hmemq : ((u.tableau q).reverse[0]'h0r) ∈ u.tableau q :=
        List.mem_reverse.mp (List.getElem_mem ..)
      have hmemj : (⟨su, Rank.king⟩ : Card) ∈ u.tableau j := mem_of_getLast? hjking
      have hqj : q = j := column_eq_of_mem hcount (by rw [← hbotking]; exact hmemq) hmemj
      subst hqj
      -- but then `v` is one of the values the column already carries
      have : (u.tableau q).length - 1 - idx = 13 - v := by omega
      omega
    · -- a live boundary: it would be a higher card of the same suit, hence free
      have hidxlt : (p.pileDepth.get q).toNat - 1 < 5 := by have := hd6 q; omega
      have hge := free_reverse_index_ge hwf hd6 hdm q hrl (by rw [hrev]; exact hefree)
      obtain ⟨hsq, hvq⟩ := (hdm q).above_code
        (show 0 < (p.pileDepth.get q).toNat from by omega)
        (show (p.pileDepth.get q).toNat ≤ (u.tableau q).length - 1 - idx from hge) hrl
      rw [hrev] at hsq hvq
      set B := (g.pos2card.get q).get (⟨(p.pileDepth.get q).toNat - 1, hidxlt⟩ : Fin 5) with hBdef
      have hBreal : IsRealCard B := hwf.pos2card_real q _
      -- `B` is a higher card of the same suit
      have hBS := SUIT_toNat B
      have hBV := VALUE_toNat B
      have hsn := congrArg UInt8.toNat hsq
      rw [encodeCard_SUIT, UInt8.toNat_ofNat'] at hsn
      have hsu4 := suitToNat_lt su
      have hBcode : B = CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (VALUE B).toNat) := by
        apply UInt8.toNat_inj.mp
        rw [cv_card_toNat (by omega) (by have := hBreal.2.2; omega)]
        rw [hesuit] at hsn
        omega
      have hBfree : isFreeCard g p B := by
        rw [isFreeCard_eq_freeAt, hBcode]
        refine kingRun_card_free g p.pileDepth (suitToNat su) ?_ (by have := hBreal.2.2; omega) hA
        omega
      exact depth_card_not_free_wf hwf q ⟨(p.pileDepth.get q).toNat - 1, hidxlt⟩
        (show (p.pileDepth.get q).toNat - 1 < (p.pileDepth.get q).toNat from by omega) hBfree

/-! ## Completing one pile

The column carries a *prefix* of the freed run (`14 - |col| … 13`); it cannot reach below
`cvKingVal + 1`, since the card at `cvKingVal` is the one the walk found un-free.  So
`reach_pile_run` fetches the rest out of the cells, dropping onto a column that is never
empty — the king is already there — and the run ends at exactly `cvKingVal + 1`. -/

theorem exists_pile_kingRun {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (hfnd : ∀ su : Suit, optRankToNat (u.foundations su)
      = cvAceVal g p.pileDepth (suitToNat su))
    {su : Suit} {j : Fin 10} (hj0 : (p.pileDepth.get j).toNat = 0)
    (hjking : (u.tableau j).getLast? = some ⟨su, Rank.king⟩) :
    cvKingVal g p.pileDepth (suitToNat su) ≤ 12 ∧
    ∃ t : State, CPReach u t ∧
      t.tableau j = kingRun su (cvKingVal g p.pileDepth (suitToNat su) + 1) ∧
      (∀ q : Fin 10, q ≠ j → t.tableau q = u.tableau q) ∧
      t.foundations = u.foundations ∧
      (∀ (i : Fin 4) (x : Card), t.cells i = some x → u.cells i = some x) := by
  have hlen13 : (u.tableau j).length ≤ 13 := PileMatches.length_le_of_zero (hdm j) hj0
  have hne : u.tableau j ≠ [] := fun hc => by rw [hc] at hjking; simp at hjking
  have hlen1 : 1 ≤ (u.tableau j).length := by
    cases hcol : u.tableau j with
    | nil => exact absurd hcol hne
    | cons x xs => simp
  have hkingmem : (⟨su, Rank.king⟩ : Card) ∈ u.tableau j := mem_of_getLast? hjking
  -- the suit is not finished: otherwise its king would be covered *and* in a column
  have hA : cvAceVal g p.pileDepth (suitToNat su) < 13 := by
    have hle := cvAceVal_le_13 g p.pileDepth (suitToNat su)
    by_contra h13
    refine not_mem_column_of_covered hcount (c := ⟨su, Rank.king⟩) ?_ hkingmem
    show rankToNat Rank.king ≤ optRankToNat (u.foundations su)
    rw [hfnd su, show rankToNat Rank.king = 13 from rfl]
    omega
  -- the column is the top of the freed run
  have hcol : u.tableau j = kingRun su (14 - (u.tableau j).length) :=
    eq_kingRun_of_pileMatches (hdm j) hj0 hlen13
      (fun d hd => by rw [show d = (⟨su, Rank.king⟩ : Card) from
        Option.some.inj ((Option.mem_def.1 hd).symm.trans hjking)])
  -- and it stops above `cvKingVal`, since that card is not free
  have hstop : (u.tableau j).length + cvKingVal g p.pileDepth (suitToNat su) ≤ 13 := by
    by_contra hlt
    have hKV : cvKingVal g p.pileDepth (suitToNat su)
        = 13 - cvKingRun g p.pileDepth (suitToNat su) := by
      unfold cvKingVal
      rw [if_neg (by omega)]
    have hKR : cvKingRun g p.pileDepth (suitToNat su)
        = runLen (kingFree g p.pileDepth (suitToNat su)) 13 := rfl
    have hT : cvKingRun g p.pileDepth (suitToNat su) ≤ 12 :=
      cvKingRun_le g p.pileDepth (suitToNat su) hA
    -- the card at `cvKingVal` sits in the column, hence is free
    have hidx : 13 - cvKingVal g p.pileDepth (suitToNat su) < (u.tableau j).length := by omega
    have hmem : cardOf su (cvKingVal g p.pileDepth (suitToNat su)) ∈ u.tableau j := by
      rw [hcol]
      simp only [kingRun]
      refine List.mem_map.2 ⟨cvKingVal g p.pileDepth (suitToNat su)
        - (14 - (u.tableau j).length), List.mem_range.2 (by omega), ?_⟩
      show cardOf su (14 - (u.tableau j).length + (cvKingVal g p.pileDepth (suitToNat su)
        - (14 - (u.tableau j).length))) = _
      rw [show 14 - (u.tableau j).length + (cvKingVal g p.pileDepth (suitToNat su)
        - (14 - (u.tableau j).length)) = cvKingVal g p.pileDepth (suitToNat su) from by omega]
    obtain ⟨idx, hidx', hval⟩ := List.getElem_of_mem hmem
    have hlenq : (u.tableau j).reverse.length = (u.tableau j).length := by simp
    have hrl : (u.tableau j).length - 1 - idx < (u.tableau j).reverse.length := by
      rw [hlenq]; omega
    have hrev : (u.tableau j).reverse[(u.tableau j).length - 1 - idx]'hrl
        = cardOf su (cvKingVal g p.pileDepth (suitToNat su)) := by
      rw [reverse_getElem_col hidx' hrl]
      exact hval
    have hfree := free_of_index_ge hwf hd6 hdm hcount j
      (show (⟨(p.pileDepth.get j).toNat, hd6 j⟩ : Fin 6).val
        ≤ (u.tableau j).length - 1 - idx from by
        show (p.pileDepth.get j).toNat ≤ _
        omega) hrl hrev
    have hcvcode : encodeCard (cardOf su (cvKingVal g p.pileDepth (suitToNat su)))
        = CARD (UInt8.ofNat (suitToNat su))
          (UInt8.ofNat (cvKingVal g p.pileDepth (suitToNat su))) := by
      show CARD (UInt8.ofNat (suitToNat (cardOf su (cvKingVal g p.pileDepth (suitToNat su))).suit))
        (UInt8.ofNat (rankToNat (cardOf su (cvKingVal g p.pileDepth (suitToNat su))).rank)) = _
      rw [show (cardOf su (cvKingVal g p.pileDepth (suitToNat su))).suit = su from rfl,
        rankToNat_cardOf su (by omega) (by omega)]
    refine runLen_stop (kingFree g p.pileDepth (suitToNat su)) 13 (by omega) ?_
    show freeAt g p.pileDepth (CARD (UInt8.ofNat (suitToNat su))
      (UInt8.ofNat (13 - runLen (kingFree g p.pileDepth (suitToNat su)) 13)))
    rw [show 13 - runLen (kingFree g p.pileDepth (suitToNat su)) 13
        = cvKingVal g p.pileDepth (suitToNat su) from by omega, ← hcvcode,
      ← isFreeCard_eq_freeAt]
    exact hfree
  -- so the drops fetch exactly the cards below the column's run
  refine ⟨by omega, ?_⟩
  obtain ⟨t, -, -, htj, htq, htf, hcellsub, hcp⟩ :=
    reach_pile_run su (cvKingVal g p.pileDepth (suitToNat su))
      ((14 - (u.tableau j).length) - (cvKingVal g p.pileDepth (suitToNat su) + 1)) u j
      (by omega)
      (show u.tableau j = kingRun su (cvKingVal g p.pileDepth (suitToNat su) + 1
          + ((14 - (u.tableau j).length) - (cvKingVal g p.pileDepth (suitToNat su) + 1))) from by
        rw [show cvKingVal g p.pileDepth (suitToNat su) + 1
            + ((14 - (u.tableau j).length) - (cvKingVal g p.pileDepth (suitToNat su) + 1))
            = 14 - (u.tableau j).length from by omega]
        exact hcol)
      (fun m hm1 hm2 => kingRun_card_in_cell hwf hd6 hdm hcount hfnd hjking hm1 (by omega))
  refine ⟨t, hcp (by omega), htj, htq, htf, fun i x hx => ?_⟩
  rcases hcellsub i with h | h
  · rw [← h]; exact hx
  · rw [h] at hx; exact absurd hx (by simp)

/-! ## One suit, done

For a suit that has a king pile the pile gets completed; for a suit that has none there is
nothing to do — a solver-empty column's bottom card is *its own* suit's king, so no column
can claim this suit without carrying its king. -/

/-- What loop 2 owes a suit: every solver-empty column whose bottom card is that suit's king
has the length `kings[su] = cvKingVal` claims. -/
def KingPileDone (g : Globals) (u : State) (p : SolverPosType) (su : Suit) : Prop :=
  ∀ q : Fin 10, (p.pileDepth.get q).toNat = 0 → ∀ d ∈ (u.tableau q).getLast?, d.suit = su →
    (u.tableau q).length + cvKingVal g p.pileDepth (suitToNat su) = 13

/-- **The bottom card of a solver-empty column is its own suit's king.** -/
theorem getLast?_of_pileMatches_zero {g : Globals} {u : State} {p : SolverPosType}
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    {q : Fin 10} (hq0 : (p.pileDepth.get q).toNat = 0) {d : Card}
    (hd : (u.tableau q).getLast? = some d) : d.rank = Rank.king := by
  obtain ⟨su', hrun⟩ := (hdm q).king_run (show (⟨_, hd6 q⟩ : Fin 6).val = 0 from hq0)
  obtain ⟨hL, hdd⟩ := getLast?_getElem hd
  have h0r : 0 < (u.tableau q).reverse.length := by simp only [List.length_reverse]; omega
  obtain ⟨-, hv⟩ := hrun 0 h0r
  rw [reverse_getElem_zero hd h0r] at hv
  refine rankInj _ _ ?_
  rw [← encodeCard_VALUE, hv]
  rfl

theorem exists_suit_kingPile {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (hfnd : ∀ su : Suit, optRankToNat (u.foundations su)
      = cvAceVal g p.pileDepth (suitToNat su))
    (su : Suit) :
    ∃ t : State, CPReach u t ∧
      (∀ q : Fin 10, t.tableau q = u.tableau q ∨
        ((t.tableau q).getLast? = some ⟨su, Rank.king⟩ ∧
          (u.tableau q).getLast? = some ⟨su, Rank.king⟩)) ∧
      t.foundations = u.foundations ∧
      (∀ (i : Fin 4) (x : Card), t.cells i = some x → u.cells i = some x) ∧
      (∀ i : Fin 10, PileMatches g (t.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩) ∧
      KingPileDone g t p su := by
  classical
  by_cases hex : ∃ q : Fin 10, (p.pileDepth.get q).toNat = 0 ∧
      (u.tableau q).getLast? = some ⟨su, Rank.king⟩
  · -- the suit has a pile: complete it
    obtain ⟨j, hj0, hjking⟩ := hex
    obtain ⟨hKV12, t, hcp, htj, htq, htf, htcells⟩ :=
      exists_pile_kingRun hwf hd6 hdm hcount hfnd hj0 hjking
    have htjlast : (t.tableau j).getLast? = some ⟨su, Rank.king⟩ := by
      rw [htj, kingRun_getLast? su (by omega)]
      rfl
    have htjlen : (t.tableau j).length
        = 13 - cvKingVal g p.pileDepth (suitToNat su) := by
      rw [htj, kingRun_length]
      omega
    -- only `j` moved, and it still bottoms out at the king
    have hframe : ∀ q : Fin 10, t.tableau q = u.tableau q ∨
        ((t.tableau q).getLast? = some ⟨su, Rank.king⟩ ∧
          (u.tableau q).getLast? = some ⟨su, Rank.king⟩) := by
      intro q
      by_cases hqj : q = j
      · subst hqj; exact Or.inr ⟨htjlast, hjking⟩
      · exact Or.inl (htq q hqj)
    have hdmt : ∀ i : Fin 10,
        PileMatches g (t.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩ := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [htj]
        exact PileMatches_kingRun (show (⟨_, hd6 i⟩ : Fin 6).val = 0 from hj0) (by omega) (by omega)
      · rw [htq i hij]; exact hdm i
    refine ⟨t, hcp, hframe, htf, htcells, hdmt, ?_⟩
    intro q hq0 d hd hdsu
    by_cases hqj : q = j
    · subst hqj
      rw [htjlen]
      omega
    · -- another solver-empty column would carry a second copy of the king
      exfalso
      rw [htq q hqj] at hd
      have hdking : d.rank = Rank.king := getLast?_of_pileMatches_zero hd6 hdm hq0 hd
      have hdk : d = (⟨su, Rank.king⟩ : Card) := Card.ext hdsu hdking
      rw [hdk] at hd
      exact hqj (column_eq_of_mem hcount (mem_of_getLast? hd) (mem_of_getLast? hjking))
  · -- the suit has no pile: nothing to do, and no column can claim it
    refine ⟨u, Relation.ReflTransGen.refl, fun q => Or.inl rfl, rfl, fun _ _ h => h, hdm, ?_⟩
    intro q hq0 d hd hdsu
    refine absurd ⟨q, hq0, ?_⟩ hex
    rw [hd]
    exact congrArg some (Card.ext hdsu (getLast?_of_pileMatches_zero hd6 hdm hq0 hd))

/-! ## `CvPrologueSim`

Half A maximizes the foundations, half B completes the king piles, and
`matchesKingConfig_cvFluteOf` reads the match off the result — the flutes for free, the
`aces` clause from half A, `king_pile` from the four `KingPileDone`s.

The configuration is the same `k` throughout.  `no_pile` transports because a column's
bottom card only disappears with the column (`botFrame`), and `realizes` is re-established
rather than transported: a suit that still has a pile gets it *completed*, so the pile's
bottom is its king; and a suit that has none has `cvKingVal = 13` — its king is not in a
cell (`CvEntry.kingNotInCell`, and no move puts a card into a cell), so it is on a
foundation or still a resident — and the column the entry configuration reserved for it is
by then empty, which is `OwnsPile`'s other branch. -/

theorem KingPileDone.frame {g : Globals} {u t : State} {p : SolverPosType} {su su' : Suit}
    (h : KingPileDone g u p su) (hne : su' ≠ su)
    (hframe : ∀ q : Fin 10, t.tableau q = u.tableau q ∨
      ((t.tableau q).getLast? = some ⟨su', Rank.king⟩ ∧
        (u.tableau q).getLast? = some ⟨su', Rank.king⟩)) :
    KingPileDone g t p su := by
  intro q hq0 d hd hdsu
  rcases hframe q with heq | ⟨hlast, -⟩
  · rw [heq] at hd ⊢
    exact h q hq0 d hd hdsu
  · exfalso
    have hdk : d = (⟨su', Rank.king⟩ : Card) :=
      Option.some.inj ((Option.mem_def.1 hd).symm.trans hlast)
    rw [hdk] at hdsu
    exact hne hdsu

/-- The bottom-card frame of one `exists_suit_kingPile` step. -/
theorem botFrame_of_suitFrame {u t : State} {su : Suit}
    (hframe : ∀ q : Fin 10, t.tableau q = u.tableau q ∨
      ((t.tableau q).getLast? = some ⟨su, Rank.king⟩ ∧
        (u.tableau q).getLast? = some ⟨su, Rank.king⟩)) :
    ∀ q : Fin 10, (t.tableau q).getLast? = (u.tableau q).getLast? ∨ t.tableau q = [] := by
  intro q
  rcases hframe q with heq | ⟨h1, h2⟩
  · exact Or.inl (by rw [heq])
  · exact Or.inl (h1.trans h2.symm)

/-- **A king in a solver-empty column is at its bottom** — it is the only card of value
`13` the run can hold. -/
theorem getLast?_of_king_mem {g : Globals} {u : State} {p : SolverPosType}
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    {q : Fin 10} (hq0 : (p.pileDepth.get q).toNat = 0) {su : Suit}
    (hmem : (⟨su, Rank.king⟩ : Card) ∈ u.tableau q) :
    (u.tableau q).getLast? = some ⟨su, Rank.king⟩ := by
  obtain ⟨su', hrun⟩ := (hdm q).king_run (show (⟨_, hd6 q⟩ : Fin 6).val = 0 from hq0)
  obtain ⟨idx, hidx, hval⟩ := List.getElem_of_mem hmem
  have hlenq : (u.tableau q).reverse.length = (u.tableau q).length := by simp
  have hrl : (u.tableau q).length - 1 - idx < (u.tableau q).reverse.length := by
    rw [hlenq]; omega
  have hrev : (u.tableau q).reverse[(u.tableau q).length - 1 - idx]'hrl
      = (⟨su, Rank.king⟩ : Card) := by
    rw [reverse_getElem_col hidx hrl]
    exact hval
  obtain ⟨-, hv⟩ := hrun ((u.tableau q).length - 1 - idx) hrl
  rw [hrev] at hv
  have h13 : (13 : Nat) = 13 - ((u.tableau q).length - 1 - idx) := by
    rw [← hv, encodeCard_VALUE]
    rfl
  have h0r : 0 < (u.tableau q).reverse.length := by rw [hlenq]; omega
  obtain ⟨d, hd⟩ := exists_getLast?_of_pos (show 0 < (u.tableau q).length from by omega)
  rw [hd]
  refine congrArg some ?_
  rw [← reverse_getElem_zero hd h0r, ← hrev]
  congr 1
  omega

/-- **A suit with no king pile has `cvKingVal = 13`.**  Its king is not in a cell, so it is
on a foundation — and then the whole suit is, so `cvAceVal = 13` — or still a resident, and
then nothing of the suit is freed at all. -/
theorem cvKingVal_eq_13_of_no_pile {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (hfnd : ∀ su : Suit, optRankToNat (u.foundations su)
      = cvAceVal g p.pileDepth (suitToNat su))
    {su : Suit} (hnocell : ∀ i : Fin 4, u.cells i ≠ some ⟨su, Rank.king⟩)
    (hno : ¬ ∃ q : Fin 10, (p.pileDepth.get q).toNat = 0 ∧
      (u.tableau q).getLast? = some ⟨su, Rank.king⟩) :
    cvKingVal g p.pileDepth (suitToNat su) = 13 := by
  by_cases hA : cvAceVal g p.pileDepth (suitToNat su) = 13
  · unfold cvKingVal
    rw [if_pos hA]
  -- the king is not free, so the frontier never moves off it
  have hnf : ¬ isFreeCard g p (encodeCard (⟨su, Rank.king⟩ : Card)) := by
    intro hfree
    rcases NoDupState.location hcount (⟨su, Rank.king⟩ : Card) with hf | ⟨i, hcell⟩ | ⟨q, hmem⟩
    · -- on a foundation: then the whole suit is
      refine hA (le_antisymm (cvAceVal_le_13 g p.pileDepth (suitToNat su)) ?_)
      unfold countFoundation at hf
      by_cases hcov : optRankToNat (u.foundations (⟨su, Rank.king⟩ : Card).suit)
          < rankToNat (⟨su, Rank.king⟩ : Card).rank
      · rw [if_pos hcov] at hf; exact absurd hf (by decide)
      · have h1 : (13 : Nat) ≤ optRankToNat (u.foundations su) := by
          have hb1 : optRankToNat (u.foundations (⟨su, Rank.king⟩ : Card).suit)
              = optRankToNat (u.foundations su) := rfl
          have hb2 : rankToNat (⟨su, Rank.king⟩ : Card).rank = 13 := rfl
          omega
        rw [hfnd su] at h1
        exact h1
    · exact absurd hcell (hnocell i)
    · -- in a column: a solver-empty one would bottom out at it, a live one cannot hold it
      by_cases hq0 : (p.pileDepth.get q).toNat = 0
      · exact hno ⟨q, hq0, getLast?_of_king_mem hd6 hdm hq0 hmem⟩
      · obtain ⟨idx, hidx, hval⟩ := List.getElem_of_mem hmem
        have hlenq : (u.tableau q).reverse.length = (u.tableau q).length := by simp
        have hrl : (u.tableau q).length - 1 - idx < (u.tableau q).reverse.length := by
          rw [hlenq]; omega
        have hrev : (u.tableau q).reverse[(u.tableau q).length - 1 - idx]'hrl
            = (⟨su, Rank.king⟩ : Card) := by
          rw [reverse_getElem_col hidx hrl]
          exact hval
        have hge := free_reverse_index_ge hwf hd6 hdm q hrl (by rw [hrev]; exact hfree)
        obtain ⟨-, hv⟩ := (hdm q).above_code
          (show 0 < (p.pileDepth.get q).toNat from by omega)
          (show (p.pileDepth.get q).toNat ≤ (u.tableau q).length - 1 - idx from hge) hrl
        rw [hrev] at hv
        have hBreal : IsRealCard ((g.pos2card.get q).get
          ⟨(⟨(p.pileDepth.get q).toNat, hd6 q⟩ : Fin 6).val - 1, by have := hd6 q; omega⟩) :=
          hwf.pos2card_real q _
        have h13 : (VALUE (encodeCard (⟨su, Rank.king⟩ : Card))).toNat = 13 := by
          rw [encodeCard_VALUE]; rfl
        have := hBreal.2.2
        omega
  -- so `cvKingRun = 0`
  have hKR : cvKingRun g p.pileDepth (suitToNat su)
      = runLen (kingFree g p.pileDepth (suitToNat su)) 13 := rfl
  have hzero : cvKingRun g p.pileDepth (suitToNat su) = 0 := by
    by_contra hpos
    refine hnf ?_
    rw [isFreeCard_eq_freeAt]
    have hk0 := runLen_holds (kingFree g p.pileDepth (suitToNat su)) 13 0 (by omega)
    show freeAt g p.pileDepth (encodeCard (⟨su, Rank.king⟩ : Card))
    rw [show encodeCard (⟨su, Rank.king⟩ : Card)
        = CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (13 - 0)) from rfl]
    exact hk0
  unfold cvKingVal
  rw [if_neg hA, hzero]

/-! ## `CvPrologueSim`, assembled -/

set_option maxHeartbeats 1000000 in
/-- **Loop 2's writes are realized by normalizing moves.**  Half A plays the foundations up
to `cvAceVal`, half B completes each king pile to `13 - cvKingVal`, and the match is read
off the result: the flutes by `cvFluteOf`, `aces_match` from half A, `king_pile` from the
four `KingPileDone`s, and the configuration `k` unchanged. -/
theorem cvPrologueSim : CvPrologueSim := by
  intro g pk s game' k hwf hpk hentry
  classical
  have hpd : (convertPre g pk).pileDepth = cvDepths pk := rfl
  have hd6 : ∀ i : Fin 10, ((convertPre g pk).pileDepth.get i).toNat < 6 := by
    intro i
    have h := hpk i
    show ((cvDepths pk).get i).toNat < 6
    rw [cvDepths_get]
    exact Nat.lt_succ_of_le h
  have hcount : ∀ c : Card, countState s c = 1 := hentry.cfg.toMatches.cards_count
  have hdm : ∀ i : Fin 10, PileMatches g (s.tableau i) i
      ⟨((convertPre g pk).pileDepth.get i).toNat, hd6 i⟩ := by
    intro i
    refine PileMatches_of_val_eq (hentry.cfg.toMatches.depth_match i) ?_
    show ((convertPre g pk).pileDepth.get i).toNat = (game'.pileDepth.get i).toNat
    rw [hpd, hentry.depths]
  -- **half A**: the foundations, maximized
  obtain ⟨u1, hr1, hc1, hdm1, hx1, hb1, hf1⟩ :=
    exists_maximal_foundations hwf hd6 s hcount hdm
  -- **half B**: one suit at a time
  obtain ⟨v1, hcpA, hfrA, hfndA, hxA, hdmA, hkA⟩ :=
    exists_suit_kingPile hwf hd6 hdm1 hc1 hf1 Suit.clubs
  have hcA : ∀ c : Card, countState v1 c = 1 := hcpA.cards_count hc1
  have hfA : ∀ su : Suit, optRankToNat (v1.foundations su)
      = cvAceVal g (convertPre g pk).pileDepth (suitToNat su) := by
    intro su; rw [hfndA]; exact hf1 su
  obtain ⟨v2, hcpB, hfrB, hfndB, hxB, hdmB, hkB⟩ :=
    exists_suit_kingPile hwf hd6 hdmA hcA hfA Suit.diamonds
  have hcB : ∀ c : Card, countState v2 c = 1 := hcpB.cards_count hcA
  have hfB : ∀ su : Suit, optRankToNat (v2.foundations su)
      = cvAceVal g (convertPre g pk).pileDepth (suitToNat su) := by
    intro su; rw [hfndB]; exact hfA su
  obtain ⟨v3, hcpC, hfrC, hfndC, hxC, hdmC, hkC⟩ :=
    exists_suit_kingPile hwf hd6 hdmB hcB hfB Suit.hearts
  have hcC : ∀ c : Card, countState v3 c = 1 := hcpC.cards_count hcB
  have hfC : ∀ su : Suit, optRankToNat (v3.foundations su)
      = cvAceVal g (convertPre g pk).pileDepth (suitToNat su) := by
    intro su; rw [hfndC]; exact hfB su
  obtain ⟨v4, hcpD, hfrD, hfndD, hxD, hdmD, hkD⟩ :=
    exists_suit_kingPile hwf hd6 hdmC hcC hfC Suit.spades
  have hcD : ∀ c : Card, countState v4 c = 1 := hcpD.cards_count hcC
  have hfD : ∀ su : Suit, optRankToNat (v4.foundations su)
      = cvAceVal g (convertPre g pk).pileDepth (suitToNat su) := by
    intro su; rw [hfndD]; exact hfC su
  -- the four suits are all done at the end
  have hk4 : ∀ su : Suit, KingPileDone g v4 (convertPre g pk) su := by
    intro su
    cases su with
    | clubs =>
      exact ((hkA.frame (by decide) hfrB).frame (by decide) hfrC).frame (by decide) hfrD
    | diamonds => exact (hkB.frame (by decide) hfrC).frame (by decide) hfrD
    | hearts => exact hkC.frame (by decide) hfrD
    | spades => exact hkD
  -- the cells only ever lost cards, and column bottoms survived
  have hxs : ∀ (i : Fin 4) (x : Card), v4.cells i = some x → s.cells i = some x :=
    fun i x hx => hx1 i x (hxA i x (hxB i x (hxC i x (hxD i x hx))))
  have hbs : ∀ q : Fin 10, (v4.tableau q).getLast? = (s.tableau q).getLast? ∨ v4.tableau q = [] :=
    botFrame_trans hb1 (botFrame_trans (botFrame_of_suitFrame hfrA)
      (botFrame_trans (botFrame_of_suitFrame hfrB)
        (botFrame_trans (botFrame_of_suitFrame hfrC) (botFrame_of_suitFrame hfrD))))
  -- `no_pile` transports along that frame
  have hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile v4 (convertPre g pk) su := by
    intro su hsu q hq0 d hd
    rcases hbs q with heq | hnil
    · refine hentry.cfg.no_pile su hsu q ?_ d ?_
      · show (game'.pileDepth.get q).toNat = 0
        rw [hentry.depths, ← hpd]
        exact hq0
      · rw [Option.mem_def, ← heq]
        exact hd
    · rw [hnil] at hd
      simp at hd
  refine ⟨v4, ?_, ?_⟩
  · -- the whole phase is normalizing
    refine (hr1.mono (fun _ _ x => Or.inl x)).trans ?_
    exact (hcpA.toNormReach.trans hcpB.toNormReach).trans
      (hcpC.toNormReach.trans hcpD.toNormReach)
  · -- and the result matches `convertPre` at its own flutes
    refine matchesKingConfig_cvFluteOf hcD hd6 hdmD ?_ ?_ ?_ hnp
    · -- `king_pile`: the completed runs have exactly the length `kings` claims
      intro q hq0 c hc
      have hval : (VALUE ((convertPre g pk).kings.get (finOfSuit c.suit))).toNat
          = cvKingVal g (convertPre g pk).pileDepth (suitToNat c.suit) := by
        rw [convertPre_kings]
        show (VALUE (CARD (UInt8.ofNat (suitToNat c.suit))
          (UInt8.ofNat (cvKingVal g (cvDepths pk) (suitToNat c.suit))))).toNat = _
        have hKV13 : cvKingVal g (cvDepths pk) (suitToNat c.suit) ≤ 13 := by
          unfold cvKingVal; split <;> omega
        rw [cv_card_value (suitToNat_lt c.suit) (by omega), UInt8.toNat_ofNat']
        have hbr : cvKingVal g (convertPre g pk).pileDepth (suitToNat c.suit)
            = cvKingVal g (cvDepths pk) (suitToNat c.suit) := rfl
        rw [hbr]
        omega
      rw [hval]
      exact hk4 c.suit q hq0 c hc rfl
    · -- `aces_match`
      intro su
      rw [convertPre_aces]
      show CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (cvAceVal g (cvDepths pk)
        (suitToNat su))) = CARD (UInt8.ofNat (suitToNat su))
          (UInt8.ofNat (optRankToNat (v4.foundations su)))
      rw [hfD su]
      rfl
    · -- `realizes`: a suit with a pile owns it; one without has an empty column reserved
      obtain ⟨assign, hown, hinj, hiff⟩ := hentry.cfg.realizes
      -- a suit whose king is nowhere to be piled: its reserved column is empty by now, and
      -- its frontier is the king itself
      have hnilcase : ∀ (su : Suit) (i : Fin 10),
          (¬ ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
            (v4.tableau q).getLast? = some ⟨su, Rank.king⟩) →
          assign su = some i →
          ((convertPre g pk).pileDepth.get i).toNat = 0 ∧ v4.tableau i = [] ∧
            (VALUE ((convertPre g pk).kings.get (finOfSuit su))).toNat = 13 := by
        intro su i hex hsi
        obtain ⟨hq0e, hphys⟩ := hown su i hsi
        have hq0 : ((convertPre g pk).pileDepth.get i).toNat = 0 := by
          show ((cvDepths pk).get i).toNat = 0
          rw [← hentry.depths]
          exact hq0e
        have hnil : v4.tableau i = [] := by
          rcases hbs i with heq | hnil
          · rcases hphys with ⟨d, hd, hdsu, hdking⟩ | ⟨hsnil, -⟩
            · refine absurd ⟨i, hq0, ?_⟩ hex
              have hdeq : d = ⟨su, Rank.king⟩ := by
                cases d; simp_all
              rw [heq, Option.mem_def.1 hd, hdeq]
            · rw [hsnil] at heq
              simp only [List.getLast?_nil] at heq
              exact List.getLast?_eq_none_iff.1 heq
          · exact hnil
        refine ⟨hq0, hnil, ?_⟩
        have hnocell : ∀ j : Fin 4, v4.cells j ≠ some ⟨su, Rank.king⟩ := by
          intro j hj
          exact hentry.kingNotInCell su ((hiff su).1 (by rw [hsi]; rfl)) j (hxs j _ hj)
        have h13 := cvKingVal_eq_13_of_no_pile hwf hd6 hdmD hcD hfD hnocell hex
        rw [convertPre_kings]
        show (VALUE (CARD (UInt8.ofNat (suitToNat su))
          (UInt8.ofNat (cvKingVal g (cvDepths pk) (suitToNat su))))).toNat = 13
        have hKV13 : cvKingVal g (cvDepths pk) (suitToNat su) = 13 := h13
        rw [cv_card_value (suitToNat_lt su) (by omega), UInt8.toNat_ofNat', hKV13]
      refine ⟨fun su => if h : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
          (v4.tableau q).getLast? = some ⟨su, Rank.king⟩ then some h.choose else assign su,
        ?_, ?_, ?_⟩
      · -- the assignment owns its column
        intro su i hsi
        dsimp only at hsi
        by_cases hex : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
            (v4.tableau q).getLast? = some ⟨su, Rank.king⟩
        · rw [dif_pos hex] at hsi
          obtain ⟨hq0, hqlast⟩ := hex.choose_spec
          rw [show hex.choose = i from Option.some.inj hsi] at hq0 hqlast
          exact ⟨hq0, Or.inl ⟨⟨su, Rank.king⟩, hqlast, rfl, rfl⟩⟩
        · rw [dif_neg hex] at hsi
          obtain ⟨hq0, hnil, h13⟩ := hnilcase su i hex hsi
          exact ⟨hq0, Or.inr ⟨hnil, h13⟩⟩
      · -- and it is injective
        intro su su' i hsi hsi'
        dsimp only at hsi hsi'
        by_cases hex : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
            (v4.tableau q).getLast? = some ⟨su, Rank.king⟩
        · by_cases hex' : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
              (v4.tableau q).getLast? = some ⟨su', Rank.king⟩
          · rw [dif_pos hex] at hsi
            rw [dif_pos hex'] at hsi'
            obtain ⟨-, h1⟩ := hex.choose_spec
            obtain ⟨-, h2⟩ := hex'.choose_spec
            rw [show hex.choose = i from Option.some.inj hsi] at h1
            rw [show hex'.choose = i from Option.some.inj hsi'] at h2
            have hcards : (⟨su, Rank.king⟩ : Card) = ⟨su', Rank.king⟩ :=
              Option.some.inj (h1.symm.trans h2)
            exact congrArg Card.suit hcards
          · exfalso
            rw [dif_pos hex] at hsi
            rw [dif_neg hex'] at hsi'
            obtain ⟨-, hnil, -⟩ := hnilcase su' i hex' hsi'
            obtain ⟨-, h1⟩ := hex.choose_spec
            rw [show hex.choose = i from Option.some.inj hsi, hnil] at h1
            simp at h1
        · by_cases hex' : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
              (v4.tableau q).getLast? = some ⟨su', Rank.king⟩
          · exfalso
            rw [dif_neg hex] at hsi
            rw [dif_pos hex'] at hsi'
            obtain ⟨-, hnil, -⟩ := hnilcase su i hex hsi
            obtain ⟨-, h2⟩ := hex'.choose_spec
            rw [show hex'.choose = i from Option.some.inj hsi', hnil] at h2
            simp at h2
          · rw [dif_neg hex] at hsi
            rw [dif_neg hex'] at hsi'
            exact hinj su su' i hsi hsi'
      · -- and it is defined exactly on the suits the configuration piles
        intro su
        dsimp only
        by_cases hex : ∃ q : Fin 10, ((convertPre g pk).pileDepth.get q).toNat = 0 ∧
            (v4.tableau q).getLast? = some ⟨su, Rank.king⟩
        · rw [dif_pos hex]
          simp only [Option.isSome_some, true_iff]
          obtain ⟨q, hq0, hqlast⟩ := hex
          intro hbit
          exact hnp su hbit q hq0 ⟨su, Rank.king⟩ hqlast rfl
        · rw [dif_neg hex]
          exact hiff su

end SolverSpec
