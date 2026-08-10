import Seahaven.CPNormal
import Seahaven.CleanupSim

/-!
# The depth vector determines the match

For a *merged* position, `StateMatchesSolverPos` carries no more information than
the depth vector (plus `aces`, which the invariant does not pin while
`busyAces ≠ 0`).  Concretely: given

* the depths agree — `PileMatches g (u.tableau i) i (pileDepth i)` for every pile,
  which is `StateMatchesSolverPos`' own `depth_match` field and is all that the
  Rules-side move analysis has to establish;
* the state is **CP-normal** — no card in a cell can be dropped on a pile;
* the position is merged (`SolverInvBase` + `PileMerged`);
* `aces` matches the foundations,

the two remaining fields of the match — `flute_match` (how long each column
physically is) and `king_pile` (how tall each king stack is) — are *forced*.

The depths alone do not force them: a flute may have any number of its cards
parked in cells.  CP-normality is what closes the gap, and it does so against
the merged invariant in both directions:

* a column cannot reach *past* `boundary - pileFlute`, because that card is not
  free (`flute_maximal`) while everything above a boundary is free;
* it cannot stop *short*, because the next card of the run is free
  (`flute_cards_free`), is above its foundation (`flute_not_aces`), and cannot be
  on another column (a free card's successor sits directly beneath it, and here
  the successor is a column *top*) — so it would be in a cell with its
  destination exposed, i.e. a `CPStep`.

`king_pile` is the same argument with `king_frontier` in place of
`flute_maximal`/`flute_cards_free`.

Together with `CPNormal.no_cpStep` (match + merged ⟹ CP-normal) this makes the
depth vector a complete invariant of merged positions, which is what lets the
completeness argument reason about a move by its effect on the depths alone.
-/

/-! ## Card-code helpers -/

theorem suitToNat_eq_of_SUIT {c d : Card} (h : SUIT (encodeCard c) = SUIT (encodeCard d)) :
    suitToNat c.suit = suitToNat d.suit := by
  have h1 := suitToNat_lt c.suit
  have h2 := suitToNat_lt d.suit
  have h3 := congrArg UInt8.toNat h
  rw [encodeCard_SUIT, encodeCard_SUIT, UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h3
  omega

/-- Same suit, one rank higher: the code goes up by one. -/
theorem encodeCard_succ {c d : Card} (hs : suitToNat c.suit = suitToNat d.suit)
    (hv : rankToNat c.rank = rankToNat d.rank + 1) : encodeCard c = encodeCard d + 1 := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, encodeCard_toNat, encodeCard_toNat, uint8_toNat_one]
  have h1 := suitToNat_lt d.suit
  have h2 := rankBounded c.rank
  have h3 := rankBounded d.rank
  omega

/-! ## Reading a column through `PileMatches` -/

/-- Below the depth, the column holds the dealt cards. -/
theorem PileMatches.resident_code {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) {k : Nat} (hk : k < n.val) (hkl : k < col.reverse.length) :
    encodeCard (col.reverse[k]'hkl)
      = (g.pos2card.get a).get ⟨k, by have := n.isLt; omega⟩ := by
  have h2 := h.2.1 ⟨k, hk⟩
  rw [List.getElem?_eq_getElem hkl, Option.map_some] at h2
  exact Option.some.inj h2

/-- At or above the boundary, the column continues the boundary's run downwards
    in value. -/
theorem PileMatches.above_code {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) (hn : 0 < n.val) {r : Nat} (hr : n.val ≤ r)
    (hrl : r < col.reverse.length) :
    SUIT (encodeCard (col.reverse[r]'hrl))
        = SUIT ((g.pos2card.get a).get ⟨n.val - 1, by have := n.isLt; omega⟩) ∧
      (VALUE (encodeCard (col.reverse[r]'hrl))).toNat
        = (VALUE ((g.pos2card.get a).get ⟨n.val - 1, by have := n.isLt; omega⟩)).toNat
            - 1 - (r - n.val) := by
  obtain ⟨h1, -, h3⟩ := h
  simp only [] at h3
  rw [dif_pos hn] at h3
  have hjlt : r - n.val < ((col.reverse.drop n.val).map encodeCard).length := by
    simp only [List.length_map, List.length_drop]
    omega
  obtain ⟨hs, hv⟩ := h3 ⟨r - n.val, hjlt⟩
  have helem : ((col.reverse.drop n.val).map encodeCard)[r - n.val]'hjlt
      = encodeCard (col.reverse[r]'hrl) := by
    rw [List.getElem_map]
    congr 1
    rw [List.getElem_drop]
    congr 1
    omega
  rw [List.get_eq_getElem, helem] at hs hv
  exact ⟨hs, hv⟩

/-- A solver-empty column is one suit's king run. -/
theorem PileMatches.king_run {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) (hn : n.val = 0) :
    ∃ su : UInt8, ∀ (r : Nat) (hrl : r < col.reverse.length),
      SUIT (encodeCard (col.reverse[r]'hrl)) = su ∧
      (VALUE (encodeCard (col.reverse[r]'hrl))).toNat = 13 - r := by
  obtain ⟨h1, -, h3⟩ := h
  simp only [] at h3
  rw [dif_neg (by omega)] at h3
  obtain ⟨su, hrun⟩ := h3
  refine ⟨su, fun r hrl => ?_⟩
  have hjlt : r < ((col.reverse.drop n.val).map encodeCard).length := by
    simp only [List.length_map, List.length_drop]
    omega
  obtain ⟨hs, hv⟩ := hrun ⟨r, hjlt⟩
  have helem : ((col.reverse.drop n.val).map encodeCard)[r]'hjlt
      = encodeCard (col.reverse[r]'hrl) := by
    rw [List.getElem_map]
    congr 1
    rw [List.getElem_drop]
    congr 1
    omega
  rw [List.get_eq_getElem, helem] at hs hv
  exact ⟨hs, by omega⟩

/-- **Directly beneath a non-resident card sits its successor.**  True in both
    branches: within a flute the values climb by one towards the boundary, and the
    card just below the flute *is* the boundary; on a king pile the whole column
    is one run. -/
theorem PileMatches.succ_below {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (hwf : WellFormedLayout g) (h : PileMatches g col a n)
    {r : Nat} (hr : n.val ≤ r) (hr0 : 0 < r) (hrl : r < col.reverse.length)
    (hr1 : r - 1 < col.reverse.length) :
    encodeCard (col.reverse[r - 1]'hr1) = encodeCard (col.reverse[r]'hrl) + 1 := by
  have hlen : col.reverse.length = col.length := by simp
  have hposr := rankToNat_pos (col.reverse[r]'hrl).rank
  have hposr1 := rankToNat_pos (col.reverse[r - 1]'hr1).rank
  have hVr := encodeCard_VALUE (col.reverse[r]'hrl)
  have hVr1 := encodeCard_VALUE (col.reverse[r - 1]'hr1)
  by_cases hn0 : n.val = 0
  · obtain ⟨su, hrun⟩ := h.king_run hn0
    obtain ⟨hs1, hv1⟩ := hrun (r - 1) hr1
    obtain ⟨hs2, hv2⟩ := hrun r hrl
    exact encodeCard_succ (suitToNat_eq_of_SUIT (by rw [hs1, hs2])) (by omega)
  · have hnpos : 0 < n.val := by omega
    have hB : IsRealCard ((g.pos2card.get a).get ⟨n.val - 1, by have := n.isLt; omega⟩) :=
      hwf.pos2card_real a _
    obtain ⟨hs2, hv2⟩ := h.above_code hnpos hr hrl
    by_cases hbnd : r - 1 < n.val
    · -- the card below is the boundary itself
      have hrn : r = n.val := by omega
      have hidx : (⟨r - 1, by have := n.isLt; omega⟩ : Fin 5)
          = ⟨n.val - 1, by have := n.isLt; omega⟩ :=
        Fin.ext (by show r - 1 = n.val - 1; omega)
      have hcode : encodeCard (col.reverse[r - 1]'hr1)
          = (g.pos2card.get a).get ⟨n.val - 1, by have := n.isLt; omega⟩ := by
        rw [← hidx]; exact h.resident_code (by omega) hr1
      have hb1 := hB.2.1
      refine encodeCard_succ (suitToNat_eq_of_SUIT (by rw [hs2, ← hcode])) ?_
      have hVB : (VALUE (encodeCard (col.reverse[r - 1]'hr1))).toNat
          = (VALUE ((g.pos2card.get a).get ⟨n.val - 1,
              by have := n.isLt; omega⟩)).toNat := by rw [hcode]
      omega
    · obtain ⟨hs1, hv1⟩ := h.above_code hnpos (by omega) hr1
      exact encodeCard_succ (suitToNat_eq_of_SUIT (by rw [hs1, hs2])) (by omega)

/-! ## Which cards in a column are free

`isFreeCard` reads only `p.pileDepth`, so with the depths agreeing it splits a
column exactly at the boundary. -/

/-- A card resident below the depth is not free. -/
theorem not_free_of_index_lt {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (i : Fin 10) {r : Nat} (hr : r < (p.pileDepth.get i).toNat)
    (hrl : r < (u.tableau i).reverse.length) :
    ¬ isFreeCard g p (encodeCard ((u.tableau i).reverse[r]'hrl)) := by
  rw [(hdm i).resident_code hr hrl]
  exact depth_card_not_free hwf hb i ⟨r, by have := hd6 i; omega⟩ hr

/-- **A card at or above the boundary is free.**  Otherwise it would also be
    sitting at its own dealt slot, i.e. twice in the state. -/
theorem free_of_index_ge {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (i : Fin 10) {r : Nat} {d : Card} (hr : (p.pileDepth.get i).toNat ≤ r)
    (hrl : r < (u.tableau i).reverse.length) (hd : (u.tableau i).reverse[r]'hrl = d) :
    isFreeCard g p (encodeCard d) := by
  have hnd : NoDupState u := fun c => le_of_eq (hcount c)
  by_contra hnf
  have hreal : IsRealCard (encodeCard d) := encodeCard_real d
  have hc64 : (encodeCard d).toNat < 64 := IsRealCard_lt64 hreal
  have hp10 : (cardPile g (encodeCard d)).toNat < 10 := hwf.pile_lt _ hreal
  set P : Fin 10 := ⟨(cardPile g (encodeCard d)).toNat, hp10⟩ with hPdef
  have hlt : (cardDepth g (encodeCard d)).toNat < (p.pileDepth.get P).toNat := by
    by_contra hge
    refine hnf (SolverSpec.isFree_of_cardDepth_ge g p hwf _ hc64 hp10 ?_)
    show (cardDepth g (encodeCard d)).toNat ≥ (p.pileDepth.get P).toNat
    omega
  have hd5 : (cardDepth g (encodeCard d)).toNat < 5 := by have := hd6 P; omega
  have hnL : (p.pileDepth.get P).toNat ≤ (u.tableau P).length := (hdm P).1
  have hrevP : (cardDepth g (encodeCard d)).toNat < (u.tableau P).reverse.length := by
    simp only [List.length_reverse]; omega
  have hcode := (hdm P).resident_code hlt hrevP
  have hround := hwf.round_trip (encodeCard d) hreal hd5
  have hdP : (u.tableau P).reverse[(cardDepth g (encodeCard d)).toNat]'hrevP = d := by
    refine encodeCard_inj ?_
    rw [hcode]
    exact hround
  by_cases hPi : P = i
  · -- the same column, at two different indices
    subst hPi
    have hnodup : (u.tableau P).reverse.Nodup := List.nodup_reverse.mpr (hnd.column_nodup P)
    have := hnodup.getElem_inj_iff.1 (hdP.trans hd.symm)
    omega
  · exact hPi (hnd.pile_unique (c := d)
      (by rw [← hdP]; exact List.mem_reverse.mp (List.getElem_mem ..))
      (by rw [← hd]; exact List.mem_reverse.mp (List.getElem_mem ..)))

/-! ## The key consequence of CP-normality -/

/-- **In a CP-normal state, a free uncovered card never has its successor
    exposed.**  It is not on a foundation by assumption; it cannot be in a cell,
    since dropping it on the exposed successor is a `CPStep`; and it cannot be in a
    column, since there its own successor sits directly beneath it
    (`succ_below`) and therefore is not a column top. -/
theorem no_free_succ_exposed {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) {i : Fin 10} (hcp : ∀ t, ¬ CPStepOn i u t)
    {x e : Card} (hfree : isFreeCard g p (encodeCard x))
    (huncov : countFoundation u.foundations x ≠ 1)
    (hhe : (u.tableau i).head? = some e) (hsucc : nextCard x = some e) : False := by
  have hnd : NoDupState u := fun c => le_of_eq (hcount c)
  -- the exposed card, as a reverse index
  have hne : u.tableau i ≠ [] := by intro h0; rw [h0] at hhe; simp at hhe
  have hlt : 0 < (u.tableau i).length := by
    cases hcol : u.tableau i with
    | nil => exact absurd hcol hne
    | cons y ys => simp
  have hE0 : (u.tableau i)[0]'hlt = e := by
    have h1 : (u.tableau i).head? = (u.tableau i)[0]? := List.head?_eq_getElem?
    rw [hhe, List.getElem?_eq_getElem hlt] at h1
    exact (Option.some.inj h1).symm
  have hrevi : (u.tableau i).length - 1 < (u.tableau i).reverse.length := by
    simp only [List.length_reverse]; omega
  have hEtop : (u.tableau i).reverse[(u.tableau i).length - 1]'hrevi = e := by
    rw [List.getElem_reverse hrevi, ← hE0]
    congr 1
    omega
  rcases NoDupState.location hcount x with hf | ⟨j, hcell⟩ | ⟨j, hmem⟩
  · exact huncov hf
  · -- in a cell: the drop is a `CPStep`
    refine hcp (updateColumn (updateCell u j none) i (x :: (updateCell u j none).tableau i))
      ⟨j, hne, ?_⟩
    rw [applyMove_eq]
    refine ⟨x, updateCell u j none, ?_, ?_⟩
    · rw [takeFromPosition, takeFromCell_eq]
      exact ⟨hcell, rfl⟩
    · rw [dropPosition, dropCol_eq]
      refine ⟨?_, rfl⟩
      rw [updateCell_tableau, hhe, hsucc]
  · -- in a column: `x`'s successor is buried under `x`
    obtain ⟨r, hrl, hrx⟩ := List.getElem_of_mem (List.mem_reverse.mpr hmem)
    have hge : (p.pileDepth.get j).toNat ≤ r := by
      by_contra hlt'
      exact not_free_of_index_lt hwf hb hd6 hdm j (by omega) hrl (by rw [hrx]; exact hfree)
    have hrjl : r < (u.tableau j).length := by
      simp only [List.length_reverse] at hrl; exact hrl
    by_cases hr0 : r = 0
    · -- `x` is the deepest card of a king pile, so it is a king
      have hd0 : (p.pileDepth.get j).toNat = 0 := by omega
      obtain ⟨su, hrun⟩ := (hdm j).king_run hd0
      obtain ⟨-, hv⟩ := hrun r hrl
      rw [hrx, encodeCard_VALUE] at hv
      have h13 := rankBounded e.rank
      have := nextCard_rank hsucc
      omega
    · have hr1 : r - 1 < (u.tableau j).reverse.length := by omega
      have hbelow := (hdm j).succ_below hwf hge (by omega) hrl hr1
      rw [hrx] at hbelow
      have hecode : encodeCard e = encodeCard x + 1 :=
        encodeCard_succ (by rw [nextCard_suit hsucc]) (nextCard_rank hsucc)
      have heq : (u.tableau j).reverse[r - 1]'hr1 = e :=
        encodeCard_inj (by rw [hbelow, hecode])
      by_cases hji : j = i
      · subst hji
        have hnodup : (u.tableau j).reverse.Nodup := List.nodup_reverse.mpr (hnd.column_nodup j)
        have := hnodup.getElem_inj_iff.1 (heq.trans hEtop.symm)
        omega
      · exact hji (hnd.pile_unique (c := e)
          (by rw [← heq]; exact List.mem_reverse.mp (List.getElem_mem ..))
          (by rw [← hEtop]; exact List.mem_reverse.mp (List.getElem_mem ..)))

/-! ## Small bridges -/

/-- The head of a column, as its last reversed index. -/
theorem head?_reverse_last {col : Column} (hne : 0 < col.length)
    (hrl : col.length - 1 < col.reverse.length) :
    col.head? = some (col.reverse[col.length - 1]'hrl) := by
  have h0 : (col[0]'hne) = col.reverse[col.length - 1]'hrl := by
    rw [List.getElem_reverse hrl]
    congr 1
    omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hne, h0]

/-- `aces` is below any card its foundation has not reached. -/
theorem aces_lt_of_foundation_lt {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    {d : Card} (h : optRankToNat (u.foundations d.suit) < rankToNat d.rank) :
    p.aces.get (finOfSuit d.suit) < encodeCard d := by
  have hsu := suitToNat_lt d.suit
  have hf13 := optRankToNat_le (u.foundations d.suit)
  rw [UInt8.lt_iff_toNat_lt, haces d.suit, encodeFoundation,
    CARD_toNat (by omega) (by omega), encodeCard_toNat]
  omega

/-- Conversely, a card above `aces` is not on its foundation. -/
theorem uncovered_of_aces_lt {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    {d : Card} (h : p.aces.get (finOfSuit d.suit) < encodeCard d) :
    countFoundation u.foundations d ≠ 1 := by
  have hsu := suitToNat_lt d.suit
  have hf13 := optRankToNat_le (u.foundations d.suit)
  rw [UInt8.lt_iff_toNat_lt, haces d.suit, encodeFoundation,
    CARD_toNat (by omega) (by omega), encodeCard_toNat] at h
  unfold countFoundation
  rw [if_pos (by omega)]
  omega

/-- A card sitting in a column is above its foundation. -/
theorem aces_lt_of_mem_column {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hcount : ∀ c : Card, countState u c = 1) {d : Card} {j : Fin 10} (hmem : d ∈ u.tableau j) :
    p.aces.get (finOfSuit d.suit) < encodeCard d :=
  aces_lt_of_foundation_lt haces
    (NoDupState.foundation_lt_of_mem_column (fun c => le_of_eq (hcount c)) hmem)

/-! ## `flute_match` is forced -/

/-- **The physical run never exceeds the recorded flute.**  A card above the
boundary is free (`free_of_index_ge`) and, sitting in a column, is not on its
foundation — while `flute_maximal` says `boundary - pileFlute` is one or the other.
So the column cannot reach that far.  Note this half needs *no* CP-normality: it is
the `flute_le` field of `DepthPlusKings`, valid at every parked state. -/
theorem flute_le_of_depth {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (i : Fin 10) (hpm : PileMerged g p i (hb.pileDepth_bound i))
    (hdpos : 0 < (p.pileDepth.get i).toNat) :
    (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat := by
  have hnL : (p.pileDepth.get i).toNat ≤ (u.tableau i).length := (hdm i).1
  have hnval : (⟨(p.pileDepth.get i).toNat, hd6 i⟩ : Fin 6).val
      = (p.pileDepth.get i).toNat := rfl
  have hidx5 : (p.pileDepth.get i).toNat - 1 < 5 := by have := hd6 i; omega
  set B := (g.pos2card.get i).get (⟨(p.pileDepth.get i).toNat - 1, hidx5⟩ : Fin 5) with hBdef
  have hBreal : IsRealCard B := hwf.pos2card_real i _
  have hB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hSB := SUIT_toNat B
  have hVB := VALUE_toNat B
  have hfpos : 1 ≤ (p.pileFlute.get i).toNat := hb.flute_pos i
  have hfle : (p.pileFlute.get i).toNat ≤ (VALUE B).toNat := by
    have := (hb.pileBase i).flute_le_value hwf (fun s => (hb.aces_kings_valid s).1) hdpos
    rw [← hBdef] at this
    exact this
  have hs4 : (SUIT B).toNat < 4 := hBreal.1
  -- the column cannot reach past `B - pileFlute`
  have hlt : (u.tableau i).length - (p.pileDepth.get i).toNat < (p.pileFlute.get i).toNat := by
    by_contra hge
    have hrl : (p.pileDepth.get i).toNat + ((p.pileFlute.get i).toNat - 1)
        < (u.tableau i).reverse.length := by
      simp only [List.length_reverse]; omega
    obtain ⟨hs, hv⟩ := (hdm i).above_code hdpos
      (r := (p.pileDepth.get i).toNat + ((p.pileFlute.get i).toNat - 1))
      (Nat.le_add_right _ _) hrl
    rw [← hBdef] at hs hv
    have hyfree := free_of_index_ge hwf hd6 hdm hcount i (by omega) hrl rfl
    have hSy := SUIT_toNat (encodeCard ((u.tableau i).reverse[(p.pileDepth.get i).toNat
      + ((p.pileFlute.get i).toNat - 1)]'hrl))
    have hVy := VALUE_toNat (encodeCard ((u.tableau i).reverse[(p.pileDepth.get i).toNat
      + ((p.pileFlute.get i).toNat - 1)]'hrl))
    have hsn := congrArg UInt8.toNat hs
    have hle : p.pileFlute.get i ≤ B := by rw [UInt8.le_iff_toNat_le]; omega
    have hycode : encodeCard ((u.tableau i).reverse[(p.pileDepth.get i).toNat
        + ((p.pileFlute.get i).toNat - 1)]'hrl) = B - p.pileFlute.get i := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_sub_of_le _ _ hle]
      omega
    rcases hpm.flute_maximal with hz | hmax
    · rw [hz] at hdpos; simp at hdpos
    · dsimp only at hmax
      rw [← hBdef] at hmax
      rcases hmax with ⟨hs4', hacesEq⟩ | hnf
      · -- `aces` would be a card sitting in the column
        have hmem : (u.tableau i).reverse[(p.pileDepth.get i).toNat
            + ((p.pileFlute.get i).toNat - 1)]'hrl ∈ u.tableau i :=
          List.mem_reverse.mp (List.getElem_mem ..)
        have hlt' := aces_lt_of_mem_column haces hcount hmem
        have hfin : (⟨(SUIT B).toNat, hs4'⟩ : Fin 4)
            = finOfSuit ((u.tableau i).reverse[(p.pileDepth.get i).toNat
              + ((p.pileFlute.get i).toNat - 1)]'hrl).suit := by
          refine Fin.ext ?_
          show (SUIT B).toNat = suitToNat _
          have := encodeCard_SUIT ((u.tableau i).reverse[(p.pileDepth.get i).toNat
            + ((p.pileFlute.get i).toNat - 1)]'hrl)
          rw [this, UInt8.toNat_ofNat'] at hsn
          have := suitToNat_lt ((u.tableau i).reverse[(p.pileDepth.get i).toNat
            + ((p.pileFlute.get i).toNat - 1)]'hrl).suit
          omega
        rw [hfin, ← hycode] at hacesEq
        rw [hacesEq, UInt8.lt_iff_toNat_lt] at hlt'
        omega
      · exact hnf (hycode ▸ hyfree)
  omega

theorem flute_match_of_depth {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (i : Fin 10) (hpm : PileMerged g p i (hb.pileDepth_bound i))
    (hcp : ∀ t, ¬ CPStepOn i u t) (hdpos : 0 < (p.pileDepth.get i).toNat) :
    (u.tableau i).length + 1 = (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat := by
  have hnL : (p.pileDepth.get i).toNat ≤ (u.tableau i).length := (hdm i).1
  have hnval : (⟨(p.pileDepth.get i).toNat, hd6 i⟩ : Fin 6).val
      = (p.pileDepth.get i).toNat := rfl
  have hidx5 : (p.pileDepth.get i).toNat - 1 < 5 := by have := hd6 i; omega
  set B := (g.pos2card.get i).get (⟨(p.pileDepth.get i).toNat - 1, hidx5⟩ : Fin 5) with hBdef
  have hBreal : IsRealCard B := hwf.pos2card_real i _
  have hB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hSB := SUIT_toNat B
  have hVB := VALUE_toNat B
  have hfpos : 1 ≤ (p.pileFlute.get i).toNat := hb.flute_pos i
  have hfle : (p.pileFlute.get i).toNat ≤ (VALUE B).toNat := by
    have := (hb.pileBase i).flute_le_value hwf (fun s => (hb.aces_kings_valid s).1) hdpos
    rw [← hBdef] at this
    exact this
  have hs4 : (SUIT B).toNat < 4 := hBreal.1
  have hlt : (u.tableau i).length - (p.pileDepth.get i).toNat < (p.pileFlute.get i).toNat := by
    have := flute_le_of_depth hwf hb hd6 hdm hcount haces i hpm hdpos
    omega
  -- nor can it stop short
  have hge : (p.pileFlute.get i).toNat
      ≤ (u.tableau i).length - (p.pileDepth.get i).toNat + 1 := by
    by_contra hlt2
    set kk := (u.tableau i).length - (p.pileDepth.get i).toNat with hkk
    have hkkval : (UInt8.ofNat (kk + 1)).toNat = kk + 1 := by
      rw [UInt8.toNat_ofNat']
      have := hBreal.2.2
      omega
    have hxfree : isFreeCard g p (B - UInt8.ofNat (kk + 1)) :=
      hb.flute_cards_free i (UInt8.ofNat (kk + 1)) hdpos (by omega) (by omega)
    have hxaces : p.aces.get ⟨(SUIT B).toNat, hs4⟩ < B - UInt8.ofNat (kk + 1) :=
      hb.flute_not_aces hwf i (UInt8.ofNat (kk + 1)) hdpos (by omega) (by omega) hs4
    have hxle : UInt8.ofNat (kk + 1) ≤ B := by
      rw [UInt8.le_iff_toNat_le]
      have := hBreal.2.2
      omega
    have hxsub : (B - UInt8.ofNat (kk + 1)).toNat = B.toNat - (kk + 1) := by
      rw [UInt8.toNat_sub_of_le _ _ hxle, hkkval]
    have hxS := SUIT_toNat (B - UInt8.ofNat (kk + 1))
    have hxV := VALUE_toNat (B - UInt8.ofNat (kk + 1))
    obtain ⟨x, hx⟩ := exists_encodeCard (c := B - UInt8.ofNat (kk + 1))
      ⟨by omega, by omega, by omega⟩
    -- the exposed top of the column is `x`'s successor
    have hLpos : 0 < (u.tableau i).length := by omega
    have hrl : (u.tableau i).length - 1 < (u.tableau i).reverse.length := by
      simp only [List.length_reverse]; omega
    have htopS : SUIT (encodeCard ((u.tableau i).reverse[(u.tableau i).length - 1]'hrl))
        = SUIT B ∧
        (VALUE (encodeCard ((u.tableau i).reverse[(u.tableau i).length - 1]'hrl))).toNat
          = (VALUE B).toNat - kk := by
      by_cases hkk0 : kk = 0
      · have hidx : (⟨(u.tableau i).length - 1, by have := hd6 i; omega⟩ : Fin 5)
            = ⟨(p.pileDepth.get i).toNat - 1, hidx5⟩ :=
          Fin.ext (by show (u.tableau i).length - 1 = (p.pileDepth.get i).toNat - 1; omega)
        have hcode0 := (hdm i).resident_code (k := (u.tableau i).length - 1) (by omega) hrl
        rw [hidx] at hcode0
        have hcode : encodeCard ((u.tableau i).reverse[(u.tableau i).length - 1]'hrl) = B := hcode0
        rw [hcode]
        exact ⟨rfl, by omega⟩
      · obtain ⟨hs, hv⟩ := (hdm i).above_code hdpos (by omega) hrl
        rw [← hBdef] at hs hv
        exact ⟨hs, by omega⟩
    have hxV' : (VALUE (encodeCard x)).toNat = (VALUE B).toNat - kk - 1 := by
      rw [hx]; omega
    have hxS' : SUIT (encodeCard x) = SUIT B := by rw [hx]; exact UInt8.toNat_inj.mp (by omega)
    refine no_free_succ_exposed hwf hb hd6 hdm hcount hcp (x := x)
      (hx ▸ hxfree) ?_ (head?_reverse_last hLpos hrl) ?_
    · refine uncovered_of_aces_lt haces ?_
      have hfin : (⟨(SUIT B).toNat, hs4⟩ : Fin 4) = finOfSuit x.suit := by
        refine Fin.ext ?_
        show (SUIT B).toNat = suitToNat x.suit
        have h1 := encodeCard_SUIT x
        have h2 := congrArg UInt8.toNat hxS'
        rw [h1, UInt8.toNat_ofNat'] at h2
        have := suitToNat_lt x.suit
        omega
      rw [hfin, ← hx] at hxaces
      exact hxaces
    · refine nextCard_of_encode ?_ ?_
      · rw [htopS.1, hxS']
      · omega
  omega

/-! ## `king_pile` is forced -/

/-- **A king stack never exceeds what `kings` records.**  The mirror of
`flute_le_of_depth`, from `king_frontier` instead of `flute_maximal`, and likewise
free of CP-normality: it holds at a state whose king run is partly parked. -/
theorem king_le_of_depth {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (i : Fin 10) (hd0 : (p.pileDepth.get i).toNat = 0) :
    ∀ d ∈ (u.tableau i).getLast?,
      (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 := by
  intro d hd
  have hdlast : (u.tableau i).getLast? = some d := hd
  have hne : u.tableau i ≠ [] := by
    intro h0
    rw [h0] at hdlast
    simp at hdlast
  have hLpos : 0 < (u.tableau i).length := by
    cases hcol : u.tableau i with
    | nil => exact absurd hcol hne
    | cons y ys => simp
  obtain ⟨su, hrun⟩ := (hdm i).king_run hd0
  -- the deepest card is `d`, a king
  have hr0l : 0 < (u.tableau i).reverse.length := by simp only [List.length_reverse]; omega
  have hdeep : (u.tableau i).reverse[0]'hr0l = d := by
    have h1 : (u.tableau i).reverse.head? = some d := by rw [List.head?_reverse]; exact hdlast
    have h2 : (u.tableau i).reverse.head? = (u.tableau i).reverse[0]? := List.head?_eq_getElem?
    rw [h1, List.getElem?_eq_getElem hr0l] at h2
    exact (Option.some.inj h2).symm
  obtain ⟨hsd, hvd⟩ := hrun 0 hr0l
  rw [hdeep] at hsd hvd
  have hsuval : (su).toNat = suitToNat d.suit := by
    have h1 := congrArg UInt8.toNat hsd
    rw [encodeCard_SUIT, UInt8.toNat_ofNat'] at h1
    have := suitToNat_lt d.suit
    omega
  have hsd4 : suitToNat d.suit < 4 := suitToNat_lt _
  -- the suit's king frontier
  have hSK : (SUIT (p.kings.get (finOfSuit d.suit))).toNat = suitToNat d.suit := by
    rw [(hb.aces_kings_valid (finOfSuit d.suit)).2.2.1]
    show ((finOfSuit d.suit).val.toUInt8).toNat = suitToNat d.suit
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    show suitToNat d.suit % 256 = suitToNat d.suit
    omega
  have hK13 : (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 :=
    (hb.aces_kings_valid (finOfSuit d.suit)).2.2.2.1
  have hSKn := SUIT_toNat (p.kings.get (finOfSuit d.suit))
  have hVKn := VALUE_toNat (p.kings.get (finOfSuit d.suit))
  obtain ⟨hfront, hfree_above⟩ := hb.king_frontier (finOfSuit d.suit)
  -- the run cannot swallow the frontier card
  have hup : (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 := by
    by_contra hgt
    have hr0 : 13 - (VALUE (p.kings.get (finOfSuit d.suit))).toNat
        < (u.tableau i).reverse.length := by
      simp only [List.length_reverse]; omega
    obtain ⟨hs, hv⟩ := hrun (13 - (VALUE (p.kings.get (finOfSuit d.suit))).toNat) hr0
    have hyS := SUIT_toNat (encodeCard ((u.tableau i).reverse[13
      - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0))
    have hyV := VALUE_toNat (encodeCard ((u.tableau i).reverse[13
      - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0))
    have hsn := congrArg UInt8.toNat hs
    have hycode : encodeCard ((u.tableau i).reverse[13
        - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0)
        = p.kings.get (finOfSuit d.suit) := by
      apply UInt8.toNat_inj.mp
      omega
    have hyfree := free_of_index_ge hwf hd6 hdm hcount i (by omega) hr0 rfl
    rcases hfront with ⟨hka, -⟩ | ⟨hlt', hnf⟩
    · -- the frontier card is the foundation top, yet it sits in a column
      have hmem : (u.tableau i).reverse[13
          - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0 ∈ u.tableau i :=
        List.mem_reverse.mp (List.getElem_mem ..)
      have hlt'' := aces_lt_of_mem_column haces hcount hmem
      have hfin : finOfSuit ((u.tableau i).reverse[13
          - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0).suit = finOfSuit d.suit := by
        refine Fin.ext ?_
        show suitToNat _ = suitToNat d.suit
        have h1 := encodeCard_SUIT ((u.tableau i).reverse[13
          - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0)
        rw [h1, UInt8.toNat_ofNat'] at hsn
        have := suitToNat_lt ((u.tableau i).reverse[13
          - (VALUE (p.kings.get (finOfSuit d.suit))).toNat]'hr0).suit
        omega
      rw [hfin, hycode, ← hka, UInt8.lt_iff_toNat_lt] at hlt''
      omega
    · exact hnf (hycode ▸ hyfree)
  -- nor can it stop above it
  exact hup

theorem king_pile_of_depth {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (i : Fin 10) (hcp : ∀ t, ¬ CPStepOn i u t) (hd0 : (p.pileDepth.get i).toNat = 0) :
    ∀ d ∈ (u.tableau i).getLast?,
      (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat = 13 := by
  intro d hd
  have hdlast : (u.tableau i).getLast? = some d := hd
  have hne : u.tableau i ≠ [] := by
    intro h0
    rw [h0] at hdlast
    simp at hdlast
  have hLpos : 0 < (u.tableau i).length := by
    cases hcol : u.tableau i with
    | nil => exact absurd hcol hne
    | cons y ys => simp
  obtain ⟨su, hrun⟩ := (hdm i).king_run hd0
  -- the deepest card is `d`, a king
  have hr0l : 0 < (u.tableau i).reverse.length := by simp only [List.length_reverse]; omega
  have hdeep : (u.tableau i).reverse[0]'hr0l = d := by
    have h1 : (u.tableau i).reverse.head? = some d := by rw [List.head?_reverse]; exact hdlast
    have h2 : (u.tableau i).reverse.head? = (u.tableau i).reverse[0]? := List.head?_eq_getElem?
    rw [h1, List.getElem?_eq_getElem hr0l] at h2
    exact (Option.some.inj h2).symm
  obtain ⟨hsd, hvd⟩ := hrun 0 hr0l
  rw [hdeep] at hsd hvd
  have hsuval : (su).toNat = suitToNat d.suit := by
    have h1 := congrArg UInt8.toNat hsd
    rw [encodeCard_SUIT, UInt8.toNat_ofNat'] at h1
    have := suitToNat_lt d.suit
    omega
  have hsd4 : suitToNat d.suit < 4 := suitToNat_lt _
  -- the suit's king frontier
  have hSK : (SUIT (p.kings.get (finOfSuit d.suit))).toNat = suitToNat d.suit := by
    rw [(hb.aces_kings_valid (finOfSuit d.suit)).2.2.1]
    show ((finOfSuit d.suit).val.toUInt8).toNat = suitToNat d.suit
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    show suitToNat d.suit % 256 = suitToNat d.suit
    omega
  have hK13 : (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 :=
    (hb.aces_kings_valid (finOfSuit d.suit)).2.2.2.1
  have hSKn := SUIT_toNat (p.kings.get (finOfSuit d.suit))
  have hVKn := VALUE_toNat (p.kings.get (finOfSuit d.suit))
  obtain ⟨hfront, hfree_above⟩ := hb.king_frontier (finOfSuit d.suit)
  -- the run cannot swallow the frontier card
  have hup : (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 :=
    king_le_of_depth hwf hb hd6 hdm hcount haces i hd0 d hd
  have hlow : 13 ≤ (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat := by
    by_contra hlt2
    have hcn : (CARD (UInt8.ofNat (suitToNat d.suit))
        (UInt8.ofNat (13 - (u.tableau i).length))).toNat
        = suitToNat d.suit * 16 + (13 - (u.tableau i).length) :=
      CARD_toNat (by omega) (by omega)
    have hc0real : IsRealCard (CARD (UInt8.ofNat (suitToNat d.suit))
        (UInt8.ofNat (13 - (u.tableau i).length))) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [SUIT_toNat]; omega
      · rw [VALUE_toNat]; omega
      · rw [VALUE_toNat]; omega
    obtain ⟨x, hx⟩ := exists_encodeCard hc0real
    have hxS : (SUIT (encodeCard x)).toNat = suitToNat d.suit := by
      rw [hx, SUIT_toNat, CARD_toNat (by omega) (by omega)]
      omega
    have hxV : (VALUE (encodeCard x)).toNat = 13 - (u.tableau i).length := by
      rw [hx, VALUE_toNat, CARD_toNat (by omega) (by omega)]
      omega
    have hfinx : finOfSuit x.suit = finOfSuit d.suit := by
      refine Fin.ext ?_
      show suitToNat x.suit = suitToNat d.suit
      have h1 := encodeCard_SUIT x
      rw [h1, UInt8.toNat_ofNat'] at hxS
      have := suitToNat_lt x.suit
      omega
    -- free, because it is above the king frontier
    have hxfree : isFreeCard g p (encodeCard x) := by
      refine hfree_above (encodeCard x) ?_ (by omega) (by omega)
      rw [encodeCard_SUIT, ← hfinx]
      rfl
    -- above the foundation, because `aces ≤ kings`
    have hxuncov : countFoundation u.foundations x ≠ 1 := by
      refine uncovered_of_aces_lt haces ?_
      have hak : p.aces.get (finOfSuit d.suit) ≤ p.kings.get (finOfSuit d.suit) :=
        (hb.aces_kings_valid (finOfSuit d.suit)).2.2.2.2
      rw [UInt8.le_iff_toNat_le] at hak
      rw [hfinx, UInt8.lt_iff_toNat_lt]
      have hxn := SUIT_toNat (encodeCard x)
      have hxn2 := VALUE_toNat (encodeCard x)
      omega
    -- its successor is the exposed top of the column
    have hrl : (u.tableau i).length - 1 < (u.tableau i).reverse.length := by
      simp only [List.length_reverse]; omega
    obtain ⟨hts, htv⟩ := hrun ((u.tableau i).length - 1) hrl
    refine no_free_succ_exposed hwf hb hd6 hdm hcount hcp hxfree hxuncov
      (head?_reverse_last hLpos hrl) ?_
    refine nextCard_of_encode ?_ ?_
    · rw [hts]
      exact UInt8.toNat_inj.mp (by omega)
    · omega
  omega

/-! ## The main theorem -/

/-- **A merged position matches every CP-normal state with its depths.**  The
converse of `StateMatchesSolverPos.no_cpStep`: together they say that, at a merged
position, the depth vector (plus the foundations) is all there is to the match. -/
theorem matches_of_depth_match_at {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (hcp : ∀ (i : Fin 10) (t : State), ¬ CPStepOn i u t)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    StateMatchesSolverPos g u p where
  cards_count := hcount
  depth_lt6 := hd6
  depth_match := hdm
  flute_match := fun i hi => flute_match_of_depth hwf hb hd6 hdm hcount haces i (hpm i) (hcp i) hi
  king_pile := fun i hi => king_pile_of_depth hwf hb hd6 hdm hcount haces i (hcp i) hi
  aces_match := haces

/-- The global form, as the existing callers use it. -/
theorem matches_of_depth_match {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) (hcp : ∀ t, ¬ CPStep u t)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    StateMatchesSolverPos g u p :=
  matches_of_depth_match_at hwf hb hpm hd6 hdm hcount
    (fun _ t h => hcp t h.toCPStep) haces
