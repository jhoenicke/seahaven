import Seahaven.UsedSpaceBound

/-!
# A canonical position only ever matches a *normalized* state

`SolverCleanupPile` leaves a pile *merged*, and the `SolverMoveAces` drain leaves
the position with `busyAces = 0`.  Read through the matching relation, those
invariants say exactly that the concrete state admits **no normalizing move** —
neither a `CPStep` (cell → non-empty pile) nor an `FMStep` (foundation move), the
two halves of `Seahaven.Normalize`'s `Normalized`.

## No cell card can be dropped on a pile (`no_cpStep`)

A cell card `c` can only be dropped on pile `q` if `q`'s *top* card is
`nextCard c`, and the match determines that top card:

* `pileDepth q > 0` — the top of the column is the outermost flute card, whose
  code is `boundary - (pileFlute q - 1)` (`top_code_pos`), so `encodeCard c` is
  forced to be `boundary - pileFlute q`, which is precisely the `prevCard` of
  `PileMerged.flute_maximal`.  That clause says `prevCard` is on its foundation
  or not free — but a card in a cell *is* free (`isFreeCard_of_cell`) and is
  *not* covered by its foundation (`aces_lt_of_cell`).
* `pileDepth q = 0` — the column is a suit's king run, whose top card is
  `kings[su] + 1` (`top_code_zero`), so `encodeCard c = kings[su]`, the king
  frontier.  `SuitClean.king_frontier` says that card is not free (or the suit is
  complete, so the card is on the foundation) — the same two contradictions.

Only the positive-depth case uses `PileMerged`; the king-pile case needs just
`SolverInvBase`.

## No card can be advanced to a foundation (`no_fmStep`)

Everything accessible is either *free* — cards in cells, cards on solver-empty
piles, interior flute cards — or is a pile's boundary card with `pileFlute = 1`.
For a free card, `SuitClean.foundation_maximal_weak` plus `busyAces = 0` refutes
readiness (`not_ready_of_free`); for a boundary card with trivial flute,
readiness is exactly `aces = boundary - pileFlute`, which
`PileMerged.busyAces_complete` turns into `busyAces ≠ 0`.

## Why this is wanted

This is the direction-agnostic bridge for the *completeness* argument: a state
matching a canonical position is already normalized, so (a) no foundation move
can precede the first real move out of such a state, and (b) re-normalizing after
a move can only redo the cleanup the solver itself performs.
-/

/-! ## Card-code arithmetic -/

/-- The card code of a `Card`, in `Nat` arithmetic. -/
theorem encodeCard_toNat (c : Card) :
    (encodeCard c).toNat = suitToNat c.suit * 16 + rankToNat c.rank := by
  have h1 : suitToNat c.suit < 4 := suitToNat_lt _
  have h2 : rankToNat c.rank ≤ 13 := rankBounded _
  rw [encodeCard, CARD_toNat (by omega) (by omega)]

theorem uint8_toNat_one : (1 : UInt8).toNat = 1 := rfl

/-- `x - 1` in `UInt8`, when it does not wrap. -/
theorem uint8_toNat_sub_one {x : UInt8} (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, uint8_toNat_one]; exact h),
    uint8_toNat_one]

theorem optRankToNat_le (r : Option Rank) : optRankToNat r ≤ 13 := by
  cases r with
  | none => simp [optRankToNat]
  | some r => simpa [optRankToNat] using rankBounded r

/-! ## Two facts about a card sitting in a cell -/

/-- **A card in a cell is above its suit's foundation top.**  The `<`-form of
`NoDupState.foundation_lt_of_cell`, read through `aces_match`; the converse of
`not_covered`. -/
theorem StateMatchesSolverPos.aces_lt_of_cell {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {d : Card} {i : Fin 4} (hc : s.cells i = some d) :
    p.aces.get (finOfSuit d.suit) < encodeCard d := by
  have hlt := h.noDup.foundation_lt_of_cell hc
  have hsu : suitToNat d.suit < 4 := suitToNat_lt _
  have hf13 := optRankToNat_le (s.foundations d.suit)
  rw [UInt8.lt_iff_toNat_lt, h.aces_match d.suit, encodeFoundation,
    CARD_toNat (by omega) (by omega), encodeCard_toNat]
  omega

/-! ## Matching does not see the cells -/

/-- **A match transports across any state with the same columns and foundations.**
The abstract position records nothing about *which* cell a freed card sits in —
`flute_match`/`depth_match`/`king_pile` read the tableau, `aces_match` reads the
foundations, and the cells enter only through `cards_count`.  So a state produced
by parking a run into cells in a different order than some reference construction
matches exactly the same positions. -/
theorem StateMatchesSolverPos.congr_of_tableau {g : Globals} {s t : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (hcount : ∀ c : Card, countState t c = 1)
    (htab : t.tableau = s.tableau) (hfnd : t.foundations = s.foundations) :
    StateMatchesSolverPos g t p where
  cards_count := hcount
  depth_lt6 := h.depth_lt6
  depth_match := fun i => by rw [htab]; exact h.depth_match i
  flute_match := fun i hi => by rw [htab]; exact h.flute_match i hi
  king_pile := fun i hi => by rw [htab]; exact h.king_pile i hi
  aces_match := fun su => by rw [hfnd]; exact h.aces_match su

/-! ## The code of a column's physically topmost card

Both statements are phrased as a suit equation plus a *value* equation, so that
callers can finish with `omega` and never have to worry about `UInt8`
subtraction wrapping. -/

/-- **The top card of a pile of positive depth** is the outermost flute card:
same suit as the boundary, and `pileFlute - 1` below it in value. -/
theorem StateMatchesSolverPos.top_code_pos {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {q : Fin 10} (hdpos : 0 < (p.pileDepth.get q).toNat)
    {e : Card} (hhe : (s.tableau q).head? = some e)
    (hidx5 : (p.pileDepth.get q).toNat - 1 < 5) :
    suitToNat e.suit = (SUIT ((g.pos2card.get q).get ⟨_, hidx5⟩)).toNat ∧
      rankToNat e.rank + (p.pileFlute.get q).toNat
        = (VALUE ((g.pos2card.get q).get ⟨_, hidx5⟩)).toNat + 1 := by
  have hlt : 0 < (s.tableau q).length := by
    cases hcol : s.tableau q with
    | nil => rw [hcol] at hhe; simp at hhe
    | cons x xs => simp
  have hE0 : (s.tableau q)[0]'hlt = e := by
    have h1 : (s.tableau q).head? = (s.tableau q)[0]? := List.head?_eq_getElem?
    rw [hhe, List.getElem?_eq_getElem hlt] at h1
    exact (Option.some.inj h1).symm
  have hnL : (p.pileDepth.get q).toNat ≤ (s.tableau q).length := (h.depth_match q).1
  have hfm := h.flute_match q hdpos
  obtain ⟨hsE, hvE⟩ := flute_elem h q hdpos ⟨_, hidx5⟩ rfl 0 (by omega) hlt
  rw [hE0] at hsE hvE
  have hSe : (SUIT (encodeCard e)).toNat = suitToNat e.suit := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat']
    have := suitToNat_lt e.suit; omega
  have hVe : (VALUE (encodeCard e)).toNat = rankToNat e.rank := encodeCard_VALUE e
  exact ⟨by rw [← hSe, hsE], by omega⟩

/-- **The top card of a solver-empty pile** is one value above the suit's king
frontier: the column holds the run `13 … kings[su]+1`. -/
theorem StateMatchesSolverPos.top_code_zero {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {q : Fin 10} (hd0 : (p.pileDepth.get q).toNat = 0)
    {e d : Card} (hhe : (s.tableau q).head? = some e)
    (hlast : (s.tableau q).getLast? = some d) :
    suitToNat e.suit = suitToNat d.suit ∧
      rankToNat e.rank = (VALUE (p.kings.get (finOfSuit d.suit))).toNat + 1 := by
  have hne : s.tableau q ≠ [] := by
    intro hnil; rw [hnil] at hhe; simp at hhe
  have hlt : 0 < (s.tableau q).length := by
    cases hcol : s.tableau q with
    | nil => exact absurd hcol hne
    | cons x xs => simp
  have hE0 : (s.tableau q)[0]'hlt = e := by
    have h1 : (s.tableau q).head? = (s.tableau q)[0]? := List.head?_eq_getElem?
    rw [hhe, List.getElem?_eq_getElem hlt] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨hlen, hcont⟩ := h.king_pile_contents q hd0 hlast
  have hrevlt : (s.tableau q).length - 1 < (s.tableau q).reverse.length := by
    simp only [List.length_reverse]; omega
  have hre : (s.tableau q).reverse[(s.tableau q).length - 1]'hrevlt = e := by
    rw [List.getElem_reverse hrevlt, ← hE0]
    congr 1
    omega
  have hcode0 := hcont ((s.tableau q).length - 1) hrevlt
  rw [hre] at hcode0
  have hsd4 : suitToNat d.suit < 4 := suitToNat_lt _
  have hse4 : suitToNat e.suit < 4 := suitToNat_lt _
  have hcode0' : (encodeCard e).toNat
      = suitToNat d.suit * 16 + (13 - ((s.tableau q).length - 1)) := by
    rw [hcode0, CARD_toNat (by omega) (by omega)]
  have hEcode := encodeCard_toNat e
  have hrb := rankBounded e.rank
  have hrp := rankToNat_pos e.rank
  constructor <;> omega

/-! ## No cell card can be dropped on a merged pile -/

/-- **The cell→pile move the state might allow is refuted by the invariant.**
See the module docstring. -/
theorem StateMatchesSolverPos.head_ne_nextCard_of_cell {g : Globals} {s : State}
    {p : SolverPosType} (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (h : StateMatchesSolverPos g s p) {i : Fin 4} {c : Card} (hcell : s.cells i = some c)
    {q : Fin 10} (hmerged : PileMerged g p q (hb.pileDepth_bound q))
    (hne : s.tableau q ≠ []) :
    (s.tableau q).head? ≠ nextCard c := by
  intro hhead
  -- The two facts about `c` that every case contradicts.
  have hfree : isFreeCard g p (encodeCard c) := h.isFreeCard_of_cell hwf hcell
  have hacesLt : p.aces.get (finOfSuit c.suit) < encodeCard c := h.aces_lt_of_cell hcell
  -- Name the top card of the column and relate it to `c`.
  obtain ⟨e, hhe⟩ : ∃ e, (s.tableau q).head? = some e := by
    cases hcol : s.tableau q with
    | nil => exact absurd hcol hne
    | cons x xs => exact ⟨x, rfl⟩
  have hnext : nextCard c = some e := by rw [← hhead, hhe]
  have hsuitE : suitToNat e.suit = suitToNat c.suit := by rw [nextCard_suit hnext]
  have hrankE : rankToNat e.rank = rankToNat c.rank + 1 := nextCard_rank hnext
  have hcpos : 1 ≤ rankToNat c.rank := rankToNat_pos _
  have hebound : rankToNat e.rank ≤ 13 := rankBounded _
  have hsc4 : suitToNat c.suit < 4 := suitToNat_lt _
  have hCcode := encodeCard_toNat c
  by_cases hd0 : (p.pileDepth.get q).toNat = 0
  · -- ## Solver-empty pile: the column is a king run, its top is `kings[su] + 1`
    obtain ⟨d, hlast⟩ : ∃ d, (s.tableau q).getLast? = some d := by
      cases hl : (s.tableau q).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
      | some d => exact ⟨d, rfl⟩
    obtain ⟨hsuitK, hvalK⟩ := h.top_code_zero hd0 hhe hlast
    -- the frontier card `kings[su]` is exactly `c`
    have hSK : (SUIT (p.kings.get (finOfSuit d.suit))).toNat = suitToNat d.suit := by
      rw [(hb.aces_kings_valid (finOfSuit d.suit)).2.2.1]
      show ((finOfSuit d.suit).val.toUInt8).toNat = suitToNat d.suit
      rw [Nat.toUInt8, UInt8.toNat_ofNat']
      show suitToNat d.suit % 256 = suitToNat d.suit
      have := suitToNat_lt d.suit; omega
    have hSKn := SUIT_toNat (p.kings.get (finOfSuit d.suit))
    have hVKn := VALUE_toNat (p.kings.get (finOfSuit d.suit))
    have hKcode : encodeCard c = p.kings.get (finOfSuit d.suit) := by
      apply UInt8.toNat_inj.mp
      omega
    have hfinsuit : finOfSuit d.suit = finOfSuit c.suit :=
      Fin.ext (by show suitToNat d.suit = suitToNat c.suit; omega)
    obtain ⟨hfront, _⟩ := hb.king_frontier (finOfSuit d.suit)
    rcases hfront with ⟨hka, _⟩ | ⟨_, hnf⟩
    · rw [hKcode, hka, hfinsuit] at hacesLt
      rw [UInt8.lt_iff_toNat_lt] at hacesLt; omega
    · rw [← hKcode] at hnf
      exact hnf hfree
  · -- ## Ordinary pile: the top is the outermost flute card
    have hdpos : 0 < (p.pileDepth.get q).toNat := by omega
    have hidx5 : (p.pileDepth.get q).toNat - 1 < 5 := by have := h.depth_lt6 q; omega
    have hfpos : 1 ≤ (p.pileFlute.get q).toNat := hb.flute_pos q
    obtain ⟨hsuitB, hvalB⟩ := h.top_code_pos hdpos hhe hidx5
    set B := (g.pos2card.get q).get
      (⟨(p.pileDepth.get q).toNat - 1, hidx5⟩ : Fin 5) with hBdef
    have hSB := SUIT_toNat B
    have hVB := VALUE_toNat B
    -- `encodeCard c` is exactly `flute_maximal`'s `prevCard`
    have hle : p.pileFlute.get q ≤ B := by
      rw [UInt8.le_iff_toNat_le]; omega
    have hcode : encodeCard c = B - p.pileFlute.get q := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_sub_of_le _ _ hle]
      omega
    rcases hmerged.flute_maximal with hz | hmax
    · rw [hz] at hdpos; simp at hdpos
    · dsimp only at hmax
      rw [← hBdef] at hmax
      rcases hmax with ⟨hs4, haces⟩ | hnf
      · have hfin : (⟨(SUIT B).toNat, hs4⟩ : Fin 4) = finOfSuit c.suit :=
          Fin.ext (by show (SUIT B).toNat = suitToNat c.suit; omega)
        rw [hfin, ← hcode] at haces
        rw [haces] at hacesLt
        rw [UInt8.lt_iff_toNat_lt] at hacesLt; omega
      · rw [← hcode] at hnf
        exact hnf hfree

/-- **A state matching a merged position admits no `CPStep`.** -/
theorem StateMatchesSolverPos.no_cpStep {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ j : Fin 10, PileMerged g p j (hb.pileDepth_bound j))
    (h : StateMatchesSolverPos g s p) : ∀ t, ¬ CPStep s t := by
  rintro t ⟨i, q, hne, hq⟩
  rw [applyMove_eq] at hq
  obtain ⟨c, s0, htake, hdrop⟩ := hq
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨hc, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨hhead, _⟩ := hdrop
  exact h.head_ne_nextCard_of_cell hwf hb hc (hpm q) hne (by simpa using hhead)

/-! ## No card can be advanced to a foundation -/

/-- A card ready for its foundation has code `aces[su] + 1`. -/
theorem StateMatchesSolverPos.ready_code {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {c : Card}
    (hready : some c.rank = nextRank (s.foundations c.suit)) :
    rankToNat c.rank = optRankToNat (s.foundations c.suit) + 1 ∧
      encodeCard c = p.aces.get (finOfSuit c.suit) + 1 := by
  have hrank : rankToNat c.rank = optRankToNat (s.foundations c.suit) + 1 := by
    unfold nextRank at hready
    exact natToRankToNat _ _ hready.symm
  have hsu : suitToNat c.suit < 4 := suitToNat_lt _
  have hrb : rankToNat c.rank ≤ 13 := rankBounded _
  have haces : (p.aces.get (finOfSuit c.suit)).toNat
      = suitToNat c.suit * 16 + optRankToNat (s.foundations c.suit) := by
    rw [h.aces_match c.suit, encodeFoundation, CARD_toNat (by omega) (by omega)]
  refine ⟨hrank, ?_⟩
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, encodeCard_toNat]
  have hone : (1 : UInt8).toNat = 1 := rfl
  omega

/-- **A free card is never ready for its foundation** once the drain has run:
`foundation_maximal_weak` says the next foundation card is unfree, and
`busyAces = 0` closes its escape clause. -/
theorem StateMatchesSolverPos.not_ready_of_free {g : Globals} {s : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hz : p.busyAces = 0) (h : StateMatchesSolverPos g s p)
    {c : Card} (hfree : isFreeCard g p (encodeCard c)) :
    some c.rank ≠ nextRank (s.foundations c.suit) := by
  intro hready
  obtain ⟨hrank, hcode⟩ := h.ready_code hready
  have hVa : (VALUE (p.aces.get (finOfSuit c.suit))).toNat
      = optRankToNat (s.foundations c.suit) := by
    have hsu : suitToNat c.suit < 4 := suitToNat_lt _
    have hf13 := optRankToNat_le (s.foundations c.suit)
    rw [VALUE_toNat, h.aces_match c.suit, encodeFoundation, CARD_toNat (by omega) (by omega)]
    omega
  rcases hb.foundation_maximal_weak (finOfSuit c.suit) with h13 | hnf | hbusy
  · -- the suit is complete, so `c` would have to be a fourteenth card
    have := rankBounded c.rank
    omega
  · exact hnf (hcode ▸ hfree)
  · rw [hz] at hbusy; simp at hbusy

/-- **A state matching a canonical position admits no `FMStep`.** -/
theorem StateMatchesSolverPos.no_fmStep {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (h : StateMatchesSolverPos g s p) : ∀ t, ¬ FMStep s t := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hz : p.busyAces = 0 := hcan.busyAces_zero
  rintro t ⟨pos, hp⟩
  rw [applyMove_eq] at hp
  obtain ⟨c, s0, htake, hdrop⟩ := hp
  simp only [dropPosition, dropFoundation_eq] at hdrop
  obtain ⟨hready, _⟩ := hdrop
  rw [takeFromPosition_foundations htake] at hready
  cases pos with
  | foundation => simp [takeFromPosition] at htake
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at htake
    exact h.not_ready_of_free hb hz (h.isFreeCard_of_cell hwf htake.1) hready
  | pile q =>
    rw [takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest, hcol, _⟩ := htake
    have hhe : (s.tableau q).head? = some c := by rw [hcol]; rfl
    have hmem : c ∈ s.tableau q := by rw [hcol]; exact List.mem_cons_self ..
    by_cases hd0 : (p.pileDepth.get q).toNat = 0
    · -- a card on a solver-empty pile is free
      exact h.not_ready_of_free hb hz (h.isFreeCard_of_empty_pile hwf hd0 hmem) hready
    · have hdpos : 0 < (p.pileDepth.get q).toNat := by omega
      have hidx5 : (p.pileDepth.get q).toNat - 1 < 5 := by have := h.depth_lt6 q; omega
      have hfpos : 1 ≤ (p.pileFlute.get q).toNat := hb.flute_pos q
      obtain ⟨hsuitB, hvalB⟩ := h.top_code_pos hdpos hhe hidx5
      set B := (g.pos2card.get q).get
        (⟨(p.pileDepth.get q).toNat - 1, hidx5⟩ : Fin 5) with hBdef
      have hSB := SUIT_toNat B
      have hVB := VALUE_toNat B
      have hCcode := encodeCard_toNat c
      have hsc4 : suitToNat c.suit < 4 := suitToNat_lt _
      by_cases hf1 : (p.pileFlute.get q).toNat = 1
      · -- the top card *is* the boundary: readiness is `busyAces_complete`'s guard
        obtain ⟨hrank, hcode⟩ := h.ready_code hready
        have hfluteOne : p.pileFlute.get q = 1 := by
          apply UInt8.toNat_inj.mp; rw [hf1]; rfl
        have hBc : encodeCard c = B := by
          apply UInt8.toNat_inj.mp; omega
        have hs4 : (SUIT B).toNat < 4 := by omega
        have hfin : (⟨(SUIT B).toNat, hs4⟩ : Fin 4) = finOfSuit c.suit :=
          Fin.ext (by show (SUIT B).toNat = suitToNat c.suit; omega)
        have hle : p.pileFlute.get q ≤ B := by
          rw [UInt8.le_iff_toNat_le]
          have := rankToNat_pos c.rank
          omega
        have haces : p.aces.get ⟨(SUIT B).toNat, hs4⟩ = B - p.pileFlute.get q := by
          rw [hfin]
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hle]
          have hone := uint8_toNat_one
          have := congrArg UInt8.toNat hcode
          rw [UInt8.toNat_add] at this
          have hbound : (p.aces.get (finOfSuit c.suit)).toNat < 62 := by
            have hsu : suitToNat c.suit < 4 := suitToNat_lt _
            have hf13 := optRankToNat_le (s.foundations c.suit)
            rw [h.aces_match c.suit, encodeFoundation, CARD_toNat (by omega) (by omega)]
            omega
          omega
        have := (hcan.pileMerged q).busyAces_complete (by omega) hs4 haces
        rw [hz] at this
        simp at this
      · -- an interior flute card, hence free
        have hjtoNat : ((p.pileFlute.get q) - 1).toNat = (p.pileFlute.get q).toNat - 1 :=
          uint8_toNat_sub_one (by omega)
        have hjlt : ((p.pileFlute.get q) - 1).toNat < (p.pileFlute.get q).toNat := by omega
        have hjpos : 0 < ((p.pileFlute.get q) - 1).toNat := by omega
        have hfr := hb.flute_cards_free q ((p.pileFlute.get q) - 1) hdpos hjpos hjlt
        rw [← hBdef] at hfr
        have hle : (p.pileFlute.get q) - 1 ≤ B := by
          rw [UInt8.le_iff_toNat_le]
          have := rankToNat_pos c.rank
          omega
        have hBc : encodeCard c = B - ((p.pileFlute.get q) - 1) := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hle]
          omega
        exact h.not_ready_of_free hb hz (hBc ▸ hfr) hready

/-! ## The packaged statement -/

/-- **Every state a canonical position matches is already normalized.**  So
normalizing a state that matches `p` can only be the identity, and in particular
no foundation move and no cell→pile move is available. -/
theorem StateMatchesSolverPos.normalized {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (h : StateMatchesSolverPos g s p) : Normalized s := by
  rintro t (hfm | hcp)
  · exact h.no_fmStep hwf hcan t hfm
  · exact h.no_cpStep hwf hcan.toSolverInvBase hcan.pileMerged t hcp

/-! ## CP-only normalization

The completeness step needs to exhaust the *cell→pile* moves while leaving the
foundation moves pending (`busyAces ≠ 0` at that point), so `exists_normalForm`
— which also drains the foundations — is the wrong normal form.  The same measure
argument works, since `CPStep.measure_lt` is already available. -/

/-- `t` is reachable from `s` by cell→non-empty-pile moves only. -/
abbrev CPReach : State → State → Prop := Relation.ReflTransGen CPStep

theorem CPReach.toReach {s t : State} (h : CPReach s t) : Reach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (NormStep.toMoveStep (Or.inr hbc))

/-- CP moves are revertible, so they change nothing about solvability. -/
theorem CPReach.solvable_iff {s t : State} (h : CPReach s t) : Solvable s ↔ Solvable t := by
  induction h with
  | refl => exact Iff.rfl
  | tail hab hbc ih => exact ih.trans ⟨hbc.preserves_Solvable, fun hc => Solvable.of_reach
      (Relation.ReflTransGen.single (NormStep.toMoveStep (Or.inr hbc))) hc⟩

/-- **A CP-normal form always exists**, and by `no_cpStep` it is the state a
merged position matches. -/
theorem exists_cpNormalForm (s : State) : ∃ t, CPReach s t ∧ ∀ u, ¬ CPStep t u := by
  suffices H : ∀ n s, normMeasure s ≤ n → ∃ t, CPReach s t ∧ ∀ u, ¬ CPStep t u from
    H (normMeasure s) s le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs
    refine ⟨s, Relation.ReflTransGen.refl, fun t hst => ?_⟩
    have := hst.measure_lt
    omega
  | succ n ih =>
    intro s hs
    by_cases hn : ∀ t, ¬ CPStep s t
    · exact ⟨s, Relation.ReflTransGen.refl, hn⟩
    · obtain ⟨t, hst⟩ : ∃ t, CPStep s t := by
        by_contra hcon
        exact hn (fun t hst => hcon ⟨t, hst⟩)
      have hlt := hst.measure_lt
      obtain ⟨u, hru, hnu⟩ := ih t (by omega)
      exact ⟨u, Relation.ReflTransGen.head hst hru, hnu⟩
