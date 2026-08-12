import Seahaven.ConvertMatch
import Seahaven.SolverCorrectness

/-!
# A reachable state matches the position its own encoding describes

`pilesKingsFromState` reports `|removeFlute (tableau i)|` as pile `i`'s depth and the
`kingBit` bitmap as slot `10`.  This file shows those are a legal query — the two
`Rules`-side obligations of `SolverIsCorrect`:

* `ValidDepths (pilesKingsFromState s)`, and
* `∃ game', CvEntry g (pilesKingsFromState s) s game' (kingCfgOf …)`.

Both rest on one structural fact about `removeFlute`, which is a *maximal* strip:

* it strips only chained cards (`removeFlute_chain`), so what it leaves is still a
  prefix of the dealt column — the depth it reports is a legal boundary
  (`pileMatches_removeFluteDepth`);
* and it strips *every* chained card (`removeFlute_of_chain`), so it never leaves a
  card above the dealt boundary — the depth it reports is at most the layout's
  (`removeFlute_length_le_of_pileMatches`), which is also why it is at most `5`.

The rest is bookkeeping: `matchesKingConfig_cvFluteOf` (`ConvertMatch`) builds the
match from the depth vector, the state's own foundations and the king piles, and the
configuration comes from `kingBitmap` — where the only content is that a column
`removeFlute` empties is a run bottoming out at a king (`nextCard king = none` is what
lets the recursion reach `[]`).
-/

/-! ## `nextCard`, as a code step -/

theorem nextCard_eq_none_iff (c : Card) : nextCard c = none ↔ c.rank = Rank.king := by
  cases c with
  | mk su rk => cases rk <;> simp [nextCard, nextRank, natToRank, optRankToNat, rankToNat]

/-- A `nextCard` step raises the code by one. -/
theorem encodeCard_of_nextCard {c d : Card} (h : nextCard c = some d) :
    encodeCard d = encodeCard c + 1 :=
  encodeCard_succ (congrArg suitToNat (nextCard_suit h)) (nextCard_rank h)

/-- …and conversely, a code step is a `nextCard` step. -/
theorem nextCard_of_encodeCard_succ {c d : Card} (h : encodeCard d = encodeCard c + 1) :
    nextCard c = some d := by
  have h1 := congrArg UInt8.toNat h
  rw [UInt8.toNat_add, encodeCard_toNat, encodeCard_toNat,
    show ((1 : UInt8).toNat = 1) from rfl] at h1
  have hs1 := suitToNat_lt c.suit
  have hs2 := suitToNat_lt d.suit
  have hr1 := rankBounded c.rank
  have hr2 := rankBounded d.rank
  have hp1 := rankToNat_pos c.rank
  have hp2 := rankToNat_pos d.rank
  refine nextCard_of_encode ?_ ?_
  · rw [encodeCard_SUIT, encodeCard_SUIT]
    exact congrArg UInt8.ofNat (by omega)
  · rw [encodeCard_VALUE, encodeCard_VALUE]; omega

/-! ## What `removeFlute` strips -/

theorem removeFlute_cons (c : Card) (rest : Column) :
    removeFlute (c :: rest)
      = if nextCard c = rest.head? then removeFlute rest else c :: rest := by
  rw [removeFlute]

theorem removeFlute_length_le : ∀ col : Column, (removeFlute col).length ≤ col.length
  | [] => le_refl 0
  | c :: rest => by
    rw [removeFlute_cons]
    by_cases hc : nextCard c = rest.head?
    · rw [if_pos hc]
      have := removeFlute_length_le rest
      simp only [List.length_cons]
      omega
    · rw [if_neg hc]

/-- **`removeFlute` strips only chained cards.**  Above the cut, every card is
followed directly by its successor — and if the whole column goes, its bottom card is
a king, since `nextCard king = none` matches the empty tail. -/
theorem removeFlute_chain : ∀ (col : Column) (j : Nat) (hj : j < col.length),
    j < col.length - (removeFlute col).length →
    nextCard (col[j]'hj) = (col.drop (j + 1)).head? := by
  intro col
  induction col with
  | nil => intro j hj _; exact absurd hj (by simp)
  | cons c rest ih =>
    intro j hj hlt
    by_cases hc : nextCard c = rest.head?
    · rw [removeFlute_cons, if_pos hc] at hlt
      cases j with
      | zero => simpa using hc
      | succ j' =>
        have hj' : j' < rest.length := by simpa using hj
        have hlt' : j' < rest.length - (removeFlute rest).length := by
          simp only [List.length_cons] at hlt; omega
        simpa using ih j' hj' hlt'
    · rw [removeFlute_cons, if_neg hc] at hlt
      simp only [List.length_cons, Nat.sub_self] at hlt
      omega

/-- **`removeFlute` strips every chained card.**  If the top `t` cards each sit
directly on their successor, all of them go. -/
theorem removeFlute_of_chain : ∀ (t : Nat) (col : Column), t ≤ col.length →
    (∀ j, j < t → ∀ hj : j < col.length, nextCard (col[j]'hj) = (col.drop (j + 1)).head?) →
    removeFlute col = removeFlute (col.drop t) := by
  intro t
  induction t with
  | zero => intro col _ _; rw [List.drop_zero]
  | succ t ih =>
    intro col hle hchain
    match col with
    | [] => simp only [List.length_nil] at hle; omega
    | c :: rest =>
      have h0 : nextCard c = rest.head? := by
        have h := hchain 0 (by omega) (by simp)
        rw [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at h
        exact h
      rw [removeFlute_cons, if_pos h0, List.drop_succ_cons]
      refine ih rest (by simpa using hle) (fun j hj hjr => ?_)
      have h := hchain (j + 1) (by omega) (by simp only [List.length_cons]; omega)
      rw [List.getElem_cons_succ, List.drop_succ_cons] at h
      exact h

theorem removeFlute_length_le_of_chain (t : Nat) (col : Column) (hle : t ≤ col.length)
    (hchain : ∀ j, j < t → ∀ hj : j < col.length,
      nextCard (col[j]'hj) = (col.drop (j + 1)).head?) :
    (removeFlute col).length ≤ col.length - t := by
  rw [removeFlute_of_chain t col hle hchain]
  have := removeFlute_length_le (col.drop t)
  simp only [List.length_drop] at this
  omega

/-! ## The depth `removeFlute` reports is a legal boundary

Two directions, both read off a `PileMatches` witness at the layout's own depth `n`:
above the boundary the column chains (`succ_below`), so `removeFlute` cuts at or below
`n`; and what it strips chains (`removeFlute_chain`), so the dealt cards between the
two cuts form a merge chain and `PileMatches_lower` applies. -/

/-- The head of a tail is the card at that index. -/
private theorem head?_drop_eq {col : Column} {i : Nat} (h : i < col.length) :
    (col.drop i).head? = some (col[i]'h) := by
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- The card the column carries at reverse index `r`, in column order. -/
private theorem getElem_reverse_col {col : Column} {r : Nat} (hr : r < col.reverse.length)
    (hj : col.length - 1 - r < col.length) :
    col.reverse[r]'hr = col[col.length - 1 - r]'hj := by
  rw [List.getElem_reverse hr]

/-- **The chain above the boundary.**  Every card above the dealt boundary sits
directly on its successor; at the very bottom (only possible when `n = 0`) the card is
a king and the tail is empty. -/
theorem pileMatches_nextCard_chain {g : Globals} (hwf : WellFormedLayout g)
    {col : Column} {a : Fin 10} {n : Fin 6} (h : PileMatches g col a n)
    (j : Nat) (hj : j < col.length) (hjlt : j < col.length - n.val) :
    nextCard (col[j]'hj) = (col.drop (j + 1)).head? := by
  have hlen : col.reverse.length = col.length := by simp
  set r := col.length - 1 - j with hrdef
  have hrl : r < col.reverse.length := by rw [hlen]; omega
  have hrn : n.val ≤ r := by omega
  have hcol : col.reverse[r]'hrl = col[j]'hj := by
    rw [getElem_reverse_col hrl (by omega)]
    congr 1
    omega
  by_cases hr0 : r = 0
  · -- the bottom card, which the run structure makes a king
    have hn0 : n.val = 0 := by omega
    obtain ⟨su, hrun⟩ := h.king_run hn0
    obtain ⟨-, hv⟩ := hrun r hrl
    have hjL : j + 1 = col.length := by omega
    have hking : (col[j]'hj).rank = Rank.king := by
      have hvr : rankToNat (col[j]'hj).rank = 13 := by
        rw [← encodeCard_VALUE, ← hcol, hv, hr0]
      exact rankInj _ _ (by rw [hvr]; rfl)
    rw [(nextCard_eq_none_iff _).2 hking, hjL, List.drop_length]
    rfl
  · -- inside the run: the card below is the successor
    have hr1 : r - 1 < col.reverse.length := by omega
    have hj1 : j + 1 < col.length := by omega
    have hcol1 : col.reverse[r - 1]'hr1 = col[j + 1]'hj1 := by
      rw [getElem_reverse_col hr1 (by omega)]
      congr 1
      omega
    have hstep := h.succ_below hwf hrn (by omega) hrl hr1
    rw [hcol, hcol1] at hstep
    rw [nextCard_of_encodeCard_succ hstep, head?_drop_eq hj1]

/-- **The reported depth is at most the layout's.**  In particular it is at most `5`. -/
theorem removeFlute_length_le_of_pileMatches {g : Globals} (hwf : WellFormedLayout g)
    {col : Column} {a : Fin 10} {n : Fin 6} (h : PileMatches g col a n) :
    (removeFlute col).length ≤ n.val := by
  have hnL : n.val ≤ col.length := h.1
  have := removeFlute_length_le_of_chain (col.length - n.val) col (by omega)
    (fun j hj hjc => pileMatches_nextCard_chain hwf h j hjc hj)
  omega

/-- **The dealt cards between the two cuts chain.**  What `removeFlute` stripped below
the layout's boundary was stripped because it chained, and down there the column *is*
the dealt column — so the chain is a statement about `pos2card`, which is what
`PileMatches_lower` wants. -/
theorem pileMatches_pos2card_chain {g : Globals}
    {col : Column} {a : Fin 10} {n : Fin 6} (h : PileMatches g col a n)
    (j : Nat) (h1 : 1 ≤ j) (hr : (removeFlute col).length ≤ j) (hjn : j < n.val)
    (hj1 : j - 1 < 5) (hj5 : j < 5) :
    (g.pos2card.get a).get ⟨j - 1, hj1⟩ = (g.pos2card.get a).get ⟨j, hj5⟩ + 1 := by
  have hnL : n.val ≤ col.length := h.1
  have hlen : col.reverse.length = col.length := by simp
  -- the two cards, at reverse indices `j` and `j - 1`
  have hjr : j < col.reverse.length := by rw [hlen]; omega
  have hj1r : j - 1 < col.reverse.length := by rw [hlen]; omega
  have hcode : encodeCard (col.reverse[j]'hjr) = (g.pos2card.get a).get ⟨j, hj5⟩ := by
    have := h.resident_code (show j < n.val from hjn) hjr
    exact this
  have hcode1 : encodeCard (col.reverse[j - 1]'hj1r) = (g.pos2card.get a).get ⟨j - 1, hj1⟩ := by
    have := h.resident_code (show j - 1 < n.val from by omega) hj1r
    exact this
  -- and the chain, read at the corresponding column index
  have hjc : col.length - 1 - j < col.length := by omega
  have hchain := removeFlute_chain col (col.length - 1 - j) hjc (by omega)
  have hc0 : col[col.length - 1 - j]'hjc = col.reverse[j]'hjr := by
    rw [getElem_reverse_col hjr hjc]
  have hidx : col.length - 1 - j + 1 = col.length - 1 - (j - 1) := by omega
  have hc1lt : col.length - 1 - (j - 1) < col.length := by omega
  have hc1 : col[col.length - 1 - (j - 1)]'hc1lt = col.reverse[j - 1]'hj1r := by
    rw [getElem_reverse_col hj1r hc1lt]
  rw [hc0, hidx, head?_drop_eq hc1lt, hc1] at hchain
  rw [← hcode, ← hcode1]
  exact encodeCard_of_nextCard hchain

/-- **The reported depth is a legal boundary.**  `PileMatches_lower` down to it, and —
when it is `0` — `PileMatches_vacate` for the last step, whose king is exactly the card
`removeFlute` needed to reach the empty list. -/
theorem pileMatches_removeFluteDepth {g : Globals} (hwf : WellFormedLayout g)
    {col : Column} {a : Fin 10} {n : Fin 6} (h : PileMatches g col a n)
    (hr6 : (removeFlute col).length < 6) :
    PileMatches g col a ⟨(removeFlute col).length, hr6⟩ := by
  have hrn : (removeFlute col).length ≤ n.val := removeFlute_length_le_of_pileMatches hwf h
  have hnL : n.val ≤ col.length := h.1
  have hchain : ∀ j, 1 ≤ j → (removeFlute col).length ≤ j → j < n.val →
      ∀ (hj1 : j - 1 < 5) (hj5 : j < 5),
      (g.pos2card.get a).get ⟨j - 1, hj1⟩ = (g.pos2card.get a).get ⟨j, hj5⟩ + 1 :=
    fun j h1 hr hjn hj1 hj5 => pileMatches_pos2card_chain h j h1 hr hjn hj1 hj5
  by_cases hr0 : (removeFlute col).length = 0
  · by_cases hn0 : n.val = 0
    · exact PileMatches_of_val_eq h (show (removeFlute col).length = n.val from by omega)
    · -- down to one dealt card, then read that card as the king it is
      have hone : PileMatches g col a ⟨1, by omega⟩ :=
        PileMatches_lower hwf h (show 1 ≤ 1 from le_refl 1) (show 1 ≤ n.val from by omega)
          (fun j hj hjn hja hjb =>
            hchain j (show 1 ≤ j from hj) (by omega) hjn hja hjb)
      have hL : 0 < col.length := by omega
      have hlen : col.reverse.length = col.length := by simp
      have h0r : 0 < col.reverse.length := by rw [hlen]; omega
      have hbot : encodeCard (col.reverse[0]'h0r) = (g.pos2card.get a).get ⟨0, by omega⟩ :=
        hone.resident_code (show 0 < 1 from by omega) h0r
      -- `removeFlute` reached `[]`, so the bottom card has no successor
      have hjc : col.length - 1 < col.length := by omega
      have hchain0 := removeFlute_chain col (col.length - 1) hjc (by omega)
      rw [show col.length - 1 + 1 = col.length from by omega, List.drop_length] at hchain0
      have hking : (col.reverse[0]'h0r).rank = Rank.king := by
        rw [getElem_reverse_col h0r (by omega)] at *
        exact (nextCard_eq_none_iff _).1 hchain0
      have hking13 : (VALUE ((g.pos2card.get a).get ⟨0, by omega⟩)).toNat = 13 := by
        rw [← hbot, encodeCard_VALUE, hking]
        rfl
      exact PileMatches_of_val_eq (PileMatches_vacate hone hking13)
        (show (removeFlute col).length = 0 from hr0)
  · refine PileMatches_lower hwf h (show 1 ≤ (removeFlute col).length from by omega) hrn
      (fun j hj hjn hja hjb => ?_)
    have hj' : (removeFlute col).length ≤ j := hj
    exact hchain j (by omega) hj' hjn hja hjb

/-! ## A card lies in only one column

Needed to pin `kings`: the king of a suit is at the bottom of at most one column, so
"the length of the column carrying suit `su`'s run" is well defined. -/

theorem le_sum_ofFn {n : Nat} (f : Fin n → Nat) (i : Fin n) : f i ≤ (List.ofFn f).sum := by
  rw [List.sum_ofFn]
  exact Finset.single_le_sum (f := f) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A card in a column is in no cell. -/
theorem not_mem_cell_of_mem_column {u : State} (hcount : ∀ c : Card, countState u c = 1)
    {c : Card} {j : Fin 10} (hmem : c ∈ u.tableau j) (i : Fin 4) : u.cells i ≠ some c := by
  intro hcell
  have h1 : 1 ≤ countColumn (u.tableau j) c := one_le_countColumn hmem
  have h2 : countColumn (u.tableau j) c ≤ countTableau u.tableau c :=
    le_sum_ofFn (fun k : Fin 10 => countColumn (u.tableau k) c) j
  have h3 : 1 ≤ countCells u.cells c := by
    have h4 : countCard (u.cells i) c ≤ countCells u.cells c :=
      le_sum_ofFn (fun k : Fin 4 => countCard (u.cells k) c) i
    rw [hcell] at h4
    have h5 : countCard (some c) c = 1 := by simp [countCard]
    omega
  have h : countFoundation u.foundations c + countCells u.cells c + countTableau u.tableau c = 1 :=
    hcount c
  omega

theorem add_le_sum_ofFn {n : Nat} (f : Fin n → Nat) {i j : Fin n} (hij : i ≠ j) :
    f i + f j ≤ (List.ofFn f).sum := by
  rw [List.sum_ofFn]
  calc f i + f j = ∑ k ∈ ({i, j} : Finset (Fin n)), f k := (Finset.sum_pair hij).symm
    _ ≤ ∑ k, f k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem column_eq_of_mem {s : State} (hcount : ∀ c : Card, countState s c = 1)
    {c : Card} {i j : Fin 10} (hi : c ∈ s.tableau i) (hj : c ∈ s.tableau j) : i = j := by
  by_contra hij
  have h1 := one_le_countColumn hi
  have h2 := one_le_countColumn hj
  have hsum := add_le_sum_ofFn (fun k : Fin 10 => countColumn (s.tableau k) c) hij
  have h := hcount c
  unfold countState countTableau at h
  omega

/-! ## Columns the encoding calls empty -/

theorem getLast?_getElem {col : Column} {c : Card} (h : col.getLast? = some c) :
    ∃ hL : 0 < col.length, col[col.length - 1]'(by omega) = c := by
  have hL : 0 < col.length := by
    cases col with
    | nil => simp at h
    | cons x xs => simp
  refine ⟨hL, ?_⟩
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
  exact Option.some.inj h

theorem head?_getElem {col : Column} {c : Card} (h : col.head? = some c) :
    ∃ hL : 0 < col.length, col[0]'hL = c := by
  cases col with
  | nil => simp at h
  | cons x xs => exact ⟨by simp, by simpa using h⟩

theorem reverse_getElem_zero {col : Column} {c : Card} (h : col.getLast? = some c)
    (h0 : 0 < col.reverse.length) : col.reverse[0]'h0 = c := by
  obtain ⟨hL, hcc⟩ := getLast?_getElem h
  rw [getElem_reverse_col h0 (by omega)]
  exact hcc

theorem reverse_getElem_last {col : Column} {c : Card} (h : col.head? = some c)
    (h1 : col.length - 1 < col.reverse.length) : col.reverse[col.length - 1]'h1 = c := by
  obtain ⟨hL, hcc⟩ := head?_getElem h
  rw [getElem_reverse_col h1 (by omega), ← hcc]
  congr 1
  omega

/-- **The bottom card of a column `removeFlute` empties is a king.**  That is the only
way the recursion reaches `[]`: `nextCard king = none` matches the empty tail. -/
theorem rank_king_of_removeFlute_nil {col : Column} (hrf : removeFlute col = [])
    {c : Card} (hc : col.getLast? = some c) : c.rank = Rank.king := by
  obtain ⟨hL, hcc⟩ := getLast?_getElem hc
  have hr0 : (removeFlute col).length = 0 := by rw [hrf]; rfl
  have hchain := removeFlute_chain col (col.length - 1) (by omega) (by omega)
  rw [show col.length - 1 + 1 = col.length from by omega, List.drop_length, hcc] at hchain
  exact (nextCard_eq_none_iff c).1 hchain

/-- **Such a column is one suit's run**, so its top and bottom cards agree on the
suit. -/
theorem suit_eq_of_pileMatches_zero {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) (hn : n.val = 0) {c d : Card}
    (hc : col.head? = some c) (hd : col.getLast? = some d) : c.suit = d.suit := by
  obtain ⟨su, hrun⟩ := h.king_run hn
  obtain ⟨hL, hcc⟩ := head?_getElem hc
  obtain ⟨-, hdd⟩ := getLast?_getElem hd
  have hlen : col.reverse.length = col.length := by simp
  have h1 : col.length - 1 < col.reverse.length := by rw [hlen]; omega
  have h0 : 0 < col.reverse.length := by rw [hlen]; omega
  obtain ⟨hs1, -⟩ := hrun (col.length - 1) h1
  obtain ⟨hs0, -⟩ := hrun 0 h0
  rw [reverse_getElem_last hc h1] at hs1
  rw [reverse_getElem_zero hd h0] at hs0
  exact suitToNat_inj (suitToNat_eq_of_SUIT (by rw [hs1, hs0]))

/-- **And it is at most a whole suit long**: the run descends from the king by one per
card and never reaches value `0`. -/
theorem PileMatches.length_le_of_zero {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) (hn : n.val = 0) : col.length ≤ 13 := by
  by_contra hlt
  obtain ⟨su, hrun⟩ := h.king_run hn
  have hlen : col.reverse.length = col.length := by simp
  have h1 : col.length - 1 < col.reverse.length := by rw [hlen]; omega
  obtain ⟨-, hv⟩ := hrun (col.length - 1) h1
  rw [encodeCard_VALUE] at hv
  have := rankToNat_pos (col.reverse[col.length - 1]'h1).rank
  omega

/-! ## The `kingBit` bitmap -/

/-- Pile `i` carries suit `su`'s king run: the encoding calls it empty, and its top
card — hence its whole run — is of suit `su`. -/
def IsKingPile (s : State) (su : Suit) (i : Fin 10) : Prop :=
  removeFlute (s.tableau i) = [] ∧ ∃ c, (s.tableau i).head? = some c ∧ c.suit = su

theorem kingBit_of_removeFlute_nil {c1 : Card} {rest : Column}
    (hrf : removeFlute (c1 :: rest) = []) :
    kingBit (c1 :: rest) = 1 <<< UInt8.ofNat (suitToNat c1.suit) := by
  rw [kingBit, suit_idxOf, hrf]
  rfl

theorem kingBit_eq_zero {c1 : Card} {rest : Column} (hrf : ¬ removeFlute (c1 :: rest) = []) :
    kingBit (c1 :: rest) = 0 := by
  rw [kingBit]
  cases hrl : removeFlute (c1 :: rest) with
  | nil => exact absurd hrl hrf
  | cons y ys => rfl

theorem kingBit_testBit (col : Column) (su : Suit) :
    (kingBit col).toNat.testBit (suitToNat su) = true
      ↔ (removeFlute col = [] ∧ ∃ c, col.head? = some c ∧ c.suit = su) := by
  cases col with
  | nil =>
    constructor
    · intro h
      rw [show kingBit ([] : Column) = 0 from rfl] at h
      simp at h
    · rintro ⟨-, c, hc, -⟩
      simp at hc
  | cons c1 rest =>
    by_cases hrf : removeFlute (c1 :: rest) = []
    · rw [kingBit_of_removeFlute_nil hrf]
      simp only [hrf, true_and, List.head?_cons, Option.some.injEq, exists_eq_left']
      cases hs : c1.suit <;> cases hu : su <;> decide
    · rw [kingBit_eq_zero hrf]
      simp [hrf]

theorem kingBitmap_testBit (s : State) (t : Nat) :
    (kingBitmap s).toNat.testBit t = true
      ↔ ∃ i : Fin 10, (kingBit (s.tableau i)).toNat.testBit t = true := by
  unfold kingBitmap
  simp only [Fin.foldl_succ, Fin.foldl_zero, UInt8.toNat_or, Nat.testBit_or, Bool.or_eq_true,
    Fin.exists_fin_succ, show (UInt8.toNat 0) = 0 from rfl, Nat.zero_testBit,
    IsEmpty.exists_iff, false_or, or_false, reduceCtorEq]
  tauto

theorem kingBitmap_testBit_suit (s : State) (su : Suit) :
    (kingBitmap s).toNat.testBit (suitToNat su) = true ↔ ∃ i : Fin 10, IsKingPile s su i := by
  rw [kingBitmap_testBit]
  exact exists_congr (fun i => kingBit_testBit _ su)

theorem mem_of_getLast? {l : List Card} {c : Card} (h : l.getLast? = some c) : c ∈ l := by
  obtain ⟨hL, hcc⟩ := getLast?_getElem h
  exact hcc ▸ List.getElem_mem _

theorem exists_head?_of_pos {col : Column} (hL : 0 < col.length) :
    ∃ c, col.head? = some c := by
  cases col with
  | nil => simp at hL
  | cons x xs => exact ⟨x, rfl⟩

theorem exists_getLast?_of_pos {col : Column} (hL : 0 < col.length) :
    ∃ c, col.getLast? = some c := by
  refine ⟨col[col.length - 1]'(by omega), ?_⟩
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]

namespace SolverSpec

/-! ## The query a state builds -/

theorem pilesKings_get (s : State) (i : Fin 10) :
    (pilesKingsFromState s).get ⟨i.val, by omega⟩ = pileDepth s i := by
  show (Vector.ofFn (fun pile : Fin 11 =>
    if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s))[i.val]'(by omega) = _
  rw [Vector.getElem_ofFn]
  exact dif_pos i.isLt

theorem pilesKings_get10 (s : State) :
    (pilesKingsFromState s).get ⟨10, by omega⟩ = kingBitmap s := by
  show (Vector.ofFn (fun pile : Fin 11 =>
    if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s))[10]'(by omega) = _
  rw [Vector.getElem_ofFn]
  exact dif_neg (by decide)

theorem cvDepths_pilesKings (s : State) (i : Fin 10) :
    (cvDepths (pilesKingsFromState s)).get i = pileDepth s i := by
  rw [cvDepths_get]
  exact pilesKings_get s i

theorem pileDepth_toNat (s : State) (i : Fin 10)
    (h5 : (removeFlute (s.tableau i)).length ≤ 5) :
    (pileDepth s i).toNat = (removeFlute (s.tableau i)).length := by
  unfold pileDepth
  rw [UInt8.toNat_ofNat']
  omega

theorem removeFlute_length_le_five {g : Globals} (hwf : WellFormedLayout g) {s : State}
    (hlayout : StateMatchesLayout g s) (i : Fin 10) :
    (removeFlute (s.tableau i)).length ≤ 5 := by
  obtain ⟨n, hn⟩ := hlayout.piles_match i
  have h1 := removeFlute_length_le_of_pileMatches hwf hn
  have h2 := n.isLt
  omega

/-- **Obligation 1: the depths a state reports are legal.** -/
theorem validDepths_pilesKings {g : Globals} (hwf : WellFormedLayout g) {s : State}
    (hlayout : StateMatchesLayout g s) : ValidDepths (pilesKingsFromState s) := by
  intro i
  rw [pilesKings_get, pileDepth_toNat s i (removeFlute_length_le_five hwf hlayout i)]
  exact removeFlute_length_le_five hwf hlayout i

theorem cvDepths_toNat {g : Globals} (hwf : WellFormedLayout g) {s : State}
    (hlayout : StateMatchesLayout g s) (i : Fin 10) :
    ((cvDepths (pilesKingsFromState s)).get i).toNat = (removeFlute (s.tableau i)).length := by
  rw [cvDepths_pilesKings, pileDepth_toNat s i (removeFlute_length_le_five hwf hlayout i)]

/-- **The reported depths are legal boundaries.** -/
theorem depthMatch_pilesKings {g : Globals} (hwf : WellFormedLayout g) {s : State}
    (hlayout : StateMatchesLayout g s) (i : Fin 10)
    (h6 : ((cvDepths (pilesKingsFromState s)).get i).toNat < 6) :
    PileMatches g (s.tableau i) i ⟨((cvDepths (pilesKingsFromState s)).get i).toNat, h6⟩ := by
  obtain ⟨n, hn⟩ := hlayout.piles_match i
  have hval := cvDepths_toNat hwf hlayout i
  exact PileMatches_of_val_eq (pileMatches_removeFluteDepth hwf hn (by omega)) hval

/-! ## The configuration the encoding names

`kingBitmap` sets bit `su` when a suit owns a pile; `^^^ 0xf` and `bits2grlex` turn that
into the internal reading, where a set bit means the suit has *no* pile.  Both tables are
concrete, so the round trip is decided. -/

/-- `bits2grlex` and `grlex2bits` are inverse tables, so the configuration's own bit is
the bitmask's bit. -/
private theorem cfg_nibble (x : Fin 16) (su : Suit) :
    ¬ CfgBitSet ⟨(bits2grlex.get x).toNat, bits2grlex_lt x⟩ su
      ↔ ¬ (x.val / 2 ^ (suitToNat su) % 2 = 1) := by
  revert su x
  decide

/-- And `^^^ 0xf` flips it. -/
private theorem xor15_bit (n : Nat) (hn : n < 16) (su : Suit) :
    ¬ ((n ^^^ 15) / 2 ^ (suitToNat su) % 2 = 1) ↔ n / 2 ^ (suitToNat su) % 2 = 1 := by
  revert su
  interval_cases n <;> decide

theorem testBit_iff_div_mod (x i : Nat) : x.testBit i = true ↔ x / 2 ^ i % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

/-- **A suit is unpiled by the queried configuration exactly when its bitmap bit is
clear.** -/
theorem cfgBitSet_kingCfgOf (pk : Vector UInt8 11)
    (h10 : (pk.get ⟨10, by omega⟩).toNat < 16) (su : Suit) :
    ¬ CfgBitSet (kingCfgOf pk h10) su
      ↔ (pk.get ⟨10, by omega⟩).toNat.testBit (suitToNat su) = true := by
  have hxlt : ((pk.get ⟨10, by omega⟩) ^^^ 0xf).toNat < 16 := cv_xor_lt16 h10
  have hx15 : (pk.get ⟨10, by omega⟩).toNat ^^^ 15 < 16 :=
    Nat.xor_lt_two_pow (n := 4) h10 (by decide)
  have h1 : kingCfgOf pk h10
      = ⟨(bits2grlex.get ⟨((pk.get ⟨10, by omega⟩) ^^^ 0xf).toNat, hxlt⟩).toNat,
          bits2grlex_lt _⟩ := rfl
  have hidx : (⟨((pk.get ⟨10, by omega⟩) ^^^ 0xf).toNat, hxlt⟩ : Fin 16)
      = ⟨(pk.get ⟨10, by omega⟩).toNat ^^^ 15, hx15⟩ :=
    Fin.ext (show ((pk.get ⟨10, by omega⟩) ^^^ 0xf).toNat
      = (pk.get ⟨10, by omega⟩).toNat ^^^ 15 from by rw [UInt8.toNat_xor]; rfl)
  rw [h1, hidx, cfg_nibble, testBit_iff_div_mod]
  exact xor15_bit _ h10 su

/-! ## The position the encoding describes -/

open Classical in
/-- The length of the column carrying suit `su`'s king run — `0` if no column has that
suit's king at its bottom.  Well defined: a card lies in only one column. -/
noncomputable def kingRunLen (s : State) (su : Suit) : Nat :=
  if h : ∃ i : Fin 10, (s.tableau i).getLast? = some ⟨su, Rank.king⟩ then
    (s.tableau h.choose).length
  else 0

theorem kingRunLen_eq {s : State} (hcount : ∀ c : Card, countState s c = 1) {su : Suit}
    {i : Fin 10} (hi : (s.tableau i).getLast? = some ⟨su, Rank.king⟩) :
    kingRunLen s su = (s.tableau i).length := by
  have hex : ∃ j : Fin 10, (s.tableau j).getLast? = some ⟨su, Rank.king⟩ := ⟨i, hi⟩
  unfold kingRunLen
  rw [dif_pos hex,
    show hex.choose = i from
      column_eq_of_mem hcount (mem_of_getLast? hex.choose_spec) (mem_of_getLast? hi)]

/-- **The position a state's own encoding describes.**  Depths and flutes as the state
carries them, foundations its own, and `kings` the length of each suit's king pile. -/
noncomputable def stateGame (s : State) : SolverPosType where
  hash := 0
  pileDepth := cvDepths (pilesKingsFromState s)
  pileFlute := cvFluteOf s (cvDepths (pilesKingsFromState s))
  aces := Vector.ofFn (fun t : Fin 4 =>
    encodeFoundation (natToSuit t) (s.foundations (natToSuit t)))
  kings := Vector.ofFn (fun t : Fin 4 =>
    CARD (UInt8.ofNat t.val) (UInt8.ofNat (13 - kingRunLen s (natToSuit t))))
  usedSpace := 0
  freePiles := 0
  busyAces := 0

theorem stateGame_aces (s : State) (su : Suit) :
    (stateGame s).aces.get (finOfSuit su) = encodeFoundation su (s.foundations su) := by
  have hnat : natToSuit ⟨(finOfSuit su).val, (finOfSuit su).isLt⟩ = su := natToSuit_suitToNat su
  show (Vector.ofFn (fun t : Fin 4 =>
    encodeFoundation (natToSuit t) (s.foundations (natToSuit t))))[(finOfSuit su).val]'
      (finOfSuit su).isLt = _
  rw [Vector.getElem_ofFn, hnat]

theorem stateGame_kings (s : State) (su : Suit) :
    (VALUE ((stateGame s).kings.get (finOfSuit su))).toNat = 13 - kingRunLen s su := by
  have hnat : natToSuit ⟨(finOfSuit su).val, (finOfSuit su).isLt⟩ = su := natToSuit_suitToNat su
  show (VALUE ((Vector.ofFn (fun t : Fin 4 =>
    CARD (UInt8.ofNat t.val) (UInt8.ofNat (13 - kingRunLen s (natToSuit t)))))[
      (finOfSuit su).val]'(finOfSuit su).isLt)).toNat = _
  rw [Vector.getElem_ofFn, hnat]
  show (VALUE (CARD (UInt8.ofNat (suitToNat su))
    (UInt8.ofNat (13 - kingRunLen s su)))).toNat = _
  rw [VALUE_toNat, cv_card_toNat (show suitToNat su < 4 from suitToNat_lt su) (by omega)]
  omega

/-! ## Obligation 2a -/

/-- **A state matching the layout matches the position its own encoding describes**, at
the configuration its own king bitmap names.  Every clause but the flute one is read off
the layout match (`matchesKingConfig_cvFluteOf` supplies that one), and the
configuration's content is that a column `removeFlute` empties is a king run. -/
theorem exists_cvEntry {g : Globals} (hwf : WellFormedLayout g) {s : State}
    (hlayout : StateMatchesLayout g s)
    (h10 : ((pilesKingsFromState s).get ⟨10, by omega⟩).toNat < 16) :
    ∃ game' : SolverPosType,
      CvEntry g (pilesKingsFromState s) s game'
        (kingCfgOf (pilesKingsFromState s) h10) := by
  classical
  set k := kingCfgOf (pilesKingsFromState s) h10 with hkdef
  have hcount := hlayout.cards_count
  have hval := cvDepths_toNat hwf hlayout
  have hd6 : ∀ i : Fin 10, ((stateGame s).pileDepth.get i).toNat < 6 := by
    intro i
    have h1 := removeFlute_length_le_five hwf hlayout i
    have h2 := hval i
    show ((cvDepths (pilesKingsFromState s)).get i).toNat < 6
    omega
  have hdm : ∀ i : Fin 10, PileMatches g (s.tableau i) i
      ⟨((stateGame s).pileDepth.get i).toNat, hd6 i⟩ := fun i =>
    depthMatch_pilesKings hwf hlayout i (hd6 i)
  -- a pile the encoding calls empty is one `removeFlute` empties
  have hnil : ∀ i : Fin 10, ((stateGame s).pileDepth.get i).toNat = 0 →
      removeFlute (s.tableau i) = [] := by
    intro i h0
    have h2 := hval i
    have h0' : ((cvDepths (pilesKingsFromState s)).get i).toNat = 0 := h0
    cases hrf : removeFlute (s.tableau i) with
    | nil => rfl
    | cons y ys =>
      rw [hrf] at h2
      simp only [List.length_cons] at h2
      omega
  -- and it carries one suit's king run
  have hown : ∀ (i : Fin 10), ((stateGame s).pileDepth.get i).toNat = 0 →
      ∀ c, (s.tableau i).head? = some c →
      ∃ d, (s.tableau i).getLast? = some d ∧ d.suit = c.suit ∧ d.rank = Rank.king := by
    intro i h0 c hc
    have hL : 0 < (s.tableau i).length := by
      cases hcol : s.tableau i with
      | nil => rw [hcol] at hc; simp at hc
      | cons x xs => simp
    obtain ⟨d, hd⟩ := exists_getLast?_of_pos hL
    exact ⟨d, hd, (suit_eq_of_pileMatches_zero (hdm i) h0 hc hd).symm,
      rank_king_of_removeFlute_nil (hnil i h0) hd⟩
  -- `kings` is pinned at the piles that carry a run
  have hking : ∀ i : Fin 10, ((stateGame s).pileDepth.get i).toNat = 0 →
      ∀ c ∈ (s.tableau i).getLast?,
        (s.tableau i).length
          + (VALUE ((stateGame s).kings.get (finOfSuit c.suit))).toNat = 13 := by
    intro i h0 c hc
    have hc' : (s.tableau i).getLast? = some c := hc
    have hrank : c.rank = Rank.king := rank_king_of_removeFlute_nil (hnil i h0) hc'
    have hcard : (⟨c.suit, Rank.king⟩ : Card) = c := by rw [← hrank]
    have hlen13 : (s.tableau i).length ≤ 13 := PileMatches.length_le_of_zero (hdm i) h0
    rw [stateGame_kings, kingRunLen_eq hcount (show (s.tableau i).getLast?
      = some ⟨c.suit, Rank.king⟩ from by rw [hcard]; exact hc')]
    omega
  -- the configuration: bit `su` clear ⟺ some pile carries `su`'s run
  have hassign : ∀ su : Suit, ¬ CfgBitSet k su ↔ ∃ i : Fin 10, IsKingPile s su i := by
    intro su
    rw [hkdef, cfgBitSet_kingCfgOf, pilesKings_get10, kingBitmap_testBit_suit]
  refine ⟨stateGame s, rfl, ?_, ?_⟩
  · refine matchesKingConfig_cvFluteOf hcount hd6 hdm hking (stateGame_aces s) ?_ ?_
    · -- **the configuration is realized**: each piled suit gets the column carrying its run
      refine ⟨fun su => if h : ∃ i : Fin 10, IsKingPile s su i then some h.choose else none,
        ?_, ?_, ?_⟩
      · intro su i hsi
        dsimp only at hsi
        by_cases hex : ∃ j : Fin 10, IsKingPile s su j
        · rw [dif_pos hex] at hsi
          have hieq : hex.choose = i := Option.some.inj hsi
          obtain ⟨hrf, c, hc, hcsu⟩ := hex.choose_spec
          rw [hieq] at hrf hc
          have h0 : ((stateGame s).pileDepth.get i).toNat = 0 := by
            have h2 := hval i
            rw [hrf] at h2
            show ((cvDepths (pilesKingsFromState s)).get i).toNat = 0
            simpa using h2
          obtain ⟨d, hd, hdsu, hdking⟩ := hown i h0 c hc
          exact ⟨h0, Or.inl ⟨d, hd, by rw [hdsu, hcsu], hdking⟩⟩
        · rw [dif_neg hex] at hsi
          exact absurd hsi (by simp)
      · intro su su' i hsi hsi'
        dsimp only at hsi hsi'
        by_cases hex : ∃ j : Fin 10, IsKingPile s su j
        · by_cases hex' : ∃ j : Fin 10, IsKingPile s su' j
          · rw [dif_pos hex] at hsi
            rw [dif_pos hex'] at hsi'
            obtain ⟨-, c, hc, hcsu⟩ := hex.choose_spec
            obtain ⟨-, c', hc', hcsu'⟩ := hex'.choose_spec
            rw [show hex.choose = i from Option.some.inj hsi] at hc
            rw [show hex'.choose = i from Option.some.inj hsi'] at hc'
            rw [← hcsu, ← hcsu', show c = c' from Option.some.inj (hc.symm.trans hc')]
          · rw [dif_neg hex'] at hsi'
            exact absurd hsi' (by simp)
        · rw [dif_neg hex] at hsi
          exact absurd hsi (by simp)
      · intro su
        dsimp only
        by_cases hex : ∃ j : Fin 10, IsKingPile s su j
        · rw [dif_pos hex]
          simp only [Option.isSome_some, true_iff]
          exact (hassign su).2 hex
        · rw [dif_neg hex]
          exact ⟨fun h => absurd h (by simp), fun h => absurd ((hassign su).1 h) hex⟩
    · -- **no other pile carries an unpiled suit**
      intro su hsu i h0 d hd hdsu
      have hd' : (s.tableau i).getLast? = some d := hd
      have hL : 0 < (s.tableau i).length := by
        cases hcol : s.tableau i with
        | nil => rw [hcol] at hd'; simp at hd'
        | cons x xs => simp
      obtain ⟨c, hc⟩ := exists_head?_of_pos hL
      have hcsu : c.suit = su := by
        rw [suit_eq_of_pileMatches_zero (hdm i) h0 hc hd', hdsu]
      exact ((hassign su).2 ⟨i, hnil i h0, c, hc, hcsu⟩) hsu

  · -- **a piled suit's king is not in a cell**: it is sitting in that suit's column
    intro su hsu cell
    obtain ⟨q, hrf, c, hc, hcsu⟩ := (hassign su).1 hsu
    have h0 : ((stateGame s).pileDepth.get q).toNat = 0 := by
      have h2 := hval q
      rw [hrf] at h2
      show ((cvDepths (pilesKingsFromState s)).get q).toNat = 0
      simpa using h2
    obtain ⟨d, hd, hdsu, hdking⟩ := hown q h0 c hc
    have hdk : d = (⟨su, Rank.king⟩ : Card) := Card.ext (by rw [hdsu, hcsu]) hdking
    refine not_mem_cell_of_mem_column hcount (j := q) ?_ cell
    rw [← hdk]
    exact mem_of_getLast? hd

end SolverSpec
