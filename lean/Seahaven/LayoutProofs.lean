import Seahaven.MathlibImports
import Seahaven.Rules
import Seahaven.Solver
import Seahaven.UInt8Lemmas
import Seahaven.CountProofs
-- CountProofs exports @[simp] lemmas for `update` that interfere with proofs here.
attribute [-simp] update_same update_diff update2

/-!
# Layout Consistency and State Matching

This file defines the bridge between the high-level `State` world and
the low-level `Globals` / `UInt8` card-code world used by the solver.

Two layers of properties are developed:

1. **Encoding**: bijection between `Rules.Card` and valid `UInt8` card codes.
   (`IsRealCard` — the image of `encodeCard` — is in `UInt8Lemmas`; well-formedness
   of the `Globals` arrays lives in `SolverInvariant`, as `WellFormedLayout`.)
2. **`StateMatchesLayout`**: a `State` is compatible with a layout,
   meaning the cards in each tableau column correspond to what the layout
   recorded for those positions.
-/

-- ============================================================
-- Section 0: Fintype instances (needed for fin_cases on Card)
-- ============================================================

instance : Fintype Suit :=
  Fintype.ofList [Suit.clubs, Suit.diamonds, Suit.hearts, Suit.spades]
    (fun s => by cases s <;> simp)

instance : Fintype Rank :=
  Fintype.ofList [Rank.ace, Rank.two, Rank.three, Rank.four, Rank.five,
                  Rank.six, Rank.seven, Rank.eight, Rank.nine, Rank.ten,
                  Rank.jack, Rank.queen, Rank.king]
    (fun r => by cases r <;> simp)

/-- `Card` is finite because it is isomorphic to `Suit × Rank`. -/
def cardEquiv : Card ≃ Suit × Rank :=
  ⟨fun c => (c.suit, c.rank), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance : Fintype Card := Fintype.ofEquiv _ cardEquiv.symm

-- ============================================================
-- Section 1: Encoding Cards
-- ============================================================

/-- Convert a `Suit` to its 0-based numeric index (clubs=0, diamonds=1,
    hearts=2, spades=3), matching the solver's suit encoding. -/
def suitToNat (s : Suit) : Nat := allSuits.idxOf s

/-- Convert a 0-based suit index back to a `Suit`. -/
def natToSuit (s : Fin 4) : Suit := allSuits.get s

/-! `suitToNat` is `idxOf`, so unfolding it no longer produces a numeral — `simp`
callers want these four equations instead of the definition. -/

@[simp] theorem suitToNat_clubs : suitToNat Suit.clubs = 0 := rfl
@[simp] theorem suitToNat_diamonds : suitToNat Suit.diamonds = 1 := rfl
@[simp] theorem suitToNat_hearts : suitToNat Suit.hearts = 2 := rfl
@[simp] theorem suitToNat_spades : suitToNat Suit.spades = 3 := rfl

theorem suitToNat_lt (s : Suit) : suitToNat s < 4 := by cases s <;> decide

theorem natToSuit_suitToNat (s : Suit) :
    natToSuit ⟨suitToNat s, suitToNat_lt s⟩ = s :=
  List.idxOf_get (suitToNat_lt s)

/-- The other direction has no generic counterpart — `idxOf (l.get i) = i` needs
`l.Nodup` — so it stays a four-case check. -/
theorem suitToNat_natToSuit (n : Fin 4) :
    suitToNat (natToSuit n) = n.val := by fin_cases n <;> rfl

/-- Encode a `Rules.Card` as the `UInt8` card code used by the solver:
    bits 7-4 = suit index, bits 3-0 = rank (1-13). -/
def encodeCard (c : Card) : UInt8 :=
  CARD (UInt8.ofNat (suitToNat c.suit)) (UInt8.ofNat (rankToNat c.rank))

/-! ### The two nibbles, read back

`encodeCard c` is `suit * 16 + rank` with `suit ≤ 3` and `rank ≤ 13`, so neither
field can carry into the other.  That single fact — `encodeCard_toNat` — is what
every lemma below is `omega` away from. -/

theorem encodeCard_toNat (c : Card) :
    (encodeCard c).toNat = suitToNat c.suit * 16 + rankToNat c.rank :=
  CARD_toNat (by have := suitToNat_lt c.suit; omega) (by have := rankBounded c.rank; omega)

theorem encodeCard_SUIT (c : Card) :
    SUIT (encodeCard c) = UInt8.ofNat (suitToNat c.suit) := by
  have hs : suitToNat c.suit < 4 := suitToNat_lt c.suit
  have hv : rankToNat c.rank ≤ 13 := rankBounded c.rank
  apply UInt8.toNat_inj.mp
  rw [SUIT_toNat, encodeCard_toNat, UInt8.toNat_ofNat']
  omega

theorem encodeCard_VALUE (c : Card) :
    (VALUE (encodeCard c)).toNat = rankToNat c.rank := by
  have hv : rankToNat c.rank ≤ 13 := rankBounded c.rank
  rw [VALUE_toNat, encodeCard_toNat]
  omega

/-- Decode a solver `UInt8` card code back to a `Rules.Card`, returning `none`
    for codes that do not represent a valid card. -/
def decodeCard (code : UInt8) : Option Card :=
  let s := (code >>> 4).toNat
  let v := (code &&& 0xf).toNat
  if hs : s < 4 then
    match natToRank v with
    | some r => some { suit := natToSuit ⟨s, hs⟩, rank := r }
    | none   => none
  else none

theorem encodeCard_real (c : Card) : IsRealCard (encodeCard c) := by
  have hs : suitToNat c.suit < 4 := suitToNat_lt c.suit
  have hv1 : 1 ≤ rankToNat c.rank := by cases c.rank <;> decide
  have hv2 : rankToNat c.rank ≤ 13 := rankBounded c.rank
  have h1 : (SUIT (encodeCard c)).toNat = suitToNat c.suit := by
    rw [SUIT_toNat, encodeCard_toNat]; omega
  have h2 : (VALUE (encodeCard c)).toNat = rankToNat c.rank := encodeCard_VALUE c
  exact ⟨by omega, by omega, by omega⟩

theorem decodeCard_encodeCard (c : Card) : decodeCard (encodeCard c) = some c := by
  have hs : suitToNat c.suit < 4 := suitToNat_lt c.suit
  have hv : rankToNat c.rank ≤ 13 := rankBounded c.rank
  have h1 : ((encodeCard c) >>> 4).toNat = suitToNat c.suit := by
    rw [show ((encodeCard c) >>> 4) = SUIT (encodeCard c) from rfl, SUIT_toNat,
      encodeCard_toNat]
    omega
  have h2 : ((encodeCard c) &&& 0xf).toNat = rankToNat c.rank := encodeCard_VALUE c
  -- both fields round-trip: the rank through `Rules`, the suit through `allSuits`
  have hrank : natToRank (rankToNat c.rank) = some c.rank := rankToNatToRank (some c.rank)
  simp only [decodeCard, h1, h2, dif_pos hs, hrank, natToSuit_suitToNat]

theorem encodeCard_inj {c1 c2 : Card} (h : encodeCard c1 = encodeCard c2) : c1 = c2 := by
  have h1 := decodeCard_encodeCard c1
  have h2 := decodeCard_encodeCard c2
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

-- ============================================================
-- Section 2: Layout Consistency
-- ============================================================

/-!
A `Globals` value is **layout-consistent** if the three arrays `pos2card`,
`card2pile`, and `card2depth` encode the same initial deal without
contradictions.  Concretely:

- `pos2card[p][d]` is the card dealt to pile `p` at depth `d`
  (depth 0 = bottom, depth 4 = top).
- `card2pile[c]` and `card2depth[c]` are the inverse: pile and depth
  where card `c` was originally placed.
- Every valid card appears in exactly one pile position, or is an extra
  card (at deal index 50 or 51) with `card2depth[c] = 5`.
-/

/-- Convenience accessor: the card at position (pile, depth) in the layout. -/
def Globals.pos2cardAt (g : Globals) (p : Fin 10) (d : Fin 5) : UInt8 :=
  (g.pos2card.get p).get d

/-- Convenience accessor: the original pile of a card code (within the 64-entry array). -/
def Globals.pileOf (g : Globals) (code : UInt8) (h : code.toNat < 64) : UInt8 :=
  g.card2pile.get ⟨code.toNat, h⟩

/-- Convenience accessor: the original depth of a card code. -/
def Globals.depthOf (g : Globals) (code : UInt8) (h : code.toNat < 64) : UInt8 :=
  g.card2depth.get ⟨code.toNat, h⟩

-- ============================================================
-- Section 3: State Matches Layout
-- ============================================================

/-!
A `State` **matches** a layout if the cards in each tableau column
are the cards that the layout says were originally dealt there.

Concretely: for each pile `p`, the bottom `n` cards of `state.tableau p`
(reading bottom-up) are `pos2card[p][0], pos2card[p][1], ..., pos2card[p][n-1]`.
The value `n` is the *pile depth* tracked by the solver.

The tableau in `State` is a `List Card` where the **head is the top**
(most accessible) card.  So the bottom card is at index `length - 1`.
The card at depth `d` from the bottom (0 = bottom) is at list index `length - 1 - d`.

We use `List.reverse` so that index 0 in the reversed list corresponds to
depth 0 (the bottom card).
-/

/-- A list of encoded card codes (ordered from deepest/highest-value to
    shallowest/lowest-value) is a **same-suit descending sequence** starting
    at value `startVal`: `cards[i]` has the given `suit` and value `startVal - i`. -/
def IsSameSuitDescending (suit : UInt8) (startVal : Nat) (cards : List UInt8) : Prop :=
  ∀ (i : Fin cards.length),
    SUIT (cards.get i) = suit ∧
    (VALUE (cards.get i)).toNat = startVal - i.val

/-- The bottom `n` entries of column `col` match `pos2card[p][0..n-1]`,
    and the remaining (flute) cards form a same-suit descending sequence
    connected to the boundary card.

    Orientation: `col` has head = top (most accessible card), last = bottom.
    `col.reverse` has index 0 = bottom, so `col.reverse[k]` is the card at
    depth `k` from the bottom.

    The flute portion is `col.reverse.drop n.val` (everything above the
    pile-bottom section), encoded as UInt8.

    - If `n > 0`: the flute continues from the boundary card `pos2card[p][n-1]`
      with the same suit and values decreasing from `VALUE(boundary) - 1`.
    - If `n = 0`: the entire column (if non-empty) is a same-suit descending
      sequence starting with KING (value 13) at the deepest position. -/
def PileMatches (g : Globals) (col : Column) (p : Fin 10) (n : Fin 6) : Prop :=
  n.val ≤ col.length ∧
  -- The bottom n cards match pos2card[p][0..n-1].
  -- Use get? to avoid an inline bound proof (the bound follows from the first conjunct + k.isLt).
  (∀ (k : Fin n.val),
    (col.reverse[k.val]?).map encodeCard =
    some ((g.pos2card.get p).get ⟨k.val, by omega⟩)) ∧
  -- The flute portion is a same-suit descending sequence.
  let fluteCards := (col.reverse.drop n.val).map encodeCard
  if h : n.val > 0 then
    -- Flute continues from the boundary card pos2card[p][n-1].
    let boundary := (g.pos2card.get p).get ⟨n.val - 1, by omega⟩
    IsSameSuitDescending (SUIT boundary) ((VALUE boundary).toNat - 1) fluteCards
  else
    -- n = 0: whole column is a king-sequence (or empty).
    ∃ suit : UInt8, IsSameSuitDescending suit 13 fluteCards

/-- `state` is consistent with layout `g`: each pile's bottom cards are those
    recorded in `pos2card`, each cell holds a valid card, and every valid card
    appears exactly once across the tableau, cells, and foundation. -/
structure StateMatchesLayout (g : Globals) (s : State) : Prop where

  /-- For each pile, the bottom `n` cards match the layout (for some `n`). -/
  piles_match : ∀ (p : Fin 10),
      ∃ (n : Fin 6), PileMatches g (s.tableau p) p n

  /-- Every card appears exactly once across foundation, cells, and tableau. -/
  cards_count : ∀ (c : Card), countState s c = 1

-- ============================================================
-- Section 4: Key Lemmas Relating the Two Predicates
-- ============================================================

/-- If a card's original pile depth `d` is less than the pile's current depth `n`,
    the card is still in the pile at the correct position. -/
theorem StateMatchesLayout.card_in_pile
    {g : Globals} {s : State}
    (p : Fin 10) (d : Fin 5)
    (hn : ∃ n : Fin 6, PileMatches g (s.tableau p) p n ∧ d.val < n.val) :
    ∃ (pos : Fin (s.tableau p).length),
        encodeCard ((s.tableau p).get pos) = g.pos2cardAt p d := by
  obtain ⟨n, ⟨hlen, hmatch, _⟩, hd⟩ := hn
  have hlen_pos : 0 < (s.tableau p).length := by omega
  have hk : d.val < (s.tableau p).length := by omega
  -- Extract the element from hmatch using the d-th index
  have h_opt := hmatch ⟨d.val, hd⟩
  -- h_opt : (s.tableau p).reverse[d.val]?.map encodeCard = some (g.pos2cardAt p d)
  -- Since d.val < (s.tableau p).reverse.length = (s.tableau p).length, get? returns some
  have hk_rev : d.val < (s.tableau p).reverse.length := by simp [List.length_reverse]; omega
  rw [List.getElem?_eq_getElem hk_rev, Option.map_some] at h_opt
  -- h_opt : encodeCard (s.tableau p).reverse[d.val] = g.pos2cardAt p d
  -- The d-th element of reverse = the (length-1-d)-th element forwards
  refine ⟨⟨(s.tableau p).length - 1 - d.val, by omega⟩, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_reverse hk_rev] at h_opt
  -- h_opt : some (encodeCard l[length-1-d]) = some (pos2cardAt p d)
  simp only [Globals.pos2cardAt]
  exact Option.some.inj h_opt

-- ============================================================
-- Section 5: Preservation Under Rules Moves
-- ============================================================


/-- Applying a valid `Rules.Move` to a state that matches the layout yields
    a state that still matches the layout.

    A move takes a card from a source position (`pile`, `cell`) and places it
    at a destination position (`pile`, `cell`, `foundation`).  The bottom
    portion of every column recorded in `pos2card` is unchanged by moves —
    only the flute (the top same-suit descending run) grows or shrinks — so
    `PileMatches` is preserved for all piles, and the partition of all 52 cards
    across foundation, cells, and tableau is maintained. -/
-- ---- Helper: removing the top card of a non-empty column gives a column
-- that still satisfies PileMatches, possibly with a smaller n.
--
-- Two cases arise depending on which card is on top:
--   col.length > n  (a flute card is on top)  → same n
--   col.length = n  (the boundary card is on top, flute is trivial) → n decreases by 1
--
-- The result is stated existentially to cover both cases uniformly.
lemma PileMatches_tail
    {g : Globals} {col : Column} {p : Fin 10} {n : Fin 6}
    (hm : PileMatches g col p n)
    (hne : 0 < col.length) :
    ∃ n' : Fin 6, n'.val ≤ n.val ∧ PileMatches g col.tail p n' := by
  obtain ⟨hlen, hbot, hflute⟩ := hm
  -- Key rewriting: col.tail.reverse = col.reverse.dropLast
  have h_rev : col.tail.reverse = col.reverse.dropLast := List.dropLast_reverse.symm
  by_cases hgt : col.length > n.val
  · -- The top card is in the flute; n stays the same.
    refine ⟨n, le_refl _, ?_, ?_, ?_⟩
    · -- length: col.tail.length = col.length - 1 ≥ n
      simp [List.length_tail]; omega
    · -- bottom n cards unchanged
      intro k
      have hk_lt : k.val < col.reverse.length - 1 := by
        simp [List.length_reverse]; omega
      rw [h_rev, List.getElem?_dropLast, if_pos hk_lt]
      exact hbot k
    · -- flute: (col.tail.reverse.drop n).map encodeCard = (fluteCards).dropLast
      -- which still satisfies IsSameSuitDescending
      simp only [h_rev]
      rw [show (col.reverse.dropLast).drop n.val = (col.reverse.drop n.val).dropLast from by
        simp [List.dropLast_eq_take, List.drop_take]; omega]
      rw [List.map_dropLast]
      -- hflute : flute condition for col; apply dropLast to get condition for col.tail
      -- Helper to transfer IsSameSuitDescending through dropLast
      have transfer : ∀ {suit sv} {cards : List UInt8},
          IsSameSuitDescending suit sv cards →
          IsSameSuitDescending suit sv cards.dropLast := fun {_ _} {cards} h i => by
        have hlen : cards.dropLast.length = cards.length - 1 := List.length_dropLast
        have h' := h ⟨i.val, by omega⟩
        simp only [List.get_eq_getElem, List.getElem_dropLast] at h' ⊢
        exact h'
      split_ifs with hn
      · -- n > 0: extract from dif, apply transfer
        simp only [dif_pos hn] at hflute
        exact transfer hflute
      · -- n = 0: king-sequence
        simp only [dif_neg hn] at hflute
        obtain ⟨suit, hf⟩ := hflute
        exact ⟨suit, transfer hf⟩
  · -- The top card is the boundary card (col.length = n); n decreases by 1.
    have heq : col.length = n.val := by omega
    have hn_pos : 0 < n.val := by omega
    have h_rev : col.tail.reverse = col.reverse.dropLast := List.dropLast_reverse.symm
    refine ⟨⟨n.val - 1, by omega⟩, by simp, ?_, ?_, ?_⟩
    · -- length: col.tail.length = n.val - 1
      simp [List.length_tail, heq]
    · -- bottom n-1 cards unchanged (they all have index < n-1 < n.val - 1 in col.reverse)
      intro k
      have hk_lt : k.val < col.reverse.length - 1 := by
        simp [List.length_reverse, heq]
      have hk_n : k.val < n.val :=
        Nat.lt_trans k.isLt (Nat.sub_lt hn_pos Nat.one_pos)
      rw [h_rev, List.getElem?_dropLast, if_pos hk_lt]
      exact hbot ⟨k.val, hk_n⟩
    · -- flute: col.tail.reverse has length n-1, so dropping n-1 gives []
      have h_empty : col.tail.reverse.drop (n.val - 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        simp [List.length_reverse, List.length_tail, heq]
      simp only [h_empty, List.map_nil]
      -- IsSameSuitDescending ... [] is vacuously true in both branches
      split_ifs
      · exact fun i => i.elim0
      · exact ⟨0, fun i => i.elim0⟩

-- nextCard preserves suit; rank increases by 1
lemma nextCard_suit {c top : Card} (h : nextCard c = some top) :
    top.suit = c.suit := by
  simp [nextCard] at h; split at h <;> simp_all [Card.ext_iff]

lemma nextCard_rank {c top : Card} (h : nextCard c = some top) :
    rankToNat top.rank = rankToNat c.rank + 1 := by
  simp [nextCard, nextRank] at h
  split at h <;> [simp at h; rename_i r hr]
  have hinjr : top.rank = r := by have := Option.some.inj h; simp [Card.ext_iff] at this; exact this.2.symm
  rw [hinjr]; exact nextRankNat (some c.rank) r (by simpa [optRankToNat, nextRank])

-- nextCard c = none means c is a king (rank 13)
lemma nextCard_none_rank {c : Card} (h : nextCard c = none) :
    rankToNat c.rank = 13 := by
  obtain ⟨suit, rank⟩ := c
  simp[nextCard] at h
  rcases h_eq: nextRank (some rank) with _ | r
  · cases rank <;> simp[nextRank,optRankToNat,rankToNat,natToRank] at h_eq
    simp[rankToNat]
  · simp[h_eq] at h

-- ---- Extend IsSameSuitDescending by appending one element
lemma IsSameSuitDescending_snoc
    {suit : UInt8} {sv : Nat} {cards : List UInt8} {c : UInt8}
    (h : IsSameSuitDescending suit sv cards)
    (hsuit : SUIT c = suit)
    (hval : (VALUE c).toNat = sv - cards.length) :
    IsSameSuitDescending suit sv (cards ++ [c]) := by
  intro ⟨i, hi⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < cards.length
  · have := h ⟨i, hlt⟩
    simp only [List.get_eq_getElem, List.getElem_append_left hlt]
    exact this
  · have heq : i = cards.length := by omega
    subst heq
    simp only [List.get_eq_getElem, List.getElem_append_right (le_refl _),
               Nat.sub_self, List.getElem_cons_zero]
    exact ⟨hsuit, hval⟩

-- ---- Helper: adding a card on top preserves PileMatches (with same n)
-- when the card continues the flute's descending sequence.
-- hcont uses the exact dropCol guard: col.head? = nextCard card.
-- When col = [], this requires nextCard card = none, i.e. card is a king.
-- When col ≠ [], it requires the current top to be the card one rank above card.
lemma PileMatches_cons
    {g : Globals} {col : Column} {p : Fin 10} {n : Fin 6} {card : Card}
    (hm : PileMatches g col p n)
    (hcont : col.head? = nextCard card) :
    PileMatches g (card :: col) p n := by
  obtain ⟨hlen, hbot, hflute⟩ := hm
  refine ⟨by simp; omega, ?_, ?_⟩
  · -- Bottom n cards unchanged: (card :: col).reverse = col.reverse ++ [card],
    -- and for k < n, k < col.reverse.length, so the ++ [card] suffix is invisible.
    intro k
    have hk : k.val < col.reverse.length := by simp [List.length_reverse]; omega
    simp only [List.reverse_cons, List.getElem?_append_left hk]
    exact hbot k
  · -- Flute condition.  New reverse = col.reverse ++ [card]; dropping n yields
    -- (col.reverse.drop n) ++ [card], so new fluteCards = old fluteCards ++ [encodeCard card].
    simp only
    rw [show (card :: col).reverse = col.reverse ++ [card] from List.reverse_cons ..]
    rw [List.drop_append_of_le_length (by simp [List.length_reverse]; omega)]
    rw [List.map_append, List.map_singleton]
    have hm_len : ((col.reverse.drop n.val).map encodeCard).length = col.length - n.val := by
      simp [List.length_drop, List.length_reverse]
    split_ifs with hn
    · -- Case n > 0: flute continues from the boundary card pos2card[p][n-1].
      simp only [dif_pos hn] at hflute
      -- col ≠ [] because col.length ≥ n ≥ 1.  Destructure to name the head `top`.
      have hne : col ≠ [] := List.ne_nil_of_length_pos (by omega)
      obtain ⟨top, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.head?] at hcont
      have hcont' : nextCard card = some top := hcont.symm
      -- Suit/rank correspondence between card and top.
      have hsuit_eq : top.suit = card.suit   := nextCard_suit hcont'
      have hrank_eq : rankToNat top.rank = rankToNat card.rank + 1 := nextCard_rank hcont'
      -- Derived encoding equalities.
      have hSUIT : SUIT (encodeCard card) = SUIT (encodeCard top) := by
        simp [encodeCard_SUIT, hsuit_eq]
      have hVALUE : (VALUE (encodeCard card)).toNat + 1 = (VALUE (encodeCard top)).toNat := by
        simp [encodeCard_VALUE, hrank_eq]
      set boundary := (g.pos2card.get p).get ⟨n.val - 1, by omega⟩
      -- Helper: the (n-1)-th element of (top :: rest).reverse is `top` when
      -- rest.length = n - 1 (i.e. the old flute is empty and top IS the boundary card).
      have hrev_last_eq_top : ∀ hm0 : (top :: rest).length = n.val,
          (top :: rest).reverse[n.val - 1]? = some top := fun hm0 => by
        rw [show (top :: rest).reverse = rest.reverse ++ [top] from List.reverse_cons ..]
        have hlen_rest : rest.length = n.val - 1 := by simp at hm0; omega
        -- reindex: n-1 = rest.reverse.length, so the append suffix is at index 0
        have hkey : n.val - 1 = rest.reverse.length := by simp [List.length_reverse, hlen_rest]
        rw [hkey, List.getElem?_append_right (le_refl _), Nat.sub_self]
        simp
      -- Helper for nonempty-flute branches: the last element of the mapped old flute is encodeCard top.
      -- We state this with getElem? (no bound argument) to avoid dependent-motive issues in rw.
      -- Proof: drop n from (rest.reverse ++ [top]) gives (rest.reverse.drop n) ++ [top];
      --        its last position (index rest.length - n) is the singleton [top].
      have hlast_is_top : ∀ hn_le : n.val ≤ rest.length,
          (((top :: rest).reverse.drop n.val).map encodeCard)[rest.length - n.val]? =
          some (encodeCard top) := fun hn_le => by
        -- (top :: rest).reverse = rest.reverse ++ [top]
        -- drop n from that = rest.reverse.drop n ++ [top]
        have hlist_eq : (top :: rest).reverse.drop n.val = rest.reverse.drop n.val ++ [top] := by
          rw [List.reverse_cons, List.drop_append_of_le_length (by simp [List.length_reverse]; omega)]
        simp only [hlist_eq, List.map_append, List.map_singleton]
        -- (map …).length at the split point
        have hlen_d : (List.map encodeCard (rest.reverse.drop n.val)).length = rest.length - n.val := by
          simp [List.length_drop, List.length_reverse]
        -- index rest.length - n.val into (A ++ [encodeCard top]) lands in the singleton
        rw [List.getElem?_append_right (by omega), hlen_d, Nat.sub_self]
        simp
      -- Shared helper for the nonempty-flute sub-case:
      -- rewrite hflute to the concrete form A ++ [encodeCard top], then index directly.
      -- The ▸ motive (fun x => IsSameSuitDescending … x) is type-correct, so no motive issues.
      have hnonempty_facts : (top :: rest).length ≠ n.val →
          SUIT (encodeCard top) = SUIT boundary ∧
          (VALUE (encodeCard top)).toNat = (VALUE boundary).toNat - 1 - (rest.length - n.val) := by
        intro hm0
        have hn_le : n.val ≤ rest.length := by simp only [List.length_cons] at hlen hm0; omega
        -- (top :: rest).reverse.drop n = rest.reverse.drop n ++ [top]
        have hflute_eq : (((top :: rest).reverse.drop n.val).map encodeCard) =
            (rest.reverse.drop n.val).map encodeCard ++ [encodeCard top] := by
          rw [show (top :: rest).reverse.drop n.val = rest.reverse.drop n.val ++ [top] from by
            rw [List.reverse_cons, List.drop_append_of_le_length (by simp [List.length_reverse]; omega)]]
          simp [List.map_append]
        -- Inline A to avoid set-opacity issues with simp.
        have hA_len : ((rest.reverse.drop n.val).map encodeCard).length = rest.length - n.val := by
          simp [List.length_drop, List.length_reverse]
        have hfidx : rest.length - n.val <
            ((rest.reverse.drop n.val).map encodeCard ++ [encodeCard top]).length := by
          simp
        -- Apply hflute (rewritten via ▸) at index A.length.
        have h_pair := (hflute_eq ▸ hflute) ⟨rest.length - n.val, hfidx⟩
        -- Reduce getElem on (A ++ [encodeCard top]) at index A.length to encodeCard top.
        -- Motive is (fun x => x = encodeCard top): type-correct, no dependency issues.
        have h_last :
            ((rest.reverse.drop n.val).map encodeCard ++ [encodeCard top])[rest.length - n.val]'hfidx =
            encodeCard top := by
          rw [List.getElem_append_right (by omega)]
          simp
        simp only [List.get_eq_getElem, h_last] at h_pair
        exact ⟨h_pair.1, h_pair.2⟩
      -- Establish SUIT (encodeCard card) = SUIT boundary.
      have hSUIT_card : SUIT (encodeCard card) = SUIT boundary := by
        rw [hSUIT]
        by_cases hm0 : (top :: rest).length = n.val
        · -- Flute empty: top IS the boundary card.
          have htop_boundary : encodeCard top = boundary := by
            have hk := hbot ⟨n.val - 1, by omega⟩
            simp only at hk
            rw [hrev_last_eq_top hm0, Option.map_some] at hk
            exact Option.some.inj hk
          rw [htop_boundary]
        · exact (hnonempty_facts hm0).1
      -- Establish VALUE (encodeCard card).toNat = startVal - m.
      have hVALUE_card :
          (VALUE (encodeCard card)).toNat =
          (VALUE boundary).toNat - 1 - (rest.length + 1 - n.val) := by
        by_cases hm0 : (top :: rest).length = n.val
        · -- Flute empty: top = boundary, m = 0.
          have htop_boundary : encodeCard top = boundary := by
            have hk := hbot ⟨n.val - 1, by omega⟩
            simp only at hk
            rw [hrev_last_eq_top hm0, Option.map_some] at hk
            exact Option.some.inj hk
          have hm_zero : (top :: rest).length - n.val = 0 := by omega
          simp only [List.length_cons] at hm_zero
          have : (VALUE (encodeCard top)).toNat = (VALUE boundary).toNat := by rw [htop_boundary]
          omega
        · have := (hnonempty_facts hm0).2
          simp only [List.length_cons] at hlen hm0
          omega
      -- Apply IsSameSuitDescending_snoc using the proved facts.
      exact IsSameSuitDescending_snoc hflute hSUIT_card (by simp; omega)
    · -- Case n = 0: whole column is a king-sequence (or empty).
      simp only [dif_neg hn] at hflute
      have hn0 : (↑n : ℕ) = 0 := by omega
      simp only [hn0, List.drop_zero] at hflute ⊢
      -- Goal: ∃ suit, IsSameSuitDescending suit 13 (col.reverse.map encodeCard ++ [encodeCard card])
      -- hflute: ∃ suit, IsSameSuitDescending suit 13 (col.reverse.map encodeCard)
      rcases col with _ | ⟨top, rest⟩
      · -- col = []: card must be a king.
        simp only [List.head?] at hcont
        have hking_rank : rankToNat card.rank = 13 := nextCard_none_rank hcont.symm
        simp only [List.reverse_nil, List.map_nil, List.nil_append]
        refine ⟨SUIT (encodeCard card), fun ⟨i, hi⟩ => ?_⟩
        simp only [List.length_singleton] at hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [List.get_eq_getElem, encodeCard_VALUE, hking_rank]
      · -- col = top :: rest: extend via IsSameSuitDescending_snoc.
        simp only [List.head?] at hcont
        have hcont' : nextCard card = some top := hcont.symm
        have hsuit_eq : top.suit = card.suit := nextCard_suit hcont'
        have hrank_eq : rankToNat top.rank = rankToNat card.rank + 1 := nextCard_rank hcont'
        have hSUIT : SUIT (encodeCard card) = SUIT (encodeCard top) := by
          simp [encodeCard_SUIT, hsuit_eq]
        have hVALUE : (VALUE (encodeCard card)).toNat + 1 = (VALUE (encodeCard top)).toNat := by
          simp [encodeCard_VALUE, hrank_eq]
        obtain ⟨suit, hflute_suit⟩ := hflute
        -- Rewrite old flute as rest.reverse.map encodeCard ++ [encodeCard top].
        have hflute_eq : ((top :: rest).reverse.map encodeCard) =
            rest.reverse.map encodeCard ++ [encodeCard top] := by
          simp [List.reverse_cons, List.map_append]
        have hlen_A : (rest.reverse.map encodeCard).length = rest.length := by
          simp [List.length_reverse]
        have hfidx : rest.length < (rest.reverse.map encodeCard ++ [encodeCard top]).length := by
          simp
        -- Apply hflute_suit (via ▸) at the last index to get suit and value for encodeCard top.
        have h_pair := (hflute_eq ▸ hflute_suit) ⟨rest.length, hfidx⟩
        have h_last : (rest.reverse.map encodeCard ++ [encodeCard top])[rest.length]'hfidx =
            encodeCard top := by
          rw [List.getElem_append_right (by omega)]
          simp
        simp only [List.get_eq_getElem, h_last] at h_pair
        -- h_pair : SUIT (encodeCard top) = suit ∧ (VALUE (encodeCard top)).toNat = 13 - rest.length
        refine ⟨suit, IsSameSuitDescending_snoc hflute_suit ?_ ?_⟩
        · rw [hSUIT]; exact h_pair.1
        · simp only [List.length_map, List.length_reverse, List.length_cons]; omega

theorem StateMatchesLayout.applyMove
    {g : Globals} {s s' : State} {m : Move}
    (hs : StateMatchesLayout g s)
    (hm : applyMove s m = some s') :
    StateMatchesLayout g s' := by
  -- Extract the moved card and the intermediate state after the take.
  have h_step : ∃ card s1,
      takeFromPosition s m.src = some (card, s1) ∧
      dropPosition s1 m.dest card = some s' := by
    rcases h_tf : takeFromPosition s m.src with _ | ⟨card, s1⟩
    · simp [_root_.applyMove, h_tf] at hm
    · -- rcases substituted takeFromPosition s m.src ↦ some (card, s1) in the goal;
      -- first conjunct is rfl. Rewrite hm to extract dropPosition.
      unfold _root_.applyMove at hm
      rw [h_tf] at hm   -- match some (card,s1) reduces
      exact Exists.intro card (Exists.intro s1 ⟨rfl, hm⟩)
  obtain ⟨card, s1, h_take, h_drop⟩ := h_step
  -- Characterize the tableau/cells of s1 based on the source.
  have h_s1_piles : ∀ q : Fin 10, s1.tableau q =
      match m.src with
      | Position.pile p => if p = q then (s.tableau q).tail else s.tableau q
      | _               => s.tableau q := by
    rcases h_src : m.src with p | c | _
    · -- source is a pile: specialize h_take then unpack it
      rw [h_src] at h_take
      simp only [takeFromPosition, takeFromCol] at h_take
      rcases h_col : s.tableau p with _ | ⟨top, rest⟩
      · simp [h_col] at h_take
      · rw [h_col] at h_take
        simp only [Option.some.injEq, Prod.mk.injEq] at h_take
        obtain ⟨rfl, rfl⟩ := h_take
        intro q; simp [updateColumn, update]
        split_ifs with h
        · subst h; simp [h_col]
        · rfl
    · -- source is a cell: tableau unchanged
      rw [h_src] at h_take
      simp only [takeFromPosition, takeFromCell] at h_take
      split at h_take
      · simp at h_take
      · simp only [Option.some.injEq, Prod.mk.injEq] at h_take
        obtain ⟨rfl, rfl⟩ := h_take; intro q; rfl
    · -- source is foundation: h_take is a contradiction
      simp [h_src, takeFromPosition] at h_take
  -- Characterize the tableau/cells of s' based on the destination.
  have h_s'_piles : ∀ q : Fin 10, s'.tableau q =
      match m.dest with
      | Position.pile p => if p = q then card :: s1.tableau q else s1.tableau q
      | _               => s1.tableau q := by
    rcases h_dest : m.dest with p | c | _
    · -- dest is a pile
      rw [h_dest] at h_drop
      simp only [dropPosition, dropCol] at h_drop
      split_ifs at h_drop with h
      · simp only [Option.some.injEq] at h_drop
        rw [← h_drop]
        intro q; simp [updateColumn, update]
        split_ifs with h2
        · subst h2; rfl
        · rfl
    · -- dest is a cell: tableau unchanged (updateCell doesn't touch tableau)
      rw [h_dest] at h_drop
      simp [dropPosition, dropCell] at h_drop
      obtain ⟨_, rfl⟩ := h_drop
      intro q; rfl
    · -- dest is foundation: use split_ifs
      rw [h_dest] at h_drop
      simp only [dropPosition, dropFoundation] at h_drop
      split_ifs at h_drop with h
      · simp only [Option.some.injEq] at h_drop; rw [← h_drop]; intro q; rfl
  constructor
  · -- piles_match: prove in two independent steps.
    -- Step 1: taking from src preserves PileMatches (only the src pile changes).
    have h_take_piles : ∀ q : Fin 10, ∃ n, PileMatches g (s1.tableau q) q n := by
      intro q
      obtain ⟨n, hn⟩ := hs.piles_match q
      rw [h_s1_piles q]
      rcases h_src2 : m.src with src | _ | _
      · -- pile source: src pile loses its top; all other piles unchanged
        by_cases h : src = q
        · simp [h]
          obtain ⟨n', _, hn'⟩ := PileMatches_tail hn (by
            subst h  -- now src = q is gone; use src everywhere
            apply List.length_pos_iff_ne_nil.mpr
            intro hnil
            rw [h_src2, takeFromPosition] at h_take
            simp [takeFromCol, hnil] at h_take)
          exact ⟨n', hn'⟩
        · simp [h]; exact ⟨n, hn⟩
      · -- cell source: no pile changes
        exact ⟨n, hn⟩
      · -- foundation source: contradiction from h_take
        simp [h_src2, takeFromPosition] at h_take
    -- Step 2: dropping to dst preserves PileMatches (only the dst pile changes).
    intro q
    obtain ⟨n, hn⟩ := h_take_piles q
    rw [h_s'_piles q]
    rcases h_dest : m.dest with dst | c | _
    · -- pile dest: dst pile gains card on top; all other piles unchanged
      by_cases h : dst = q
      · simp [h]
        simp[dropPosition,h_dest,dropCol,h] at h_drop
        obtain⟨headcard,_⟩ := h_drop
        exact ⟨n, PileMatches_cons hn headcard⟩
      · simp [h]; exact ⟨n, hn⟩
    · -- cell dest: no pile changes
      exact ⟨n, hn⟩
    · -- foundation dest: no pile changes
      exact ⟨n, hn⟩
  · -- cards_count: preserved by movePreservesCards
    intro c
    have hpres := congrFun (movePreservesCards s m s' hm) c
    rw [← hpres]; exact hs.cards_count c
