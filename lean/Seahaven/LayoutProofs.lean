import Seahaven.Rules
import Seahaven.Solver

/-!
# Layout Consistency and State Matching

This file defines the bridge between the high-level `Rules.State` world and
the low-level `Globals` / `UInt8` card-code world used by the solver.

Three layers of properties are developed:

1. **Encoding**: bijection between `Rules.Card` and valid `UInt8` card codes.
2. **`LayoutConsistent`**: the `Globals` arrays `pos2card`, `card2pile`,
   `card2depth` are mutually consistent (they encode a valid initial deal).
3. **`StateMatchesLayout`**: a `Rules.State` is compatible with a layout,
   meaning the cards in each tableau column correspond to what the layout
   recorded for those positions.
-/

-- ============================================================
-- Section 1: Encoding Cards
-- ============================================================

/-- Convert a `Suit` to its 0-based numeric index (clubs=0, diamonds=1,
    hearts=2, spades=3), matching the solver's suit encoding. -/
def suitToNat : Suit → Nat
  | Suit.clubs    => 0
  | Suit.diamonds => 1
  | Suit.hearts   => 2
  | Suit.spades   => 3

/-- Convert a 0-based suit index back to a `Suit`. -/
def natToSuit : Fin 4 → Suit
  | ⟨0, _⟩ => Suit.clubs
  | ⟨1, _⟩ => Suit.diamonds
  | ⟨2, _⟩ => Suit.hearts
  | ⟨3, _⟩ => Suit.spades

theorem suitToNat_lt (s : Suit) : suitToNat s < 4 := by cases s <;> simp [suitToNat]

theorem natToSuit_suitToNat (s : Suit) :
    natToSuit ⟨suitToNat s, suitToNat_lt s⟩ = s := by cases s <;> simp [suitToNat, natToSuit]

theorem suitToNat_natToSuit (n : Fin 4) :
    suitToNat (natToSuit n) = n.val := by fin_cases n <;> simp [natToSuit, suitToNat]

/-- Encode a `Rules.Card` as the `UInt8` card code used by the solver:
    bits 7-4 = suit index, bits 3-0 = rank (1-13). -/
def encodeCard (c : Card) : UInt8 :=
  CARD (UInt8.ofNat (suitToNat c.suit)) (UInt8.ofNat (rankToNat c.rank))

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

/-- A `UInt8` code is a **valid card** if its high nibble is a suit (0-3)
    and its low nibble is a rank value (1-13). -/
def IsValidCard (code : UInt8) : Prop :=
  (code >>> 4).toNat < 4 ∧
  1 ≤ (code &&& 0xf).toNat ∧ (code &&& 0xf).toNat ≤ 13

theorem encodeCard_valid (c : Card) : IsValidCard (encodeCard c) := by
  simp [IsValidCard, encodeCard, CARD, SUIT, VALUE, suitToNat_lt]
  constructor
  · omega
  exact ⟨by have := rankBounded c.rank; omega, by exact rankBounded c.rank⟩

/-- Valid card codes fit in the 64-entry lookup arrays. -/
theorem IsValidCard_lt64 {code : UInt8} (h : IsValidCard code) : code.toNat < 64 := by
  obtain ⟨hs, hv_lo, hv_hi⟩ := h
  have : code.toNat = (code >>> 4).toNat * 16 + (code &&& 0xf).toNat := by
    simp [UInt8.toNat_shiftRight, UInt8.toNat_and]
    omega
  omega

theorem decodeCard_encodeCard (c : Card) : decodeCard (encodeCard c) = some c := by
  simp [decodeCard, encodeCard, CARD, SUIT, VALUE, suitToNat_lt, suitToNat_natToSuit]
  constructor
  · exact suitToNat_lt c.suit
  · rw [natToSuit_suitToNat, rankToNatToRank]

theorem encodeCard_inj {c1 c2 : Card} (h : encodeCard c1 = encodeCard c2) : c1 = c2 := by
  have := decodeCard_encodeCard c1
  have := decodeCard_encodeCard c2
  simp [h] at *
  exact this.symm.trans ‹_›

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

structure LayoutConsistent (g : Globals) : Prop where

  /-- Every entry in `pos2card` is a valid card code. -/
  pos2card_valid : ∀ (p : Fin 10) (d : Fin 5),
      IsValidCard (g.pos2cardAt p d)

  /-- `card2pile` is the left inverse of `pos2card`'s pile index:
      the pile stored for a card equals the pile it was placed in. -/
  card2pile_eq : ∀ (p : Fin 10) (d : Fin 5),
      let code := g.pos2cardAt p d
      have hlt : code.toNat < 64 := IsValidCard_lt64 (g.pos2card_valid p d)
      (g.pileOf code hlt).toNat = p.val

  /-- `card2depth` is the left inverse of `pos2card`'s depth index. -/
  card2depth_eq : ∀ (p : Fin 10) (d : Fin 5),
      let code := g.pos2cardAt p d
      have hlt : code.toNat < 64 := IsValidCard_lt64 (g.pos2card_valid p d)
      (g.depthOf code hlt).toNat = d.val

  /-- `pos2card` is injective: distinct positions hold distinct cards. -/
  pos2card_inj : ∀ (p1 p2 : Fin 10) (d1 d2 : Fin 5),
      g.pos2cardAt p1 d1 = g.pos2cardAt p2 d2 → p1 = p2 ∧ d1 = d2

  /-- Every valid card is either in some pile position or is an extra card
      (not placed in any pile), identified by `card2depth[c] = 5`. -/
  card_coverage : ∀ (code : UInt8) (hv : IsValidCard code),
      (∃ (p : Fin 10) (d : Fin 5), g.pos2cardAt p d = code) ∨
      (g.depthOf code (IsValidCard_lt64 hv)).toNat = 5

/-- A consequence: the round-trip `pos2card[card2pile[c]][card2depth[c]] = c`
    holds for cards that appear in the pile layout. -/
theorem LayoutConsistent.pos2card_roundtrip
    {g : Globals} (hg : LayoutConsistent g)
    (p : Fin 10) (d : Fin 5) :
    let code := g.pos2cardAt p d
    have hlt := IsValidCard_lt64 (hg.pos2card_valid p d)
    g.pos2cardAt
      ⟨(g.pileOf code hlt).toNat, by
        have := hg.card2pile_eq p d; simp at this; omega⟩
      ⟨(g.depthOf code hlt).toNat, by
        have := hg.card2depth_eq p d; simp at this; omega⟩
    = code := by
  intro code hlt
  have hp := hg.card2pile_eq p d
  have hd := hg.card2depth_eq p d
  simp only at hp hd
  conv_rhs => rw [show p = ⟨(g.pileOf code hlt).toNat, _⟩ from by ext; exact hp.symm]
  conv_rhs => rw [show d = ⟨(g.depthOf code hlt).toNat, _⟩ from by ext; exact hd.symm]

-- ============================================================
-- Section 3: State Matches Layout
-- ============================================================

/-!
A `Rules.State` **matches** a layout if the cards in each tableau column
are the cards that the layout says were originally dealt there.

Concretely: for each pile `p`, the bottom `n` cards of `state.tableau p`
(reading bottom-up) are `pos2card[p][0], pos2card[p][1], ..., pos2card[p][n-1]`.
The value `n` is the *pile depth* tracked by the solver.

The tableau in `Rules.State` is a `List Card` where the **head is the top**
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
  (∀ (k : Fin n.val),
    encodeCard (col.reverse.get ⟨k.val, by
      simp [List.length_reverse]; omega⟩) =
    (g.pos2card.get p).get ⟨k.val, by omega⟩) ∧
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
structure StateMatchesLayout (g : Globals) (s : Rules.State) : Prop where

  /-- For each pile, the bottom `n` cards match the layout (for some `n`). -/
  piles_match : ∀ (p : Fin 10),
      ∃ (n : Fin 6), PileMatches g (s.tableau p) p n

  /-- Every card in a cell is a valid card code when encoded. -/
  cells_valid : ∀ (i : Fin 4) (c : Card),
      s.cells i = some c → IsValidCard (encodeCard c)

  /-- Every valid card code appears in exactly one location across
      foundation, cells, and tableau. -/
  cards_partition : ∀ (code : UInt8), IsValidCard code →
      -- card is on its foundation (rank ≤ foundation top for its suit)
      let suit := natToSuit ⟨(code >>> 4).toNat, by obtain ⟨h, _⟩ := ‹IsValidCard code›; exact h⟩
      let rank := (code &&& 0xf).toNat
      (rank ≤ optRankToNat (s.foundations suit)) ∨
      -- card is in a cell
      (∃ (i : Fin 4), s.cells i = some (decodeCard code).get!) ∨
      -- card is somewhere in the tableau
      (∃ (p : Fin 10), ∃ (pos : Fin (s.tableau p).length),
          encodeCard ((s.tableau p).get pos) = code)

-- ============================================================
-- Section 4: Key Lemmas Relating the Two Predicates
-- ============================================================

/-- In a consistent layout, the pile depth of a card (its original depth index)
    is always < 5. -/
theorem LayoutConsistent.depthOf_lt5
    {g : Globals} (hg : LayoutConsistent g) (p : Fin 10) (d : Fin 5) :
    (g.depthOf (g.pos2cardAt p d) (IsValidCard_lt64 (hg.pos2card_valid p d))).toNat < 5 := by
  have := hg.card2depth_eq p d; simp only at this; omega

/-- If a card's original pile depth `d` is less than the pile's current depth `n`,
    the card is still in the pile at the correct position. -/
theorem StateMatchesLayout.card_in_pile
    {g : Globals} {s : Rules.State}
    (hg : LayoutConsistent g)
    (hs : StateMatchesLayout g s)
    (p : Fin 10) (d : Fin 5)
    (hn : ∃ n : Fin 6, PileMatches g (s.tableau p) p n ∧ d.val < n.val) :
    ∃ (pos : Fin (s.tableau p).length),
        encodeCard ((s.tableau p).get pos) = g.pos2cardAt p d := by
  obtain ⟨n, ⟨hlen, hmatch⟩, hd⟩ := hn
  have hk : d.val < (s.tableau p).reverse.length := by simp [List.length_reverse]; omega
  exact ⟨⟨(s.tableau p).length - 1 - d.val, by omega⟩,
    by rw [List.get_eq_get_reverse (s.tableau p) ⟨_, by omega⟩]
       exact hmatch ⟨d.val, hd⟩⟩
