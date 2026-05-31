import Mathlib.Tactic
import Seahaven.Rules
import Seahaven.Solver

/-!
# Layout Consistency and State Matching

This file defines the bridge between the high-level `State` world and
the low-level `Globals` / `UInt8` card-code world used by the solver.

Three layers of properties are developed:

1. **Encoding**: bijection between `Rules.Card` and valid `UInt8` card codes.
2. **`LayoutConsistent`**: the `Globals` arrays `pos2card`, `card2pile`,
   `card2depth` are mutually consistent (they encode a valid initial deal).
3. **`StateMatchesLayout`**: a `State` is compatible with a layout,
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

instance (code : UInt8) : Decidable (IsValidCard code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem encodeCard_valid (c : Card) : IsValidCard (encodeCard c) := by
  fin_cases c <;> native_decide

/-- Valid card codes fit in the 64-entry lookup arrays. -/
theorem IsValidCard_lt64 {code : UInt8} (h : IsValidCard code) : code.toNat < 64 := by
  obtain ⟨hs, _, _⟩ := h
  -- (code >>> 4).toNat = code.toNat / 16, so code.toNat / 16 < 4 → code.toNat < 64
  have hshift : (code >>> 4).toNat = code.toNat / 16 := by
    simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decodeCard_encodeCard (c : Card) : decodeCard (encodeCard c) = some c := by
  fin_cases c <;> native_decide

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

structure LayoutConsistent (g : Globals) : Prop where

  /-- Every entry in `pos2card` is a valid card code. -/
  pos2card_valid : ∀ (p : Fin 10) (d : Fin 5),
      IsValidCard (g.pos2cardAt p d)

  /-- `card2pile` is the left inverse of `pos2card`'s pile index.
      The caller supplies the validity proof `hv`; `hlt` is derived from it. -/
  card2pile_eq : ∀ (p : Fin 10) (d : Fin 5)
      (hv : IsValidCard (g.pos2cardAt p d)),
      (g.pileOf (g.pos2cardAt p d) (IsValidCard_lt64 hv)).toNat = p.val

  /-- `card2depth` is the left inverse of `pos2card`'s depth index. -/
  card2depth_eq : ∀ (p : Fin 10) (d : Fin 5)
      (hv : IsValidCard (g.pos2cardAt p d)),
      (g.depthOf (g.pos2cardAt p d) (IsValidCard_lt64 hv)).toNat = d.val

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
    let hv  := hg.pos2card_valid p d
    let hlt := IsValidCard_lt64 hv
    let code := g.pos2cardAt p d
    g.pos2cardAt
      ⟨(g.pileOf code hlt).toNat,
        (hg.card2pile_eq p d (hg.pos2card_valid p d)).symm ▸ p.isLt⟩
      ⟨(g.depthOf code hlt).toNat,
        (hg.card2depth_eq p d (hg.pos2card_valid p d)).symm ▸ d.isLt⟩
    = code := by
  simp only
  have hv := hg.pos2card_valid p d
  have hp := hg.card2pile_eq  p d hv
  have hd := hg.card2depth_eq p d hv
  congr 1
  · exact Fin.ext hp
  · exact Fin.ext hd

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

  /-- Every card in a cell is a valid card code when encoded. -/
  cells_valid : ∀ (i : Fin 4) (c : Card),
      s.cells i = some c → IsValidCard (encodeCard c)

  /-- Every valid card code appears in exactly one location across
      foundation, cells, and tableau. -/
  cards_partition : ∀ (code : UInt8) (hv : IsValidCard code),
      -- card is on its foundation (rank ≤ foundation top for its suit)
      let suit := natToSuit ⟨(code >>> 4).toNat, hv.1⟩
      let rank := (code &&& 0xf).toNat
      (rank ≤ optRankToNat (s.foundations suit)) ∨
      -- card is in a cell (exists a cell containing a card that encodes to code)
      (∃ (i : Fin 4) (c : Card), s.cells i = some c ∧ encodeCard c = code) ∨
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
  have := hg.card2depth_eq p d (hg.pos2card_valid p d); omega

/-- If a card's original pile depth `d` is less than the pile's current depth `n`,
    the card is still in the pile at the correct position. -/
theorem StateMatchesLayout.card_in_pile
    {g : Globals} {s : State}
    (hg : LayoutConsistent g)
    (hs : StateMatchesLayout g s)
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
private lemma PileMatches_tail
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

-- ---- Helper: adding a card on top preserves PileMatches (with same n)
-- when the card continues the flute's descending sequence.
private lemma PileMatches_cons
    {g : Globals} {col : Column} {p : Fin 10} {n : Fin 6} {card : Card}
    (hm : PileMatches g col p n)
    (hcont : col = [] ∨ col.head?.map encodeCard =
             (nextCard card).map encodeCard) :
    PileMatches g (card :: col) p n := by
  sorry

theorem StateMatchesLayout.applyMove
    {g : Globals} {s s' : State} {m : Move}
    (hg : LayoutConsistent g)
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
    rcases m.dest with dst | _ | _
    · -- pile dest: dst pile gains card on top; all other piles unchanged
      by_cases h : dst = q
      · simp [h]
        exact ⟨n, PileMatches_cons hn (by sorry)⟩
      · simp [h]; exact ⟨n, hn⟩
    · -- cell dest: no pile changes
      exact ⟨n, hn⟩
    · -- foundation dest: no pile changes
      exact ⟨n, hn⟩
  · -- cells_valid
    sorry
  · -- cards_partition
    sorry
