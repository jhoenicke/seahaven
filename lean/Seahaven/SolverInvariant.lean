import Mathlib.Tactic
import Seahaven.Solver

/-- Card `c` is **free**: its original pile's depth has been reduced to or
    past its original position, meaning it has been moved off the pile. -/
def isFreeCard (g : Globals) (p : SolverPosType) (c : UInt8) : Prop :=
  let pile      : UInt8 := if h : c.toNat < 64 then g.card2pile.get  ⟨c.toNat, h⟩ else 0
  let origDepth : UInt8 := if h : c.toNat < 64 then g.card2depth.get ⟨c.toNat, h⟩ else 0
  let pileDepth : Int8  :=
    if h : pile.toNat < 10 then p.pileDepth.get ⟨pile.toNat, h⟩ else 0
  origDepth.toNat ≥ pileDepth.toNatClampNeg

-- ---------------------------------------------------------------------------
-- Layout well-formedness
--
-- The three global arrays `pos2card` / `card2pile` / `card2depth` encode a fixed
-- deal.  `WellFormedLayout` states that they are mutually consistent — this is
-- what `initcard` establishes and what the `isFreeCard`-based invariants need.
-- ---------------------------------------------------------------------------

/-- The original pile index of card `c` (mirrors `isFreeCard`'s indexing). -/
def cardPile (g : Globals) (c : UInt8) : UInt8 :=
  if h : c.toNat < 64 then g.card2pile.get ⟨c.toNat, h⟩ else 0

/-- The original within-pile depth of card `c` (mirrors `isFreeCard`). -/
def cardDepth (g : Globals) (c : UInt8) : UInt8 :=
  if h : c.toNat < 64 then g.card2depth.get ⟨c.toNat, h⟩ else 0

/-- `c` is a **real card**: suit in `0..3`, value in `1..13`.  (Consequently
    `c.toNat ≤ 3*16+13 = 61 < 64`, so it is a valid `card2*` index.) -/
def IsRealCard (c : UInt8) : Prop :=
  (SUIT c).toNat < 4 ∧ 1 ≤ (VALUE c).toNat ∧ (VALUE c).toNat ≤ 13

/-- **Well-formed layout** (cf. `VerificationPlan.md §1`).  The deal arrays are
    mutually consistent: `card2pile`/`card2depth` locate each real card, the two
    extra cards (deal positions 50–51) carry the sentinel depth `5`, `pos2card`
    inverts them, and `pos2card` is injective within each pile.  This is the
    hypothesis under which `SolverConvertFromPilesKings` produces a canonical
    state; proving `initcard` establishes it is future work. -/
structure WellFormedLayout (g : Globals) : Prop where
  /-- Every real card is assigned to one of the ten piles. -/
  pile_lt : ∀ c : UInt8, IsRealCard c → (cardPile g c).toNat < 10
  /-- Depths are `0..4` for pile cards and the sentinel `5` for the two extra
      cards; in all cases `≤ 5` (so `≥` any live pile depth means "freed"). -/
  depth_le : ∀ c : UInt8, IsRealCard c → (cardDepth g c).toNat ≤ 5
  /-- `pos2card` inverts `card2pile`/`card2depth` for cards sitting in a pile. -/
  round_trip : ∀ c : UInt8, ∀ hc : IsRealCard c, ∀ hd : (cardDepth g c).toNat < 5,
    (g.pos2card.get ⟨(cardPile g c).toNat, pile_lt c hc⟩).get
      ⟨(cardDepth g c).toNat, hd⟩ = c
  /-- Within a pile, distinct slots hold distinct cards (the deal is injective). -/
  pos2card_inj : ∀ (pile : Fin 10) (d₁ d₂ : Fin 5),
    (g.pos2card.get pile).get d₁ = (g.pos2card.get pile).get d₂ → d₁ = d₂
  /-- Cards stored in `pos2card` are real cards. -/
  pos2card_real : ∀ (pile : Fin 10) (d : Fin 5), IsRealCard ((g.pos2card.get pile).get d)

/-- **Base layer of the canonical-form tower.**  These are the invariants that
    hold throughout the solver once the initial state has been set up, *before*
    per-pile cleanup and foundation draining have run.  They deliberately omit:

    - (2) `merge_complete` and (3b) `flute_maximal` — established pile-by-pile by
      `SolverCleanupPile` (a raw pile with `pileFlute = 1` need not satisfy them);
    - (6) `busyAces_complete` — likewise established per pile by cleanup (a pile
      top may equal `aces[s]+1` while `busyAces = 0` at entry);
    - (7) `busyAces_zero` — established only after the `SolverMoveAces` drain.

    See `SolverInvMerged` and `IsCanonicalPos` for the layers that add these. -/
structure SolverInvBase (g : Globals) (p : SolverPosType) : Prop where

  /-- **(0) Pile depth bound.** All pile depths are at most 5 (the initial
      deal size), expressed as a `Nat` bound so it is directly usable by
      `omega` when constructing `Fin 5` indices. -/
  pileDepth_bound : ∀ i : Fin 10, (p.pileDepth.get i).toNatClampNeg ≤ 5

  /-- **(0b) Pile depths non-negative.** Pile depths never go below zero. -/
  pileDepth_nonneg : ∀ i : Fin 10, 0 ≤ p.pileDepth.get i

  /-- **(1) Aces and kings well-formedness.** For each suit `s`:
      - `aces[s]` has suit `s` and value in `[0, 13]`;
      - `kings[s]` has suit `s` and value in `[1, 13]` (value 0 would mean
        all cards of the suit are free and should have been moved to the
        foundation already);
      - `aces[s] ≤ kings[s]` (equality holds iff the suit is complete, i.e.
        `VALUE(aces[s]) = 13`). -/
  aces_kings_valid : ∀ s : Fin 4,
    SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 ∧
    (VALUE (p.aces.get s).toUInt8).toNat ≤ 13 ∧
    SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 ∧
    1 ≤ (VALUE (p.kings.get s).toUInt8).toNat ∧
    (VALUE (p.kings.get s).toUInt8).toNat ≤ 13 ∧
    p.aces.get s ≤ p.kings.get s

  /-- **(3) Flute length.** `pileFlute[i] ≥ 1` always.  The boundary card is
      the "start" of the flute and is not free (it is still in the pile), so
      the minimum meaningful flute length is 1.  For empty piles (`pileDepth =
      0`) there is no boundary card, and we canonicalise `pileFlute = 1`. -/
  flute_pos : ∀ i : Fin 10, 1 ≤ (p.pileFlute.get i).toNat

  flute_empty : ∀ i : Fin 10,
    p.pileDepth.get i = 0 → p.pileFlute.get i = 1

  /-- **(3a) Flute cards are free.** For every non-empty pile, the
      `pileFlute[i] - 1` cards strictly below the boundary (i.e.
      `boundary - j` for `0 < j < pileFlute[i]`) are free.
      The boundary card itself is NOT free — it is still in the pile. -/
  flute_cards_free : ∀ i : Fin 10, ∀ j : UInt8,
    (p.pileDepth.get i).toNatClampNeg > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    isFreeCard g p
      ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
          by have := pileDepth_bound i; omega⟩ -
       j)

  /-- **(3c) Interior flute cards not aces-captured.** Each interior flute card
      (positions 1 through pileFlute-2) has not yet been moved to the foundation:
      `aces[suit] < (boundary - j)` as `Int8`.  This, combined with `flute_maximal`,
      uniquely pins `pileFlute`. -/
  flute_not_aces : ∀ i : Fin 10, ∀ j : UInt8,
    (p.pileDepth.get i).toNatClampNeg > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩)).toNat < 4,
    p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩)).toNat, hs⟩ <
    ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩ - j).toInt8

  /-- **(4a) Foundation cards are free.** Every card of suit `s` with value
      between 1 and `VALUE(aces[s])` (inclusive) has been freed. -/
  foundation_cards_free : ∀ s : Fin 4, ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s).toUInt8).toNat →
    isFreeCard g p c

  /-- **(4b-weak) Foundation maximal (intermediate form).**  The strong claim
      "`aces[s]+1` is not free" is *false* in the intermediate states produced by
      `SolverCleanupPile` and mid-way through `SolverMoveAces`, because a movable
      run can be merged (freeing its shallower cards) before the foundation drain
      catches up.  So we only require that `aces[s]+1` is one of:

      1. the completed-suit sentinel (`VALUE(aces[s]) = 13`);
      2. not free;
      3. the **most accessible card of some pile's flute** — the physically
         topmost (smallest-value) card of a non-empty pile, i.e.
         `boundary_i − (pileFlute[i] − 1) = aces[s]+1` (the case `SolverCleanupPile`
         creates by merging);
      4. a card on the **king pile** of its suit — `VALUE(aces[s]+1) > VALUE(kings[s])`
         (the case that arises mid-scan in `SolverMoveAces`, where `aces` has been
         advanced into the freed king suffix while `kings[s]` still holds its old
         value).  This predicate doubles as the inner-loop invariant of `moveAcesLoop`.

      The strong form (`IsCanonicalPos.foundation_maximal`) is recovered once the
      drain has run (`busyAces_zero`), which rules out disjuncts 3 and 4. -/
  foundation_maximal_weak : ∀ s : Fin 4,
    (VALUE (p.aces.get s).toUInt8).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1) ∨
    (∃ i : Fin 10, (p.pileDepth.get i).toNatClampNeg > 0 ∧
      (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
          by have := pileDepth_bound i; omega⟩ - (p.pileFlute.get i - 1)
        = (p.aces.get s).toUInt8 + 1) ∨
    (VALUE (p.kings.get s).toUInt8).toNat < (VALUE ((p.aces.get s).toUInt8 + 1)).toNat

  /-- **(5) King frontier.** Either the suit is complete — all 13 cards are in
      the foundation and `kings[s] = aces[s]` — or `kings[s]` is the
      lowest-value card in the suit that is still not free, and every card of
      the same suit with a strictly higher value (up to 13) is free. -/
  king_frontier : ∀ s : Fin 4,
    ((VALUE (p.aces.get s).toUInt8).toNat = 13 ∧ p.kings.get s = p.aces.get s) ∨
    (¬ isFreeCard g p (p.kings.get s).toUInt8 ∧
     ∀ c : UInt8,
       SUIT c = s.val.toUInt8 →
       (VALUE c).toNat > (VALUE (p.kings.get s).toUInt8).toNat →
       (VALUE c).toNat ≤ 13 →
       isFreeCard g p c)

  /-- **(8) Hash formula.** The hash is the dot product of `pileHashes` and
      `pileDepth` (mod 2^32), so it is uniquely determined by `pileDepth`. -/
  hash_def : p.hash = (List.finRange 10).foldl
    (fun acc i => acc + pileHashes.get i * (p.pileDepth.get i).toNatClampNeg.toUInt32) 0

  /-- **(9) Free-piles count.** `freePiles` equals the number of piles whose
      depth is zero.  (Lone-king piles are vacated to depth 0 during cleanup.) -/
  freePiles_def : p.freePiles.toInt =
    (p.pileDepth.toList.countP (· == 0) : Nat)

  /-- **(10) Used-space formula.**  The merge-loop depth decrements and the
      lone-king `usedSpace` correction cancel exactly, leaving:
        usedSpace = 52 − Σ depths − Σ VALUE(aces[s]) − Σ_{dp>0} (pileFlute[i]−1). -/
  usedSpace_def : p.usedSpace.toInt =
    (52 : Int)
    - (p.pileDepth.toList.foldl (fun acc d => acc + d.toNatClampNeg) 0 : Nat)
    - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
    - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (· + ·) 0 : Nat)

/-- **Middle layer of the tower.**  Extends `SolverInvBase` with the invariants
    that `SolverCleanupPile` establishes pile-by-pile: (2) `merge_complete`,
    (3b) `flute_maximal`, and (6) `busyAces_complete` (rephrased per pile).

    A `SolverInvMerged` state is "canonical except the foundation drain has not
    run": every pile is clean, but `busyAces` may still be non-zero.  This is the
    state after `SolverConvertFromPilesKings`'s cleanup loop and the state between
    successive `SolverMoveAces` calls. -/
structure SolverInvMerged (g : Globals) (p : SolverPosType) : Prop extends SolverInvBase g p where

  /-- **(2) Merge complete.** For every non-trivial pile, the card just below
      the boundary is not the same-suit predecessor of the boundary card.
      (The merge loop in `SolverCleanupPile` has terminated.) -/
  merge_complete : ∀ i : Fin 10,
    p.pileDepth.get i ≤ 1 ∨
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 2,
        by have := pileDepth_bound i; omega⟩ ≠
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩ + 1

  /-- **(3b) Flute maximal.** For every non-empty pile, the card that would
      further extend the flute downward (`prevCard = boundary - pileFlute`) is
      either at or below the foundation level for that suit, or is not free.
      (The freed-predecessor loop in `SolverCleanupPile` has terminated.) -/
  flute_maximal : ∀ i : Fin 10,
    p.pileDepth.get i = 0 ∨
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩
    let prevCard := boundary - p.pileFlute.get i
    (∃ hs : (SUIT boundary).toNat < 4,
      p.aces.get ⟨(SUIT boundary).toNat, hs⟩ ≥ prevCard.toInt8) ∨
    ¬ isFreeCard g p prevCard

  /-- **(6) busyAces complete (per pile).**  If the boundary card of a non-empty
      pile is the next foundation card of *its own* suit (`= aces[suit] + 1`,
      suit taken from the boundary card), then that suit's bit is set in
      `busyAces`.  Established pile-by-pile by `SolverCleanupPile` (which sets the
      bit) and preserved by `SolverMoveAces`. -/
  busyAces_complete : ∀ i : Fin 10,
    (p.pileDepth.get i).toNatClampNeg > 0 →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩)).toNat < 4,
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩ =
    (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound i; omega⟩)).toNat, hs⟩).toUInt8 + 1 →
    p.busyAces &&& ((1 : UInt8) <<< (SUIT ((g.pos2card.get i).get
        ⟨(p.pileDepth.get i).toNatClampNeg - 1, by have := pileDepth_bound i; omega⟩))) ≠ 0

/-- A `SolverPosType` is in **canonical form** — the form produced by
    `SolverConvertFromPilesKings` followed by `SolverCleanupPile` and
    `SolverMoveAces` — when it is `SolverInvMerged` and additionally the
    foundation drain has completed, i.e. (7) `busyAces_zero` holds.

    Key consequence: two canonical positions with equal `pileDepth` vectors
    are necessarily equal (see `IsCanonicalPos_unique`), because every other
    field is uniquely determined by the pile depths. -/
structure IsCanonicalPos (g : Globals) (p : SolverPosType) : Prop extends SolverInvMerged g p where

  /-- **(7) busyAces zero.** No foundation advancement is pending:
      `SolverMoveAces` has run to quiescence and all bits are clear. -/
  busyAces_zero : p.busyAces = 0

  /-- **(4b) Foundation maximal (strong form).** In the fully drained canonical
      state the card just above `aces[s]` is not free (or the suit is complete).
      This is the strong form of `foundation_maximal_weak`: with `busyAces_zero`
      no foundation advance is pending, so disjuncts 3 (flute top) and 4 (king
      pile) of the weak form cannot hold and it collapses to this. -/
  foundation_maximal : ∀ s : Fin 4,
    (VALUE (p.aces.get s).toUInt8).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1)

-- ---------------------------------------------------------------------------
-- Modular component predicates
--
-- These give per-pile / per-suit / per-phase views of the tower above, so that
-- specs about the individual solver functions can talk about exactly the
-- conditions they establish or preserve.  The bridge lemmas at the end connect
-- them back to `SolverInvBase` / `SolverInvMerged` / `IsCanonicalPos`.
-- ---------------------------------------------------------------------------

/-- **All per-pile conditions for one pile `i`.**  Fixing the pile index, this
    bundles every pile-local conjunct of the tower (base + merged).  A pile is
    "clean" exactly when `SolverCleanupPile` has finished with it. -/
structure PileClean (g : Globals) (p : SolverPosType) (i : Fin 10) : Prop where
  pileDepth_bound : (p.pileDepth.get i).toNatClampNeg ≤ 5
  pileDepth_nonneg : 0 ≤ p.pileDepth.get i
  merge_complete :
    p.pileDepth.get i ≤ 1 ∨
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 2,
        by have := pileDepth_bound; omega⟩ ≠
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩ + 1
  flute_pos : 1 ≤ (p.pileFlute.get i).toNat
  flute_empty : p.pileDepth.get i = 0 → p.pileFlute.get i = 1
  flute_cards_free : ∀ j : UInt8,
    (p.pileDepth.get i).toNatClampNeg > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    isFreeCard g p
      ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
          by have := pileDepth_bound; omega⟩ - j)
  flute_not_aces : ∀ j : UInt8,
    (p.pileDepth.get i).toNatClampNeg > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat < 4,
    p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat, hs⟩ <
    ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩ - j).toInt8
  flute_maximal :
    p.pileDepth.get i = 0 ∨
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩
    let prevCard := boundary - p.pileFlute.get i
    (∃ hs : (SUIT boundary).toNat < 4,
      p.aces.get ⟨(SUIT boundary).toNat, hs⟩ ≥ prevCard.toInt8) ∨
    ¬ isFreeCard g p prevCard
  busyAces_complete :
    (p.pileDepth.get i).toNatClampNeg > 0 →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat < 4,
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩ =
    (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat, hs⟩).toUInt8 + 1 →
    p.busyAces &&& ((1 : UInt8) <<< (SUIT ((g.pos2card.get i).get
        ⟨(p.pileDepth.get i).toNatClampNeg - 1, by have := pileDepth_bound; omega⟩))) ≠ 0

/-- **The cleanup-established conditions for one pile `i`** — the (2)/(3b)/(6)
    subset that `SolverCleanupPile` adds on top of `SolverInvBase`.  Used as the
    per-pile part of the cleanup-loop invariant `MergedUpTo`. -/
structure PileMerged (g : Globals) (p : SolverPosType) (i : Fin 10) : Prop where
  pileDepth_bound : (p.pileDepth.get i).toNatClampNeg ≤ 5
  merge_complete :
    p.pileDepth.get i ≤ 1 ∨
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 2,
        by have := pileDepth_bound; omega⟩ ≠
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩ + 1
  flute_maximal :
    p.pileDepth.get i = 0 ∨
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩
    let prevCard := boundary - p.pileFlute.get i
    (∃ hs : (SUIT boundary).toNat < 4,
      p.aces.get ⟨(SUIT boundary).toNat, hs⟩ ≥ prevCard.toInt8) ∨
    ¬ isFreeCard g p prevCard
  busyAces_complete :
    (p.pileDepth.get i).toNatClampNeg > 0 →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat < 4,
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩ =
    (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
        by have := pileDepth_bound; omega⟩)).toNat, hs⟩).toUInt8 + 1 →
    p.busyAces &&& ((1 : UInt8) <<< (SUIT ((g.pos2card.get i).get
        ⟨(p.pileDepth.get i).toNatClampNeg - 1, by have := pileDepth_bound; omega⟩))) ≠ 0

/-- **All per-suit conditions for one suit `s`** — the foundation/king conjuncts
    of the tower, fixing the suit index. -/
structure SuitClean (g : Globals) (p : SolverPosType) (s : Fin 4) : Prop where
  aces_kings_valid :
    SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 ∧
    (VALUE (p.aces.get s).toUInt8).toNat ≤ 13 ∧
    SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 ∧
    1 ≤ (VALUE (p.kings.get s).toUInt8).toNat ∧
    (VALUE (p.kings.get s).toUInt8).toNat ≤ 13 ∧
    p.aces.get s ≤ p.kings.get s
  foundation_cards_free : ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s).toUInt8).toNat →
    isFreeCard g p c
  foundation_maximal :
    (VALUE (p.aces.get s).toUInt8).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1)
  king_frontier :
    ((VALUE (p.aces.get s).toUInt8).toNat = 13 ∧ p.kings.get s = p.aces.get s) ∨
    (¬ isFreeCard g p (p.kings.get s).toUInt8 ∧
     ∀ c : UInt8,
       SUIT c = s.val.toUInt8 →
       (VALUE c).toNat > (VALUE (p.kings.get s).toUInt8).toNat →
       (VALUE c).toNat ≤ 13 →
       isFreeCard g p c)

/-- **Cleanup-loop invariant.**  `SolverInvBase` holds globally, and the first
    `k` piles have additionally been cleaned (`PileMerged`).  This is the loop
    invariant of `SolverConvertFromPilesKings`'s per-pile cleanup loop:
    `MergedUpTo … 0` is the state right after setup, and `MergedUpTo … 10` is
    exactly `SolverInvMerged` (see `mergedUpTo_ten_iff`). -/
def MergedUpTo (g : Globals) (p : SolverPosType) (k : Nat) : Prop :=
  SolverInvBase g p ∧ ∀ i : Fin 10, i.val < k → PileMerged g p i

-- ---------------------------------------------------------------------------
-- Bridge lemmas between the components and the tower
-- ---------------------------------------------------------------------------

/-- Every pile of a canonical position is clean. -/
theorem IsCanonicalPos.pileClean {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) (i : Fin 10) : PileClean g p i :=
  ⟨h.pileDepth_bound i, h.pileDepth_nonneg i, h.merge_complete i, h.flute_pos i,
   h.flute_empty i, h.flute_cards_free i, h.flute_not_aces i, h.flute_maximal i,
   h.busyAces_complete i⟩

/-- Every suit of a canonical position is clean. -/
theorem IsCanonicalPos.suitClean {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) (s : Fin 4) : SuitClean g p s :=
  ⟨h.aces_kings_valid s, h.foundation_cards_free s, h.foundation_maximal s, h.king_frontier s⟩

/-- The merged (2)/(3b)/(6) conditions of a canonical position, per pile. -/
theorem IsCanonicalPos.pileMerged {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) (i : Fin 10) : PileMerged g p i :=
  ⟨h.pileDepth_bound i, h.merge_complete i, h.flute_maximal i, h.busyAces_complete i⟩

/-- `MergedUpTo … 10` is exactly the middle layer of the tower. -/
theorem mergedUpTo_ten_iff {g : Globals} {p : SolverPosType} :
    MergedUpTo g p 10 ↔ SolverInvMerged g p := by
  constructor
  · rintro ⟨hbase, hpm⟩
    exact ⟨hbase, fun i => (hpm i i.isLt).merge_complete,
      fun i => (hpm i i.isLt).flute_maximal, fun i => (hpm i i.isLt).busyAces_complete⟩
  · intro h
    exact ⟨h.toSolverInvBase, fun i _ =>
      ⟨h.pileDepth_bound i, h.merge_complete i, h.flute_maximal i, h.busyAces_complete i⟩⟩

/-- Canonical projects to merged + drained.  (The converse additionally needs the
    strong `foundation_maximal` — see `IsCanonicalPos.of_merged_drained` — which is
    recovered from the drain, not from the middle layer alone.) -/
theorem IsCanonicalPos.toMergedBusyZero {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) : SolverInvMerged g p ∧ p.busyAces = 0 :=
  ⟨h.toSolverInvMerged, h.busyAces_zero⟩

/-- Build a canonical state from the middle layer, the drained flag, and the
    strong foundation-maximal fact.  The final `while busyAces ≠ 0` drain supplies
    all three: it reaches `busyAces = 0` and, having scanned each suit up to a
    buried card, the strong `foundation_maximal`. -/
theorem IsCanonicalPos.of_merged_drained {g : Globals} {p : SolverPosType}
    (h : SolverInvMerged g p) (hb : p.busyAces = 0)
    (hfm : ∀ s : Fin 4, (VALUE (p.aces.get s).toUInt8).toNat = 13 ∨
      ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1)) : IsCanonicalPos g p :=
  ⟨h, hb, hfm⟩

/-- Build the middle layer from the base layer plus per-pile cleanup facts. -/
theorem SolverInvMerged.of_base {g : Globals} {p : SolverPosType}
    (hbase : SolverInvBase g p) (hpm : ∀ i, PileMerged g p i) : SolverInvMerged g p :=
  ⟨hbase, fun i => (hpm i).merge_complete, fun i => (hpm i).flute_maximal,
   fun i => (hpm i).busyAces_complete⟩

-- ---------------------------------------------------------------------------
-- Arithmetic helpers for SUIT / VALUE
-- ---------------------------------------------------------------------------

private theorem nat_and_15 (n : Nat) : n &&& 15 = n % 16 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod n 4

private theorem VALUE_toNat (c : UInt8) : (VALUE c).toNat = c.toNat % 16 := by
  simp [VALUE, UInt8.toNat_and, nat_and_15]

private theorem SUIT_toNat (c : UInt8) : (SUIT c).toNat = c.toNat / 16 := by
  simp [SUIT, Nat.shiftRight_eq_div_pow]

private theorem toNat_succ (c : UInt8) (hc : c.toNat < 255) : (c + 1).toNat = c.toNat + 1 := by
  simp only [UInt8.toNat_add, UInt8.toNat_ofNat]; omega

/-- Adding 1 to a card preserves suit when its value is at most 14. -/
private theorem SUIT_succ (c : UInt8) (h : (VALUE c).toNat < 15) : SUIT (c + 1) = SUIT c := by
  apply UInt8.toNat_inj.mp; rw [SUIT_toNat, SUIT_toNat]
  have hv := VALUE_toNat c
  rw [toNat_succ c (by have := c.toNat_lt; omega)]; omega

/-- Adding 1 to a card increments its value when the value is at most 14. -/
private theorem VALUE_succ (c : UInt8) (h : (VALUE c).toNat < 15) :
    (VALUE (c + 1)).toNat = (VALUE c).toNat + 1 := by
  simp only [VALUE_toNat]
  have hv := VALUE_toNat c
  rw [toNat_succ c (by have := c.toNat_lt; omega)]; omega

/-- Two cards with the same suit and value are equal. -/
private theorem card_eq_of_suit_value (c d : UInt8)
    (hs : SUIT c = SUIT d) (hv : (VALUE c).toNat = (VALUE d).toNat) : c = d := by
  apply UInt8.toNat_inj.mp
  have hsc : c.toNat = (SUIT c).toNat * 16 + (VALUE c).toNat := by
    rw [SUIT_toNat, VALUE_toNat]; omega
  have hsd : d.toNat = (SUIT d).toNat * 16 + (VALUE d).toNat := by
    rw [SUIT_toNat, VALUE_toNat]; omega
  rw [hsc, hsd, hs, hv]

-- ---------------------------------------------------------------------------
-- Arithmetic helpers for Int8 / toNatClampNeg
-- ---------------------------------------------------------------------------

private theorem toNatClampNeg_pos {x : Int8} (h1 : 0 ≤ x) (h2 : x ≠ 0) :
    x.toNatClampNeg > 0 := by
  rw [Int8.le_iff_toInt_le, show (0 : Int8).toInt = 0 from rfl] at h1
  have h3 : x.toInt ≠ 0 := fun h => h2 (Int8.toInt_inj.mp h)
  show x.toInt.toNat > 0
  omega

-- ---------------------------------------------------------------------------
-- Uniqueness theorem
-- ---------------------------------------------------------------------------

/-- Two canonical `SolverPosType`s with identical pile depths are equal.
    Because `isFreeCard` depends only on `pileDepth`, all other fields are
    uniquely pinned by the canonical-form conditions. -/
theorem IsCanonicalPos_unique (g : Globals) (p q : SolverPosType)
    (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (hdepth : p.pileDepth = q.pileDepth) : p = q := by
  -- isFreeCard is identical for p and q (depends only on pileDepth)
  have free_iff : ∀ c : UInt8, isFreeCard g p c ↔ isFreeCard g q c := fun c => by
    simp only [isFreeCard, hdepth]
  -- busyAces: both are 0
  have hbusy : p.busyAces = q.busyAces := by
    rw [hp.busyAces_zero, hq.busyAces_zero]
  -- aces: uniquely determined by the free-prefix walk
  have haces : p.aces = q.aces := by
    apply Vector.ext; intro sn hn
    let s : Fin 4 := ⟨sn, hn⟩
    show p.aces.get s = q.aces.get s
    -- It suffices to show the VALUE components agree (SUIT is s for both)
    have hpsuit := (hp.aces_kings_valid s).1
    have hqsuit := (hq.aces_kings_valid s).1
    have hpval  := (hp.aces_kings_valid s).2.1
    have hqval  := (hq.aces_kings_valid s).2.1
    suffices hv : (VALUE (p.aces.get s).toUInt8).toNat = (VALUE (q.aces.get s).toUInt8).toNat by
      -- UInt8 equality, then Int8 equality
      have hUInt8 : (p.aces.get s).toUInt8 = (q.aces.get s).toUInt8 :=
        card_eq_of_suit_value _ _ (hpsuit.trans hqsuit.symm) hv
      exact congrArg Int8.ofUInt8 hUInt8
    apply Nat.le_antisymm
    · -- VALUE(p.aces) ≤ VALUE(q.aces):
      -- if not, the card (q.aces+1) would be free in p but forbidden by foundation_maximal
      by_contra hlt; push Not at hlt
      have hcval : (VALUE (q.aces.get s).toUInt8).toNat < 15 := by omega
      have hcsuit : SUIT ((q.aces.get s).toUInt8 + 1) = s.val.toUInt8 :=
        (SUIT_succ _ hcval).trans hqsuit
      have hcval1 : 1 ≤ (VALUE ((q.aces.get s).toUInt8 + 1)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hcval2 : (VALUE ((q.aces.get s).toUInt8 + 1)).toNat ≤
          (VALUE (p.aces.get s).toUInt8).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hfree_p := hp.foundation_cards_free s _ hcsuit hcval1 hcval2
      have hfree_q := (free_iff _).mp hfree_p
      rcases hq.foundation_maximal s with h13 | hnfree
      · omega
      · exact hnfree hfree_q
    · -- VALUE(q.aces) ≤ VALUE(p.aces): symmetric
      by_contra hlt; push Not at hlt
      have hcval : (VALUE (p.aces.get s).toUInt8).toNat < 15 := by omega
      have hcsuit : SUIT ((p.aces.get s).toUInt8 + 1) = s.val.toUInt8 :=
        (SUIT_succ _ hcval).trans hpsuit
      have hcval1 : 1 ≤ (VALUE ((p.aces.get s).toUInt8 + 1)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hcval2 : (VALUE ((p.aces.get s).toUInt8 + 1)).toNat ≤
          (VALUE (q.aces.get s).toUInt8).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hfree_q := hq.foundation_cards_free s _ hcsuit hcval1 hcval2
      have hfree_p := (free_iff _).mpr hfree_q
      rcases hp.foundation_maximal s with h13 | hnfree
      · omega
      · exact hnfree hfree_p
  -- kings: uniquely determined by the free-suffix walk
  have hkings : p.kings = q.kings := by
    apply Vector.ext; intro sn hn
    let s : Fin 4 := ⟨sn, hn⟩
    show p.kings.get s = q.kings.get s
    have hpsuit := (hp.aces_kings_valid s).2.2.1   -- SUIT(p.kings[s]) = s
    have hqsuit := (hq.aces_kings_valid s).2.2.1   -- SUIT(q.kings[s]) = s
    have hpval1 := (hp.aces_kings_valid s).2.2.2.1  -- 1 ≤ VALUE(p.kings[s])
    have hqval1 := (hq.aces_kings_valid s).2.2.2.1  -- 1 ≤ VALUE(q.kings[s])
    have hpval  := (hp.aces_kings_valid s).2.2.2.2.1 -- VALUE(p.kings[s]) ≤ 13
    have hqval  := (hq.aces_kings_valid s).2.2.2.2.1 -- VALUE(q.kings[s]) ≤ 13
    -- Helper: VALUE(kings[s]) = 13 when king_frontier case 1 holds
    have kings_val_13 : ∀ (r : SolverPosType) (t : Fin 4),
        r.kings.get t = r.aces.get t →
        (VALUE (r.aces.get t).toUInt8).toNat = 13 →
        (VALUE (r.kings.get t).toUInt8).toNat = 13 := fun r t hkeq h13 =>
      (congrArg (fun x : Int8 => (VALUE x.toUInt8).toNat) hkeq).trans h13
    suffices hv : (VALUE (p.kings.get s).toUInt8).toNat = (VALUE (q.kings.get s).toUInt8).toNat by
      have hUInt8 := card_eq_of_suit_value _ _ (hpsuit.trans hqsuit.symm) hv
      exact congrArg Int8.ofUInt8 hUInt8
    apply Nat.le_antisymm
    · -- VALUE(p.kings) ≤ VALUE(q.kings)
      -- Contradiction assumption: VALUE_q < VALUE_p
      by_contra hlt; push Not at hlt
      rcases hp.king_frontier s with ⟨h13p, hkp⟩ | ⟨hnfp, hap⟩
      · -- hp case 1: VALUE(p.aces) = 13, p.kings = p.aces, so VALUE(p.kings) = 13.
        -- q.kings is free in p (foundation covers all of suit s up to 13).
        -- Contradiction from q's king_frontier.
        have hkp13 := kings_val_13 p s hkp h13p
        have hkq_free_p := hp.foundation_cards_free s (q.kings.get s).toUInt8
          hqsuit hqval1 (by omega)
        rcases hq.king_frontier s with ⟨h13q, hkq⟩ | ⟨hnfq, _⟩
        · exact absurd (kings_val_13 q s hkq h13q) (by omega)
        · exact hnfq ((free_iff _).mp hkq_free_p)
      · -- hp case 2: p.kings is not free; all above p.kings are free in p.
        -- Since VALUE_q < VALUE_p, p.kings is above q.kings in q's frontier.
        rcases hq.king_frontier s with ⟨h13q, hkq⟩ | ⟨hnfq, haq⟩
        · -- hq case 1: VALUE(q.kings) = 13; hlt gives 13 < VALUE_p ≤ 13
          exact absurd (kings_val_13 q s hkq h13q) (by omega)
        · -- hq case 2: p.kings is above q.kings (VALUE_p > VALUE_q), free in q, hence in p
          exact hnfp ((free_iff _).mpr (haq _ hpsuit (by omega) (by omega)))
    · -- VALUE(q.kings) ≤ VALUE(p.kings): symmetric
      -- Contradiction assumption: VALUE_p < VALUE_q
      by_contra hlt; push Not at hlt
      rcases hq.king_frontier s with ⟨h13q, hkq⟩ | ⟨hnfq, haq⟩
      · -- hq case 1: VALUE(q.aces) = 13, q.kings = q.aces, so VALUE(q.kings) = 13.
        -- p.kings is free in q (foundation covers all of suit s up to 13).
        -- Contradiction from p's king_frontier.
        have hkq13 := kings_val_13 q s hkq h13q
        have hkp_free_q := hq.foundation_cards_free s (p.kings.get s).toUInt8
          hpsuit hpval1 (by omega)
        rcases hp.king_frontier s with ⟨h13p, hkp⟩ | ⟨hnfp, _⟩
        · exact absurd (kings_val_13 p s hkp h13p) (by omega)
        · exact hnfp ((free_iff _).mpr hkp_free_q)
      · -- hq case 2: q.kings is not free; all above q.kings are free in q.
        rcases hp.king_frontier s with ⟨h13p, hkp⟩ | ⟨hnfp, hap⟩
        · -- hp case 1: VALUE(p.kings) = 13; hlt gives 13 < VALUE_q ≤ 13
          exact absurd (kings_val_13 p s hkp h13p) (by omega)
        · -- hp case 2: q.kings is above p.kings (VALUE_q > VALUE_p), free in p, hence in q
          exact hnfq ((free_iff _).mp (hap _ hqsuit (by omega) (by omega)))
  -- pileFlute: uniquely determined by the same isFreeCard / aces plus flute_not_aces
  have hflute : p.pileFlute = q.pileFlute := by
    apply Vector.ext; intro in_ hn
    let i : Fin 10 := ⟨in_, hn⟩
    show p.pileFlute.get i = q.pileFlute.get i
    have hdepth_i : p.pileDepth.get i = q.pileDepth.get i :=
      congrArg (fun v : Vector Int8 10 => v.get i) hdepth
    by_cases hd : p.pileDepth.get i = 0
    · -- Empty pile: both pileFlute = 1 by flute_empty
      rw [hp.flute_empty i hd, hq.flute_empty i (hdepth_i ▸ hd)]
    · -- Non-empty pile: use antisymmetry
      have hdp_pos : (p.pileDepth.get i).toNatClampNeg > 0 :=
        toNatClampNeg_pos (hp.pileDepth_nonneg i) hd
      have hdq_pos : (q.pileDepth.get i).toNatClampNeg > 0 := hdepth_i ▸ hdp_pos
      -- The boundary card is the same for p and q (same pos2card index)
      have hdnc : (p.pileDepth.get i).toNatClampNeg = (q.pileDepth.get i).toNatClampNeg :=
        congrArg Int8.toNatClampNeg hdepth_i
      have hbdy : (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
              by have := hp.pileDepth_bound i; omega⟩ =
                 (g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
              by have := hq.pileDepth_bound i; omega⟩ :=
        congrArg (g.pos2card.get i).get (Fin.ext (congrArg (· - 1) hdnc))
      -- Helper: apply flute_not_aces contradiction given the aces/card equalities
      -- pileFlute_p ≤ pileFlute_q
      have hle1 : (p.pileFlute.get i).toNat ≤ (q.pileFlute.get i).toNat := by
        by_contra hlt
        have hlt' : (q.pileFlute.get i).toNat < (p.pileFlute.get i).toNat := Nat.lt_of_not_le hlt
        have hj1 : 0 < (q.pileFlute.get i).toNat := hq.flute_pos i
        -- boundary_p - pileFlute_q is interior to p's flute, hence free in both
        have hfree_q := (free_iff _).mp
          (hp.flute_cards_free i (q.pileFlute.get i) hdp_pos hj1 hlt')
        rcases hq.flute_maximal i with hd0 | ⟨hs, hge⟩ | hnfree
        · exact hd (hdepth_i.symm ▸ hd0)
        · -- aces_q ≥ prevCard_q; flute_not_aces of p gives aces_p < same card
          have hsuit : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
                          by have := hp.pileDepth_bound i; omega⟩)).toNat =
                       (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
                          by have := hq.pileDepth_bound i; omega⟩)).toNat :=
            congrArg UInt8.toNat (congrArg SUIT hbdy)
          have hs' : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
                        by have := hp.pileDepth_bound i; omega⟩)).toNat < 4 := hsuit ▸ hs
          have hlt_aces := hp.flute_not_aces i (q.pileFlute.get i) hdp_pos hj1 hlt' hs'
          have haces_s : p.aces.get ⟨_, hs'⟩ = q.aces.get ⟨_, hs⟩ :=
            (congrArg (fun v : Vector Int8 4 => v.get ⟨_, hs'⟩) haces).trans
              (congrArg q.aces.get (Fin.ext hsuit))
          have hcard : ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
                          by have := hp.pileDepth_bound i; omega⟩ -
                        q.pileFlute.get i).toInt8 =
                       ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
                          by have := hq.pileDepth_bound i; omega⟩ -
                        q.pileFlute.get i).toInt8 := by rw [hbdy]
          rw [haces_s, hcard] at hlt_aces
          exact absurd hge (Int8.not_le.mpr hlt_aces)
        · exact hnfree (hbdy ▸ hfree_q)
      -- pileFlute_q ≤ pileFlute_p (symmetric)
      have hle2 : (q.pileFlute.get i).toNat ≤ (p.pileFlute.get i).toNat := by
        by_contra hlt
        have hlt' : (p.pileFlute.get i).toNat < (q.pileFlute.get i).toNat := Nat.lt_of_not_le hlt
        have hj1 : 0 < (p.pileFlute.get i).toNat := hp.flute_pos i
        have hfree_p := (free_iff _).mpr
          (hq.flute_cards_free i (p.pileFlute.get i) hdq_pos hj1 hlt')
        rcases hp.flute_maximal i with hd0 | ⟨hs, hge⟩ | hnfree
        · exact hd hd0
        · have hsuit : (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
                          by have := hq.pileDepth_bound i; omega⟩)).toNat =
                       (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
                          by have := hp.pileDepth_bound i; omega⟩)).toNat :=
            congrArg UInt8.toNat (congrArg SUIT hbdy.symm)
          have hs' : (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
                        by have := hq.pileDepth_bound i; omega⟩)).toNat < 4 := hsuit ▸ hs
          have hlt_aces := hq.flute_not_aces i (p.pileFlute.get i) hdq_pos hj1 hlt' hs'
          have haces_s : q.aces.get ⟨_, hs'⟩ = p.aces.get ⟨_, hs⟩ :=
            (congrArg (fun v : Vector Int8 4 => v.get ⟨_, hs'⟩) haces.symm).trans
              (congrArg p.aces.get (Fin.ext hsuit))
          have hcard : ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNatClampNeg - 1,
                          by have := hq.pileDepth_bound i; omega⟩ -
                        p.pileFlute.get i).toInt8 =
                       ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNatClampNeg - 1,
                          by have := hp.pileDepth_bound i; omega⟩ -
                        p.pileFlute.get i).toInt8 := by rw [hbdy.symm]
          rw [haces_s, hcard] at hlt_aces
          exact absurd hge (Int8.not_le.mpr hlt_aces)
        · exact hnfree (hbdy.symm ▸ hfree_p)
      exact UInt8.ext (Nat.le_antisymm hle1 hle2)
  -- freePiles: count of piles with depth 0, so determined by pileDepth
  have hfree : p.freePiles = q.freePiles :=
    Int8.toInt_inj.mp (hp.freePiles_def.trans (by rw [hdepth]) |>.trans hq.freePiles_def.symm)
  -- usedSpace: formula in pileDepth, aces, pileFlute
  have hused : p.usedSpace = q.usedSpace :=
    Int8.toInt_inj.mp (hp.usedSpace_def.trans (by rw [hdepth, haces, hflute]) |>.trans hq.usedSpace_def.symm)
  -- hash: dot product of pileHashes and pileDepth
  have hhash : p.hash = q.hash :=
    hp.hash_def.trans (by rw [hdepth]) |>.trans hq.hash_def.symm
  -- Combine all field equalities into p = q
  obtain ⟨ph, ppd, ppf, pa, pk, pus, pfp, pba⟩ := p
  obtain ⟨qh, qpd, qpf, qa, qk, qus, qfp, qba⟩ := q
  simp only [SolverPosType.mk.injEq] at *
  exact ⟨hhash, hdepth, hflute, haces, hkings, hused, hfree, hbusy⟩

-- ---------------------------------------------------------------------------
-- Hash injectivity
-- ---------------------------------------------------------------------------

/-- An `Int8` that is nonnegative is determined by `x.toInt.toNat`. -/
private theorem Int8_eq_of_toNat_eq {x y : Int8} (hx : (0 : Int8) ≤ x) (hy : (0 : Int8) ≤ y)
    (h : x.toInt.toNat = y.toInt.toNat) : x = y := by
  apply Int8.toInt_inj.mp
  have hx' : (0 : Int) ≤ x.toInt := Int8.le_iff_toInt_le.mp hx
  have hy' : (0 : Int) ≤ y.toInt := Int8.le_iff_toInt_le.mp hy
  omega

/-- **Base-6 hash injectivity, arithmetic core.**  If two base-6 dot products of
    ten digits each in `{0,…,5}` agree as `UInt32`, the digits agree.  The sum is
    at most `6^10 - 1 = 60466175 < 2^32`, so the `UInt32` reduction never wraps and
    the equation is a genuine `Nat` equation, decided by `omega`. -/
private theorem hash_dot_inj (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Nat) (hd0 : d0 ≤ 5) (hd1 : d1 ≤ 5) (hd2 : d2 ≤ 5) (hd3 : d3 ≤ 5) (hd4 : d4 ≤ 5) (hd5 : d5 ≤ 5) (hd6 : d6 ≤ 5) (hd7 : d7 ≤ 5) (hd8 : d8 ≤ 5) (hd9 : d9 ≤ 5) (he0 : e0 ≤ 5) (he1 : e1 ≤ 5) (he2 : e2 ≤ 5) (he3 : e3 ≤ 5) (he4 : e4 ≤ 5) (he5 : e5 ≤ 5) (he6 : e6 ≤ 5) (he7 : e7 ≤ 5) (he8 : e8 ≤ 5) (he9 : e9 ≤ 5)
    (h : (0 + 1 * d0.toUInt32 + 6 * d1.toUInt32 + 36 * d2.toUInt32 + 216 * d3.toUInt32 + 1296 * d4.toUInt32 + 7776 * d5.toUInt32 + 46656 * d6.toUInt32 + 279936 * d7.toUInt32 + 1679616 * d8.toUInt32 + 10077696 * d9.toUInt32 : UInt32) =
         (0 + 1 * e0.toUInt32 + 6 * e1.toUInt32 + 36 * e2.toUInt32 + 216 * e3.toUInt32 + 1296 * e4.toUInt32 + 7776 * e5.toUInt32 + 46656 * e6.toUInt32 + 279936 * e7.toUInt32 + 1679616 * e8.toUInt32 + 10077696 * e9.toUInt32 : UInt32)) :
    d0 = e0 ∧ d1 = e1 ∧ d2 = e2 ∧ d3 = e3 ∧ d4 = e4 ∧ d5 = e5 ∧ d6 = e6 ∧ d7 = e7 ∧ d8 = e8 ∧ d9 = e9 := by
  -- Rewrite each side as `(Nat dot product).toUInt32` via the ring homomorphism `Nat.toUInt32`.
  rw [show (0 + 1 * d0.toUInt32 + 6 * d1.toUInt32 + 36 * d2.toUInt32 + 216 * d3.toUInt32 + 1296 * d4.toUInt32 + 7776 * d5.toUInt32 + 46656 * d6.toUInt32 + 279936 * d7.toUInt32 + 1679616 * d8.toUInt32 + 10077696 * d9.toUInt32 : UInt32)
          = (1 * d0 + 6 * d1 + 36 * d2 + 216 * d3 + 1296 * d4 + 7776 * d5 + 46656 * d6 + 279936 * d7 + 1679616 * d8 + 10077696 * d9).toUInt32 from by
        simp only [show ∀ x : Nat, x.toUInt32 = UInt32.ofNat x from fun _ => rfl,
                   UInt32.ofNat_add, UInt32.ofNat_mul, UInt32.reduceOfNat, UInt32.zero_add],
      show (0 + 1 * e0.toUInt32 + 6 * e1.toUInt32 + 36 * e2.toUInt32 + 216 * e3.toUInt32 + 1296 * e4.toUInt32 + 7776 * e5.toUInt32 + 46656 * e6.toUInt32 + 279936 * e7.toUInt32 + 1679616 * e8.toUInt32 + 10077696 * e9.toUInt32 : UInt32)
          = (1 * e0 + 6 * e1 + 36 * e2 + 216 * e3 + 1296 * e4 + 7776 * e5 + 46656 * e6 + 279936 * e7 + 1679616 * e8 + 10077696 * e9).toUInt32 from by
        simp only [show ∀ x : Nat, x.toUInt32 = UInt32.ofNat x from fun _ => rfl,
                   UInt32.ofNat_add, UInt32.ofNat_mul, UInt32.reduceOfNat, UInt32.zero_add]] at h
  -- Both dot products are `< 2^32`, so taking `.toNat` yields a plain `Nat` equation.
  have bp : 1 * d0 + 6 * d1 + 36 * d2 + 216 * d3 + 1296 * d4 + 7776 * d5 + 46656 * d6 + 279936 * d7 + 1679616 * d8 + 10077696 * d9 < 4294967296 := by omega
  have bq : 1 * e0 + 6 * e1 + 36 * e2 + 216 * e3 + 1296 * e4 + 7776 * e5 + 46656 * e6 + 279936 * e7 + 1679616 * e8 + 10077696 * e9 < 4294967296 := by omega
  have hnat : 1 * d0 + 6 * d1 + 36 * d2 + 216 * d3 + 1296 * d4 + 7776 * d5 + 46656 * d6 + 279936 * d7 + 1679616 * d8 + 10077696 * d9 = 1 * e0 + 6 * e1 + 36 * e2 + 216 * e3 + 1296 * e4 + 7776 * e5 + 46656 * e6 + 279936 * e7 + 1679616 * e8 + 10077696 * e9 := by
    have hh := congrArg UInt32.toNat h
    simp only [show ∀ x : Nat, x.toUInt32 = UInt32.ofNat x from fun _ => rfl,
               UInt32.toNat_ofNat', Nat.reducePow] at hh
    rwa [Nat.mod_eq_of_lt bp, Nat.mod_eq_of_lt bq] at hh
  -- Base-6 uniqueness with digits in {0,…,5}, one omega call per digit.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- If two canonical positions have equal hashes, their pile depth vectors are
    identical.  The hash is `Σ 6^i · depth[i]` with `depth[i] ∈ {0,…,5}`,
    i.e., the base-6 representation of the depth vector, which is injective
    because `6^10 − 1 = 60 466 175 < 2^32` (no overflow). -/
theorem IsCanonicalPos_hash_inj (g : Globals) (p q : SolverPosType)
    (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (hhash : p.hash = q.hash) : p.pileDepth = q.pileDepth := by
  -- Extract hash foldl equality as UInt32.
  -- Omega (Lean 4.6+) handles UInt32 natively, so no need to take .toNat.
  have hfoldl :
      (List.finRange 10).foldl
        (fun acc i => acc + pileHashes.get i * (p.pileDepth.get i).toNatClampNeg.toUInt32) 0 =
      (List.finRange 10).foldl
        (fun acc i => acc + pileHashes.get i * (q.pileDepth.get i).toNatClampNeg.toUInt32) 0 :=
    hp.hash_def.symm.trans (hhash.trans hq.hash_def)
  -- Expand the foldl: List.finRange → ofFn → concrete list, then foldl_cons/nil steps.
  -- Vector.get unfolds v.get ⟨k,h⟩ → v.toArray[...]; getElem_toArray then converts
  -- v.toArray[k] → v[k] so all depth terms use GetElem ([k]) notation, matching the
  -- bounds below and the goal produced by Vector.ext.
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
             pileHashes, Vector.get, Vector.getElem_toArray, Fin.isValue, Fin.val_cast,
             Fin.val_zero, Fin.val_succ, Nat.reduceAdd, List.getElem_toArray,
             List.getElem_cons_succ, List.getElem_cons_zero, Int8.toNatClampNeg] at hfoldl
  -- Bounds stated with [k] getElem notation (definitionally equal to .get ⟨k,_⟩ via the
  -- GetElem instance), so omega sees the same atoms as in hfoldl and the Vector.ext goal.
  have hpb0 : (p.pileDepth[0] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨0, by omega⟩
  have hpb1 : (p.pileDepth[1] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨1, by omega⟩
  have hpb2 : (p.pileDepth[2] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨2, by omega⟩
  have hpb3 : (p.pileDepth[3] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨3, by omega⟩
  have hpb4 : (p.pileDepth[4] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨4, by omega⟩
  have hpb5 : (p.pileDepth[5] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨5, by omega⟩
  have hpb6 : (p.pileDepth[6] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨6, by omega⟩
  have hpb7 : (p.pileDepth[7] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨7, by omega⟩
  have hpb8 : (p.pileDepth[8] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨8, by omega⟩
  have hpb9 : (p.pileDepth[9] : Int8).toNatClampNeg ≤ 5 := hp.pileDepth_bound ⟨9, by omega⟩
  have hqb0 : (q.pileDepth[0] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨0, by omega⟩
  have hqb1 : (q.pileDepth[1] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨1, by omega⟩
  have hqb2 : (q.pileDepth[2] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨2, by omega⟩
  have hqb3 : (q.pileDepth[3] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨3, by omega⟩
  have hqb4 : (q.pileDepth[4] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨4, by omega⟩
  have hqb5 : (q.pileDepth[5] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨5, by omega⟩
  have hqb6 : (q.pileDepth[6] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨6, by omega⟩
  have hqb7 : (q.pileDepth[7] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨7, by omega⟩
  have hqb8 : (q.pileDepth[8] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨8, by omega⟩
  have hqb9 : (q.pileDepth[9] : Int8).toNatClampNeg ≤ 5 := hq.pileDepth_bound ⟨9, by omega⟩
  -- Normalize toNatClampNeg → toInt.toNat everywhere.
  simp only [Int8.toNatClampNeg] at *
  -- Reduce the `UInt32` hash equation to the ten pointwise digit equalities via the
  -- arithmetic core.  The bounds fix each abstract digit to the corresponding depth, so
  -- `hfoldl` matches by first-order unification (no expensive `getElem` reduction).
  have key := hash_dot_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hpb0 hpb1 hpb2 hpb3 hpb4 hpb5 hpb6 hpb7 hpb8 hpb9
    hqb0 hqb1 hqb2 hqb3 hqb4 hqb5 hqb6 hqb7 hqb8 hqb9 hfoldl
  -- Drop the (large) `UInt32` hash equation so the tactics below do not choke on it.
  clear hfoldl
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := key
  -- Each component follows from its digit equality (`k0 … k9`, found by `assumption` once
  -- `interval_cases` has fixed the index) plus nonnegativity.  `Int8_eq_of_toNat_eq` does
  -- the `.toInt.toNat → .toInt → Int8` bridge that `omega` cannot do on `Int8` directly.
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    exact Int8_eq_of_toNat_eq (hp.pileDepth_nonneg ⟨_, by omega⟩)
      (hq.pileDepth_nonneg ⟨_, by omega⟩) (by assumption)
