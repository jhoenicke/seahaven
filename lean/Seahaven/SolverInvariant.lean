import Mathlib.Tactic
import Seahaven.Solver
import Seahaven.UInt8Lemmas

/-- Card `c` is **free**: its original pile's depth has been reduced to or
    past its original position, meaning it has been moved off the pile. -/
def isFreeCard (g : Globals) (p : SolverPosType) (c : UInt8) : Prop :=
  let pile      : UInt8 := if h : c.toNat < 64 then g.card2pile.get  ⟨c.toNat, h⟩ else 0
  let origDepth : UInt8 := if h : c.toNat < 64 then g.card2depth.get ⟨c.toNat, h⟩ else 0
  let pileDepth : UInt8  :=
    if h : pile.toNat < 10 then p.pileDepth.get ⟨pile.toNat, h⟩ else 0
  origDepth.toNat ≥ pileDepth.toNat

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
    state; `InitCard.initcard_ok` proves `initcard` establishes it (for a deal
    that is a genuine permutation of the 52 card codes). -/
structure WellFormedLayout (g : Globals) : Prop where
  /-- Every real card is assigned to one of the ten piles. -/
  pile_lt : ∀ c : UInt8, IsRealCard c → (cardPile g c).toNat < 10
  /-- Every `card2pile` entry — including the never-read entries at non-real
      card codes, which `initcard` leaves zero-initialized — is a valid pile
      index.  (The freed-predecessor loop's run characterization needs the
      bound for all indices it could touch.) -/
  card2pile_lt : ∀ (i : Nat) (h : i < 64), (g.card2pile[i]'h).toNat < 10
  /-- Depths are `0..4` for pile cards and the sentinel `5` for the two extra
      cards; in all cases `≤ 5` (so `≥` any live pile depth means "freed"). -/
  depth_le : ∀ c : UInt8, IsRealCard c → (cardDepth g c).toNat ≤ 5
  /-- `pos2card` inverts `card2pile`/`card2depth` for cards sitting in a pile. -/
  round_trip : ∀ c : UInt8, ∀ hc : IsRealCard c, ∀ hd : (cardDepth g c).toNat < 5,
    (g.pos2card.get ⟨(cardPile g c).toNat, pile_lt c hc⟩).get
      ⟨(cardDepth g c).toNat, hd⟩ = c
  /-- Cards stored in `pos2card` are real cards. -/
  pos2card_real : ∀ (pile : Fin 10) (d : Fin 5), IsRealCard ((g.pos2card.get pile).get d)
  /-- **Inverse round-trip**: the card sitting at slot `(pile, d)` reports that
      exact slot as its own `cardPile`/`cardDepth`.  (`round_trip` goes the
      other way: a card's own recorded slot recovers the card.)  This is what
      makes a pile's current top card never free (`boundary_not_free`) — the
      key fact behind cross-pile flute disjointness and hence `usedSpace ≥ 0`.
      It also makes the old within-pile-only `pos2card_inj` redundant: the
      full *cross-pile* injectivity of `pos2card` (distinct slots anywhere in
      the whole layout hold distinct cards) is now a one-line corollary — see
      `WellFormedLayout.pos2card_inj` below. -/
  round_trip_inv : ∀ (pile : Fin 10) (d : Fin 5),
    (cardPile g ((g.pos2card.get pile).get d)).toNat = pile.val ∧
    (cardDepth g ((g.pos2card.get pile).get d)).toNat = d.val

-- ---------------------------------------------------------------------------
-- Modular per-pile predicates
--
-- These give the per-pile view used both by `SolverInvBase`/`SolverInvMerged`
-- (as `∀ i, PileBase g p i` / `∀ i, PileMerged g p i _`) and standalone by specs
-- about individual solver functions.  Declared before the tower so both can use
-- them directly, avoiding field-by-field duplication.
-- ---------------------------------------------------------------------------

/-- **The base per-pile conditions for one pile `i`** — the (0)/(0b)/(3)/(3a)/(3c)
    subset that holds throughout, before `SolverCleanupPile` has necessarily run.
    Shared by `SolverInvBase` (fixed as `∀ i, PileBase g p i`) and by
    `PileClean` (which adds the merged facts on top). -/
structure PileBase (g : Globals) (p : SolverPosType) (i : Fin 10) : Prop where
  pileDepth_bound : (p.pileDepth.get i).toNat ≤ 5
  pileDepth_nonneg : 0 ≤ p.pileDepth.get i
  flute_pos : 1 ≤ (p.pileFlute.get i).toNat
  flute_empty : p.pileDepth.get i = 0 → p.pileFlute.get i = 1
  flute_cards_free : ∀ j : UInt8,
    (p.pileDepth.get i).toNat > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    isFreeCard g p
      ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := pileDepth_bound; omega⟩ - j)
  flute_not_aces :
    (p.pileDepth.get i).toNat > 0 →
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := pileDepth_bound; omega⟩
    ∀ hs : (SUIT boundary).toNat < 4,
    (p.aces.get ⟨(SUIT boundary).toNat, hs⟩).toNat + (p.pileFlute.get i).toNat ≤
      boundary.toNat

/-- **The cleanup-established conditions for one pile `i`** — the (2)/(3b)/(6)
    subset that `SolverCleanupPile` adds on top of `SolverInvBase`.  Used as the
    per-pile part of the cleanup-loop invariant `MergedUpTo`.  Takes the depth
    bound as an explicit parameter (rather than its own field) so it stays a
    lean 3-field bundle — `PileClean` supplies it from `PileBase`'s own field,
    and `MergedUpTo`/`SolverInvMerged` supply it from `SolverInvBase`'s. -/
structure PileMerged (g : Globals) (p : SolverPosType) (i : Fin 10)
    (pileDepth_bound : (p.pileDepth.get i).toNat ≤ 5) : Prop where
  merge_complete :
    p.pileDepth.get i ≤ 1 ∨
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 2,
        by have := pileDepth_bound; omega⟩ ≠
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := pileDepth_bound; omega⟩ + 1
  flute_maximal :
    p.pileDepth.get i = 0 ∨
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := pileDepth_bound; omega⟩
    let prevCard := boundary - p.pileFlute.get i
    (∃ hs : (SUIT boundary).toNat < 4,
      p.aces.get ⟨(SUIT boundary).toNat, hs⟩ = prevCard) ∨
    ¬ isFreeCard g p prevCard
  busyAces_complete :
    (p.pileDepth.get i).toNat > 0 →
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := pileDepth_bound; omega⟩
    ∀ hs : (SUIT boundary).toNat < 4,
    (p.aces.get ⟨(SUIT boundary).toNat, hs⟩) = boundary - p.pileFlute.get i →
    p.busyAces &&& ((1 : UInt8) <<< (SUIT boundary)) ≠ 0

/-- **All per-pile conditions for one pile `i`.**  Fixing the pile index, this
    bundles every pile-local conjunct of the tower (base + merged).  A pile is
    "clean" exactly when `SolverCleanupPile` has finished with it. -/
structure PileClean (g : Globals) (p : SolverPosType) (i : Fin 10) : Prop
    extends PileBase g p i, PileMerged g p i (by have := pileDepth_bound; omega)

/-- **All per-suit conditions for one suit `s`** — the foundation/king conjuncts
    of the tower, fixing the suit index. -/
structure SuitClean (g : Globals) (p : SolverPosType) (s : Fin 4)
    (pileDepth_bound : ∀ i : Fin 10, (p.pileDepth.get i).toNat ≤ 5) : Prop where
  /-- **(1) Aces and kings well-formedness.** For each suit `s`:
      - `aces[s]` has suit `s` and value in `[0, 13]`;
      - `kings[s]` has suit `s` and value in `[0, 13]`;
      - `aces[s] ≤ kings[s]`.

      `aces[s] == kings[s]` is unconditionally *allowed* here.  If value < 13 this
      means that the king flute can be moved to foundation and `busyAces` should have
      the corresponding bit set. -/
  aces_kings_valid :
    SUIT (p.aces.get s) = s.val.toUInt8 ∧
    (VALUE (p.aces.get s)).toNat ≤ 13 ∧
    SUIT (p.kings.get s) = s.val.toUInt8 ∧
    (VALUE (p.kings.get s)).toNat ≤ 13 ∧
    p.aces.get s ≤ p.kings.get s
  /-- **(4a) Foundation cards are free.** Every card of suit `s` with value
      between 1 and `VALUE(aces[s])` (inclusive) has been freed. -/
  foundation_cards_free : ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s)).toNat →
    isFreeCard g p c

  /-- **(4b-weak) Foundation maximal (intermediate form).**
    In the weak maximal form (which is true even before SolverCleanupPile), the next
    foundation card is either not free, the top card of a pile, or the top card of
    a king flute.
    The strong form, when `busyAces = 0` then implies that the next foundation card
    is not free (and not even the boundary card of a pile.) -/
  foundation_maximal_weak:
    (VALUE (p.aces.get s)).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s) + 1) ∨
    p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0

  /-- **(5) King frontier.** Either `kings[s] = aces[s]` — because the suit is
      complete (all 13 cards in the foundation or king flute), or the king frontier
      is not free.  If kings[s]=aces[s], then it's either = 13 or the aces must
      be marked as busy.
      In any case all cards > kings[s] up to and includeing the king are free. -/
  king_frontier :
    ((p.kings.get s = p.aces.get s ∧
        ((VALUE (p.aces.get s)).toNat = 13 ∨
          p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0)) ∨
      (p.aces.get s < p.kings.get s
       ∧ ¬ isFreeCard g p (p.kings.get s))) ∧
    ∀ c : UInt8,
      SUIT c = s.val.toUInt8 →
      (VALUE c).toNat > (VALUE (p.kings.get s)).toNat →
      (VALUE c).toNat ≤ 13 →
      isFreeCard g p c

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

  /-- **(0)/(0b)/(3)/(3a)/(3c)** Every pile satisfies the base per-pile
      conditions (depth bound/non-negativity, flute length/emptiness, flute
      cards free, interior flute cards not aces-captured) — see `PileBase`. -/
  pileBase : ∀ i : Fin 10, PileBase g p i

  /-- **(1) (4) (5) ** Every suit satisfies the per suit requirements. -/
  suitClean : ∀ s : Fin 4, SuitClean g p s (fun i => (pileBase i).pileDepth_bound)

  /-- **(8) Hash formula.** The hash is the dot product of `pileHashes` and
      `pileDepth` (mod 2^32), so it is uniquely determined by `pileDepth`. -/
  hash_def : p.hash = (List.finRange 10).foldl
    (fun acc i => acc + pileHashes.get i * (p.pileDepth.get i).toNat.toUInt32) 0

  /-- **(10) Used-space formula.**  The merge-loop depth decrements and the
      lone-king `usedSpace` correction cancel exactly, leaving:
        usedSpace = 52 − Σ depths − Σ VALUE(aces[s]) − Σ_{dp>0} (pileFlute[i]−1). -/
  usedSpace_def : p.usedSpace.toInt =
    (52 : Int)
    - (p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
    - (p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
    - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (· + ·) 0 : Nat)

  /-- **(11) `busyAces` only ever uses its low 4 bits.**  Every write to
      `busyAces` anywhere in the solver either leaves it alone or ORs in
      exactly `1 <<< SUIT B` for some *real* card `B` (a `pos2card` entry,
      via `WellFormedLayout.pos2card_real`), and `SUIT` of a real card is
      always `< 4` — so bits `4..7` are never set.  This isn't visible from
      any of the *other* fields above (`foundation_maximal_weak`/
      `king_frontier`/`busyAces_complete` only ever *test* bits `s.val` for
      `s : Fin 4`, never excluding higher ones), so it needs its own field.
      `SolverMoveAces` genuinely needs it: it uses `ctz p.busyAces` as a raw
      index into the 4-entry `aces`/`kings` vectors. -/
  busyAces_lt16 : p.busyAces < 16

/-- Shims preserving the pre-refactor field-access names now that
    `pileDepth_bound`/`pileDepth_nonneg`/`flute_pos`/`flute_empty`/
    `flute_cards_free`/`flute_not_aces` are bundled into
    `pileBase : ∀ i, PileBase g p i`. -/
theorem SolverInvBase.pileDepth_bound {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (i : Fin 10) : (p.pileDepth.get i).toNat ≤ 5 :=
  (h.pileBase i).pileDepth_bound

theorem SolverInvBase.pileDepth_nonneg {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (i : Fin 10) : 0 ≤ p.pileDepth.get i :=
  (h.pileBase i).pileDepth_nonneg

theorem SolverInvBase.flute_pos {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (i : Fin 10) : 1 ≤ (p.pileFlute.get i).toNat :=
  (h.pileBase i).flute_pos

theorem SolverInvBase.flute_empty {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (i : Fin 10) :
    p.pileDepth.get i = 0 → p.pileFlute.get i = 1 :=
  (h.pileBase i).flute_empty

theorem SolverInvBase.flute_cards_free {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (i : Fin 10) (j : UInt8) :
    (p.pileDepth.get i).toNat > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    isFreeCard g p
      ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := h.pileDepth_bound i; omega⟩ - j) :=
  (h.pileBase i).flute_cards_free j

-- `SolverInvBase.flute_not_aces` (the per-offset UInt8-comparison shim derived from the
-- new Nat-based `PileBase.flute_not_aces` field) is defined further below, after
-- `int8_nonneg_of_suit`/`SUIT_toNat`/`VALUE_toNat` (its proof needs them) — see the
-- theorem of the same name just before `PileBase.flute_le_value`.

theorem SolverInvBase.aces_kings_valid {g p}
    (h : SolverInvBase g p) (s : Fin 4) :
    SUIT (p.aces.get s) = s.val.toUInt8 ∧
    (VALUE (p.aces.get s)).toNat ≤ 13 ∧
    SUIT (p.kings.get s) = s.val.toUInt8 ∧
    (VALUE (p.kings.get s)).toNat ≤ 13 ∧
    p.aces.get s ≤ p.kings.get s :=
    (h.suitClean s).aces_kings_valid

theorem SolverInvBase.foundation_cards_free {g p}
    (h : SolverInvBase g p) (s : Fin 4) :
    ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s)).toNat →
    isFreeCard g p c :=
    (h.suitClean s).foundation_cards_free

theorem SolverInvBase.foundation_maximal_weak {g p}
    (h : SolverInvBase g p) (s : Fin 4) :
    (VALUE (p.aces.get s)).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s) + 1) ∨
    p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0 :=
    (h.suitClean s).foundation_maximal_weak

theorem SolverInvBase.king_frontier {g p}
    (h : SolverInvBase g p) (s : Fin 4) :
    ((p.kings.get s = p.aces.get s ∧
        ((VALUE (p.aces.get s)).toNat = 13 ∨
          p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0)) ∨
      (p.aces.get s < p.kings.get s ∧ ¬ isFreeCard g p (p.kings.get s))) ∧
    ∀ c : UInt8,
      SUIT c = s.val.toUInt8 →
      (VALUE c).toNat > (VALUE (p.kings.get s)).toNat →
      (VALUE c).toNat ≤ 13 →
      isFreeCard g p c :=
    (h.suitClean s).king_frontier

/-! ## The local layer

`SolverInvBase`'s per-pile and per-suit conditions on their own, without the `hash` and
`usedSpace` formulas.  Everything the *cleanup simulation* reads lives here, and the
split matters for one reason: a **relaxed reading** of a position — one whose flutes are
the runs a state physically carries rather than the solver's own, shorter ones —
satisfies exactly these and *not* `usedSpace_def`, whose right-hand side charges the
extra run cards to the cells. -/

/-- The pile-local and suit-local part of `SolverInvBase`. -/
structure SolverInvLocal (g : Globals) (p : SolverPosType) : Prop where
  pileBase : ∀ i : Fin 10, PileBase g p i
  suitClean : ∀ s : Fin 4, SuitClean g p s (fun i => (pileBase i).pileDepth_bound)

theorem SolverInvBase.toLocal {g : Globals} {p : SolverPosType} (h : SolverInvBase g p) :
    SolverInvLocal g p := ⟨h.pileBase, h.suitClean⟩

theorem SolverInvLocal.pileDepth_bound {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (i : Fin 10) : (p.pileDepth.get i).toNat ≤ 5 :=
  (h.pileBase i).pileDepth_bound

theorem SolverInvLocal.pileDepth_nonneg {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (i : Fin 10) : 0 ≤ p.pileDepth.get i :=
  (h.pileBase i).pileDepth_nonneg

theorem SolverInvLocal.flute_pos {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (i : Fin 10) : 1 ≤ (p.pileFlute.get i).toNat :=
  (h.pileBase i).flute_pos

theorem SolverInvLocal.flute_empty {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (i : Fin 10) :
    p.pileDepth.get i = 0 → p.pileFlute.get i = 1 :=
  (h.pileBase i).flute_empty

theorem SolverInvLocal.flute_cards_free {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (i : Fin 10) (j : UInt8) :
    (p.pileDepth.get i).toNat > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    isFreeCard g p
      ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := h.pileDepth_bound i; omega⟩ - j) :=
  (h.pileBase i).flute_cards_free j

theorem SolverInvLocal.aces_kings_valid {g p}
    (h : SolverInvLocal g p) (s : Fin 4) :
    SUIT (p.aces.get s) = s.val.toUInt8 ∧
    (VALUE (p.aces.get s)).toNat ≤ 13 ∧
    SUIT (p.kings.get s) = s.val.toUInt8 ∧
    (VALUE (p.kings.get s)).toNat ≤ 13 ∧
    p.aces.get s ≤ p.kings.get s :=
    (h.suitClean s).aces_kings_valid

theorem SolverInvLocal.foundation_cards_free {g p}
    (h : SolverInvLocal g p) (s : Fin 4) :
    ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s)).toNat →
    isFreeCard g p c :=
    (h.suitClean s).foundation_cards_free

theorem SolverInvLocal.king_frontier {g p}
    (h : SolverInvLocal g p) (s : Fin 4) :
    ((p.kings.get s = p.aces.get s ∧
        ((VALUE (p.aces.get s)).toNat = 13 ∨
          p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0)) ∨
      (p.aces.get s < p.kings.get s ∧ ¬ isFreeCard g p (p.kings.get s))) ∧
    ∀ c : UInt8,
      SUIT c = s.val.toUInt8 →
      (VALUE c).toNat > (VALUE (p.kings.get s)).toNat →
      (VALUE c).toNat ≤ 13 →
      isFreeCard g p c :=
    (h.suitClean s).king_frontier

/-- **Middle layer of the tower.**  Extends `SolverInvBase` with the invariants
    from `PileMerged` pile-by-pile: (2) `merge_complete`,
    (3b) `flute_maximal`, and (6) `busyAces_complete` (rephrased per pile),
    plus the **(9)** *global*
    free-piles count.

    A `SolverInvMerged` state is "canonical except the foundation drain has not
    run": every pile is clean, but `busyAces` may still be non-zero.  This is the
    state after `SolverConvertFromPilesKings`'s cleanup loop, after `SolverRemoveFromPile`,
    and the state between successive `SolverMoveAces` calls. -/
structure SolverInvMerged (g : Globals) (p : SolverPosType) : Prop extends SolverInvBase g p where

  /-- **(2)/(3b)/(6)** Every pile satisfies the cleanup-established conditions
      (merge complete, flute maximal, busyAces complete) — see `PileMerged`. -/
  pileMerged : ∀ i : Fin 10, PileMerged g p i (pileBase i).pileDepth_bound

  /-- **(9) Free-piles count.** `freePiles` equals the number of piles whose
      depth is zero.  (Lone-king piles are vacated to depth 0 during cleanup.) -/
  freePiles_def : p.freePiles.toInt =
    (p.pileDepth.toList.countP (· == 0) : Nat)

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

/-- Number of already-emptied piles among the first `k`.  During the cleanup loop
    `freePiles` counts only the piles processed so far (`< k`), not the raw piles
    still awaiting cleanup; at `k = 10` this coincides with the global count. -/
def freePilesUpTo (p : SolverPosType) (k : Nat) : Nat :=
  (p.pileDepth.toList.take k).countP (· == 0)

@[simp] theorem freePilesUpTo_ten (p : SolverPosType) :
    freePilesUpTo p 10 = p.pileDepth.toList.countP (· == 0) := by
  unfold freePilesUpTo
  rw [List.take_of_length_le (by simp)]

/-- **Cleanup-loop invariant.**  `SolverInvBase` holds globally, `freePiles`
    matches the *prefix-relative* count `freePilesUpTo … k` (the cleanup loop
    builds `freePiles` up pile-by-pile — it counts only the already-processed
    piles `< k`, not the raw piles still awaiting cleanup), the first `k`
    piles have additionally been cleaned (`PileMerged`), and every pile `≥ k`
    (not yet reached by the loop) still carries the default `pileFlute = 1` —
    nothing but pile `k`'s own cleanup step ever touches pile `k`'s flute, so
    this holds throughout and is exactly what makes `fluteNorm` a no-op on
    pile `k` (needed to bridge to `cleanupPile_base`'s fluteNorm'd
    precondition — see `solverCleanupPile_step`).  `MergedUpTo … 0` is the
    state right after setup, and `MergedUpTo … 10` is exactly `SolverInvMerged`
    (where the prefix count becomes the global `freePiles_def`, and the new
    flute clause is vacuous — no `i : Fin 10` has `i.val ≥ 10`; see
    `mergedUpTo_ten_iff`). -/
def MergedUpTo (g : Globals) (p : SolverPosType) (k : Nat) : Prop :=
  ∃ h : SolverInvBase g p, p.freePiles.toInt = (freePilesUpTo p k : Nat) ∧
    (∀ i : Fin 10, i.val < k → PileMerged g p i (h.pileDepth_bound i)) ∧
    (∀ i : Fin 10, k ≤ i.val → p.pileFlute.get i = 1)

-- ---------------------------------------------------------------------------
-- Bridge lemmas between the components and the tower
-- ---------------------------------------------------------------------------

/-- `MergedUpTo … 10` is exactly the middle layer of the tower. -/
theorem mergedUpTo_ten_iff {g : Globals} {p : SolverPosType} :
    MergedUpTo g p 10 ↔ SolverInvMerged g p := by
  constructor
  · rintro ⟨hbase, hfp, hpm, _⟩
    exact ⟨hbase, fun i => hpm i i.isLt, hfp.trans (by rw [freePilesUpTo_ten])⟩
  · intro h
    refine ⟨h.toSolverInvBase, ?_, fun i _ => h.pileMerged i, fun i hi => absurd i.isLt (by omega)⟩
    rw [freePilesUpTo_ten]; exact h.freePiles_def

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
    (hm : SolverInvMerged g p) (hb : p.busyAces = 0) : IsCanonicalPos g p :=
  ⟨hm, hb⟩

/-- Build the middle layer from the base layer plus per-pile cleanup facts. -/
theorem SolverInvMerged.of_base {g : Globals} {p : SolverPosType}
    (hbase : SolverInvBase g p) (hpm : ∀ i, PileMerged g p i (hbase.pileDepth_bound i))
    (hfp : p.freePiles.toInt = (p.pileDepth.toList.countP (· == 0) : Nat)):
    SolverInvMerged g p :=
  ⟨hbase, hpm, hfp⟩

/-- Shims preserving the pre-refactor field-access names now that
    `merge_complete`/`flute_maximal`/`busyAces_complete` are bundled into
    `pileMerged : ∀ i, PileMerged g p i _`. -/
theorem SolverInvMerged.merge_complete {g : Globals} {p : SolverPosType}
    (h : SolverInvMerged g p) (i : Fin 10) :
    p.pileDepth.get i ≤ 1 ∨
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 2,
        by have := h.pileDepth_bound i; omega⟩ ≠
    (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩ + 1 :=
  (h.pileMerged i).merge_complete

theorem SolverInvMerged.flute_maximal {g : Globals} {p : SolverPosType}
    (h : SolverInvMerged g p) (i : Fin 10) :
    p.pileDepth.get i = 0 ∨
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩
    let prevCard := boundary - p.pileFlute.get i
    (∃ hs : (SUIT boundary).toNat < 4,
      p.aces.get ⟨(SUIT boundary).toNat, hs⟩ = prevCard) ∨
    ¬ isFreeCard g p prevCard :=
  (h.pileMerged i).flute_maximal

theorem SolverInvMerged.busyAces_complete {g : Globals} {p : SolverPosType}
    (h : SolverInvMerged g p) (i : Fin 10) :
    (p.pileDepth.get i).toNat > 0 →
    let boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩
    ∀ hs : (SUIT boundary).toNat < 4,
    (p.aces.get ⟨(SUIT boundary).toNat, hs⟩) = boundary - p.pileFlute.get i →
    p.busyAces &&& ((1 : UInt8) <<< (SUIT boundary)) ≠ 0 :=
  (h.pileMerged i).busyAces_complete

-- ---------------------------------------------------------------------------
-- Arithmetic helpers for SUIT / VALUE
-- ---------------------------------------------------------------------------

private theorem nat_and_15 (n : Nat) : n &&& 15 = n % 16 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod n 4

theorem VALUE_toNat (c : UInt8) : (VALUE c).toNat = c.toNat % 16 := by
  simp [VALUE, UInt8.toNat_and, nat_and_15]

theorem SUIT_toNat (c : UInt8) : (SUIT c).toNat = c.toNat / 16 := by
  simp [SUIT, Nat.shiftRight_eq_div_pow]

theorem toNat_succ (c : UInt8) (hc : c.toNat < 255) : (c + 1).toNat = c.toNat + 1 := by
  simp only [UInt8.toNat_add, UInt8.toNat_ofNat]; omega

/-- Adding 1 to a card preserves suit when its value is at most 14. -/
theorem SUIT_succ (c : UInt8) (h : (VALUE c).toNat < 15) : SUIT (c + 1) = SUIT c := by
  apply UInt8.toNat_inj.mp; rw [SUIT_toNat, SUIT_toNat]
  have hv := VALUE_toNat c
  rw [toNat_succ c (by have := c.toNat_lt; omega)]; omega

/-- Adding 1 to a card increments its value when the value is at most 14. -/
theorem VALUE_succ (c : UInt8) (h : (VALUE c).toNat < 15) :
    (VALUE (c + 1)).toNat = (VALUE c).toNat + 1 := by
  simp only [VALUE_toNat]
  have hv := VALUE_toNat c
  rw [toNat_succ c (by have := c.toNat_lt; omega)]; omega

/-- Two cards with the same suit and value are equal. -/
theorem card_eq_of_suit_value (c d : UInt8)
    (hs : SUIT c = SUIT d) (hv : (VALUE c).toNat = (VALUE d).toNat) : c = d := by
  apply UInt8.toNat_inj.mp
  have hsc : c.toNat = (SUIT c).toNat * 16 + (VALUE c).toNat := by
    rw [SUIT_toNat, VALUE_toNat]; omega
  have hsd : d.toNat = (SUIT d).toNat * 16 + (VALUE d).toNat := by
    rw [SUIT_toNat, VALUE_toNat]; omega
  rw [hsc, hsd, hs, hv]

-- ---------------------------------------------------------------------------
-- Arithmetic helpers for UInt8 / toNatClampNeg
-- ---------------------------------------------------------------------------

private theorem toNatClampNeg_pos {x : UInt8} (_h1 : 0 ≤ x) (h2 : x ≠ 0) :
    x.toNat > 0 := by
  have h3 : x.toNat ≠ 0 := fun h => h2 (UInt8.toNat_inj.mp h)
  omega

/-- Trivial now that the field is `uint8_t`: every value is non-negative.
    (Kept so downstream call sites need no change.) -/
theorem int8_nonneg_of_suit {x : UInt8} {s : Fin 4}
    (_hs : SUIT x = s.val.toUInt8) : (0 : UInt8) ≤ x :=
  UInt8.le_iff_toNat_le.mpr (Nat.zero_le _)

/-- **Per-offset `UInt8` shim, derived from the Nat-based `PileBase.flute_not_aces`
    field.**  Preserves the pre-refactor call shape (`h.flute_not_aces i j hdi hj0
    hjlt hs : aces < (boundary - j)`) used throughout this file, now proved
    from the new field `aces.toNat + pileFlute.toNat ≤ boundary.toNat`
    (wraparound-safe: `aces` is nonnegative via `aces_kings_valid`/`int8_nonneg_of_suit`,
    and `boundary` is `< 64` via `WellFormedLayout`/`IsRealCard`, so every UInt8/UInt8
    cast involved stays comfortably below the 128 sign threshold). -/
theorem SolverInvLocal.flute_not_aces {g : Globals} {p : SolverPosType}
    (h : SolverInvLocal g p) (hwf : WellFormedLayout g) (i : Fin 10) (j : UInt8) :
    (p.pileDepth.get i).toNat > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩)).toNat < 4,
    p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩)).toNat, hs⟩ <
    ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩ - j) := by
  intro hdi hj0 hjlt hs
  set boundary := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
      by have := h.pileDepth_bound i; omega⟩ with hbdef
  set aces := p.aces.get ⟨(SUIT boundary).toNat, hs⟩ with hacesdef
  -- Obtain the new Nat-based field fact with an explicit type ascription (rather
  -- than relying on `set`'s syntactic rewriting to fold it) — the field's own
  -- internal `pileDepth_bound` proof term differs syntactically from ours, so we
  -- let `isDefEq`/proof-irrelevance bridge the two instead of `kabstract`.
  have hbound : aces.toNat + (p.pileFlute.get i).toNat ≤ boundary.toNat :=
    (h.pileBase i).flute_not_aces hdi hs
  -- `aces` carries the same suit as `boundary`, so it's a real (nonnegative) card.
  have haces_nonneg : (0 : UInt8) ≤ aces :=
    int8_nonneg_of_suit ((h.aces_kings_valid ⟨(SUIT boundary).toNat, hs⟩).1)
  -- `boundary` itself is a real card (WellFormedLayout), hence < 64.
  have hreal : IsRealCard boundary := hwf.pos2card_real i _
  have hb64 : boundary.toNat < 64 := by
    have h1 := hreal.1
    have h2 := hreal.2.2
    have h3 := SUIT_toNat boundary
    have h4 := VALUE_toNat boundary
    omega
  -- No underflow: j.toNat < pileFlute.toNat ≤ boundary.toNat (from hbound, since
  -- aces.toNat ≥ 0), so the `UInt8` subtraction is a plain Nat subtraction.
  have hjleU : j ≤ boundary := by
    rw [UInt8.le_iff_toNat_le]
    omega
  have hsub : (boundary - j).toNat = boundary.toNat - j.toNat :=
    UInt8.toNat_sub_of_le _ _ hjleU
  -- Pure Nat arithmetic, no wraparound concern: both sides stay well below 128.
  have haces_lt : aces.toNat < (boundary - j).toNat := by
    rw [hsub]; omega
  rw [UInt8.lt_iff_toInt_lt]
  have hLHS : aces.toInt = (aces.toNat : Int) := rfl
  have hRHS : ((boundary - j)).toInt = ((boundary - j).toNat : Int) := rfl
  rw [hLHS, hRHS]
  exact_mod_cast haces_lt

/-- **Per-pile counterpart of `SolverInvBase.flute_le_value`.**  `PileClean`
    bundles only per-pile facts, so it has no `aces_kings_valid` of its own —
    the one extra ingredient needed (the ace's own suit matches, so it can't
    sit below its own suit's block) is taken as an explicit hypothesis instead
    of reached through a full `SolverInvBase`. Same proof as the base
    version otherwise. -/
theorem PileBase.flute_le_value {g : Globals} {p : SolverPosType} {i : Fin 10}
    (hc : PileBase g p i) (hwf : WellFormedLayout g)
    (hak : ∀ s : Fin 4, SUIT (p.aces.get s) = s.val.toUInt8)
    (hdi : (p.pileDepth.get i).toNat > 0) :
    (p.pileFlute.get i).toNat ≤
      (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := hc.pileDepth_bound; omega⟩)).toNat := by
  set B := (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
      by have := hc.pileDepth_bound; omega⟩ with hBdef
  have hreal : IsRealCard B := hwf.pos2card_real i _
  have hs4 : (SUIT B).toNat < 4 := hreal.1
  set S := (SUIT B).toNat with hSdef
  -- Explicit type ascription (rather than relying on syntactic folding): the new
  -- Nat-based field, directly giving the bound with no offset/case-split needed.
  have hna : (p.aces.get ⟨S, hs4⟩).toNat + (p.pileFlute.get i).toNat ≤ B.toNat :=
    hc.flute_not_aces hdi hs4
  have hSAeq : (SUIT (p.aces.get ⟨S, hs4⟩)).toNat = S := by
    have h1 := congrArg UInt8.toNat (hak ⟨S, hs4⟩)
    have h2 : ((⟨S, hs4⟩ : Fin 4).val.toUInt8).toNat = S := by
      show (S.toUInt8).toNat = S
      rw [UInt8.toNat_ofNat']
      omega
    omega
  have hAdecomp : (p.aces.get ⟨S, hs4⟩).toNat =
      16 * S + (VALUE (p.aces.get ⟨S, hs4⟩)).toNat := by
    have h1 := SUIT_toNat (p.aces.get ⟨S, hs4⟩)
    have h2 := VALUE_toNat (p.aces.get ⟨S, hs4⟩)
    omega
  have hBdecomp : B.toNat = 16 * S + (VALUE B).toNat := by
    have h1 := SUIT_toNat B
    have h2 := VALUE_toNat B
    omega
  -- aces.toNat ≥ 16*S (suit-block lower bound), combined with `hna` and
  -- the 16*S+VALUE decomposition of `B.toNat`, gives the bound directly — no
  -- wraparound, no case-split, just Nat arithmetic.
  omega

/-- **(3e) Flute length bounded by card value** — derived, not a base-invariant
    field.  `pileFlute[i] ≤ VALUE(boundary)`: if the flute reached down to
    offset `VALUE(boundary)` or beyond, `flute_not_aces` would force
    `aces[suit] < boundary − VALUE(boundary)`, i.e. `aces[suit]` strictly below
    the suit's own zero-value sentinel (`SUIT`/`VALUE` decompose a card as
    `suit*16 + value`, so subtracting the boundary's own value lands exactly on
    `suit*16`) — but `aces_kings_valid` says `aces[suit]` HAS suit `suit`,
    contradiction (a suit-`s` card can't sit below `s`'s own block). -/
theorem SolverInvLocal.flute_le_value {g : Globals} {p : SolverPosType}
    (hbase : SolverInvLocal g p) (hwf : WellFormedLayout g) (i : Fin 10)
    (hdi : (p.pileDepth.get i).toNat > 0) :
    (p.pileFlute.get i).toNat ≤
      (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := hbase.pileDepth_bound i; omega⟩)).toNat :=
    (hbase.pileBase i).flute_le_value hwf (fun s => (hbase.aces_kings_valid s).1) hdi

theorem SolverInvBase.flute_not_aces {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (hwf : WellFormedLayout g) (i : Fin 10) (j : UInt8) :
    (p.pileDepth.get i).toNat > 0 →
    0 < j.toNat → j.toNat < (p.pileFlute.get i).toNat →
    ∀ hs : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩)).toNat < 4,
    p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩)).toNat, hs⟩ <
    ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
        by have := h.pileDepth_bound i; omega⟩ - j) :=
  h.toLocal.flute_not_aces hwf i j

theorem SolverInvBase.flute_le_value {g : Globals} {p : SolverPosType}
    (hbase : SolverInvBase g p) (hwf : WellFormedLayout g) (i : Fin 10)
    (hdi : (p.pileDepth.get i).toNat > 0) :
    (p.pileFlute.get i).toNat ≤
      (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := hbase.pileDepth_bound i; omega⟩)).toNat :=
  hbase.toLocal.flute_le_value hwf i hdi

/-- Every pile of a canonical position is clean. -/
theorem IsCanonicalPos.pileClean {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) (i : Fin 10) : PileClean g p i :=
  ⟨⟨h.pileDepth_bound i, h.pileDepth_nonneg i, h.flute_pos i,
    h.flute_empty i, h.flute_cards_free i, (h.pileBase i).flute_not_aces⟩,
   h.merge_complete i, h.flute_maximal i, h.busyAces_complete i⟩

/-- Canonical positions satisfy foundation maximal in the strong form -/
theorem IsCanonicalPos.foundation_maximal {g: Globals} {p: SolverPosType}
    (_hwf : WellFormedLayout g) (h : IsCanonicalPos g p) (s : Fin 4) :
    (VALUE (p.aces.get s)).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s) + 1) := by
    rcases h.foundation_maximal_weak s with h13 | hnfree | hbusy
    · exact Or.inl h13
    · exact Or.inr hnfree
    · exact absurd hbusy (by rw [h.busyAces_zero]; simp)

/-- **Kings have value `≥ 1` in canonical positions.**  The base layer no longer
    requires this (the lone-king branch of `SolverCleanupPile` can transiently
    drive `kings[s]` to the value-0 sentinel), but once the foundation drain has
    run it is forced: value 0 would make the suit's ace free (everything above
    `kings[s]` is free by `king_frontier`) while the foundation is empty,
    contradicting the strong `foundation_maximal`. -/
theorem IsCanonicalPos.kings_value_pos {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : IsCanonicalPos g p) (s : Fin 4) :
    1 ≤ (VALUE (p.kings.get s)).toNat := by
  obtain ⟨hsa, hva, hsk, hvk, hak⟩ := h.aces_kings_valid s
  by_contra h0
  have hvk0 : (VALUE (p.kings.get s)).toNat = 0 := by omega
  -- `aces ≤ kings` within one suit forces `VALUE(aces) = 0` as well.
  have hna : (0 : UInt8) ≤ p.aces.get s := int8_nonneg_of_suit hsa
  have hnk : (0 : UInt8) ≤ p.kings.get s := int8_nonneg_of_suit hsk
  have hle : (p.aces.get s).toNat ≤ (p.kings.get s).toNat :=
    UInt8.le_iff_toNat_le.mp hak
  have hsuits : (p.aces.get s).toNat / 16 = (p.kings.get s).toNat / 16 := by
    have h1 := congrArg UInt8.toNat hsa
    have h2 := congrArg UInt8.toNat hsk
    rw [SUIT_toNat] at h1 h2
    omega
  have hva0 : (VALUE (p.aces.get s)).toNat = 0 := by
    rw [VALUE_toNat] at hvk0 ⊢
    omega
  -- The ace card sits strictly above `kings[s]`, so `king_frontier` frees it
  -- (its `∀c`-clause is unconditional — no case split needed).
  have hfree : isFreeCard g p ((p.aces.get s) + 1) := by
    have hall := (h.king_frontier s).2
    refine hall _ ((SUIT_succ _ (by omega)).trans hsa) ?_ ?_
    · rw [VALUE_succ _ (by omega)]; omega
    · rw [VALUE_succ _ (by omega)]; omega
  -- …but the foundation is empty, contradicting strong foundation-maximality.
  rcases h.foundation_maximal hwf s with h13 | hnfree
  · omega
  · exact hnfree hfree

-- ---------------------------------------------------------------------------
-- Cross-pile disjointness (towards `usedSpace ≥ 0`)
--
-- `boundary_not_free` is the key structural fact: a pile's own current top
-- card is never free.  It follows purely from `WellFormedLayout`'s
-- `round_trip_inv` (the slot a card sits in reports itself as that card's own
-- `cardPile`/`cardDepth`) plus the definition of `isFreeCard`: the boundary
-- sits at original depth `d-1` while the pile's *current* depth is `d`, and
-- `isFreeCard` requires original depth ≥ current depth.
--
-- Consequence: for two piles sharing a suit, the lower-value pile's boundary
-- blocks the higher-value pile's freed-loop from reaching past it (the walk
-- can only proceed onto *free* cards), so their flutes cannot overlap.  This
-- is the disjointness fact `usedSpace ≥ 0` ultimately rests on.
-- ---------------------------------------------------------------------------

/-- **Full cross-pile injectivity of `pos2card`.**  Distinct slots *anywhere*
    in the layout — not just within one pile, as the old `pos2card_inj` field
    stated — hold distinct cards.  Immediate from `round_trip_inv`: if the same
    card sits at both `(p1, d1)` and `(p2, d2)`, applying `round_trip_inv` to
    each slot recovers `(p1, d1)` and `(p2, d2)` as that card's own recorded
    `(cardPile, cardDepth)` — so they must be the same slot. -/
theorem WellFormedLayout.pos2card_inj {g : Globals} (hwf : WellFormedLayout g)
    (p1 p2 : Fin 10) (d1 d2 : Fin 5)
    (heq : (g.pos2card.get p1).get d1 = (g.pos2card.get p2).get d2) :
    p1 = p2 ∧ d1 = d2 := by
  obtain ⟨hp1, hd1⟩ := hwf.round_trip_inv p1 d1
  obtain ⟨hp2, hd2⟩ := hwf.round_trip_inv p2 d2
  rw [heq] at hp1 hd1
  exact ⟨Fin.ext (hp1.symm.trans hp2), Fin.ext (hd1.symm.trans hd2)⟩

/-- **A pile's current top card is never free.**  Direct consequence of
    `round_trip_inv`: the boundary card's own recorded `(cardPile, cardDepth)` is
    exactly `(i, d-1)`, one less than the pile's current depth `d`, so
    `isFreeCard`'s `origDepth ≥ currentDepth` test fails. -/
theorem depth_card_not_free_wf {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (i : Fin 10) (d : Fin 5)
    (hd : d.val < (p.pileDepth.get i).toNat) :
    ¬ isFreeCard g p ((g.pos2card.get i).get d) := by
  set c := (g.pos2card.get i).get d with hcdef
  have hreal : IsRealCard c := hwf.pos2card_real i d
  have h64 : c.toNat < 64 := by
    have hsn := SUIT_toNat c
    have h1 := hreal.1
    omega
  obtain ⟨hpileEq, hdepthEq⟩ := hwf.round_trip_inv i d
  unfold isFreeCard
  simp only [dif_pos h64]
  have hpileEq' : g.card2pile.get ⟨c.toNat, h64⟩ = cardPile g c := by unfold cardPile; simp [h64]
  have hpile64 : (cardPile g c).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt c.toNat h64
  simp only [hpileEq', dif_pos hpile64]
  have hdepthEq' : g.card2depth.get ⟨c.toNat, h64⟩ = cardDepth g c := by
    unfold cardDepth; simp [h64]
  rw [hdepthEq']
  have hpileI : (⟨(cardPile g c).toNat, hpile64⟩ : Fin 10) = i := Fin.ext hpileEq
  rw [show (p.pileDepth.get ⟨(cardPile g c).toNat, hpile64⟩) = p.pileDepth.get i from
    congrArg p.pileDepth.get hpileI]
  have hdepthEq2 : (cardDepth g c).toNat = d.val := hdepthEq
  show ¬ (cardDepth g c).toNat ≥ (p.pileDepth.get i).toNat
  omega

/-- The layout is all this needs; the invariant argument of the original spelling was
already unused. -/
theorem depth_card_not_free {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (_h : SolverInvBase g p) (i : Fin 10) (d : Fin 5)
    (hd : d.val < (p.pileDepth.get i).toNat) :
    ¬ isFreeCard g p ((g.pos2card.get i).get d) :=
  depth_card_not_free_wf hwf i d hd

theorem boundary_not_free {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (h : SolverInvBase g p) (i : Fin 10)
    (hdi : (p.pileDepth.get i).toNat > 0) :
    ¬ isFreeCard g p ((g.pos2card.get i).get
        ⟨(p.pileDepth.get i).toNat - 1, by have := h.pileDepth_bound i; omega⟩) :=
  depth_card_not_free hwf h i ⟨(p.pileDepth.get i).toNat - 1,
    by have := h.pileDepth_bound i; omega⟩
    (show (p.pileDepth.get i).toNat - 1 < (p.pileDepth.get i).toNat by omega)

/-- `boundary_not_free`, at the local layer. -/
theorem boundary_not_free_local {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (h : SolverInvLocal g p) (i : Fin 10)
    (hdi : (p.pileDepth.get i).toNat > 0) :
    ¬ isFreeCard g p ((g.pos2card.get i).get
        ⟨(p.pileDepth.get i).toNat - 1, by have := h.pileDepth_bound i; omega⟩) :=
  depth_card_not_free_wf hwf i ⟨(p.pileDepth.get i).toNat - 1,
    by have := h.pileDepth_bound i; omega⟩
    (show (p.pileDepth.get i).toNat - 1 < (p.pileDepth.get i).toNat by omega)

/-- **A pile's flute never absorbs another pile's current top card.**  Direct
    corollary of `boundary_not_free`: interior flute cards are always free
    (`flute_cards_free`), but no pile's own boundary ever is, so a free card
    can never equal any pile's boundary. -/
theorem free_card_ne_boundary {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) (j : Fin 10)
    (hdj : (p.pileDepth.get j).toNat > 0) (k : UInt8)
    (hk : isFreeCard g p k) :
    k ≠ (g.pos2card.get j).get
      ⟨(p.pileDepth.get j).toNat - 1, by have := h.pileDepth_bound j; omega⟩ := by
  intro heq
  exact boundary_not_free hwf h j hdj (heq ▸ hk)

/-- **A pile's flute cannot reach down to or past a not-free card that sits
    below its boundary.**  If `C` is not free and `C < Bj` (pile `j`'s
    boundary), then every card in pile `j`'s flute footprint — boundary and
    interior alike — is strictly above `C`.  (Static counterpart of
    `SolverSpec.freed_below_other_boundary`, which needs the freed loop's
    live guard; here the blocker `C` is already known not-free, so no run
    history is needed — only `flute_cards_free`.)  Reaching to or below `C`
    would, by the flute's contiguous descent, claim `C` itself as an interior
    card, contradicting `flute_cards_free`. -/
theorem flute_stays_above {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p)
    (j : Fin 10) (hdj : (p.pileDepth.get j).toNat > 0)
    (C : UInt8) (hCnotfree : ¬ isFreeCard g p C)
    (hClt : C.toNat < ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := h.pileDepth_bound j; omega⟩ : UInt8).toNat)
    (offset : UInt8) (hoffLt : offset.toNat < (p.pileFlute.get j).toNat) :
    C.toNat < (((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := h.pileDepth_bound j; omega⟩ : UInt8) - offset).toNat := by
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1,
    by have := h.pileDepth_bound j; omega⟩ : Fin 5) with hBjdef
  have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
  have hBj64 : Bj.toNat < 64 := by
    have hsn := SUIT_toNat Bj; have h1 := hBjreal.1; omega
  -- `flute_le_value` bounds the flute length by `VALUE(Bj) ≤ Bj.toNat`, so
  -- `offset < flute_j` never reaches or exceeds `Bj` itself.
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE Bj).toNat := h.flute_le_value hwf j hdj
  have hVBj : (VALUE Bj).toNat ≤ Bj.toNat := by rw [VALUE_toNat]; omega
  have hoffle : offset.toNat < Bj.toNat := by omega
  by_contra hle
  push Not at hle
  have h1Bj : (1 : UInt8) ≤ Bj := by rw [UInt8.le_iff_toNat_le]; show 1 ≤ Bj.toNat; omega
  have hoffle' : offset ≤ Bj := by rw [UInt8.le_iff_toNat_le]; omega
  -- the target offset making `Bj - k = C` exactly
  set k := Bj.toNat - C.toNat with hkdef
  have hkof : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
  have hkoff : k ≤ offset.toNat := by
    have hsub : (Bj - offset).toNat = Bj.toNat - offset.toNat :=
      UInt8.toNat_sub_of_le _ _ hoffle'
    omega
  have hkoffLt : k < (p.pileFlute.get j).toNat := by omega
  have hkpos : 0 < k := by omega
  have hkle : UInt8.ofNat k ≤ Bj := by
    rw [UInt8.le_iff_toNat_le, hkof]; omega
  have hBjkC : Bj - UInt8.ofNat k = C := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hkle, hkof]
    omega
  have hfree := h.flute_cards_free j (UInt8.ofNat k) hdj (by rw [hkof]; exact hkpos)
    (by rw [hkof]; exact hkoffLt)
  rw [← hBjdef, hBjkC] at hfree
  exact hCnotfree hfree

-- ---------------------------------------------------------------------------
-- Cardinality bound (`usedSpace ≥ 0`)
--
-- `usedSpace_def` says `usedSpace = 52 − ΣDepth − ΣAceVal − ΣFluteTerm`.  To
-- show this is `≥ 0` we exhibit an injective map from a `ΣDepth+ΣAceVal+
-- ΣFluteTerm`-sized domain into the 52 real cards: depth-slot `(i,d)` ↦
-- `pos2card[i][d]`; ace-slot `(s,v)` ↦ `CARD s (v+1)`; flute-slot `(i,k)` ↦
-- the `(k+1)`-th interior card below pile `i`'s boundary.  Injectivity is
-- exactly the disjointness lemmas proved above (`pos2card_inj`,
-- `boundary_not_free`/`isFreeCard` dichotomy, `flute_not_aces`,
-- `flute_stays_above`).
-- ---------------------------------------------------------------------------

private def uint8ToFin256 (c : UInt8) : Fin 256 := ⟨c.toNat, c.toNat_lt⟩
private def finToUint8_256 (i : Fin 256) : UInt8 := UInt8.ofNat i.val

noncomputable instance : Fintype UInt8 := Fintype.ofEquiv (Fin 256)
  { toFun := finToUint8_256
    invFun := uint8ToFin256
    left_inv := fun i => by
      simp only [uint8ToFin256, finToUint8_256, UInt8.toNat_ofNat']
      have := i.isLt
      ext; simp
    right_inv := fun c => by
      simp only [uint8ToFin256, finToUint8_256]
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have := c.toNat_lt
      omega }

instance : DecidablePred IsRealCard := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The 52 valid card codes. -/
noncomputable def RealCardsFinset : Finset UInt8 := Finset.univ.filter IsRealCard

theorem RealCardsFinset.card_eq : RealCardsFinset.card = 52 := by decide

/-- `Vector.toList.foldl (fun acc x => acc + f x) 0 = Σ f (v.get i)`: bridges
    `usedSpace_def`'s `List.foldl`-based sums to `Finset.sum` over `Fin n`. -/
private theorem list_foldl_add_eq_sum (l : List Nat) : l.foldl (·+·) 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, Nat.zero_add]
    have h := @List.foldl_assoc Nat (·+·) _ l a 0
    simp only [Nat.add_zero] at h
    rw [h, ih, List.sum_cons]

private theorem vector_foldl_add_eq_finsum {n : Nat} {α : Type} (v : Vector α n) (f : α → Nat) :
    v.toList.foldl (fun acc x => acc + f x) 0 = ∑ i : Fin n, f (v.get i) := by
  have h1 : v.toList = List.ofFn v.get := by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp only [List.getElem_ofFn, Vector.getElem_toList]
      rfl
  rw [h1,
    show (List.ofFn v.get).foldl (fun acc x => acc + f x) 0 =
      ((List.ofFn v.get).map f).foldl (·+·) 0 from (List.foldl_map ..).symm,
    List.map_ofFn, list_foldl_add_eq_sum, List.sum_ofFn]
  rfl

private theorem zipWith_toList_eq_ofFn {n : Nat} {α β γ : Type} (g : α → β → γ)
    (v1 : Vector α n) (v2 : Vector β n) :
    List.zipWith g v1.toList v2.toList = List.ofFn (fun i => g (v1.get i) (v2.get i)) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn, List.getElem_zipWith]
    congr 1

private theorem zipWith_foldl_add_eq_finsum {n : Nat} {α β : Type}
    (v1 : Vector α n) (v2 : Vector β n) (g : α → β → Nat) :
    (List.zipWith g v1.toList v2.toList).foldl (·+·) 0 = ∑ i : Fin n, g (v1.get i) (v2.get i) := by
  rw [zipWith_toList_eq_ofFn, list_foldl_add_eq_sum, List.sum_ofFn]

/-- The counting domain: one unit per depth-counted card slot, per ace-counted
    card, and per interior flute card. -/
private def CountDomain (p : SolverPosType) : Type :=
  (Σ _i : Fin 10, Fin (p.pileDepth.get _i).toNat) ⊕
  (Σ _s : Fin 4, Fin (VALUE (p.aces.get _s)).toNat) ⊕
  (Σ _i : Fin 10, Fin (if (p.pileDepth.get _i).toNat ≠ 0 then
      (p.pileFlute.get _i).toNat - 1 else 0))

private instance (p : SolverPosType) : Fintype (CountDomain p) := by unfold CountDomain; infer_instance

/-- The card assigned to each unit: depth slot `(i,d)` ↦ `pos2card[i][d]`;
    ace unit `(s,v)` ↦ `CARD s (v+1)`; flute unit `(i,k)` ↦ the `(k+1)`-th
    interior card below pile `i`'s boundary. -/
private def cardOf (g : Globals) (p : SolverPosType) : CountDomain p → UInt8
  | .inl ⟨i, d⟩ =>
    if h : d.val < 5 then (g.pos2card.get i).get ⟨d.val, h⟩ else 0
  | .inr (.inl ⟨s, v⟩) => CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))
  | .inr (.inr ⟨i, k⟩) =>
    if h : (p.pileDepth.get i).toNat > 0 ∧
        (p.pileDepth.get i).toNat ≤ 5 then
      (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, by omega⟩ -
        UInt8.ofNat (k.val + 1)
    else 0

/-- `CARD s v` as raw `Nat` arithmetic, wrap-free for `s<16, v<16`. -/
theorem CARD_toNat {s v : Nat} (hs : s < 16) (hv : v < 16) :
    (CARD (UInt8.ofNat s) (UInt8.ofNat v)).toNat = s * 16 + v := by
  unfold CARD
  rw [UInt8.toNat_add, UInt8.toNat_shiftLeft]
  have h1 : (UInt8.ofNat s).toNat = s := by rw [UInt8.toNat_ofNat']; omega
  have h2 : (UInt8.ofNat v).toNat = v := by rw [UInt8.toNat_ofNat']; omega
  rw [h1, h2, show ((4:UInt8).toNat % 8 = 4) from by decide, Nat.shiftLeft_eq]
  omega

private theorem cardOf_isReal {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hdb : ∀ i : Fin 10, (p.pileDepth.get i).toNat ≤ 5)
    (hak : ∀ s : Fin 4, (VALUE (p.aces.get s)).toNat ≤ 13)
    (hflv : ∀ i : Fin 10, (p.pileDepth.get i).toNat > 0 →
      (p.pileFlute.get i).toNat ≤
        (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
            by have := hdb i; omega⟩)).toNat) :
    ∀ x : CountDomain p, IsRealCard (cardOf g p x) := by
  intro x
  match x with
  | .inl ⟨i, d⟩ =>
    have hd5 : d.val < 5 := by have := hdb i; have := d.isLt; omega
    simp only [cardOf, dif_pos hd5]
    exact hwf.pos2card_real i ⟨d.val, hd5⟩
  | .inr (.inl ⟨s, v⟩) =>
    simp only [cardOf]
    have hv13 : v.val + 1 ≤ 13 := by have := hak s; have := v.isLt; omega
    have hs4 : s.val < 4 := s.isLt
    have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat = s.val * 16 + (v.val + 1) :=
      CARD_toNat (by omega) (by omega)
    have hSv : (SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = s.val := by
      rw [SUIT_toNat, hct]; omega
    have hVv : (VALUE (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = v.val + 1 := by
      rw [VALUE_toNat, hct]; omega
    exact ⟨by rw [hSv]; omega, by rw [hVv]; omega, by rw [hVv]; omega⟩
  | .inr (.inr ⟨i, k⟩) =>
    simp only [cardOf]
    by_cases hd0 : (p.pileDepth.get i).toNat > 0 ∧
        (p.pileDepth.get i).toNat ≤ 5
    · simp only [dif_pos hd0]
      set B := (g.pos2card.get i).get
        (⟨(p.pileDepth.get i).toNat - 1, by omega⟩ : Fin 5) with hBdef
      have hBreal : IsRealCard B := hwf.pos2card_real i _
      have hB64 : B.toNat < 64 := by
        have hsn := SUIT_toNat B; have h1 := hBreal.1; omega
      have hflvB : (p.pileFlute.get i).toNat ≤ (VALUE B).toNat := hflv i hd0.1
      have hVB := VALUE_toNat B
      have hSB := SUIT_toNat B
      have hVB1 := hBreal.2.1
      have hVB2 := hBreal.2.2
      have hne : (p.pileDepth.get i).toNat ≠ 0 := by omega
      have heq : (if (p.pileDepth.get i).toNat ≠ 0 then
          (p.pileFlute.get i).toNat - 1 else 0) = (p.pileFlute.get i).toNat - 1 := if_pos hne
      have hthis := k.isLt
      have hkLt : k.val < (p.pileFlute.get i).toNat - 1 := by omega
      have h1B : (1 : UInt8) ≤ B := by
        rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
      have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hkle : UInt8.ofNat (k.val + 1) ≤ B := by
        rw [UInt8.le_iff_toNat_le, hkof]; omega
      have hsub : (B - UInt8.ofNat (k.val + 1)).toNat = B.toNat - (k.val + 1) := by
        rw [UInt8.toNat_sub_of_le _ _ hkle, hkof]
      refine ⟨?_, ?_, ?_⟩
      · show (SUIT (B - UInt8.ofNat (k.val + 1))).toNat < 4
        rw [SUIT_toNat, hsub]
        omega
      · show 1 ≤ (VALUE (B - UInt8.ofNat (k.val + 1))).toNat
        rw [VALUE_toNat, hsub]
        omega
      · show (VALUE (B - UInt8.ofNat (k.val + 1))).toNat ≤ 13
        rw [VALUE_toNat, hsub]
        omega
    · exfalso
      have hd0' : (p.pileDepth.get i).toNat = 0 := by have := hdb i; omega
      have hne : ¬ (p.pileDepth.get i).toNat ≠ 0 := by omega
      have heq : (if (p.pileDepth.get i).toNat ≠ 0 then
          (p.pileFlute.get i).toNat - 1 else 0) = 0 := if_neg hne
      have := k.isLt
      omega

/-- The boundary card of a non-empty pile, in closed form (matches `cardOf`'s
    own `if`-guarded computation, unfolded once the guard is known true). -/
private theorem cardOf_flute_eq {g : Globals} {p : SolverPosType} (i : Fin 10)
    (hd0 : (p.pileDepth.get i).toNat > 0 ∧ (p.pileDepth.get i).toNat ≤ 5)
    (k : Fin (if (p.pileDepth.get i).toNat ≠ 0 then (p.pileFlute.get i).toNat - 1 else 0)) :
    cardOf g p (.inr (.inr ⟨i, k⟩)) =
      (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, by omega⟩ -
        UInt8.ofNat (k.val + 1) := by
  simp only [cardOf, dif_pos hd0]

/-- Any offset `< flute_i` is `< 256`, so its `UInt8.ofNat` round-trips exactly.
    (`flute_i ≤ VALUE(boundary) ≤ 13`, via `flute_le_value` + realness.) -/
private theorem flute_offset_lt256 {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) (i : Fin 10)
    (hd0 : (p.pileDepth.get i).toNat > 0) (m : Nat)
    (hm : m < (p.pileFlute.get i).toNat) : m < 256 := by
  have hb := h.pileDepth_bound i
  have hBreal := hwf.pos2card_real i (⟨(p.pileDepth.get i).toNat - 1, by omega⟩ : Fin 5)
  have := h.flute_le_value hwf i hd0
  have := hBreal.2.2
  omega

private theorem uint8_eq_finVal_toUInt8 {c : UInt8} {n : Fin 4} (h : c.toNat = n.val) :
    c = n.val.toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [h, UInt8.toNat_ofNat']
  have := n.isLt
  omega

/-- Trivial now: `UInt8.toInt` *is* the `toNat` cast. -/
private theorem uint8_toInt8_toInt_of_lt128 {c : UInt8} (_h : c.toNat < 128) :
    c.toInt = (c.toNat : Int) := rfl

/-- Same-suit small `UInt8` cards: `VALUE` order matches `UInt8` order (via `toInt8`). -/
private theorem card_le_of_value_le {c d : UInt8} (hc64 : c.toNat < 64) (hd64 : d.toNat < 64)
    (hcd : SUIT c = SUIT d) (hv : (VALUE c).toNat ≤ (VALUE d).toNat) :
    c ≤ d := by
  rw [UInt8.le_iff_toInt_le, uint8_toInt8_toInt_of_lt128 (show c.toNat < 128 by omega),
    uint8_toInt8_toInt_of_lt128 (show d.toNat < 128 by omega)]
  have hcv := VALUE_toNat c
  have hdv := VALUE_toNat d
  have hcs := SUIT_toNat c
  have hds := SUIT_toNat d
  have hsuiteq : (SUIT c).toNat = (SUIT d).toNat := congrArg UInt8.toNat hcd
  omega

/-- A flute card (boundary minus a valid offset) has the same suit as the boundary. -/
private theorem flute_card_suit_eq {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) (j : Fin 10)
    (hdj : (p.pileDepth.get j).toNat > 0) (offset : UInt8)
    (hoffLt : offset.toNat < (p.pileFlute.get j).toNat) :
    SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := h.pileDepth_bound j; omega⟩ - offset) =
      SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := h.pileDepth_bound j; omega⟩) := by
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1,
    by have := h.pileDepth_bound j; omega⟩ : Fin 5) with hBjdef
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE Bj).toNat := h.flute_le_value hwf j hdj
  have hVBj := VALUE_toNat Bj
  have hoffle : offset.toNat < Bj.toNat := by omega
  have hoffle' : offset ≤ Bj := by rw [UInt8.le_iff_toNat_le]; omega
  have hsub : (Bj - offset).toNat = Bj.toNat - offset.toNat := UInt8.toNat_sub_of_le _ _ hoffle'
  apply UInt8.toNat_inj.mp
  rw [SUIT_toNat, SUIT_toNat, hsub]
  omega

theorem cardOf_injective {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) :
    Function.Injective (cardOf g p) := by
  have hdb := h.pileDepth_bound
  have hfob := flute_offset_lt256 hwf h
  intro x y hxy
  rcases x with ⟨i, d⟩ | ⟨s, v⟩ | ⟨j, k⟩ <;> rcases y with ⟨i', d'⟩ | ⟨s', v'⟩ | ⟨j', k'⟩
  · -- depth vs depth
    have hd5 : d.val < 5 := by have := hdb i; have := d.isLt; omega
    have hd5' : d'.val < 5 := by have := hdb i'; have := d'.isLt; omega
    simp only [cardOf, dif_pos hd5, dif_pos hd5'] at hxy
    obtain ⟨hi, hdv⟩ := hwf.pos2card_inj i i' ⟨d.val, hd5⟩ ⟨d'.val, hd5'⟩ hxy
    subst hi
    have hdv' := congrArg Fin.val hdv
    have hdeq : d = d' := Fin.ext hdv'
    subst hdeq
    rfl
  · -- depth vs ace
    exfalso
    have hd5 : d.val < 5 := by have := hdb i; have := d.isLt; omega
    have hnotfree : ¬ isFreeCard g p ((g.pos2card.get i).get ⟨d.val, hd5⟩) :=
      depth_card_not_free hwf h i ⟨d.val, hd5⟩ d.isLt
    have hVas13' := (h.aces_kings_valid s').2.1
    have hv13' : v'.val + 1 ≤ (VALUE (p.aces.get s')).toNat := by have := v'.isLt; omega
    have hct' : (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))).toNat =
        s'.val * 16 + (v'.val + 1) := CARD_toNat (by have := s'.isLt; omega) (by omega)
    have hVv' : (VALUE (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1)))).toNat = v'.val + 1 := by
      rw [VALUE_toNat, hct']; omega
    have hSv0' : (SUIT (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1)))).toNat = s'.val := by
      rw [SUIT_toNat, hct']; omega
    have hSv' : SUIT (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))) = s'.val.toUInt8 :=
      uint8_eq_finVal_toUInt8 hSv0'
    have hfree : isFreeCard g p (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))) :=
      h.foundation_cards_free s' _ hSv' (by omega) (by omega)
    simp only [cardOf, dif_pos hd5] at hxy
    rw [hxy] at hnotfree
    exact hnotfree hfree
  · -- depth vs flute
    exfalso
    have hjne' : (p.pileDepth.get j').toNat ≠ 0 := by
      intro h
      have hk' := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hd0' : (p.pileDepth.get j').toNat > 0 ∧ (p.pileDepth.get j').toNat ≤ 5 :=
      ⟨by omega, hdb j'⟩
    have hd5 : d.val < 5 := by have := hdb i; have := d.isLt; omega
    simp only [cardOf, dif_pos hd5, dif_pos hd0'] at hxy
    have hkLt' : k'.val + 1 < (p.pileFlute.get j').toNat := by
      have hklt0' := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = (p.pileFlute.get j').toNat - 1 := if_pos hjne'
      omega
    have hkof' : (UInt8.ofNat (k'.val + 1)).toNat = k'.val + 1 := by
      rw [UInt8.toNat_ofNat']
      have := hfob j' hd0'.1 (k'.val + 1) hkLt'
      omega
    have hfreey : isFreeCard g p
        ((g.pos2card.get j').get ⟨(p.pileDepth.get j').toNat - 1, by omega⟩ -
          UInt8.ofNat (k'.val + 1)) :=
      h.flute_cards_free j' (UInt8.ofNat (k'.val + 1)) hd0'.1
        (by rw [hkof']; omega) (by rw [hkof']; exact hkLt')
    have hnotfreex : ¬ isFreeCard g p ((g.pos2card.get i).get ⟨d.val, hd5⟩) :=
      depth_card_not_free hwf h i ⟨d.val, hd5⟩ d.isLt
    rw [hxy] at hnotfreex
    exact hnotfreex hfreey
  · -- ace vs depth
    exfalso
    have hd5' : d'.val < 5 := by have := hdb i'; have := d'.isLt; omega
    have hnotfree : ¬ isFreeCard g p ((g.pos2card.get i').get ⟨d'.val, hd5'⟩) :=
      depth_card_not_free hwf h i' ⟨d'.val, hd5'⟩ d'.isLt
    have hVas13 := (h.aces_kings_valid s).2.1
    have hv13 : v.val + 1 ≤ (VALUE (p.aces.get s)).toNat := by have := v.isLt; omega
    have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat = s.val * 16 + (v.val + 1) :=
      CARD_toNat (by have := s.isLt; omega) (by omega)
    have hVv : (VALUE (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = v.val + 1 := by
      rw [VALUE_toNat, hct]; omega
    have hSv0 : (SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = s.val := by
      rw [SUIT_toNat, hct]; omega
    have hSv : SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))) = s.val.toUInt8 :=
      uint8_eq_finVal_toUInt8 hSv0
    have hfree : isFreeCard g p (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))) :=
      h.foundation_cards_free s _ hSv (by omega) (by omega)
    simp only [cardOf, dif_pos hd5'] at hxy
    rw [hxy] at hfree
    exact hnotfree hfree
  · -- ace vs ace
    have hVas13 := (h.aces_kings_valid s).2.1
    have hVas13' := (h.aces_kings_valid s').2.1
    have hv13 : v.val + 1 ≤ (VALUE (p.aces.get s)).toNat := by have := v.isLt; omega
    have hv13' : v'.val + 1 ≤ (VALUE (p.aces.get s')).toNat := by have := v'.isLt; omega
    have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat = s.val * 16 + (v.val + 1) :=
      CARD_toNat (by have := s.isLt; omega) (by omega)
    have hct' : (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))).toNat =
        s'.val * 16 + (v'.val + 1) := CARD_toNat (by have := s'.isLt; omega) (by omega)
    simp only [cardOf] at hxy
    have hnat := congrArg UInt8.toNat hxy
    rw [hct, hct'] at hnat
    have hsval : s.val = s'.val := by have := s.isLt; have := s'.isLt; omega
    have hs : s = s' := Fin.ext hsval
    subst hs
    have hvval : v.val = v'.val := by omega
    have hveq : v = v' := Fin.ext hvval
    subst hveq
    rfl
  · -- ace vs flute
    exfalso
    have hjne' : (p.pileDepth.get j').toNat ≠ 0 := by
      intro h
      have hk' := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hd0' : (p.pileDepth.get j').toNat > 0 ∧ (p.pileDepth.get j').toNat ≤ 5 :=
      ⟨by omega, hdb j'⟩
    simp only [cardOf, dif_pos hd0'] at hxy
    set Bj := (g.pos2card.get j').get (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5)
      with hBjdef
    have hVas13 := (h.aces_kings_valid s).2.1
    have hv13 : v.val + 1 ≤ (VALUE (p.aces.get s)).toNat := by have := v.isLt; omega
    have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat = s.val * 16 + (v.val + 1) :=
      CARD_toNat (by have := s.isLt; omega) (by omega)
    have hVv : (VALUE (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = v.val + 1 := by
      rw [VALUE_toNat, hct]; omega
    have hSv0 : (SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = s.val := by
      rw [SUIT_toNat, hct]; omega
    have hSv : SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))) = s.val.toUInt8 :=
      uint8_eq_finVal_toUInt8 hSv0
    have hkLt' : k'.val + 1 < (p.pileFlute.get j').toNat := by
      have hklt0 := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = (p.pileFlute.get j').toNat - 1 := if_pos hjne'
      omega
    have hkof' : (UInt8.ofNat (k'.val + 1)).toNat = k'.val + 1 := by
      rw [UInt8.toNat_ofNat']
      have := hfob j' hd0'.1 (k'.val + 1) hkLt'
      omega
    have hSAeq : SUIT (p.aces.get s) = s.val.toUInt8 := (h.aces_kings_valid s).1
    have hSAnat : (SUIT (p.aces.get s)).toNat = s.val := by
      rw [hSAeq, UInt8.toNat_ofNat']; have := s.isLt; omega
    have hd64 : ((p.aces.get s)).toNat < 64 := by
      have hVAn := VALUE_toNat (p.aces.get s)
      have hSAn := SUIT_toNat (p.aces.get s)
      omega
    have hc64 : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat < 64 := by omega
    have hSeq : SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))) =
        SUIT (p.aces.get s) := by rw [hSv, hSAeq]
    have hVle : (VALUE (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat ≤
        (VALUE (p.aces.get s)).toNat := by rw [hVv]; exact hv13
    have hle := card_le_of_value_le hc64 hd64 hSeq hVle
    by_cases hBs : SUIT Bj = s.val.toUInt8
    · have hs4 : (SUIT Bj).toNat < 4 := by
        rw [hBs, UInt8.toNat_ofNat']; have := s.isLt; omega
      have hlt := h.flute_not_aces hwf j' (UInt8.ofNat (k'.val + 1)) hd0'.1
        (by rw [hkof']; omega) (by rw [hkof']; exact hkLt') hs4
      have hidxeq : (⟨(SUIT Bj).toNat, hs4⟩ : Fin 4) = s := by
        apply Fin.ext
        show (SUIT Bj).toNat = s.val
        rw [hBs, UInt8.toNat_ofNat']
        have := s.isLt
        omega
      have hlt2 : p.aces.get s < (Bj - UInt8.ofNat (k'.val + 1)) := hidxeq ▸ hlt
      rw [← hxy] at hlt2
      exact absurd hle (UInt8.not_le.mpr hlt2)
    · have hsuit_eq : SUIT (Bj - UInt8.ofNat (k'.val + 1)) = SUIT Bj :=
        flute_card_suit_eq hwf h j' hd0'.1 (UInt8.ofNat (k'.val + 1)) (by rw [hkof']; exact hkLt')
      exact hBs (by rw [← hsuit_eq, ← hxy, hSv])
  · -- flute vs depth
    exfalso
    have hjne : (p.pileDepth.get j).toNat ≠ 0 := by
      intro h
      have hk := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hd0 : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5 :=
      ⟨by omega, hdb j⟩
    have hd5' : d'.val < 5 := by have := hdb i'; have := d'.isLt; omega
    simp only [cardOf, dif_pos hd5', dif_pos hd0] at hxy
    have hkLt : k.val + 1 < (p.pileFlute.get j).toNat := by
      have hklt0 := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 := if_pos hjne
      omega
    have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
      rw [UInt8.toNat_ofNat']
      have := hfob j hd0.1 (k.val + 1) hkLt
      omega
    have hfreex : isFreeCard g p
        ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, by omega⟩ -
          UInt8.ofNat (k.val + 1)) :=
      h.flute_cards_free j (UInt8.ofNat (k.val + 1)) hd0.1
        (by rw [hkof]; omega) (by rw [hkof]; exact hkLt)
    have hnotfreey : ¬ isFreeCard g p ((g.pos2card.get i').get ⟨d'.val, hd5'⟩) :=
      depth_card_not_free hwf h i' ⟨d'.val, hd5'⟩ d'.isLt
    rw [hxy] at hfreex
    exact hnotfreey hfreex
  · -- flute vs ace
    exfalso
    have hjne : (p.pileDepth.get j).toNat ≠ 0 := by
      intro h
      have hk := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hd0 : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5 :=
      ⟨by omega, hdb j⟩
    simp only [cardOf, dif_pos hd0] at hxy
    set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)
      with hBjdef
    have hVas13' := (h.aces_kings_valid s').2.1
    have hv13' : v'.val + 1 ≤ (VALUE (p.aces.get s')).toNat := by have := v'.isLt; omega
    have hct' : (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))).toNat =
        s'.val * 16 + (v'.val + 1) := CARD_toNat (by have := s'.isLt; omega) (by omega)
    have hVv' : (VALUE (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1)))).toNat = v'.val + 1 := by
      rw [VALUE_toNat, hct']; omega
    have hSv0' : (SUIT (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1)))).toNat = s'.val := by
      rw [SUIT_toNat, hct']; omega
    have hSv' : SUIT (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))) = s'.val.toUInt8 :=
      uint8_eq_finVal_toUInt8 hSv0'
    have hkLt : k.val + 1 < (p.pileFlute.get j).toNat := by
      have hklt0 := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 := if_pos hjne
      omega
    have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
      rw [UInt8.toNat_ofNat']
      have := hfob j hd0.1 (k.val + 1) hkLt
      omega
    have hSAeq : SUIT (p.aces.get s') = s'.val.toUInt8 := (h.aces_kings_valid s').1
    have hSAnat : (SUIT (p.aces.get s')).toNat = s'.val := by
      rw [hSAeq, UInt8.toNat_ofNat']; have := s'.isLt; omega
    have hd64 : ((p.aces.get s')).toNat < 64 := by
      have hVAn := VALUE_toNat (p.aces.get s')
      have hSAn := SUIT_toNat (p.aces.get s')
      omega
    have hc64 : (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))).toNat < 64 := by omega
    have hSeq : SUIT (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1))) =
        SUIT (p.aces.get s') := by rw [hSv', hSAeq]
    have hVle : (VALUE (CARD s'.val.toUInt8 (UInt8.ofNat (v'.val + 1)))).toNat ≤
        (VALUE (p.aces.get s')).toNat := by rw [hVv']; exact hv13'
    have hle := card_le_of_value_le hc64 hd64 hSeq hVle
    by_cases hBs : SUIT Bj = s'.val.toUInt8
    · have hs4 : (SUIT Bj).toNat < 4 := by
        rw [hBs, UInt8.toNat_ofNat']; have := s'.isLt; omega
      have hlt := h.flute_not_aces hwf j (UInt8.ofNat (k.val + 1)) hd0.1
        (by rw [hkof]; omega) (by rw [hkof]; exact hkLt) hs4
      have hidxeq : (⟨(SUIT Bj).toNat, hs4⟩ : Fin 4) = s' := by
        apply Fin.ext
        show (SUIT Bj).toNat = s'.val
        rw [hBs, UInt8.toNat_ofNat']
        have := s'.isLt
        omega
      have hlt2 : p.aces.get s' < (Bj - UInt8.ofNat (k.val + 1)) := hidxeq ▸ hlt
      rw [hxy] at hlt2
      exact absurd hle (UInt8.not_le.mpr hlt2)
    · have hsuit_eq : SUIT (Bj - UInt8.ofNat (k.val + 1)) = SUIT Bj :=
        flute_card_suit_eq hwf h j hd0.1 (UInt8.ofNat (k.val + 1)) (by rw [hkof]; exact hkLt)
      exact hBs (by rw [← hsuit_eq, hxy, hSv'])
  · -- flute vs flute
    have hjne : (p.pileDepth.get j).toNat ≠ 0 := by
      intro h
      have hk := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hjne' : (p.pileDepth.get j').toNat ≠ 0 := by
      intro h
      have hk' := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = 0 := if_neg (by omega)
      omega
    have hd0 : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5 :=
      ⟨by omega, hdb j⟩
    have hd0' : (p.pileDepth.get j').toNat > 0 ∧ (p.pileDepth.get j').toNat ≤ 5 :=
      ⟨by omega, hdb j'⟩
    simp only [cardOf, dif_pos hd0, dif_pos hd0'] at hxy
    have hkLt : k.val + 1 < (p.pileFlute.get j).toNat := by
      have hklt0 := k.isLt
      have heq : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 := if_pos hjne
      omega
    have hkLt' : k'.val + 1 < (p.pileFlute.get j').toNat := by
      have hklt0' := k'.isLt
      have heq' : (if (p.pileDepth.get j').toNat ≠ 0 then
          (p.pileFlute.get j').toNat - 1 else 0) = (p.pileFlute.get j').toNat - 1 := if_pos hjne'
      omega
    have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
      rw [UInt8.toNat_ofNat']; have := hfob j hd0.1 (k.val + 1) hkLt; omega
    have hkof' : (UInt8.ofNat (k'.val + 1)).toNat = k'.val + 1 := by
      rw [UInt8.toNat_ofNat']; have := hfob j' hd0'.1 (k'.val + 1) hkLt'; omega
    by_cases hjj : j = j'
    · subst hjj
      have hflv := h.flute_le_value hwf j hd0.1
      have hVBj := VALUE_toNat ((g.pos2card.get j).get
        (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
      have hleBj : UInt8.ofNat (k.val + 1) ≤ (g.pos2card.get j).get
          (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5) := by
        rw [UInt8.le_iff_toNat_le, hkof]; omega
      have hleBj' : UInt8.ofNat (k'.val + 1) ≤ (g.pos2card.get j).get
          (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5) := by
        rw [UInt8.le_iff_toNat_le, hkof']; omega
      have hsub : (((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
          - UInt8.ofNat (k.val + 1)).toNat =
          ((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)).toNat
            - (k.val + 1) := by rw [UInt8.toNat_sub_of_le _ _ hleBj, hkof]
      have hsub' : (((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
          - UInt8.ofNat (k'.val + 1)).toNat =
          ((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)).toNat
            - (k'.val + 1) := by rw [UInt8.toNat_sub_of_le _ _ hleBj', hkof']
      have hnat := congrArg UInt8.toNat hxy
      rw [hsub, hsub'] at hnat
      have hkeq : k.val = k'.val := by omega
      have hkeq' : k = k' := Fin.ext hkeq
      subst hkeq'
      rfl
    · exfalso
      have hBne : ((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
          ≠ ((g.pos2card.get j').get
            (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5)) := by
        intro heq
        obtain ⟨hji, _⟩ := hwf.pos2card_inj j j'
          ⟨(p.pileDepth.get j).toNat - 1, by omega⟩
          ⟨(p.pileDepth.get j').toNat - 1, by omega⟩ heq
        exact hjj hji
      rcases Nat.lt_trichotomy
          (((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)).toNat)
          (((g.pos2card.get j').get
            (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5)).toNat)
        with hlt | heqn | hlt
      · have hC : ¬ isFreeCard g p ((g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)) :=
          boundary_not_free hwf h j hd0.1
        have hsa := flute_stays_above hwf h j' hd0'.1
          ((g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
          hC hlt (UInt8.ofNat (k'.val + 1)) (by rw [hkof']; exact hkLt')
        rw [← hxy] at hsa
        have hflv := h.flute_le_value hwf j hd0.1
        have hVBj := VALUE_toNat ((g.pos2card.get j).get
          (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
        have hleBj : UInt8.ofNat (k.val + 1) ≤ (g.pos2card.get j).get
            (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5) := by
          rw [UInt8.le_iff_toNat_le, hkof]; omega
        have hsub : (((g.pos2card.get j).get
              (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5))
            - UInt8.ofNat (k.val + 1)).toNat =
            ((g.pos2card.get j).get
              (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5)).toNat
              - (k.val + 1) := by rw [UInt8.toNat_sub_of_le _ _ hleBj, hkof]
        rw [hsub] at hsa
        omega
      · exact hBne (UInt8.toNat_inj.mp heqn)
      · have hC : ¬ isFreeCard g p ((g.pos2card.get j').get
            (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5)) :=
          boundary_not_free hwf h j' hd0'.1
        have hsa := flute_stays_above hwf h j hd0.1
          ((g.pos2card.get j').get (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5))
          hC hlt (UInt8.ofNat (k.val + 1)) (by rw [hkof]; exact hkLt)
        rw [hxy] at hsa
        have hflv' := h.flute_le_value hwf j' hd0'.1
        have hVBj' := VALUE_toNat ((g.pos2card.get j').get
          (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5))
        have hleBj' : UInt8.ofNat (k'.val + 1) ≤ (g.pos2card.get j').get
            (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5) := by
          rw [UInt8.le_iff_toNat_le, hkof']; omega
        have hsub' : (((g.pos2card.get j').get
              (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5))
            - UInt8.ofNat (k'.val + 1)).toNat =
            ((g.pos2card.get j').get
              (⟨(p.pileDepth.get j').toNat - 1, by omega⟩ : Fin 5)).toNat
              - (k'.val + 1) := by rw [UInt8.toNat_sub_of_le _ _ hleBj', hkof']
        rw [hsub'] at hsa
        omega

@[simp] theorem UInt8.toInt_zero : (0 : UInt8).toInt = 0 := rfl

theorem UInt8.toInt_sub_of_le {a b : UInt8} (h : b ≤ a) : (a - b).toInt = a.toInt - b.toInt := by
  have hle : b.toNat ≤ a.toNat := UInt8.le_iff_toNat_le.mp h
  have : (a - b).toNat = a.toNat - b.toNat := UInt8.toNat_sub_of_le _ _ h
  simp only [UInt8.toInt, this]; omega

theorem Int32.toUInt32_toNat_of_nonneg (x : Int32) (h0 : 0 ≤ x.toInt) :
    x.toUInt32.toNat = x.toInt.toNat := by
  have hb : x.toInt = ((x.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
    show x.toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_bmod]; rfl
  have hlt : x.toUInt32.toNat < 2 ^ 32 := x.toUInt32.toNat_lt_size
  rw [hb] at h0 ⊢
  rw [Int.bmod] at h0 ⊢
  norm_num at h0 ⊢
  omega

/-- `Int32 -> uint8_t` truncation, in range: what the twins do when writing a
computed depth/flute back into a `uint8_t` field. -/
theorem Int32.toUInt8_toNat_of_lt256 (x : Int32) (h0 : 0 ≤ x.toInt) (h : x.toInt < 256) :
    (x.toUInt32.toUInt8).toNat = x.toInt.toNat := by
  rw [UInt32.toNat_toUInt8, Int32.toUInt32_toNat_of_nonneg x h0]
  omega

/-- **`freePiles ∈ [0, 10]`**, from `freePiles_def`: it counts the zero entries
    of a ten-element vector.  This is what makes the defensive `min … 10` clamp
    in `closureInfoOf` never fire on an invariant-satisfying position. -/
theorem freePiles_bound {g : Globals} {p : SolverPosType} (h : SolverInvMerged g p) :
    0 ≤ p.freePiles.toInt ∧ p.freePiles.toInt ≤ 10 := by
  rw [h.freePiles_def]
  have hlen : p.pileDepth.toList.length = 10 := by simp
  have hle := List.countP_le_length (l := p.pileDepth.toList) (p := (· == 0))
  omega

theorem freePiles_toNat_le {g : Globals} {p : SolverPosType} (h : SolverInvMerged g p) :
    p.freePiles.toNat ≤ 10 := by
  have := freePiles_bound h
  have hc : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
  omega

/-- **`usedSpace ∈ [0, 52]`**, derived from `usedSpace_def` + the counting
    injection `cardOf_injective` (no longer a base-invariant field — see
    `cardOf_injective`'s docstring history). -/
theorem usedSpace_nonneg {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) :
    0 ≤ p.usedSpace.toInt ∧ p.usedSpace.toInt ≤ 52 := by
  have hdb := h.pileDepth_bound
  have hak : ∀ s : Fin 4, (VALUE (p.aces.get s)).toNat ≤ 13 :=
    fun s => (h.aces_kings_valid s).2.1
  have hflv := (fun j hj => h.flute_le_value hwf j hj)
  have hreal := cardOf_isReal hwf hdb hak hflv
  have hinj' : Function.Injective (fun x : CountDomain p =>
      (⟨cardOf g p x, hreal x⟩ : {c : UInt8 // IsRealCard c})) := by
    intro a b hab
    exact cardOf_injective hwf h (congrArg Subtype.val hab)
  have hcard_le : Fintype.card (CountDomain p) ≤ Fintype.card {c : UInt8 // IsRealCard c} :=
    Fintype.card_le_of_injective _ hinj'
  have hcard52 : Fintype.card {c : UInt8 // IsRealCard c} = 52 :=
    (Fintype.card_subtype IsRealCard).trans RealCardsFinset.card_eq
  have hcardCD : Fintype.card (CountDomain p) =
      (∑ i : Fin 10, (p.pileDepth.get i).toNat) +
      ((∑ s : Fin 4, (VALUE (p.aces.get s)).toNat) +
       (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
           (p.pileFlute.get i).toNat - 1 else 0))) := by
    have heq : Fintype.card (CountDomain p) = Fintype.card
        ((Σ _i : Fin 10, Fin (p.pileDepth.get _i).toNat) ⊕
         (Σ _s : Fin 4, Fin (VALUE (p.aces.get _s)).toNat) ⊕
         (Σ _i : Fin 10, Fin (if (p.pileDepth.get _i).toNat ≠ 0 then
             (p.pileFlute.get _i).toNat - 1 else 0))) :=
      Fintype.card_congr (Equiv.cast rfl)
    rw [heq]
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rw [hcardCD, hcard52] at hcard_le
  have hsum1 : (∑ i : Fin 10, (p.pileDepth.get i).toNat) =
      p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 :=
    (vector_foldl_add_eq_finsum p.pileDepth (fun d => d.toNat)).symm
  have hsum2 : (∑ s : Fin 4, (VALUE (p.aces.get s)).toNat) =
      p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 :=
    (vector_foldl_add_eq_finsum p.aces (fun a => (VALUE a).toNat)).symm
  have hsum3eq : ∀ i : Fin 10,
      (if (p.pileDepth.get i).toNat ≠ 0 then (p.pileFlute.get i).toNat - 1 else 0) =
      (if (p.pileDepth.get i) ≠ (0 : UInt8) then (p.pileFlute.get i).toNat - 1 else 0) := by
    intro i
    by_cases hz : p.pileDepth.get i = 0
    · simp [hz]
    · have hpos := toNatClampNeg_pos (h.pileDepth_nonneg i) hz
      rw [if_pos (by omega : (p.pileDepth.get i).toNat ≠ 0), if_pos hz]
  have hsum3 : (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
        (p.pileFlute.get i).toNat - 1 else 0)) =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList).foldl (·+·) 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hsum3eq i)]
    exact (zipWith_foldl_add_eq_finsum p.pileDepth p.pileFlute
      (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)).symm
  rw [hsum1, hsum2, hsum3] at hcard_le
  have hdef := h.usedSpace_def
  omega

/-- **Generalizes `usedSpace_nonneg`'s counting argument.**  Given `n` pairwise
    distinct, currently-free, real cards that are furthermore known to be
    disjoint from every one of `usedSpace_def`'s three already-counted
    "occupied" families (a pile's resident cards, a foundation's played cards,
    or any pile's flute-interior run — collectively `cardOf`'s range, reusing
    the SAME injection `cardOf_injective`/`cardOf_isReal` that proves
    `usedSpace_nonneg`), `usedSpace` must have room for all `n` of them too:
    `n ≤ usedSpace`.  Freeness alone already rules out collision with the
    depth-slot family (`depth_card_not_free`); the caller supplies
    `hdisjoint` to rule out the ace-slot/flute-slot families, since which
    cards those are depends on the specific application (e.g. the freed-loop's
    absorbed run in `preCleanupPile_usedSpace_def`, or — eventually — a
    "usedSpace ≥ sum of king flutes" bound). -/
theorem usedSpace_ge_of_disjoint_free {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p)
    {n : Nat} (c : Fin n → UInt8) (hinj : Function.Injective c)
    (hreal : ∀ k, IsRealCard (c k))
    (hdisjoint : ∀ (k : Fin n) (x : CountDomain p), cardOf g p x ≠ c k) :
    (n : Int) ≤ p.usedSpace.toInt := by
  have hdb := h.pileDepth_bound
  have hak : ∀ s : Fin 4, (VALUE (p.aces.get s)).toNat ≤ 13 :=
    fun s => (h.aces_kings_valid s).2.1
  have hflv := (fun j hj => h.flute_le_value hwf j hj)
  have hCreal := cardOf_isReal hwf hdb hak hflv
  have hinj' : Function.Injective (fun x : CountDomain p ⊕ Fin n =>
      (⟨Sum.elim (cardOf g p) c x, by
        cases x with
        | inl x => exact hCreal x
        | inr k => exact hreal k⟩ : {c : UInt8 // IsRealCard c})) := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have : a = b := cardOf_injective hwf h hab'
        rw [this]
      | inr b => exact absurd hab' (hdisjoint b a)
    | inr a =>
      cases b with
      | inl b => exact absurd hab'.symm (hdisjoint a b)
      | inr b =>
        have : a = b := hinj hab'
        rw [this]
  have hcard_le : Fintype.card (CountDomain p ⊕ Fin n) ≤ Fintype.card {c : UInt8 // IsRealCard c} :=
    Fintype.card_le_of_injective _ hinj'
  have hcard52 : Fintype.card {c : UInt8 // IsRealCard c} = 52 :=
    (Fintype.card_subtype IsRealCard).trans RealCardsFinset.card_eq
  have hcardsum : Fintype.card (CountDomain p ⊕ Fin n) =
      Fintype.card (CountDomain p) + n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
  rw [hcardsum, hcard52] at hcard_le
  have hcardCD : Fintype.card (CountDomain p) =
      (∑ i : Fin 10, (p.pileDepth.get i).toNat) +
      ((∑ s : Fin 4, (VALUE (p.aces.get s)).toNat) +
       (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
           (p.pileFlute.get i).toNat - 1 else 0))) := by
    have heq : Fintype.card (CountDomain p) = Fintype.card
        ((Σ _i : Fin 10, Fin (p.pileDepth.get _i).toNat) ⊕
         (Σ _s : Fin 4, Fin (VALUE (p.aces.get _s)).toNat) ⊕
         (Σ _i : Fin 10, Fin (if (p.pileDepth.get _i).toNat ≠ 0 then
             (p.pileFlute.get _i).toNat - 1 else 0))) :=
      Fintype.card_congr (Equiv.cast rfl)
    rw [heq]
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rw [hcardCD] at hcard_le
  have hsum1 : (∑ i : Fin 10, (p.pileDepth.get i).toNat) =
      p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 :=
    (vector_foldl_add_eq_finsum p.pileDepth (fun d => d.toNat)).symm
  have hsum2 : (∑ s : Fin 4, (VALUE (p.aces.get s)).toNat) =
      p.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 :=
    (vector_foldl_add_eq_finsum p.aces (fun a => (VALUE a).toNat)).symm
  have hsum3eq : ∀ i : Fin 10,
      (if (p.pileDepth.get i).toNat ≠ 0 then (p.pileFlute.get i).toNat - 1 else 0) =
      (if (p.pileDepth.get i) ≠ (0 : UInt8) then (p.pileFlute.get i).toNat - 1 else 0) := by
    intro i
    by_cases hz : p.pileDepth.get i = 0
    · simp [hz]
    · have hpos := toNatClampNeg_pos (h.pileDepth_nonneg i) hz
      rw [if_pos (by omega : (p.pileDepth.get i).toNat ≠ 0), if_pos hz]
  have hsum3 : (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
        (p.pileFlute.get i).toNat - 1 else 0)) =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList).foldl (·+·) 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hsum3eq i)]
    exact (zipWith_foldl_add_eq_finsum p.pileDepth p.pileFlute
      (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)).symm
  rw [hsum1, hsum2, hsum3] at hcard_le
  have hdef := h.usedSpace_def
  omega

/-- **`usedSpace_ge_of_disjoint_free` with the `cardOf` obligations spelled out.**
    The three families `usedSpace_def` already counts are

    * cards still resident in a pile — excluded by `isFreeCard` alone
      (`depth_card_not_free`);
    * cards played to a foundation — excluded by `haces`: each of our cards
      strictly outranks its own suit's foundation;
    * the interior cards of some pile's flute, i.e. `boundary[j] - m` for
      `1 ≤ m < pileFlute[j]` — excluded by `hflute`.

    Stated this way so that callers in other files — which cannot name the
    private `CountDomain`/`cardOf` — can still use the counting argument.  The
    intended application is "cards in cells plus cards on king piles", giving
    `#cells + Σ king stacks ≤ usedSpace`. -/
theorem usedSpace_ge_of_free_above {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p)
    {n : Nat} (c : Fin n → UInt8) (hinj : Function.Injective c)
    (hreal : ∀ k, IsRealCard (c k))
    (hfree : ∀ k, isFreeCard g p (c k))
    (haces : ∀ (k : Fin n) (hs : (SUIT (c k)).toNat < 4),
      p.aces.get ⟨(SUIT (c k)).toNat, hs⟩ < c k)
    (hflute : ∀ (k : Fin n) (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
      ∀ m : Nat, 1 ≤ m → m < (p.pileFlute.get j).toNat →
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
          by have := h.pileDepth_bound j; omega⟩ - UInt8.ofNat m ≠ c k) :
    (n : Int) ≤ p.usedSpace.toInt := by
  apply usedSpace_ge_of_disjoint_free hwf h c hinj hreal
  intro k x
  match x with
  | .inl ⟨i, d⟩ =>
    have hd5 : d.val < 5 := by have := h.pileDepth_bound i; have := d.isLt; omega
    intro heq
    have hnotfree := depth_card_not_free hwf h i ⟨d.val, hd5⟩ d.isLt
    simp only [cardOf, dif_pos hd5] at heq
    rw [heq] at hnotfree
    exact hnotfree (hfree k)
  | .inr (.inl ⟨s, v⟩) =>
    intro heq
    simp only [cardOf] at heq
    have hs4 : (SUIT (c k)).toNat < 4 := (hreal k).1
    have hVas13 : (VALUE (p.aces.get s)).toNat ≤ 13 := (h.aces_kings_valid s).2.1
    have hv13 : v.val + 1 ≤ (VALUE (p.aces.get s)).toNat := by have := v.isLt; omega
    have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat =
        s.val * 16 + (v.val + 1) := CARD_toNat (by have := s.isLt; omega) (by omega)
    have hck : (c k).toNat = s.val * 16 + (v.val + 1) := by rw [← heq]; exact hct
    have hSck : (SUIT (c k)).toNat = s.val := by
      rw [SUIT_toNat, hck]; have := s.isLt; omega
    -- same suit as `aces[s]`, but `haces` puts it strictly above — while the
    -- ace-slot card is at or below the foundation top.
    have hlt := haces k hs4
    rw [show (⟨(SUIT (c k)).toNat, hs4⟩ : Fin 4) = s from Fin.ext hSck] at hlt
    have hltNat : (p.aces.get s).toNat < (c k).toNat := UInt8.lt_iff_toNat_lt.mp hlt
    have hAS := congrArg UInt8.toNat (h.aces_kings_valid s).1
    have hb1 := SUIT_toNat (p.aces.get s)
    have hb2 := VALUE_toNat (p.aces.get s)
    have hSval : ((s.val.toUInt8)).toNat = s.val := by
      rw [UInt8.toNat_ofNat']; have := s.isLt; omega
    omega
  | .inr (.inr ⟨j, k'⟩) =>
    intro heq
    have hk'lt := k'.isLt
    by_cases hdj : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5
    · simp only [cardOf, dif_pos hdj] at heq
      have hif : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 :=
        if_pos (by omega)
      exact hflute k j hdj.1 (k'.val + 1) (by omega) (by omega) heq
    · push Not at hdj
      have hd0 : (p.pileDepth.get j).toNat = 0 := by have := h.pileDepth_bound j; omega
      have hif : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg (by omega)
      omega

/-- **`usedSpace_ge_of_disjoint_free`, specialized to a downward run below a
    not-free card `B`.**  Given `B` not free (e.g. some pile's own current
    boundary) and `f` pairwise-distinct free cards `B-1, …, B-f` each strictly
    above the current foundation for `B`'s suit, `f ≤ usedSpace`.  The
    ace-slot exclusion is immediate from the value bound (`aces[suit] <
    B-l`); the flute-slot exclusion splits on whether the OTHER pile's
    boundary sits below or above `B`: below forces it to coincide with one of
    our (free) target cards, contradicting `boundary_not_free`; above,
    `flute_stays_above` (with `C := B`, itself not free) keeps that pile's
    *entire* flute footprint strictly above `B`, hence above our whole range. -/
theorem usedSpace_ge_freed_run {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p)
    (B : UInt8) (hBreal : IsRealCard B) (hBnotfree : ¬ isFreeCard g p B)
    (hs4 : (SUIT B).toUInt32.toNat < 4)
    (f : Nat) (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < B - UInt8.ofNat l)
    (hBflute1 : ∀ (j : Fin 10) (hdj : (p.pileDepth.get j).toNat > 0),
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
          by have := h.pileDepth_bound j; omega⟩ = B → p.pileFlute.get j = 1) :
    (f : Int) ≤ p.usedSpace.toInt := by
  have hVB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hVBn := VALUE_toNat B
  have hSBn := SUIT_toNat B
  have hB64 : B.toNat < 64 := by have := hBreal.1; omega
  have hf_le : f ≤ B.toNat - 1 := by omega
  let hc : Fin f → UInt8 := fun l => B - UInt8.ofNat (l.val + 1)
  have hcof : ∀ l : Fin f, (l.val + 1) ≤ f := fun l => l.isLt
  have hcnat : ∀ l : Fin f, (hc l).toNat = B.toNat - (l.val + 1) := by
    intro l
    have hle : UInt8.ofNat (l.val + 1) ≤ B := by
      rw [UInt8.le_iff_toNat_le]
      have hn : (UInt8.ofNat (l.val + 1)).toNat = l.val + 1 := by
        rw [UInt8.toNat_ofNat']; have := hcof l; omega
      omega
    show (B - UInt8.ofNat (l.val + 1)).toNat = B.toNat - (l.val + 1)
    rw [UInt8.toNat_sub_of_le _ _ hle]
    congr 1
    rw [UInt8.toNat_ofNat']
    have := hcof l; omega
  -- `l+1 ≤ f ≤ VALUE(B)-1`, so subtracting stays within `B`'s own suit block:
  -- same `SUIT`, `VALUE` drops by exactly `l+1`.
  have hcSuit : ∀ l : Fin f, (SUIT (hc l)) = SUIT B := by
    intro l
    apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hcnat]
    have := hcof l
    omega
  have hcVal : ∀ l : Fin f, (VALUE (hc l)).toNat = (VALUE B).toNat - (l.val + 1) := by
    intro l
    rw [VALUE_toNat, hcnat]
    have := hcof l
    omega
  have hcfree : ∀ l : Fin f, isFreeCard g p (hc l) := fun l =>
    (hffree (l.val + 1) (by omega) (hcof l)).1
  have hcaces : ∀ l : Fin f, p.aces[(SUIT B).toUInt32.toNat]'hs4 < hc l := fun l =>
    (hffree (l.val + 1) (by omega) (hcof l)).2
  have hcreal : ∀ l : Fin f, IsRealCard (hc l) := by
    intro l
    have h1 := hcSuit l; have h2 := hcVal l; have h3 := hcof l
    refine ⟨?_, ?_, ?_⟩
    · show (SUIT (hc l)).toNat < 4
      rw [h1]; exact hs4
    · show 1 ≤ (VALUE (hc l)).toNat
      omega
    · show (VALUE (hc l)).toNat ≤ 13
      omega
  have hcinj : Function.Injective hc := by
    intro l1 l2 heq
    have h1 := hcnat l1; have h2 := hcnat l2
    have heqn : (hc l1).toNat = (hc l2).toNat := congrArg UInt8.toNat heq
    apply Fin.ext
    omega
  apply usedSpace_ge_of_disjoint_free hwf h hc hcinj hcreal
  intro l x
  match x with
  | .inl ⟨i, d⟩ =>
    have hd5 : d.val < 5 := by have := h.pileDepth_bound i; have := d.isLt; omega
    intro heq
    have hnotfree : ¬ isFreeCard g p ((g.pos2card.get i).get ⟨d.val, hd5⟩) :=
      depth_card_not_free hwf h i ⟨d.val, hd5⟩ d.isLt
    simp only [cardOf, dif_pos hd5] at heq
    rw [heq] at hnotfree
    exact hnotfree (hcfree l)
  | .inr (.inl ⟨s, v⟩) =>
    intro heq
    simp only [cardOf] at heq
    by_cases hsB : s.val = (SUIT B).toUInt32.toNat
    · -- Same suit as `B`: the ace-slot card's value is `≤ VALUE(aces[SUIT B])`,
      -- but `hcaces` puts `hc l`'s value strictly above it.
      have hseq : s = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) := Fin.ext hsB
      have hcast : p.aces[(SUIT B).toUInt32.toNat]'hs4 = p.aces.get s := by rw [hseq]; rfl
      have hVas13 : (VALUE (p.aces.get s)).toNat ≤ 13 := (h.aces_kings_valid s).2.1
      have hv13 : v.val + 1 ≤ (VALUE (p.aces.get s)).toNat := by have := v.isLt; omega
      have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat =
          s.val * 16 + (v.val + 1) :=
        CARD_toNat (by have := s.isLt; omega) (by have := v.isLt; omega)
      have hVv : (VALUE (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = v.val + 1 := by
        rw [VALUE_toNat, hct]; omega
      have hlt := hcaces l
      rw [hcast] at hlt
      have hltNat : (p.aces.get s).toNat < (hc l).toNat := UInt8.lt_iff_toNat_lt.mp hlt
      have hb1 := SUIT_toNat (p.aces.get s)
      have hb2 := VALUE_toNat (p.aces.get s)
      have hAS := congrArg UInt8.toNat (h.aces_kings_valid s).1
      have hSval : (s.val.toUInt8).toNat = s.val := by
        rw [UInt8.toNat_ofNat']; have := s.isLt; omega
      have hAv : (p.aces.get s).toNat = 16 * s.val + (VALUE (p.aces.get s)).toNat := by omega
      have hcnatl := hcnat l
      have hcln := hcnat l
      rw [← heq, hct] at hcln
      omega
    · -- Different suit: the ace-slot card has `SUIT = s`, but `hc l` has
      -- `SUIT B ≠ s`.
      have hSc : (SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = s.val := by
        have hv13 : v.val + 1 ≤ 13 := by
          have := (h.aces_kings_valid s).2.1; have := v.isLt; omega
        have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat =
            s.val * 16 + (v.val + 1) := CARD_toNat (by have := s.isLt; omega) (by omega)
        rw [SUIT_toNat, hct]; omega
      have hSB : (SUIT (hc l)).toNat = (SUIT B).toUInt32.toNat := by
        rw [hcSuit, UInt8.toNat_toUInt32]
      rw [← heq] at hSB
      omega
  | .inr (.inr ⟨j, k⟩) =>
    intro heq
    by_cases hdj : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5
    · simp only [cardOf, dif_pos hdj] at heq
      set Bj := (g.pos2card.get j).get
        (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5) with hBjdef
      have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
      have hBjV13 := hBjreal.2.2
      have hBjSn := SUIT_toNat Bj
      have hBjVn := VALUE_toNat Bj
      have hBj64 : Bj.toNat < 64 := by have := hBjreal.1; omega
      have hBjnotfree : ¬ isFreeCard g p Bj := boundary_not_free hwf h j hdj.1
      have hflv' := h.flute_le_value hwf j hdj.1
      rw [← hBjdef] at hflv'
      have hklt' := k.isLt
      have heq' : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 :=
        if_pos (by omega)
      have hkltFl : (k.val + 1) < (p.pileFlute.get j).toNat := by omega
      have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
        rw [UInt8.toNat_ofNat']; omega
      by_cases hlt : Bj.toNat < B.toNat
      · by_cases hmem : ∃ l' : Fin f, Bj = hc l'
        · obtain ⟨l', hl'⟩ := hmem
          exact hBjnotfree (hl' ▸ hcfree l')
        · push Not at hmem
          have hBjBelow : Bj.toNat < B.toNat - f := by
            by_contra hge
            push Not at hge
            have hex : ∃ l' : Fin f, Bj.toNat = B.toNat - (l'.val + 1) := by
              refine ⟨⟨B.toNat - Bj.toNat - 1, by omega⟩, ?_⟩
              simp only
              omega
            obtain ⟨l', hl'⟩ := hex
            apply hmem l'
            apply UInt8.toNat_inj.mp
            rw [hcnat l']; omega
          have hle : UInt8.ofNat (k.val + 1) ≤ Bj := by
            rw [UInt8.le_iff_toNat_le, hkof]; omega
          have hsub0 := UInt8.toNat_sub_of_le _ _ hle
          have hsub : (Bj - UInt8.ofNat (k.val + 1)).toNat = Bj.toNat - (k.val + 1) := by
            rw [hsub0, hkof]
          rw [heq] at hsub
          have hcln := hcnat l
          omega
      · push Not at hlt
        rcases lt_or_eq_of_le hlt with hltB | hEqB
        · have hstay := flute_stays_above hwf h j hdj.1 B hBnotfree
            (by rw [← hBjdef]; exact hltB) (UInt8.ofNat (k.val + 1))
            (by rw [hkof]; exact hkltFl)
          rw [← hBjdef, heq] at hstay
          have hcln := hcnat l
          omega
        · -- `Bj = B`: `hBflute1` forces pile `j`'s own flute to be trivial
          -- (no interior at all), so `k`'s domain is empty — contradiction.
          exfalso
          have hBeq : Bj = B := UInt8.toNat_inj.mp hEqB.symm
          have hflute1 : p.pileFlute.get j = 1 := hBflute1 j hdj.1 (hBjdef.symm.trans hBeq)
          have hfluteNat : (p.pileFlute.get j).toNat = 1 := by rw [hflute1]; rfl
          omega
    · push Not at hdj
      have hd0 : (p.pileDepth.get j).toNat = 0 := by have := h.pileDepth_bound j; omega
      have hne : ¬ (p.pileDepth.get j).toNat ≠ 0 := by omega
      have heq' : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg hne
      have := k.isLt
      omega

/-- **Ace-side mirror of `usedSpace_ge_freed_run`.**  If `found`-many
    consecutive cards immediately ABOVE `suit`'s current foundation card are
    all free (the shape `SolverMoveAces`'s walk discovers), `usedSpace` must
    already have room for them.  Unlike the downward (pile-boundary) mirror,
    no `B`-self-overlap side condition is needed — instead `hAboveAll` rules
    out a different failure mode: another pile's same-suit flute run dipping
    down into the walked range (which would double-count that pile's own
    flute-domain slot against the walked count); different-suit piles never
    collide since neither side ever crosses a 16-wide suit block. -/
theorem usedSpace_ge_found_run {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p)
    (suit : Fin 4) (found : Nat)
    (hfound_le : found ≤ 13 - (VALUE (p.aces.get suit)).toNat)
    (hfoundfree : ∀ l, 1 ≤ l → l ≤ found →
      isFreeCard g p ((p.aces.get suit) + UInt8.ofNat l))
    (hAboveAll : ∀ (i : Fin 10) (hdi : (p.pileDepth.get i).toNat > 0),
      SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := h.pileDepth_bound i; omega⟩) = suit.val.toUInt8 →
      (p.aces.get suit).toNat + found + (p.pileFlute.get i).toNat <
        ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
          by have := h.pileDepth_bound i; omega⟩ : UInt8).toNat) :
    (found : Int) ≤ p.usedSpace.toInt := by
  set A := p.aces.get suit with hAdef
  have hAsuit : SUIT A = suit.val.toUInt8 := (h.aces_kings_valid suit).1
  have hAval13 : (VALUE A).toNat ≤ 13 := (h.aces_kings_valid suit).2.1
  have hsuitU8 : (suit.val.toUInt8).toNat = suit.val := by
    rw [UInt8.toNat_ofNat']; have := suit.isLt; omega
  have hAsuitNat : (SUIT A).toNat = suit.val := by rw [hAsuit, hsuitU8]
  have hAs4 : (SUIT A).toNat < 4 := by rw [hAsuitNat]; exact suit.isLt
  have hASn := SUIT_toNat A
  have hAVn := VALUE_toNat A
  have hA64 : A.toNat < 64 := by omega
  let hc : Fin found → UInt8 := fun l => A + UInt8.ofNat (l.val + 1)
  have hcof : ∀ l : Fin found, (l.val + 1) ≤ found := fun l => l.isLt
  have hcnat : ∀ l : Fin found, (hc l).toNat = A.toNat + (l.val + 1) := by
    intro l
    have hn : (UInt8.ofNat (l.val + 1)).toNat = l.val + 1 := by
      rw [UInt8.toNat_ofNat']; have := hcof l; omega
    show (A + UInt8.ofNat (l.val + 1)).toNat = A.toNat + (l.val + 1)
    rw [UInt8.toNat_add, hn]
    have := hcof l
    omega
  have hcSuit : ∀ l : Fin found, SUIT (hc l) = SUIT A := by
    intro l
    apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hcnat]
    have := hcof l
    omega
  have hcVal : ∀ l : Fin found, (VALUE (hc l)).toNat = (VALUE A).toNat + (l.val + 1) := by
    intro l
    rw [VALUE_toNat, hcnat]
    have := hcof l
    omega
  have hcfree : ∀ l : Fin found, isFreeCard g p (hc l) := fun l =>
    hfoundfree (l.val + 1) (by omega) (hcof l)
  have hcreal : ∀ l : Fin found, IsRealCard (hc l) := by
    intro l
    have h1 := hcSuit l; have h2 := hcVal l; have h3 := hcof l
    refine ⟨?_, ?_, ?_⟩
    · show (SUIT (hc l)).toNat < 4
      rw [h1]; exact hAs4
    · show 1 ≤ (VALUE (hc l)).toNat
      omega
    · show (VALUE (hc l)).toNat ≤ 13
      omega
  have hcinj : Function.Injective hc := by
    intro l1 l2 heq
    have h1 := hcnat l1; have h2 := hcnat l2
    have heqn : (hc l1).toNat = (hc l2).toNat := congrArg UInt8.toNat heq
    apply Fin.ext
    omega
  apply usedSpace_ge_of_disjoint_free hwf h hc hcinj hcreal
  intro l x
  match x with
  | .inl ⟨i, d⟩ =>
    have hd5 : d.val < 5 := by have := h.pileDepth_bound i; have := d.isLt; omega
    intro heq
    have hnotfree : ¬ isFreeCard g p ((g.pos2card.get i).get ⟨d.val, hd5⟩) :=
      depth_card_not_free hwf h i ⟨d.val, hd5⟩ d.isLt
    simp only [cardOf, dif_pos hd5] at heq
    rw [heq] at hnotfree
    exact hnotfree (hcfree l)
  | .inr (.inl ⟨s, v⟩) =>
    intro heq
    simp only [cardOf] at heq
    by_cases hsA : s.val = suit.val
    · -- Same suit as `A`: the ace-slot domain bound gives `v+1 ≤ VALUE(A)`,
      -- but our found card's value is strictly ABOVE `VALUE(A)` — direct
      -- contradiction once `s = suit` identifies the two.
      have hseq : s = suit := Fin.ext hsA
      subst hseq
      have hv13 : v.val + 1 ≤ (VALUE A).toNat := by
        have := v.isLt; rw [hAdef]; omega
      have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat =
          s.val * 16 + (v.val + 1) :=
        CARD_toNat (by have := s.isLt; omega) (by have := v.isLt; omega)
      have hcln := hcnat l
      rw [← heq, hct] at hcln
      omega
    · -- Different suit: the ace-slot card has `SUIT = s`, but `hc l` has
      -- `SUIT = suit ≠ s`.
      have hSc : (SUIT (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1)))).toNat = s.val := by
        have hv13 : v.val + 1 ≤ 13 := by
          have := (h.aces_kings_valid s).2.1; have := v.isLt; omega
        have hct : (CARD s.val.toUInt8 (UInt8.ofNat (v.val + 1))).toNat =
            s.val * 16 + (v.val + 1) := CARD_toNat (by have := s.isLt; omega) (by omega)
        rw [SUIT_toNat, hct]; omega
      have hSA : (SUIT (hc l)).toNat = suit.val := by rw [hcSuit, hAsuitNat]
      rw [← heq] at hSA
      omega
  | .inr (.inr ⟨j, k⟩) =>
    intro heq
    by_cases hdj : (p.pileDepth.get j).toNat > 0 ∧ (p.pileDepth.get j).toNat ≤ 5
    · simp only [cardOf, dif_pos hdj] at heq
      set Bj := (g.pos2card.get j).get
        (⟨(p.pileDepth.get j).toNat - 1, by omega⟩ : Fin 5) with hBjdef
      have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
      have hBjV13 := hBjreal.2.2
      have hBjSn := SUIT_toNat Bj
      have hBjVn := VALUE_toNat Bj
      have hBj64 : Bj.toNat < 64 := by have := hBjreal.1; omega
      have hflv' := h.flute_le_value hwf j hdj.1
      rw [← hBjdef] at hflv'
      have hklt' := k.isLt
      have heq' : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = (p.pileFlute.get j).toNat - 1 :=
        if_pos (by omega)
      have hkltFl : (k.val + 1) < (p.pileFlute.get j).toNat := by omega
      have hkof : (UInt8.ofNat (k.val + 1)).toNat = k.val + 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hkleBj : UInt8.ofNat (k.val + 1) ≤ Bj := by
        rw [UInt8.le_iff_toNat_le, hkof]; omega
      have hsub : (Bj - UInt8.ofNat (k.val + 1)).toNat = Bj.toNat - (k.val + 1) := by
        rw [UInt8.toNat_sub_of_le _ _ hkleBj, hkof]
      by_cases hSBj : SUIT Bj = suit.val.toUInt8
      · -- Same suit: `hAboveAll` places pile `j`'s flute range strictly
        -- above the entire walked range, ruling out the overlap directly.
        have hbound := hAboveAll j hdj.1 (hBjdef ▸ hSBj)
        rw [← hBjdef] at hbound
        have heqNat : (Bj - UInt8.ofNat (k.val + 1)).toNat = (hc l).toNat :=
          congrArg UInt8.toNat heq
        rw [hsub, hcnat l] at heqNat
        have hll := l.isLt
        omega
      · -- Different suit: subtracting `(k+1) < pileFlute[j] ≤ VALUE(Bj)`
        -- never crosses a suit boundary, so `SUIT(Bj-(k+1)) = SUIT Bj ≠ suit`.
        have hSBjSub : (SUIT (Bj - UInt8.ofNat (k.val + 1))).toNat = (SUIT Bj).toNat := by
          rw [SUIT_toNat, SUIT_toNat, hsub]
          omega
        have hSeqNat : (SUIT (hc l)).toNat = (SUIT (Bj - UInt8.ofNat (k.val + 1))).toNat :=
          congrArg (fun c => (SUIT c).toNat) heq.symm
        have hSA : (SUIT (hc l)).toNat = suit.val := by rw [hcSuit, hAsuitNat]
        apply hSBj
        apply UInt8.toNat_inj.mp
        rw [hsuitU8]
        omega
    · push Not at hdj
      have hd0 : (p.pileDepth.get j).toNat = 0 := by have := h.pileDepth_bound j; omega
      have hne : ¬ (p.pileDepth.get j).toNat ≠ 0 := by omega
      have heq' : (if (p.pileDepth.get j).toNat ≠ 0 then
          (p.pileFlute.get j).toNat - 1 else 0) = 0 := if_neg hne
      have := k.isLt
      omega

-- ---------------------------------------------------------------------------
-- Uniqueness theorem
-- ---------------------------------------------------------------------------

/-- Two canonical `SolverPosType`s with identical pile depths are equal.
    Because `isFreeCard` depends only on `pileDepth`, all other fields are
    uniquely pinned by the canonical-form conditions. -/
theorem IsCanonicalPos_unique (g : Globals) (p q : SolverPosType)
    (hwf : WellFormedLayout g) (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (hdepth : p.pileDepth = q.pileDepth) : p = q := by
  -- isFreeCard is identical for p and q (depends only on pileDepth)
  have free_iff : ∀ c : UInt8, isFreeCard g p c ↔ isFreeCard g q c := fun c => by
    simp only [isFreeCard, hdepth]
  -- busyAces: both are 0
  have hbusy : p.busyAces = q.busyAces := by
    rw [hp.busyAces_zero, hq.busyAces_zero]
  -- `king_frontier`'s busyAces-pending disjunct never fires in a canonical
  -- position (`busyAces_zero`), so its "case" component collapses back to
  -- the plain form; the `∀c`-clause is unconditional, so it's just `.2`.
  have king_frontier13 : ∀ (r : SolverPosType), IsCanonicalPos g r → ∀ t : Fin 4,
      ((VALUE (r.aces.get t)).toNat = 13 ∧ r.kings.get t = r.aces.get t) ∨
      ¬ isFreeCard g r (r.kings.get t) := fun r hr t => by
    rcases (hr.king_frontier t).1 with ⟨hkeq, h13OrBusy⟩ | ⟨_, hnf⟩
    · rcases h13OrBusy with h13 | hbusy'
      · exact Or.inl ⟨h13, hkeq⟩
      · exact absurd hbusy' (by rw [hr.busyAces_zero]; simp)
    · exact Or.inr hnf
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
    suffices hv : (VALUE (p.aces.get s)).toNat = (VALUE (q.aces.get s)).toNat by
      -- UInt8 equality, then UInt8 equality
      have hUInt8 : (p.aces.get s) = (q.aces.get s) :=
        card_eq_of_suit_value _ _ (hpsuit.trans hqsuit.symm) hv
      exact hUInt8
    apply Nat.le_antisymm
    · -- VALUE(p.aces) ≤ VALUE(q.aces):
      -- if not, the card (q.aces+1) would be free in p but forbidden by foundation_maximal
      by_contra hlt; push Not at hlt
      have hcval : (VALUE (q.aces.get s)).toNat < 15 := by omega
      have hcsuit : SUIT ((q.aces.get s) + 1) = s.val.toUInt8 :=
        (SUIT_succ _ hcval).trans hqsuit
      have hcval1 : 1 ≤ (VALUE ((q.aces.get s) + 1)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hcval2 : (VALUE ((q.aces.get s) + 1)).toNat ≤
          (VALUE (p.aces.get s)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hfree_p := hp.foundation_cards_free s _ hcsuit hcval1 hcval2
      have hfree_q := (free_iff _).mp hfree_p
      rcases hq.foundation_maximal hwf s with h13 | hnfree
      · omega
      · exact hnfree hfree_q
    · -- VALUE(q.aces) ≤ VALUE(p.aces): symmetric
      by_contra hlt; push Not at hlt
      have hcval : (VALUE (p.aces.get s)).toNat < 15 := by omega
      have hcsuit : SUIT ((p.aces.get s) + 1) = s.val.toUInt8 :=
        (SUIT_succ _ hcval).trans hpsuit
      have hcval1 : 1 ≤ (VALUE ((p.aces.get s) + 1)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hcval2 : (VALUE ((p.aces.get s) + 1)).toNat ≤
          (VALUE (q.aces.get s)).toNat := by
        have h := VALUE_succ _ hcval; omega
      have hfree_q := hq.foundation_cards_free s _ hcsuit hcval1 hcval2
      have hfree_p := (free_iff _).mpr hfree_q
      rcases hp.foundation_maximal hwf s with h13 | hnfree
      · omega
      · exact hnfree hfree_p
  -- kings: uniquely determined by the free-suffix walk
  have hkings : p.kings = q.kings := by
    apply Vector.ext; intro sn hn
    let s : Fin 4 := ⟨sn, hn⟩
    show p.kings.get s = q.kings.get s
    have hpsuit := (hp.aces_kings_valid s).2.2.1   -- SUIT(p.kings[s]) = s
    have hqsuit := (hq.aces_kings_valid s).2.2.1   -- SUIT(q.kings[s]) = s
    have hpval1 := hp.kings_value_pos hwf s         -- 1 ≤ VALUE(p.kings[s])
    have hqval1 := hq.kings_value_pos hwf s         -- 1 ≤ VALUE(q.kings[s])
    have hpval  := (hp.aces_kings_valid s).2.2.2.1  -- VALUE(p.kings[s]) ≤ 13
    have hqval  := (hq.aces_kings_valid s).2.2.2.1  -- VALUE(q.kings[s]) ≤ 13
    -- Helper: VALUE(kings[s]) = 13 when king_frontier case 1 holds
    have kings_val_13 : ∀ (r : SolverPosType) (t : Fin 4),
        r.kings.get t = r.aces.get t →
        (VALUE (r.aces.get t)).toNat = 13 →
        (VALUE (r.kings.get t)).toNat = 13 := fun r t hkeq h13 =>
      (congrArg (fun x : UInt8 => (VALUE x).toNat) hkeq).trans h13
    suffices hv : (VALUE (p.kings.get s)).toNat = (VALUE (q.kings.get s)).toNat by
      have hUInt8 := card_eq_of_suit_value _ _ (hpsuit.trans hqsuit.symm) hv
      exact hUInt8
    apply Nat.le_antisymm
    · -- VALUE(p.kings) ≤ VALUE(q.kings)
      -- Contradiction assumption: VALUE_q < VALUE_p
      by_contra hlt; push Not at hlt
      rcases king_frontier13 p hp s with ⟨h13p, hkp⟩ | hnfp
      · -- hp case 1: VALUE(p.aces) = 13, p.kings = p.aces, so VALUE(p.kings) = 13.
        -- q.kings is free in p (foundation covers all of suit s up to 13).
        -- Contradiction from q's king_frontier.
        have hkp13 := kings_val_13 p s hkp h13p
        have hkq_free_p := hp.foundation_cards_free s (q.kings.get s)
          hqsuit hqval1 (by omega)
        rcases king_frontier13 q hq s with ⟨h13q, hkq⟩ | hnfq
        · exact absurd (kings_val_13 q s hkq h13q) (by omega)
        · exact hnfq ((free_iff _).mp hkq_free_p)
      · -- hp case 2: p.kings is not free; all above p.kings are free in p.
        -- Since VALUE_q < VALUE_p, p.kings is above q.kings in q's frontier.
        rcases king_frontier13 q hq s with ⟨h13q, hkq⟩ | hnfq
        · -- hq case 1: VALUE(q.kings) = 13; hlt gives 13 < VALUE_p ≤ 13
          exact absurd (kings_val_13 q s hkq h13q) (by omega)
        · -- hq case 2: p.kings is above q.kings (VALUE_p > VALUE_q), free in q, hence in p
          exact hnfp ((free_iff _).mpr ((hq.king_frontier s).2 _ hpsuit (by omega) (by omega)))
    · -- VALUE(q.kings) ≤ VALUE(p.kings): symmetric
      -- Contradiction assumption: VALUE_p < VALUE_q
      by_contra hlt; push Not at hlt
      rcases king_frontier13 q hq s with ⟨h13q, hkq⟩ | hnfq
      · -- hq case 1: VALUE(q.aces) = 13, q.kings = q.aces, so VALUE(q.kings) = 13.
        -- p.kings is free in q (foundation covers all of suit s up to 13).
        -- Contradiction from p's king_frontier.
        have hkq13 := kings_val_13 q s hkq h13q
        have hkp_free_q := hq.foundation_cards_free s (p.kings.get s)
          hpsuit hpval1 (by omega)
        rcases king_frontier13 p hp s with ⟨h13p, hkp⟩ | hnfp
        · exact absurd (kings_val_13 p s hkp h13p) (by omega)
        · exact hnfp ((free_iff _).mpr hkp_free_q)
      · -- hq case 2: q.kings is not free; all above q.kings are free in q.
        rcases king_frontier13 p hp s with ⟨h13p, hkp⟩ | hnfp
        · -- hp case 1: VALUE(p.kings) = 13; hlt gives 13 < VALUE_q ≤ 13
          exact absurd (kings_val_13 p s hkp h13p) (by omega)
        · -- hp case 2: q.kings is above p.kings (VALUE_q > VALUE_p), free in p, hence in q
          exact hnfq ((free_iff _).mp ((hp.king_frontier s).2 _ hqsuit (by omega) (by omega)))
  -- pileFlute: uniquely determined by the same isFreeCard / aces plus flute_not_aces
  have hflute : p.pileFlute = q.pileFlute := by
    apply Vector.ext; intro in_ hn
    let i : Fin 10 := ⟨in_, hn⟩
    show p.pileFlute.get i = q.pileFlute.get i
    have hdepth_i : p.pileDepth.get i = q.pileDepth.get i :=
      congrArg (fun v : Vector UInt8 10 => v.get i) hdepth
    by_cases hd : p.pileDepth.get i = 0
    · -- Empty pile: both pileFlute = 1 by flute_empty
      rw [hp.flute_empty i hd, hq.flute_empty i (hdepth_i ▸ hd)]
    · -- Non-empty pile: use antisymmetry
      have hdp_pos : (p.pileDepth.get i).toNat > 0 :=
        toNatClampNeg_pos (hp.pileDepth_nonneg i) hd
      have hdq_pos : (q.pileDepth.get i).toNat > 0 := hdepth_i ▸ hdp_pos
      -- The boundary card is the same for p and q (same pos2card index)
      have hdnc : (p.pileDepth.get i).toNat = (q.pileDepth.get i).toNat :=
        congrArg Int.toNat (congrArg UInt8.toInt hdepth_i)
      have hbdy : (g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
              by have := hp.pileDepth_bound i; omega⟩ =
                 (g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
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
          have hsuit : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
                          by have := hp.pileDepth_bound i; omega⟩)).toNat =
                       (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
                          by have := hq.pileDepth_bound i; omega⟩)).toNat :=
            congrArg UInt8.toNat (congrArg SUIT hbdy)
          have hs' : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
                        by have := hp.pileDepth_bound i; omega⟩)).toNat < 4 := hsuit ▸ hs
          have hlt_aces := hp.flute_not_aces hwf i (q.pileFlute.get i) hdp_pos hj1 hlt' hs'
          have haces_s : p.aces.get ⟨_, hs'⟩ = q.aces.get ⟨_, hs⟩ :=
            (congrArg (fun v : Vector UInt8 4 => v.get ⟨_, hs'⟩) haces).trans
              (congrArg q.aces.get (Fin.ext hsuit))
          have hcard : ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
                          by have := hp.pileDepth_bound i; omega⟩ -
                        q.pileFlute.get i) =
                       ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
                          by have := hq.pileDepth_bound i; omega⟩ -
                        q.pileFlute.get i) := by rw [hbdy]
          rw [haces_s, hcard] at hlt_aces
          exact absurd (congrArg UInt8.toInt hge) (ne_of_lt (UInt8.lt_iff_toInt_lt.mp hlt_aces))
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
        · have hsuit : (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
                          by have := hq.pileDepth_bound i; omega⟩)).toNat =
                       (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
                          by have := hp.pileDepth_bound i; omega⟩)).toNat :=
            congrArg UInt8.toNat (congrArg SUIT hbdy.symm)
          have hs' : (SUIT ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
                        by have := hq.pileDepth_bound i; omega⟩)).toNat < 4 := hsuit ▸ hs
          have hlt_aces := hq.flute_not_aces hwf i (p.pileFlute.get i) hdq_pos hj1 hlt' hs'
          have haces_s : q.aces.get ⟨_, hs'⟩ = p.aces.get ⟨_, hs⟩ :=
            (congrArg (fun v : Vector UInt8 4 => v.get ⟨_, hs'⟩) haces.symm).trans
              (congrArg p.aces.get (Fin.ext hsuit))
          have hcard : ((g.pos2card.get i).get ⟨(q.pileDepth.get i).toNat - 1,
                          by have := hq.pileDepth_bound i; omega⟩ -
                        p.pileFlute.get i) =
                       ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1,
                          by have := hp.pileDepth_bound i; omega⟩ -
                        p.pileFlute.get i) := by rw [hbdy.symm]
          rw [haces_s, hcard] at hlt_aces
          exact absurd (congrArg UInt8.toInt hge) (ne_of_lt (UInt8.lt_iff_toInt_lt.mp hlt_aces))
        · exact hnfree (hbdy.symm ▸ hfree_p)
      exact UInt8.ext (Nat.le_antisymm hle1 hle2)
  -- freePiles: count of piles with depth 0, so determined by pileDepth
  have hfree : p.freePiles = q.freePiles :=
    UInt8.toInt_inj.mp (hp.freePiles_def.trans (by rw [hdepth]) |>.trans hq.freePiles_def.symm)
  -- usedSpace: formula in pileDepth, aces, pileFlute
  have hused : p.usedSpace = q.usedSpace :=
    UInt8.toInt_inj.mp (hp.usedSpace_def.trans (by rw [hdepth, haces, hflute]) |>.trans hq.usedSpace_def.symm)
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

/-- An `UInt8` that is nonnegative is determined by `x.toNat`. -/
theorem UInt8_eq_of_toNat_eq {x y : UInt8} (_hx : (0 : UInt8) ≤ x) (_hy : (0 : UInt8) ≤ y)
    (h : x.toNat = y.toNat) : x = y :=
  UInt8.toNat_inj.mp h

/-- **Base-6 hash injectivity, arithmetic core.**  If two base-6 dot products of
    ten digits each in `{0,…,5}` agree as `UInt32`, the digits agree.  The sum is
    at most `6^10 - 1 = 60466175 < 2^32`, so the `UInt32` reduction never wraps and
    the equation is a genuine `Nat` equation, decided by `omega`. -/
theorem hash_dot_inj (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Nat) (hd0 : d0 ≤ 5) (hd1 : d1 ≤ 5) (hd2 : d2 ≤ 5) (hd3 : d3 ≤ 5) (hd4 : d4 ≤ 5) (hd5 : d5 ≤ 5) (hd6 : d6 ≤ 5) (hd7 : d7 ≤ 5) (hd8 : d8 ≤ 5) (hd9 : d9 ≤ 5) (he0 : e0 ≤ 5) (he1 : e1 ≤ 5) (he2 : e2 ≤ 5) (he3 : e3 ≤ 5) (he4 : e4 ≤ 5) (he5 : e5 ≤ 5) (he6 : e6 ≤ 5) (he7 : e7 ≤ 5) (he8 : e8 ≤ 5) (he9 : e9 ≤ 5)
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
        (fun acc i => acc + pileHashes.get i * (p.pileDepth.get i).toNat.toUInt32) 0 =
      (List.finRange 10).foldl
        (fun acc i => acc + pileHashes.get i * (q.pileDepth.get i).toNat.toUInt32) 0 :=
    hp.hash_def.symm.trans (hhash.trans hq.hash_def)
  -- Expand the foldl: List.finRange → ofFn → concrete list, then foldl_cons/nil steps.
  -- Vector.get unfolds v.get ⟨k,h⟩ → v.toArray[...]; getElem_toArray then converts
  -- v.toArray[k] → v[k] so all depth terms use GetElem ([k]) notation, matching the
  -- bounds below and the goal produced by Vector.ext.
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
             pileHashes, Vector.get, Vector.getElem_toArray, Fin.isValue, Fin.val_cast,
             Fin.val_zero, Fin.val_succ, Nat.reduceAdd, List.getElem_toArray,
             List.getElem_cons_succ, List.getElem_cons_zero] at hfoldl
  -- Bounds stated with [k] getElem notation (definitionally equal to .get ⟨k,_⟩ via the
  -- GetElem instance), so omega sees the same atoms as in hfoldl and the Vector.ext goal.
  have hpb0 : (p.pileDepth[0] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨0, by omega⟩
  have hpb1 : (p.pileDepth[1] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨1, by omega⟩
  have hpb2 : (p.pileDepth[2] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨2, by omega⟩
  have hpb3 : (p.pileDepth[3] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨3, by omega⟩
  have hpb4 : (p.pileDepth[4] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨4, by omega⟩
  have hpb5 : (p.pileDepth[5] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨5, by omega⟩
  have hpb6 : (p.pileDepth[6] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨6, by omega⟩
  have hpb7 : (p.pileDepth[7] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨7, by omega⟩
  have hpb8 : (p.pileDepth[8] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨8, by omega⟩
  have hpb9 : (p.pileDepth[9] : UInt8).toNat ≤ 5 := hp.pileDepth_bound ⟨9, by omega⟩
  have hqb0 : (q.pileDepth[0] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨0, by omega⟩
  have hqb1 : (q.pileDepth[1] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨1, by omega⟩
  have hqb2 : (q.pileDepth[2] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨2, by omega⟩
  have hqb3 : (q.pileDepth[3] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨3, by omega⟩
  have hqb4 : (q.pileDepth[4] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨4, by omega⟩
  have hqb5 : (q.pileDepth[5] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨5, by omega⟩
  have hqb6 : (q.pileDepth[6] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨6, by omega⟩
  have hqb7 : (q.pileDepth[7] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨7, by omega⟩
  have hqb8 : (q.pileDepth[8] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨8, by omega⟩
  have hqb9 : (q.pileDepth[9] : UInt8).toNat ≤ 5 := hq.pileDepth_bound ⟨9, by omega⟩
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
  -- `interval_cases` has fixed the index) plus nonnegativity.  `UInt8_eq_of_toNat_eq` does
  -- the `.toNat → .toInt → UInt8` bridge that `omega` cannot do on `UInt8` directly.
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    exact UInt8_eq_of_toNat_eq (hp.pileDepth_nonneg ⟨_, by omega⟩)
      (hq.pileDepth_nonneg ⟨_, by omega⟩) (by assumption)
