import Seahaven.Solver

-- Safe accessor: original card at position `pos` in `pile`'s initial layout.
-- Returns 0 when `pos` is out of range (negative or ≥ 5).
private def pos2cardAt (g : Globals) (pile : Fin 10) (pos : Int32) : UInt8 :=
  if h : pos.toNatClampNeg < 5 then
    (g.pos2card.get pile).get ⟨pos.toNatClampNeg, h⟩
  else 0

-- Safe accessors for aces / kings (indexed by suit as UInt8; default 0).
private def aceLevel (p : SolverPosType) (suit : UInt8) : Int8 :=
  if h : suit.toNat < 4 then p.aces.get ⟨suit.toNat, h⟩ else 0

private def kingLevel (p : SolverPosType) (suit : UInt8) : Int8 :=
  if h : suit.toNat < 4 then p.kings.get ⟨suit.toNat, h⟩ else 0

/-- Card `c` is **free**: its original pile's depth has been reduced to or
    below its original position, so it has been moved off the pile. -/
def isFreeCard (g : Globals) (p : SolverPosType) (c : UInt8) : Prop :=
  let pile      : UInt8 := if h : c.toNat < 64 then g.card2pile.get  ⟨c.toNat, h⟩ else 0
  let origDepth : UInt8 := if h : c.toNat < 64 then g.card2depth.get ⟨c.toNat, h⟩ else 0
  let pileDepth : Int8  :=
    if h : pile.toNat < 10 then p.pileDepth.get ⟨pile.toNat, h⟩ else 0
  origDepth.toNat ≥ pileDepth.toNatClampNeg

/-- A `SolverPosType` is in **canonical form** — the form produced by
    `SolverConvertFromPilesKings` followed by `SolverCleanupPile` and
    `SolverMoveAces` — when all five conditions below hold.

    Key consequence: two canonical positions with equal `pileDepth` vectors
    are necessarily equal (see `IsCanonicalPos_unique`), because every other
    field is uniquely determined by the pile depths. -/
structure IsCanonicalPos (g : Globals) (p : SolverPosType) : Prop where

  /-- **(1) Merge complete.** For every non-trivial pile, the card immediately
      below the boundary is *not* the same-suit predecessor of the boundary
      card.  (The merge loop in `SolverCleanupPile` has terminated.) -/
  merge_complete : ∀ i : Fin 10,
    p.pileDepth.get i ≤ 1 ∨
    pos2cardAt g i ((p.pileDepth.get i).toInt32 - 2) ≠
    pos2cardAt g i ((p.pileDepth.get i).toInt32 - 1) + 1

  /-- **(2) Flute maximal.** For every non-empty pile, the card that would
      further extend the flute upward is either at or below the foundation
      level for that suit, or is not free.
      (The freed-predecessor loop in `SolverCleanupPile` has terminated.) -/
  flute_maximal : ∀ i : Fin 10,
    p.pileDepth.get i = 0 ∨
    (let boundary := pos2cardAt g i ((p.pileDepth.get i).toInt32 - 1)
     let prevCard := boundary - p.pileFlute.get i
     aceLevel p (SUIT boundary) ≥ prevCard.toInt8 ∨ ¬ isFreeCard g p prevCard)

  /-- **(3a) Foundation cards are free.** Every card of suit `s` with value
      between 1 and `VALUE(aces[s])` (inclusive) has been freed. -/
  foundation_cards_free : ∀ s : Fin 4, ∀ c : UInt8,
    SUIT c = s.val.toUInt8 →
    1 ≤ (VALUE c).toNat →
    (VALUE c).toNat ≤ (VALUE (p.aces.get s).toUInt8).toNat →
    isFreeCard g p c

  /-- **(3b) Foundation maximal.** The card just above `aces[s]` is not free
      (or the suit is already complete with `ace = 13`). -/
  foundation_maximal : ∀ s : Fin 4,
    (VALUE (p.aces.get s).toUInt8).toNat = 13 ∨
    ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1)

  /-- **(4) King frontier.** Either the suit is complete — all 13 cards are in
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

  /-- **(5) No pending foundation work.** `busyAces = 0` means
      `SolverMoveAces` has been called to quiescence. -/
  busyAces_zero : p.busyAces = 0

/-- Two canonical `SolverPosType`s with identical pile depths are equal.
    Proof sketch: with the same `pileDepth`, `isFreeCard` is identical for
    every card, uniquely determining `aces` (free-prefix walk from ACE),
    `kings` (free-suffix walk from KING), `pileFlute` (merge + freed-
    predecessor walk), `usedSpace`, `freePiles`, `hash`, and `busyAces = 0`. -/
theorem IsCanonicalPos_unique (g : Globals) (p q : SolverPosType)
    (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (hdepth : p.pileDepth = q.pileDepth) : p = q := by
  sorry
