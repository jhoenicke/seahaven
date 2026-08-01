import Seahaven.FoundationRun
import Seahaven.LayoutProofs
import Seahaven.SolverInvariant

/-!
# Matching a `Rules.State` against a `SolverPosType`

`StateMatchesLayout` only ties a `State` to the static deal (`g.pos2card`).  This
file adds the missing half: a relation between a `State` and an abstract
*position*.

The relation is deliberately **many-to-many**, and constrains only what the
concrete state actually determines:

* one `s` matches several `p` — the flute of a pile grows as cards are dropped
  back onto it, so a state that is not normalized matches a position with
  shorter flutes than the canonical one.  At most one matching `p` is canonical,
  and some states match no canonical `p` at all;
* one `p` is matched by many `s` — the abstract position records neither *which*
  empty pile carries a king stack nor *which* cell holds which card.

Nothing here presupposes `SolverInvBase`/`IsCanonicalPos`; those stay on the
solver side, where they are already proved to be preserved.  The consequence is
that this relation still holds at the intermediate, non-canonical positions that
`SolverMoveAces` and `SolverCleanupPile` pass through — which is exactly what a
simulation argument needs.
-/

/-! ## `IsValidCard` is `IsRealCard` -/

/-- The two spellings of "this `UInt8` codes a real card" coincide definitionally:
`SUIT c` is `c >>> 4` and `VALUE c` is `c &&& 0xf`. -/
theorem isValidCard_iff_isRealCard (c : UInt8) : IsValidCard c ↔ IsRealCard c := Iff.rfl

theorem IsRealCard_lt64 {c : UInt8} (h : IsRealCard c) : c.toNat < 64 :=
  IsValidCard_lt64 ((isValidCard_iff_isRealCard c).2 h)

theorem encodeCard_real (c : Card) : IsRealCard (encodeCard c) :=
  (isValidCard_iff_isRealCard _).1 (encodeCard_valid c)

/-! ## Encoding a foundation -/

/-- The `Fin 4` index the solver uses for a suit. -/
def finOfSuit (su : Suit) : Fin 4 := ⟨suitToNat su, suitToNat_lt su⟩

/-- The code the solver stores in `aces[su]`: the suit's foundation top, with the
sentinel `CARD su 0` when the foundation is still empty. -/
def encodeFoundation (su : Suit) (r : Option Rank) : UInt8 :=
  CARD (UInt8.ofNat (suitToNat su)) (UInt8.ofNat (optRankToNat r))

theorem encodeFoundation_some (su : Suit) (r : Rank) :
    encodeFoundation su (some r) = encodeCard { suit := su, rank := r } := rfl

/-! ## The relation -/

/-- `StateMatchesSolverPos g s p` : the concrete state `s` is one of the states
the abstract position `p` stands for.  See the module docstring for why this is
many-to-many. -/
structure StateMatchesSolverPos (g : Globals) (s : State) (p : SolverPosType) : Prop where
  /-- Full deck, no duplicates: every card is on a foundation, in a cell, or in
      the tableau, exactly once. -/
  cards_count : ∀ c : Card, countState s c = 1
  /-- Depths are in range. -/
  depth_lt6 : ∀ i : Fin 10, (p.pileDepth.get i).toInt.toNat < 6
  /-- **Depths match**: pile `i`'s bottom `pileDepth i` cards are still the dealt
      ones, and everything stacked above them is a same-suit descending run
      continuing from the boundary card.  For `pileDepth i = 0` this degenerates
      to `PileMatches`' king-run branch: the column is empty or a run topped out
      at a king. -/
  depth_match : ∀ i : Fin 10,
      PileMatches g (s.tableau i) i ⟨(p.pileDepth.get i).toInt.toNat, depth_lt6 i⟩
  /-- **Flutes match** the *physical* run above the boundary.  This is what makes
      space accounting exact without assuming the state is normalized: a card
      still sitting in a cell is simply not part of the flute. -/
  flute_match : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toInt.toNat →
      (s.tableau i).length + 1
        = (p.pileDepth.get i).toInt.toNat + (p.pileFlute.get i).toNat
  /-- A pile the solver treats as empty carries either nothing or a *complete*
      king stack for its suit — as many cards as the suit has freed from the top,
      per `kings`.  (A partially assembled king stack matches no position; such
      states occur only transiently, inside a flute move.) -/
  king_pile : ∀ i : Fin 10, (p.pileDepth.get i).toInt.toNat = 0 →
      ∀ c ∈ (s.tableau i).getLast?,
        (s.tableau i).length
          + (VALUE (p.kings.get (finOfSuit c.suit)).toUInt8).toNat = 13
  /-- **Foundations match.**  Unlike `kings`, `aces` is *not* determined by the
      depths — a freed card may be on the foundation or in a cell — so this has
      to be said. -/
  aces_match : ∀ su : Suit,
      (p.aces.get (finOfSuit su)).toUInt8 = encodeFoundation su (s.foundations su)

/-! ## Immediate consequences -/

theorem StateMatchesSolverPos.toStateMatchesLayout {g : Globals} {s : State}
    {p : SolverPosType} (h : StateMatchesSolverPos g s p) : StateMatchesLayout g s where
  piles_match i := ⟨⟨(p.pileDepth.get i).toInt.toNat, h.depth_lt6 i⟩, h.depth_match i⟩
  cards_count := h.cards_count

theorem StateMatchesSolverPos.noDup {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) : NoDupState s :=
  fun c => le_of_eq (h.cards_count c)

/-- The foundation readout, in `Rules` terms. -/
theorem StateMatchesSolverPos.foundation_value {g : Globals} {s : State}
    {p : SolverPosType} (h : StateMatchesSolverPos g s p) (su : Suit) :
    (VALUE (p.aces.get (finOfSuit su)).toUInt8).toNat = optRankToNat (s.foundations su) := by
  have hr : optRankToNat (s.foundations su) ≤ 13 := by
    cases hf : s.foundations su with
    | none => simp [optRankToNat]
    | some r => simpa [optRankToNat] using rankBounded r
  have hs : suitToNat su < 4 := suitToNat_lt su
  rw [h.aces_match su, encodeFoundation, VALUE_toNat, CARD_toNat (by omega) (by omega)]
  omega
