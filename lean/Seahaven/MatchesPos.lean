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
          + (VALUE (p.kings.get (finOfSuit c.suit))).toNat = 13
  /-- **Foundations match.**  Unlike `kings`, `aces` is *not* determined by the
      depths — a freed card may be on the foundation or in a cell — so this has
      to be said. -/
  aces_match : ∀ su : Suit,
      (p.aces.get (finOfSuit su)) = encodeFoundation su (s.foundations su)

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
    (VALUE (p.aces.get (finOfSuit su))).toNat = optRankToNat (s.foundations su) := by
  have hr : optRankToNat (s.foundations su) ≤ 13 := by
    cases hf : s.foundations su with
    | none => simp [optRankToNat]
    | some r => simpa [optRankToNat] using rankBounded r
  have hs : suitToNat su < 4 := suitToNat_lt su
  rw [h.aces_match su, encodeFoundation, VALUE_toNat, CARD_toNat (by omega) (by omega)]
  omega

/-! ## Encoding bridge and the flute split -/

theorem nextCard_of_encode {c d : Card}
    (hs : SUIT (encodeCard d) = SUIT (encodeCard c))
    (hv : (VALUE (encodeCard d)).toNat = (VALUE (encodeCard c)).toNat + 1) :
    nextCard c = some d := by
  rw [encodeCard_SUIT, encodeCard_SUIT] at hs
  rw [encodeCard_VALUE, encodeCard_VALUE] at hv
  have hsuit : d.suit = c.suit := by
    have h1 : suitToNat d.suit < 4 := suitToNat_lt _
    have h2 : suitToNat c.suit < 4 := suitToNat_lt _
    have heq : suitToNat d.suit = suitToNat c.suit := by
      have := congrArg UInt8.toNat hs
      rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at this
      omega
    rw [← natToSuit_suitToNat d.suit, ← natToSuit_suitToNat c.suit]
    congr 1
    exact Fin.ext heq
  have hnr : nextRank (some c.rank) = some d.rank := by
    unfold nextRank
    rw [show optRankToNat (some c.rank) = rankToNat c.rank from rfl, ← hv]
    exact rankToNatToRank (some d.rank)
  unfold nextCard
  rw [hnr]
  simp [Card.ext_iff, hsuit]

theorem isRun_of_getElem : ∀ {l : List Card},
    (∀ (j : Nat) (hj : j + 1 < l.length), nextCard l[j] = some l[j + 1]) → IsRun l
  | [], _ => trivial
  | [_], _ => ⟨by simp, trivial⟩
  | x :: y :: t, h => by
    refine ⟨?_, isRun_of_getElem (fun j hj => ?_)⟩
    · intro z hz
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h 0 (by simp)
    · exact h (j + 1) (by simpa using hj)

theorem reverse_drop_eq_take_reverse (l : List Card) (n : Nat) (hn : n ≤ l.length) :
    l.reverse.drop n = (l.take (l.length - n)).reverse := by
  rw [List.reverse_take]
  · congr 1; omega

theorem rankToNat_pos (r : Rank) : 1 ≤ rankToNat r := by cases r <;> simp [rankToNat]

/-- Every card of the flute, indexed from the top of the column, carries the
boundary's suit and a value that climbs by one towards the boundary. -/
theorem flute_elem {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10)
    (hd : 0 < (p.pileDepth.get i).toInt.toNat)
    (b : Fin 5) (hb : b.val = (p.pileDepth.get i).toInt.toNat - 1) :
    ∀ (idx : Nat), idx < (s.tableau i).length + 1 - (p.pileDepth.get i).toInt.toNat →
      ∀ (hlt : idx < (s.tableau i).length),
      SUIT (encodeCard (s.tableau i)[idx]) = SUIT ((g.pos2card.get i).get b) ∧
      (VALUE (encodeCard (s.tableau i)[idx])).toNat
          + ((s.tableau i).length - (p.pileDepth.get i).toInt.toNat)
        = (VALUE ((g.pos2card.get i).get b)).toNat + idx := by
  intro idx hidx hlt
  obtain ⟨h1, hbot, h3⟩ := h.depth_match i
  simp only [] at h3
  rw [dif_pos (by simpa using hd)] at h3
  have hbfin : (⟨(p.pileDepth.get i).toInt.toNat - 1, by have := h.depth_lt6 i; omega⟩ : Fin 5) = b :=
    Fin.ext hb.symm
  rw [hbfin] at h3
  set col := s.tableau i with hcoldef
  set L := col.length with hL
  set n := (p.pileDepth.get i).toInt.toNat with hn
  set B := (g.pos2card.get i).get b with hB
  have hnL : n ≤ L := h1
  by_cases hbnd : idx = L - n
  · have hk : n - 1 < n := by omega
    have hbk := hbot ⟨n - 1, hk⟩
    have hrevlt : n - 1 < col.reverse.length := by simp [hL]; omega
    rw [List.getElem?_eq_getElem hrevlt, Option.map_some, List.getElem_reverse hrevlt] at hbk
    have hidxeq : col.length - 1 - (n - 1) = idx := by omega
    simp only [hidxeq] at hbk
    have hBfin : (⟨n - 1, by have := h.depth_lt6 i; omega⟩ : Fin 5) = b := Fin.ext hb.symm
    rw [hBfin] at hbk
    have heq : encodeCard col[idx] = B := Option.some.inj hbk
    rw [heq, hbnd]
    exact ⟨rfl, by omega⟩
  · have hidxlt : idx < L - n := by omega
    set m := L - n - 1 - idx with hm
    have hflen : ((col.reverse.drop n).map encodeCard).length = L - n := by simp [hL]
    have hmlt : m < ((col.reverse.drop n).map encodeCard).length := by rw [hflen]; omega
    obtain ⟨hs3, hv3⟩ := h3 ⟨m, hmlt⟩
    have hdroplt : n + m < col.reverse.length := by simp [hL]; omega
    have helem : ((col.reverse.drop n).map encodeCard)[m] = encodeCard col[idx] := by
      rw [List.getElem_map, List.getElem_drop, List.getElem_reverse hdroplt]
      congr 2
      omega
    rw [List.get_eq_getElem, helem] at hs3 hv3
    have hpos : 1 ≤ (VALUE (encodeCard col[idx])).toNat := by
      rw [encodeCard_VALUE]; exact rankToNat_pos _
    have hkey : m + idx + 1 = L - n := by omega
    simp only [Fin.val_mk] at hv3
    refine ⟨hs3, ?_⟩
    show (VALUE (encodeCard col[idx])).toNat + (L - n) = (VALUE B).toNat + idx
    omega

/-- **The bridge to `FluteMoves`.**  A pile with positive depth splits as
`top ++ boundary :: rest`, where `top` is the physical flute above the boundary
(`pileFlute - 1` cards), `rest` is what stays put (`pileDepth - 1` cards), and
`top ++ [boundary]` is a run — exactly the shape `run_fluteMoves` consumes. -/
theorem StateMatchesSolverPos.flute_split {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10)
    (hd : 0 < (p.pileDepth.get i).toInt.toNat) :
    ∃ (top rest : Column) (c : Card),
      s.tableau i = top ++ c :: rest ∧
      top.length + 1 = (p.pileFlute.get i).toNat ∧
      rest.length + 1 = (p.pileDepth.get i).toInt.toNat ∧
      IsRun (top ++ [c]) := by
  have hfm := h.flute_match i hd
  have hnL : (p.pileDepth.get i).toInt.toNat ≤ (s.tableau i).length := (h.depth_match i).1
  have hb5 : (p.pileDepth.get i).toInt.toNat - 1 < 5 := by have := h.depth_lt6 i; omega
  have helem := flute_elem h i hd ⟨(p.pileDepth.get i).toInt.toNat - 1, hb5⟩ rfl
  set col := s.tableau i with hcoldef
  set n := (p.pileDepth.get i).toInt.toNat with hn
  set k := col.length - n with hk
  have hklt : k < col.length := by omega
  refine ⟨col.take k, col.drop (k + 1), col[k], ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop k col]
    rw [List.drop_eq_getElem_cons hklt]
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega
  · have hsucc : col.take k ++ [col[k]] = col.take (k + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hklt]; rfl
    rw [hsucc]
    refine isRun_of_getElem (fun j hj => ?_)
    simp only [List.length_take] at hj
    have hj1 : j + 1 < col.length := by omega
    have hjl : j < col.length := by omega
    have hgj : (col.take (k + 1))[j] = col[j] := List.getElem_take ..
    have hgj1 : (col.take (k + 1))[j + 1] = col[j + 1] := List.getElem_take ..
    rw [hgj, hgj1]
    obtain ⟨hs0, hv0⟩ := helem j (by omega) hjl
    obtain ⟨hs1, hv1⟩ := helem (j + 1) (by omega) hj1
    exact nextCard_of_encode (hs1.trans hs0.symm) (by omega)
