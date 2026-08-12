import Seahaven.SolverSpecCommon

/-!
# Spec for `kingMove`

Field-projection helpers (mirroring the `preCleanupPile` family) and the
`PileBase`/`PileMerged`/`PileClean`/`SuitClean` preservation theorems for
`kingMove`, the pure step that drains a pile down to a freshly exposed king.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **`kingMove` always leaves the drained pile `PileClean`.**  No hypotheses
    on the entry position are needed at all: `kingMove` unconditionally sets
    `pileDepth[pile] := 0`/`pileFlute[pile] := 1`, and every `PileBase`/
    `PileMerged` clause for pile `i` is either immediate from `flute = 1` or
    vacuous once `depth = 0` (the `flute_cards_free`/`flute_not_aces`/
    `busyAces_complete` clauses all have `depth > 0` as a hypothesis; the
    `merge_complete`/`flute_maximal` clauses have a `depth ≤ 1`/`depth = 0`
    escape-hatch disjunct). -/
theorem kingMove_pileClean_self (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    PileClean g (kingMove pile hpile suit hs4 ph p) ⟨pile.toNat, hpile⟩ := by
  have hd0 : (kingMove pile hpile suit hs4 ph p).pileDepth.get ⟨pile.toNat, hpile⟩ = 0 := by
    show (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile = 0
    unfold kingMove
    rw [Vector.getElem_set_self]
  have hf1 : (kingMove pile hpile suit hs4 ph p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
    show (kingMove pile hpile suit hs4 ph p).pileFlute[pile.toNat]'hpile = 1
    unfold kingMove
    rw [Vector.getElem_set_self]
  exact {
    pileDepth_bound := by rw [hd0]; decide
    flute_pos := by rw [hf1]; decide
    flute_empty := fun _ => hf1
    flute_cards_free := fun _ hpos _ _ => absurd hpos (by rw [hd0]; decide)
    flute_not_aces := fun hpos _ => absurd hpos (by rw [hd0]; decide)
    merge_complete := Or.inl (by rw [hd0]; decide)
    flute_maximal := Or.inl hd0
    busyAces_complete := fun hpos => absurd hpos (by rw [hd0]; decide) }

-- ---------------------------------------------------------------------------
-- `kingMove` field-projection helpers, mirroring the `preCleanupPile` family
-- above (`preCleanupPile_pileDepth_eq_of_ne` etc.): `kingMove` only ever
-- writes `freePiles`/`usedSpace`/`kings[suit]`/`hash`/`pileDepth[pile]`/
-- `pileFlute[pile]`, so every other field/index is literally untouched.
-- ---------------------------------------------------------------------------

/-- `kingMove` never touches `aces`. -/
theorem kingMove_aces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).aces = p.aces := by
  simp only [kingMove]

/-- `kingMove` never touches `busyAces`. -/
theorem kingMove_busyAces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).busyAces = p.busyAces := by
  simp only [kingMove]

/-- `kingMove` leaves `kings[s]` literally unchanged for every suit `s ≠ suit`. -/
theorem kingMove_kings_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (s : Fin 4) (hs : s.val ≠ suit.toUInt32.toNat) :
    (kingMove pile hpile suit hs4 ph p).kings.get s = p.kings.get s := by
  show (kingMove pile hpile suit hs4 ph p).kings[s.val]'s.isLt = p.kings[s.val]'s.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hs4 s.isLt (Ne.symm hs)]

/-- `kingMove`'s exact effect on `kings[suit]`: it drops by the drained
    pile's flute length. -/
theorem kingMove_kings_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).kings.get (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) =
      p.kings.get (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) -
        (p.pileFlute[pile.toNat]'hpile) := by
  show (kingMove pile hpile suit hs4 ph p).kings[suit.toUInt32.toNat]'hs4 =
    p.kings[suit.toUInt32.toNat]'hs4 - (p.pileFlute[pile.toNat]'hpile)
  simp only [kingMove]
  rw [Vector.getElem_set_self]

/-- `kingMove` literally leaves `pileDepth[j]` unchanged at every `j ≠ pile`. -/
theorem kingMove_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (kingMove pile hpile suit hs4 ph p).pileDepth.get j = p.pileDepth.get j := by
  show (kingMove pile hpile suit hs4 ph p).pileDepth[j.val]'j.isLt = p.pileDepth[j.val]'j.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `kingMove` literally leaves `pileFlute[j]` unchanged at every `j ≠ pile`. -/
theorem kingMove_pileFlute_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (kingMove pile hpile suit hs4 ph p).pileFlute.get j = p.pileFlute.get j := by
  show (kingMove pile hpile suit hs4 ph p).pileFlute[j.val]'j.isLt = p.pileFlute[j.val]'j.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `kingMove` unconditionally sets `pileDepth[pile] := 0`. -/
theorem kingMove_pileDepth_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := by
  show (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile = 0
  simp only [kingMove]
  rw [Vector.getElem_set_self]

/-- `kingMove` unconditionally sets `pileFlute[pile] := 1`. -/
theorem kingMove_pileFlute_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).pileFlute.get (⟨pile.toNat, hpile⟩ : Fin 10) = 1 := by
  show (kingMove pile hpile suit hs4 ph p).pileFlute[pile.toNat]'hpile = 1
  simp only [kingMove]
  rw [Vector.getElem_set_self]

/-- `kingMove` only ever decreases `pileDepth`, pointwise across all ten piles:
    `pile`'s own depth drops (to `0`); every other pile is literally untouched.
    The direct `kingMove` counterpart of `preCleanupPile_pileDepth_le`, needed
    for the same `isFreeCard_mono` transfer argument. -/
theorem kingMove_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (i : Fin 10) :
    ((kingMove pile hpile suit hs4 ph p).pileDepth.get i).toNat ≤
      (p.pileDepth.get i).toNat := by
  by_cases hip : i.val = pile.toNat
  · have hi : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hip
    rw [hi, kingMove_pileDepth_self]
    exact Nat.zero_le _
  · rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip]

/-- **A real card, other than the just-revealed boundary `K`, keeps its
    freeness status across `kingMove`.**  `kingMove` only ever changes
    `pileDepth[pile]` (from `1` to `0`), which only newly frees the single
    card sitting at depth-index `0` — exactly `K` (`pile`'s sole remaining
    boundary card, per `hd1`).  For any OTHER real card `C ≠ K`: if `C`'s home
    pile isn't `pile`, `kingMove` doesn't touch it at all; if it IS `pile`,
    `round_trip` would force `C` to sit at index `0` too (the only occupied
    slot), i.e. `C = K`, contradicting `hne`.  So `C`'s home pile is
    genuinely untouched either way, and `¬isFreeCard`/`isFreeCard` transfer by
    the usual `cardDepth`-vs-`pileDepth` bridge. -/
private theorem kingMove_not_free_of_ne (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g) (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32)
    (p : SolverPosType) (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (C : UInt8) (hCreal : IsRealCard C) (hne : C ≠ K) (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (kingMove pile hpile suit hs4 ph p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
  have hcp_ne : (cardPile g C).toNat ≠ pile.toNat := by
    intro hcp
    apply hne
    have hcd0 : (cardDepth g C).toNat = 0 := by
      by_contra hcdne
      apply hnfree
      apply isFree_of_cardDepth_ge g p hwf C hc64 hp64
      have hpdEq : p.pileDepth[(cardPile g C).toNat]'hp64 = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hpdEq, hd1]
      show (cardDepth g C).toNat ≥ ((1 : UInt8)).toNat
      have h1 : ((1 : UInt8)).toNat = 1 := by decide
      omega
    have hcd_lt5 : (cardDepth g C).toNat < 5 := by omega
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) =
        (⟨0, by omega⟩ : Fin 5) := Fin.ext hcd0
    rw [hcpEq, hcdEq] at hround
    rw [hKdef]
    exact hround.symm
  intro hfree
  have hge := isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
  have hpdEq' : (kingMove pile hpile suit hs4 ph p).pileDepth[(cardPile g C).toNat]'hp64 =
      p.pileDepth[(cardPile g C).toNat]'hp64 :=
    kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p ⟨(cardPile g C).toNat, hp64⟩ hcp_ne
  rw [hpdEq'] at hge
  exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)

/-- **`PileBase` survives `kingMove` at every OTHER pile `j ≠ pile`.**  Easier
    than the `preCleanupPile` counterpart (`preCleanupPile_pileBase_ne`):
    `kingMove` only ever drops `pile`'s own depth to `0` (never partially
    reveals a range the way `preCleanupPile`'s `m`/`f` do), so `j`'s own
    depth/flute are literally unchanged
    (`kingMove_pileDepth_eq_of_ne`/`_pileFlute_eq_of_ne`) and the freeness
    clause (`flute_cards_free`) transfers via `isFreeCard_mono` using
    `kingMove_pileDepth_le` (depths only ever decrease everywhere, so anything
    free before stays free); `flute_not_aces` doesn't even mention freeness
    (`aces` is untouched by `kingMove_aces_eq`), so it transfers verbatim. -/
theorem kingMove_pileBase_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) (hb : PileBase g p j) :
    PileBase g (kingMove pile hpile suit hs4 ph p) j := by
  have hdeq := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj
  have hfeq := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p j hj
  have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
  have hdmono := kingMove_pileDepth_le pile hpile suit hs4 ph p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeq]; exact hb.pileDepth_bound
  · rw [hfeq]; exact hb.flute_pos
  · intro h0
    rw [hfeq]
    apply hb.flute_empty
    rwa [hdeq] at h0
  · intro k hdpos hk0 hklt
    have hdpos' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdpos
    have hklt' : k.toNat < (p.pileFlute.get j).toNat := by rw [← hfeq]; exact hklt
    have hidxEq : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toNat - 1, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    rw [hXeq]
    exact isFreeCard_mono hdmono (hb.flute_cards_free k hdpos' hk0 hklt')
  · intro hdpos
    have hdpos' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdpos
    have hidxEq : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toNat - 1, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `kingMove` terms
    -- first (so the `let boundary` in the field's own statement gets expanded
    -- concretely), THEN reduce those wrappers uniformly.
    show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
        ).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat < 4,
      ((kingMove pile hpile suit hs4 ph p).aces.get
        ⟨(SUIT ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
            ).pileDepth.get j).toNat - 1,
            by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat, hs⟩).toNat +
        ((kingMove pile hpile suit hs4 ph p).pileFlute.get j).toNat ≤
      UInt8.toNat ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
          ).pileDepth.get j).toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)
    rw [hXeq, hfeq, haeq]
    intro hs
    exact hb.flute_not_aces hdpos' hs

/-- **`PileMerged` survives `kingMove` at every OTHER pile `j ≠ pile`.**
    `merge_complete`/`busyAces_complete` are even more trivial than in the
    `preCleanupPile` counterpart (`preCleanupPile_pileMerged_ne`): `kingMove`
    doesn't touch `busyAces` at all (`kingMove_busyAces_eq`), and doesn't
    touch `pos2card`/`pileDepth[j]`/`pileFlute[j]`/`aces` for `j ≠ pile`
    (all literal equalities, not just index-shift ones).  `flute_maximal[j]`
    is the one clause needing real work, but it's EASIER here than in
    `preCleanupPile_pileMerged_ne`: `kingMove` reveals exactly ONE card
    (`pile`'s own boundary `K`, going from not-free to free as depth drops
    from `1` to `0`).  The key sub-argument, `kingMove_prevCard_ne_K`-style
    (inlined below): pile `j`'s own flute-bottom `prevCard` can never equal
    `K`, because `K` has `VALUE = 13` (`hVK13`) — if `prevCard = K` then
    `VALUE boundary_j = VALUE prevCard + pileFlute[j] = 13 + pileFlute[j] ≥ 14`
    (`flute_pos : pileFlute[j] ≥ 1`), contradicting `boundary_j`'s own
    realness (`VALUE ≤ 13`, from `pos2card_real`).  So `prevCard ≠ K`
    unconditionally, and `¬isFreeCard` transfers via `kingMove_not_free_of_ne`
    — no round-trip/uniqueness reasoning needed at all (simpler than
    `preCleanupPile_pileMerged_ne`'s `k`-indexed exclusion argument, which had
    to rule out a whole absorbed *range* rather than a single card). -/
theorem kingMove_pileMerged_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (hVK13 : (VALUE K).toNat = 13)
    (hak : ∀ s : Fin 4, SUIT (p.aces.get s) = s.val.toUInt8)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hb : PileBase g p j) (hpm : PileMerged g p j hb.pileDepth_bound) :
    PileMerged g (kingMove pile hpile suit hs4 ph p) j
      (by rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj]
          exact hb.pileDepth_bound) := by
  have hdeq := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj
  have hfeq := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p j hj
  have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
  have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete: transfers verbatim (only reads `pos2card`/`pileDepth[j]`).
    have hidxEq2 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 2 =
        (p.pileDepth.get j).toNat - 2 := by rw [hdeq]
    have hidxEq1 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hX2 : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toNat - 2, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq2
    have hX1 : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toNat - 1, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq1
    rw [hX2, hX1, hdeq]
    exact hpm.merge_complete
  · -- (3b) flute_maximal: the hard clause.
    by_cases hd0 : p.pileDepth.get j = 0
    · left
      rw [hdeq]
      exact hd0
    · have hdj : (p.pileDepth.get j).toNat > 0 :=
        Nat.pos_of_ne_zero (fun h => hd0 (UInt8.toNat_inj.mp h))
      right
      set boundaryNew := (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
            ).pileDepth.get j).toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew_def
      set prevCardNew := boundaryNew -
          (kingMove pile hpile suit hs4 ph p).pileFlute.get j with hprevCardNew_def
      show (∃ hs : (SUIT boundaryNew).toNat < 4,
          (kingMove pile hpile suit hs4 ph p).aces.get ⟨(SUIT boundaryNew).toNat, hs⟩ =
            prevCardNew) ∨
        ¬ isFreeCard g (kingMove pile hpile suit hs4 ph p) prevCardNew
      set boundary := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
          by have := hb.pileDepth_bound; omega⟩ with hboundary_def
      set prevCard := boundary - p.pileFlute.get j with hprevCard_def
      have hidxEqB : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 1 =
          (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
      have hboundEq : boundaryNew = boundary := by
        rw [hboundaryNew_def, hboundary_def]
        congr 1
        exact Fin.ext hidxEqB
      have hprevEq : prevCardNew = prevCard := by
        rw [hprevCardNew_def, hprevCard_def, hboundEq, hfeq]
      rw [hboundEq, hprevEq, haeq]
      have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
      have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
      have hBDrange : boundary.toNat ≤ 61 := by
        have hsn := SUIT_toNat boundary
        have hvn := VALUE_toNat boundary
        have h1 := hrealBd.1; have h2 := hrealBd.2.1; have h3 := hrealBd.2.2
        omega
      have hflv : (p.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
        hb.flute_le_value hwf hak hdj
      have hVsn_bd := VALUE_toNat boundary
      have hSsn_bd := SUIT_toNat boundary
      have hfleB : p.pileFlute.get j ≤ boundary := by
        rw [UInt8.le_iff_toNat_le]
        have := Nat.mod_le boundary.toNat 16
        omega
      have hprevNat : prevCard.toNat = boundary.toNat - (p.pileFlute.get j).toNat :=
        UInt8.toNat_sub_of_le _ _ hfleB
      have hSUITeq : SUIT prevCard = SUIT boundary := by
        apply UInt8.toNat_inj.mp
        rw [SUIT_toNat, SUIT_toNat, hprevNat]
        omega
      have hVALeq : (VALUE prevCard).toNat =
          (VALUE boundary).toNat - (p.pileFlute.get j).toNat := by
        rw [VALUE_toNat, hprevNat]
        omega
      have hsuiteq : SUIT boundary = (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 := by
        show SUIT boundary = ((SUIT boundary).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      rcases hpm.flute_maximal.resolve_left hd0 with hOldA | hOldNF
      · left
        exact hOldA
      · by_cases hV0 : (VALUE prevCard).toNat = 0
        · -- `prevCard` is the suit's own zero-value sentinel: the NEW
          -- unconditional Nat-based `flute_not_aces` upper bound (`hb`, no
          -- offset/case-split needed), combined with the suit-block lower
          -- bound, pins `aces = prevCard` exactly (no old `≥`/inequality
          -- special-casing needed anymore).
          left
          refine ⟨hs4', ?_⟩
          have hSuitAcesEq :
              SUIT ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩)) = SUIT boundary := by
            rw [hak ⟨(SUIT boundary).toNat, hs4'⟩, ← hsuiteq]
          have hVBnat := VALUE_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSBnat := SUIT_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSeq := congrArg UInt8.toNat hSuitAcesEq
          have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
          have hacesGeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat ≥ prevCard.toNat := by
            rw [hprevNat0]; omega
          have hboundUpper : (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat +
              (p.pileFlute.get j).toNat ≤ boundary.toNat := hb.flute_not_aces hdj hs4'
          have hacesLeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat ≤ prevCard.toNat := by
            rw [hprevNat]; omega
          have hacesEqNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat = prevCard.toNat :=
            le_antisymm hacesLeNat hacesGeNat
          exact UInt8.toNat_inj.mp hacesEqNat
        · -- `prevCard` is a genuine real card: it can't equal `K` (the only
          -- card `kingMove` newly reveals), so `¬isFreeCard` transfers via
          -- `kingMove_not_free_of_ne` directly — no need to rule out a whole
          -- absorbed range as in `preCleanupPile_pileMerged_ne`.
          right
          have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
          have hVle : (VALUE prevCard).toNat ≤ 13 := by
            have := hrealBd.2.2
            omega
          have hCrealPrev : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
          have hne : prevCard ≠ K := by
            intro hpeqK
            have hVKeq : (VALUE prevCard).toNat = 13 := by rw [hpeqK]; exact hVK13
            have hflpos : 1 ≤ (p.pileFlute.get j).toNat := hb.flute_pos
            have hBle13 := hrealBd.2.2
            omega
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef
            prevCard hCrealPrev hne hOldNF
  · -- (6) busyAces_complete
    intro hdi
    have hdi' : (p.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdi
    set boundaryNew2 := (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
          ).pileDepth.get j).toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew2_def
    show ∀ hs : (SUIT boundaryNew2).toNat < 4,
        ((kingMove pile hpile suit hs4 ph p
          ).aces.get ⟨(SUIT boundaryNew2).toNat, hs⟩) =
          boundaryNew2 - (kingMove pile hpile suit hs4 ph p).pileFlute.get j →
        (kingMove pile hpile suit hs4 ph p
          ).busyAces &&& ((1 : UInt8) <<< SUIT boundaryNew2) ≠ 0
    set boundaryOld2 := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ with hboundaryOld2_def
    have hidxEqB2 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toNat - 1 =
        (p.pileDepth.get j).toNat - 1 := by rw [hdeq]
    have hboundEq2 : boundaryNew2 = boundaryOld2 := by
      rw [hboundaryNew2_def, hboundaryOld2_def]
      congr 1
      exact Fin.ext hidxEqB2
    rw [hboundEq2, hfeq, haeq, hbeq]
    exact hpm.busyAces_complete hdi'

set_option maxHeartbeats 1000000 in
/-- **`SuitClean` holds for every suit `s` after `kingMove`.**  Split on
    whether `s` is the drained suit (`s.val = (SUIT K).toUInt32.toNat`, where
    `K` is `pile`'s sole remaining boundary card, the king being drained) or
    not.

    **Other suits**: trivial — `kings`/`aces` for suit `s` are completely
    untouched by `kingMove` (it only ever writes `kings[suit]` for the ONE
    passed-in `suit`), and the only way a fact about suit `s` could break is a
    freeness claim about a suit-`s` card colliding with the one newly-revealed
    card `K` — ruled out immediately since `K` has the DRAINED suit, not `s`.

    **Drained suit**: needs the full derivation chain — `K`'s old value at
    `kings[suit]` is pinned down exactly (`hsc.king_frontier` forces
    `kings[suit] = K`), the new `kings[suit] = K - pileFlute[pile] = prevCard`
    matches `kingMove`'s own formula, and `hnfreeprev`/`hsc.foundation_cards_free`
    together place `aces[suit]` at or below `prevCard` (mirroring the
    `PileMerged.flute_maximal` "sentinel vs genuine" split from
    `kingMove_pileMerged_ne`: when `prevCard`'s value is exactly `0`,
    `aces[suit] = prevCard` follows from `flute_cards_free`/`busyAces_complete`
    rather than a strict inequality). -/
theorem kingMove_suitClean (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (hpdb : ∀ i : Fin 10, (p.pileDepth.get i).toNat ≤ 5)
    (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (hVK13 : (VALUE K).toNat = 13)
    (hsuiteq : suit = SUIT K)
    (hak : ∀ t : Fin 4, SUIT (p.aces.get t) = t.val.toUInt8)
    (hc : PileClean g p ⟨pile.toNat, hpile⟩)
    (s : Fin 4) (hsc : SuitClean g p s hpdb) :
    SuitClean g (kingMove pile hpile suit hs4 ph p) s
      (fun i => le_trans (kingMove_pileDepth_le pile hpile suit hs4 ph p i) (hpdb i)) := by
  have hsK : (SUIT K).toUInt32.toNat < 4 := by rw [← hsuiteq]; exact hs4
  have hd1' : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat = 1 := by
    show (p.pileDepth[pile.toNat]'hpile).toNat = 1
    rw [hd1]; decide
  have hidxpf : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1 < 5 := by omega
  have hboundIdx : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1 = 0 := by omega
  have hdpilepos : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat > 0 := by omega
  have hKeqBoundary : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩ = K := by
    rw [hKdef]; congr 1; exact Fin.ext hboundIdx
  have hKreal : IsRealCard K :=
    hKeqBoundary ▸ hwf.pos2card_real (⟨pile.toNat, hpile⟩ : Fin 10)
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩
  have hsBoundary4 : (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat < 4 := by
    rw [hKeqBoundary]; exact hKreal.1
  -- Bridges the pile's own internally-computed `SUIT boundary`-indexed `Fin 4`
  -- (as used by `PileBase`/`PileMerged` fields like `flute_not_aces`/
  -- `busyAces_complete`) to the `SUIT K`-indexed one used throughout this
  -- proof — needed as its own `have` (rather than a direct `rw`) since `K`
  -- appears both as the `Fin 4` value AND inside the embedded `< 4` proof,
  -- the usual dependent-rewrite gotcha.
  have hFinEqBd : (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat,
      hsBoundary4⟩ : Fin 4) = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := by
    apply Fin.ext
    show (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat =
      (SUIT K).toUInt32.toNat
    rw [hKeqBoundary, UInt8.toNat_toUInt32]
  have hKnotfree : ¬ isFreeCard g p K := by
    rw [← hKeqBoundary]
    exact depth_card_not_free_wf hwf (⟨pile.toNat, hpile⟩ : Fin 10)
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩ (by
        show (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1 <
          (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat
        omega)
  -- `pileFlute[pile] ≤ VALUE K = 13`, so `SUIT (K - pileFlute[pile]) = SUIT K`
  -- (no suit-block underflow) — needed regardless of which suit we're proving.
  have hflv : (p.pileFlute.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat ≤
      (VALUE ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat :=
    hc.flute_le_value hwf hak hdpilepos
  have hflv13 : (p.pileFlute[pile.toNat]'hpile).toNat ≤ 13 := by
    rw [hKeqBoundary, hVK13] at hflv
    exact hflv
  have hfleK : p.pileFlute[pile.toNat]'hpile ≤ K := by
    rw [UInt8.le_iff_toNat_le]
    have hVKn := VALUE_toNat K
    omega
  have hprevNat : (K - p.pileFlute[pile.toNat]'hpile).toNat =
      K.toNat - (p.pileFlute[pile.toNat]'hpile).toNat := UInt8.toNat_sub_of_le _ _ hfleK
  have hSUITprev : SUIT (K - p.pileFlute[pile.toNat]'hpile) = SUIT K := by
    apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hprevNat]
    have hVKn := VALUE_toNat K
    omega
  have hVprev : (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat =
      13 - (p.pileFlute[pile.toNat]'hpile).toNat := by
    rw [VALUE_toNat, hprevNat]
    have hVKn := VALUE_toNat K
    omega
  by_cases hsame : s.val = (SUIT K).toUInt32.toNat
  · -- **Drained suit.**
    have hseq : s = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := Fin.ext hsame
    subst hseq
    have hSKeqSval : SUIT K = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4).val.toUInt8 := by
      show SUIT K = ((SUIT K).toUInt32.toNat).toUInt8
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have h2 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
      have hsn := SUIT_toNat K
      omega
    -- Step 2: `kings[suit] = K` exactly, from `hsc.king_frontier`'s `∀c`
    -- clause at `c := K` (contrapositive: `K` not free forces
    -- `VALUE(kings[suit]) ≥ 13`, hence `= 13` by `aces_kings_valid`).
    have hVKge13 : 13 ≤ (VALUE (p.kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))).toNat := by
      by_contra hlt
      push Not at hlt
      exact hKnotfree (hsc.king_frontier.2 K hSKeqSval (by omega) (by omega))
    have hVKeq13 : (VALUE (p.kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))).toNat = 13 := by
      have hle := hsc.aces_kings_valid.2.2.2.1
      omega
    have hSKingsEqK : SUIT (p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) =
        SUIT K := hsc.aces_kings_valid.2.2.1.trans hSKeqSval.symm
    have hKingsEqK : (p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) = K :=
      card_eq_of_suit_value _ _ hSKingsEqK (hVKeq13.trans hVK13.symm)
    -- Step 3: `new_kings[suit] = K - pileFlute[pile] = prevCard`.
    have hnewkings8 : ((kingMove pile hpile suit hs4 ph p).kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) =
        K - p.pileFlute[pile.toNat]'hpile := by
      have hsFinEq : (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) =
          (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := Fin.ext (by
        show suit.toUInt32.toNat = (SUIT K).toUInt32.toNat
        rw [hsuiteq])
      have step1 := kingMove_kings_self pile hpile suit hs4 ph p
      rw [hsFinEq] at step1
      have hOldEq : p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) = K := hKingsEqK
      rw [step1, hOldEq]
    have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
    have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
    -- Step 4: `aces[suit] ≤ prevCard`, with equality forced (via
    -- `busyAces_complete`) exactly when `prevCard` is the suit's own
    -- zero-value sentinel (`pileFlute[pile] = 13`); a genuine strict `<`
    -- otherwise (via `foundation_cards_free`'s contrapositive).
    have hprevlt64 : (K - p.pileFlute[pile.toNat]'hpile).toNat < 64 := by
      have hb1 := SUIT_toNat (K - p.pileFlute[pile.toNat]'hpile)
      have hb2 := VALUE_toNat (K - p.pileFlute[pile.toNat]'hpile)
      have hb3 := congrArg UInt8.toNat hSUITprev
      have h1 := hKreal.1
      have hsn2 := SUIT_toNat K
      omega
    have hbusyRaw := hc.busyAces_complete hdpilepos hsBoundary4
    have hbusyEq : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
        (K - p.pileFlute[pile.toNat]'hpile) →
        p.busyAces &&& ((1 : UInt8) <<< SUIT K) ≠ 0 := by
      intro haceq
      rw [← hKeqBoundary]
      apply hbusyRaw
      have hFinEq : (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat,
          hsBoundary4⟩ : Fin 4) = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := by
        apply Fin.ext
        show (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat =
          (SUIT K).toUInt32.toNat
        rw [hKeqBoundary, UInt8.toNat_toUInt32]
      have hgetEq : p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat,
          hsBoundary4⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) :=
        congrArg p.aces.get hFinEq
      rw [hgetEq, haceq, hKeqBoundary]
      rfl
    have hprevlt128 : (K - p.pileFlute[pile.toNat]'hpile).toNat < 128 := by omega
    have hKlt128 : K.toNat < 128 := by
      have h1 := hKreal.1; have h2 := hKreal.2.1; have h3 := hKreal.2.2
      have hsn := SUIT_toNat K
      omega
    have hSacesEqK : SUIT (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) =
        SUIT K := by
      rw [hak (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4), ← hSKeqSval]
    have hkey : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
          (K - p.pileFlute[pile.toNat]'hpile) ∨
        (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) <
          (K - p.pileFlute[pile.toNat]'hpile) ∧
          IsRealCard (K - p.pileFlute[pile.toNat]'hpile) ∧
          ¬ isFreeCard g p (K - p.pileFlute[pile.toNat]'hpile)) := by
      have hne : p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) ≠ 0 := by
        intro hz
        rw [hz] at hd1'
        exact absurd hd1' (by decide)
      -- Unconditional upper bound (the new Nat-based `flute_not_aces`, no
      -- case-split on `pileFlute`/sentinel needed at all): `aces ≤ prevCard`
      -- always. Combined with the suit-block lower bound, this pins down
      -- whether we're in the equality or strict-`<` case WITHOUT relying on
      -- which disjunct `hc.flute_maximal`'s own proof term happens to use
      -- (the two disjuncts of `flute_maximal` are not mutually exclusive, so
      -- deciding via `aces` vs `prevCard` directly is the robust approach).
      have hboundUpperNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat +
          (p.pileFlute[pile.toNat]'hpile).toNat ≤ K.toNat := by
        have h := hc.flute_not_aces hdpilepos hsBoundary4
        rwa [show p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
              ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat,
            hsBoundary4⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) from
          congrArg p.aces.get hFinEqBd, hKeqBoundary] at h
      have hacesLeNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat ≤
          (K - p.pileFlute[pile.toNat]'hpile).toNat := by
        rw [hprevNat]; omega
      have hacesGeNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat ≥
          16 * (SUIT K).toNat := by
        have hb1 := SUIT_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
        have hb2 := congrArg UInt8.toNat hSacesEqK
        have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
        omega
      by_cases haceqNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat =
          (K - p.pileFlute[pile.toNat]'hpile).toNat
      · -- Equality case: `aces = prevCard` directly from the Nat equality.
        left
        apply UInt8.toInt_inj.mp
        rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
        have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat : Int) =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
          rfl
        have hacesIntEqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat := rfl
        omega
      · -- Strict case: `aces ≠ prevCard` (Nat) forces `VALUE(prevCard) ≥ 1`
        -- (else both would be pinned to the suit's zero-sentinel, forcing
        -- equality) — so `foundation_cards_free`'s contrapositive route is
        -- safe here. `¬isFreeCard(prevCard)` itself comes from
        -- `hc.flute_maximal`: its equality disjunct is impossible (would
        -- force `aces = prevCard`, contradicting `haceqNat`), so the
        -- not-free disjunct must hold.
        right
        have hVprev_pos : 1 ≤ (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat := by
          have hKsn := SUIT_toNat K
          have hKvn := VALUE_toNat K
          have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
          omega
        have hnfreeprev : ¬ isFreeCard g p (K - p.pileFlute[pile.toNat]'hpile) := by
          rcases hc.flute_maximal.resolve_left hne with ⟨hsB, heq⟩ | hnf'
          · exfalso
            apply haceqNat
            have hEq2 : p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                  ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩)).toNat,
                hsB⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) :=
              congrArg p.aces.get hFinEqBd
            rw [← hEq2, heq, hKeqBoundary]
            rfl
          · rwa [hKeqBoundary] at hnf'
        have hSprevSval : SUIT (K - p.pileFlute[pile.toNat]'hpile) =
            (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4).val.toUInt8 := by
          rw [hSUITprev]; exact hSKeqSval
        refine ⟨?_, ⟨by rw [hSUITprev]; exact hKreal.1, hVprev_pos, by omega⟩, hnfreeprev⟩
        rw [UInt8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128]
        have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat : Int) =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
          rfl
        have hacesIntEqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat := rfl
        omega
    have haces_le_prevCard : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) ≤
        (K - p.pileFlute[pile.toNat]'hpile) := by
      rcases hkey with h | h
      · exact UInt8.le_iff_toInt_le.mpr (le_of_eq (congrArg UInt8.toInt h))
      · exact UInt8.le_iff_toInt_le.mpr (le_of_lt (UInt8.lt_iff_toInt_lt.mp h.1))
    have hprevLtK : (K - p.pileFlute[pile.toNat]'hpile) < K := by
      rw [UInt8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128, uint8_toInt8_toInt_of_lt128 hKlt128]
      have hflpos : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat := hc.flute_pos
      have hVKn := VALUE_toNat K
      omega
    have hacesLtK : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) < K := by
      rw [UInt8.lt_iff_toInt_lt]
      have h1 := UInt8.le_iff_toInt_le.mp haces_le_prevCard
      have h2 := UInt8.lt_iff_toInt_lt.mp hprevLtK
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) aces_kings_valid
      rw [haeq, hnewkings8]
      refine ⟨hsc.aces_kings_valid.1, hsc.aces_kings_valid.2.1, ?_, ?_, haces_le_prevCard⟩
      · exact hSUITprev.trans hSKeqSval
      · omega
    · -- (4a) foundation_cards_free
      intro c h1 h2 h3
      rw [haeq] at h3
      exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
        (hsc.foundation_cards_free c h1 h2 h3)
    · -- (4b-weak) foundation_maximal_weak
      rw [haeq]
      rcases hkey with haceq | ⟨hacest, hCrealPrev, _⟩
      · -- `aces = prevCard` forces the busy bit via `busyAces_complete`
        -- (packaged above as `hbusyEq`), and `kingMove` never touches
        -- `busyAces` (`hbeq`), so the bit is still set in the output.
        rw [hbeq, ← hSKeqSval]
        exact Or.inr (Or.inr (hbusyEq haceq))
      · rcases hsc.foundation_maximal_weak with h13 | hnfreeA | hbusy
        · exfalso
          have hAeqK : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) = K :=
            card_eq_of_suit_value _ _ hSacesEqK (h13.trans hVK13.symm)
          rw [hAeqK] at hacesLtK
          have := UInt8.lt_iff_toInt_lt.mp hacesLtK
          omega
        · -- disjunct 2: transfers, since `aces + 1 ≠ K` (strict `hacest` gives
          -- `aces + 1 ≤ prevCard < K`).
          have hacesNat_lt_prevNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
              ).toNat < (K - p.pileFlute[pile.toNat]'hpile).toNat := by
            rw [UInt8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128] at hacest
            have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat
                : Int) = (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
              rfl
            have heqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat =
                (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toNat := rfl
            omega
          have hflpos : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat := hc.flute_pos
          have hne : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)) + 1 ≠ K := by
            intro heq
            have hlt256 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
                ).toNat + 1 < 2 ^ 8 := by omega
            have h2 := congrArg UInt8.toNat heq
            rw [UInt8.toNat_add, show (1 : UInt8).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt256] at h2
            omega
          have hAV12 : (VALUE (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
              ).toNat ≤ 12 := by
            have hb1 := SUIT_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
            have hb2 := VALUE_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
            have hb3 := congrArg UInt8.toNat hSacesEqK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hlt := hacesNat_lt_prevNat
            have heqp := hprevNat
            omega
          have hrealA : IsRealCard ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
              ) + 1) := by
            have hVsucc := VALUE_succ (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
              (by omega)
            refine ⟨?_, by omega, by omega⟩
            rw [SUIT_succ _ (by omega), hSacesEqK]; exact hsK
          exact Or.inr (Or.inl (kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K
            hKdef _ hrealA hne hnfreeA))
        · -- busy bit already set for this suit before the move; `kingMove`
          -- never touches `busyAces`, so it stays set in the output.
          rw [hbeq]
          exact Or.inr (Or.inr hbusy)
    · -- (9) king_frontier
      constructor
      · rw [hnewkings8, haeq, hbeq]
        rcases hkey with haceq | ⟨hacest, hCrealPrev, hnfreeprev⟩
        · left
          exact ⟨haceq.symm, Or.inr (hSKeqSval ▸ hbusyEq haceq)⟩
        · right
          refine ⟨hacest, ?_⟩
          have hprevNeK : (K - p.pileFlute[pile.toNat]'hpile) ≠ K := by
            intro heq
            rw [heq] at hprevLtK
            have := UInt8.lt_iff_toInt_lt.mp hprevLtK
            omega
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef _
            hCrealPrev hprevNeK hnfreeprev
      · intro c hSc hgt hle
        rw [hnewkings8] at hgt
        by_cases hcK : c = K
        · subst hcK
          have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat - 1, hidxpf⟩
          rw [hKeqBoundary] at hrt
          have hc64K : c.toNat < 64 := by
            have h1 := hKreal.1
            have hsn := SUIT_toNat c
            omega
          have hp64K : (cardPile g c).toNat < 10 := by rw [hrt.1]; exact hpile
          show isFreeCard g (kingMove pile hpile suit hs4 ph p) c
          apply isFree_of_cardDepth_ge g _ hwf c hc64K hp64K
          have hpdK : (kingMove pile hpile suit hs4 ph p).pileDepth[(cardPile g c).toNat]'hp64K
              = 0 := by
            have hstep : (kingMove pile hpile suit hs4 ph p
                ).pileDepth[(cardPile g c).toNat]'hp64K =
                (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile := by
              congr 1; exact hrt.1
            rw [hstep]
            exact kingMove_pileDepth_self pile hpile suit hs4 ph p
          rw [hpdK]
          have hcdK0 : (cardDepth g c).toNat = 0 := by rw [hrt.2]; exact hboundIdx
          have hz0 : (0 : UInt8).toNat = 0 := by decide
          omega
        · have hScK : SUIT c = SUIT K := hSc.trans hSKeqSval.symm
          have hle' : (VALUE c).toNat ≤ 13 := hle
          have hcLeK : c.toNat ≤ K.toNat := by
            have hb1 := SUIT_toNat c; have hb2 := VALUE_toNat c
            have hb3 := congrArg UInt8.toNat hScK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hVK13' := hVK13
            omega
          have hcLtK : c.toNat < K.toNat := lt_of_le_of_ne hcLeK (fun heq => hcK (UInt8.toNat_inj.mp heq))
          have hoffsetPos : 0 < K.toNat - c.toNat := by omega
          have hgt' : (VALUE c).toNat > (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat := hgt
          have hoffsetLtFlute : K.toNat - c.toNat < (p.pileFlute[pile.toNat]'hpile).toNat := by
            have hb1 := SUIT_toNat c
            have hb2 := VALUE_toNat c
            have hb3 := congrArg UInt8.toNat hScK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hVK13' := hVK13
            have hVpr := hVprev
            omega
          have hoff8 : (UInt8.ofNat (K.toNat - c.toNat)).toNat = K.toNat - c.toNat := by
            rw [UInt8.toNat_ofNat']; omega
          have hCeqKMinusOffset : c = K - UInt8.ofNat (K.toNat - c.toNat) := by
            apply UInt8.toNat_inj.mp
            rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hoff8]; omega), hoff8]
            omega
          have hfree_old : isFreeCard g p c := by
            rw [hCeqKMinusOffset]
            have h := hc.flute_cards_free (UInt8.ofNat (K.toNat - c.toNat)) hdpilepos
              (by rw [hoff8]; omega) (by rw [hoff8]; omega)
            rwa [hKeqBoundary] at h
          exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p) hfree_old
  · -- **Other suits.**
    have hsne : s.val ≠ suit.toUInt32.toNat := by rw [hsuiteq]; exact hsame
    have hkingsEq := kingMove_kings_eq_of_ne pile hpile suit hs4 ph p s hsne
    have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
    have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [haeq, hkingsEq]; exact hsc.aces_kings_valid
    · intro c h1 h2 h3
      rw [haeq] at h3
      exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
        (hsc.foundation_cards_free c h1 h2 h3)
    · rw [haeq]
      by_cases hAV13 : (VALUE (p.aces.get s)).toNat = 13
      · exact Or.inl hAV13
      · have hAV12 : (VALUE (p.aces.get s)).toNat ≤ 12 := by
          have := hsc.aces_kings_valid.2.1
          omega
        rcases hsc.foundation_maximal_weak with h13 | hnfreeA | hbusy
        · exact absurd h13 hAV13
        · have hVsucc := VALUE_succ (p.aces.get s) (by omega)
          have hrealA : IsRealCard ((p.aces.get s) + 1) := by
            refine ⟨?_, ?_, ?_⟩
            · rw [SUIT_succ _ (by omega), hsc.aces_kings_valid.1]
              show (s.val.toUInt8).toNat < 4
              rw [UInt8.toNat_ofNat']
              have := s.isLt
              omega
            · rw [hVsucc]; omega
            · rw [hVsucc]; omega
          have hne : (p.aces.get s) + 1 ≠ K := by
            intro heq
            apply hsame
            have hSA := SUIT_succ (p.aces.get s) (by omega)
            rw [heq] at hSA
            have hSKeqSval2 : SUIT K = s.val.toUInt8 := hSA.trans hsc.aces_kings_valid.1
            have hb1 := congrArg UInt8.toNat hSKeqSval2
            have hb2 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
            omega
          exact Or.inr (Or.inl (kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K
            hKdef _ hrealA hne hnfreeA))
        · -- busy bit already set for this suit before the move; `kingMove`
          -- never touches `busyAces`, so it stays set in the output.
          rw [hbeq]
          exact Or.inr (Or.inr hbusy)
    · constructor
      · rcases hsc.king_frontier.1 with ⟨hkeqA, hcase⟩ | ⟨hv1, hnfree⟩
        · left
          rw [hkingsEq, haeq, hbeq]
          exact ⟨hkeqA, hcase⟩
        · right
          rw [hkingsEq, haeq]
          refine ⟨hv1, ?_⟩
          have hne : (p.kings.get s) ≠ K := by
            intro heq
            apply hsame
            have hSKeq : SUIT (p.kings.get s) = SUIT K := by rw [heq]
            have hSKeqSval2 := hsc.aces_kings_valid.2.2.1
            have hb1 := congrArg UInt8.toNat (hSKeqSval2.symm.trans hSKeq)
            have hb2 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
            omega
          have hrealK : IsRealCard (p.kings.get s) := by
            have hSAs : SUIT (p.aces.get s) = s.val.toUInt8 := hsc.aces_kings_valid.1
            have hSs : SUIT (p.kings.get s) = s.val.toUInt8 :=
              hsc.aces_kings_valid.2.2.1
            have hAKlt : (p.aces.get s).toNat < (p.kings.get s).toNat :=
              UInt8.lt_iff_toNat_lt.mp hv1
            have hb1 := VALUE_toNat (p.aces.get s)
            have hb2 := SUIT_toNat (p.aces.get s)
            have hb3 := congrArg UInt8.toNat hSAs
            have hb4 := VALUE_toNat (p.kings.get s)
            have hb5 := SUIT_toNat (p.kings.get s)
            have hb6 := congrArg UInt8.toNat hSs
            have hb7 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hsval := s.isLt
            have hVKge1 : 1 ≤ (VALUE (p.kings.get s)).toNat := by omega
            have hs4' : (SUIT (p.kings.get s)).toNat < 4 := by omega
            exact ⟨hs4', hVKge1, hsc.aces_kings_valid.2.2.2.1⟩
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef _
            hrealK hne hnfree
      · intro c hSc hgt hle
        rw [hkingsEq] at hgt
        exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
          (hsc.king_frontier.2 c hSc hgt hle)

end SolverSpec
