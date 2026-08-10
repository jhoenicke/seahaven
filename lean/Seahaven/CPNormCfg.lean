import Seahaven.CPNormMatch
import Seahaven.EmptyPileCfg

/-!
# CP-normalizing keeps the king configuration

Step 3 of the completeness argument, finished.  Fix the successor position `q` —
the game after `SolverMove` and `SolverCleanupPile`, *before* the `SolverMoveAces`
drain — and the state `v` the play reaches by making the critical move.  The
middle layer already matches (`DepthPlusKingsCfg g v q k_t`); what is wanted is a
state matching `q` **outright**, at the same configuration.

`exists_match_of_depthMatch` (`CPNormMatch`) supplies the depth half: exhaust the
cell→pile drops and `matches_of_depth_match` upgrades `flute_le`/`king_le` to
equalities, because at a CP-normal state every flute is as long as the position
says.  This file supplies the configuration half, and it is sharper than
"preserved":

> **A `CPStep` changes no column's `getLast?`, and no column's emptiness.**

The definition of `CPStep` demands a *non-empty* destination column
(`Normalize.lean`), so a drop can neither empty a column nor fill an empty one —
the two events that move a king run on or off a pile.  Every clause the
configuration is made of (`OwnsPile`, `NoKingPile`, `PiledSuit`) reads only those
two things, so all of them are literally invariant, in both directions.

Consequently `k_t` needs no adjustment: the CP-normal successor matches `q` at
`k_t` itself, no `forcedKings` correction enters here, and nothing has to be
re-chosen.  (A king moving from the cells onto an *empty* column is a legal move,
but it is not a `CPStep`; that is the solver's `kingMove`, and it is accounted for
by `SolverCleanupPile`'s `forcedKings` — i.e. it has already happened by the time
`q` is fixed.)

The foundations need no argument either: the critical move is not a foundation
move, and neither `SolverMove` nor `SolverCleanupPile` touches `aces`, so
`aces_match` travels from the critical state to `v` and on to its CP-normal form
(`CPReach.foundations`).
-/

/-! ## What a `CPStep` does to the columns

Both facts come out of the same computation: the move is `cell i → pile r` with
`u.tableau r ≠ []`, so `v.tableau = update u.tableau r (card :: u.tableau r)`. -/

theorem CPStep.tableau_eq {u v : State} (h : CPStep u v) :
    ∃ (r : Fin 10) (card : Card), u.tableau r ≠ [] ∧
      v.tableau = update u.tableau r (card :: u.tableau r) := by
  obtain ⟨i, r, hne, hap⟩ := h
  rw [applyMove_eq] at hap
  obtain ⟨card, s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨-, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨-, rfl⟩ := hdrop
  exact ⟨r, card, hne, rfl⟩

/-- **A cp move changes no column's deepest card.**  The destination column was
already non-empty, so the card lands *above* its last card. -/
theorem CPStep.getLast?_eq {u v : State} (h : CPStep u v) (i : Fin 10) :
    (v.tableau i).getLast? = (u.tableau i).getLast? := by
  obtain ⟨r, card, hne, hteq⟩ := h.tableau_eq
  rw [hteq]
  by_cases hir : r = i
  · subst hir
    rw [update_same]
    exact getLast?_cons_of_ne_nil hne
  · rw [update_diff _ _ _ _ hir]

/-- **A cp move empties no column and fills no empty one.** -/
theorem CPStep.nil_iff {u v : State} (h : CPStep u v) (i : Fin 10) :
    v.tableau i = [] ↔ u.tableau i = [] := by
  obtain ⟨r, card, hne, hteq⟩ := h.tableau_eq
  rw [hteq]
  by_cases hir : r = i
  · subst hir
    rw [update_same]
    simp [hne]
  · rw [update_diff _ _ _ _ hir]

/-! ## …and therefore to the configuration

`OwnsPile`, `NoKingPile` and `PiledSuit` mention the state only through
`getLast?` and `= []`, so each of them is an `↔` along a `CPReach`. -/

theorem CPReach.getLast?_eq {u v : State} (h : CPReach u v) (i : Fin 10) :
    (v.tableau i).getLast? = (u.tableau i).getLast? := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [hbc.getLast?_eq, ih]

theorem CPReach.nil_iff {u v : State} (h : CPReach u v) (i : Fin 10) :
    v.tableau i = [] ↔ u.tableau i = [] := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact (hbc.nil_iff i).trans ih

theorem CPReach.ownsPile_iff {u v : State} (h : CPReach u v) (p : SolverPosType)
    (su : Suit) (i : Fin 10) : OwnsPile v p su i ↔ OwnsPile u p su i := by
  unfold OwnsPile
  rw [h.getLast?_eq i, h.nil_iff i]

theorem CPReach.realizes {u v : State} {p : SolverPosType} {k : Fin 16}
    (h : CPReach u v) (hr : RealizesKingConfig u p k) : RealizesKingConfig v p k := by
  obtain ⟨assign, hown, hinj, hiff⟩ := hr
  exact ⟨assign, fun su i ha => (h.ownsPile_iff p su i).2 (hown su i ha), hinj, hiff⟩

theorem CPReach.noKingPile {u v : State} {p : SolverPosType} {su : Suit}
    (h : CPReach u v) (hn : NoKingPile u p su) : NoKingPile v p su := by
  intro i hd0 d hd
  exact hn i hd0 d (by rwa [← h.getLast?_eq i])

theorem CPReach.piledSuit_iff {u v : State} (h : CPReach u v) (p : SolverPosType)
    (su : Suit) : PiledSuit v p su ↔ PiledSuit u p su := by
  unfold PiledSuit
  simp only [h.getLast?_eq]

/-- **The configuration is literally unchanged.** -/
theorem CPReach.cfgOf_eq {u v : State} (h : CPReach u v) (p : SolverPosType) :
    cfgOf v p = cfgOf u p :=
  cfgOf_congr (fun su => h.piledSuit_iff p su)

/-! ## Step 3, with the configuration carried

The two halves, joined.  Nothing here knows that `v` came from a critical move —
only that it matches the successor position's depths and foundations. -/

/-- **The CP-normal form matches the successor position at the same
configuration.**  The depth half is `exists_match_of_depthMatch`; the
configuration half is the invariance above. -/
theorem exists_matchCfg_of_depthMatch {g : Globals} {v : State} {q : SolverPosType}
    {k : Fin 16} (hwf : WellFormedLayout g) (hb : SolverInvBase g q)
    (hpm : ∀ i : Fin 10, PileMerged g q i (hb.pileDepth_bound i))
    (hdm : DepthMatchesV g v (depthVec q (fun i => by have := hb.pileDepth_bound i; omega)))
    (hcount : ∀ c : Card, countState v c = 1)
    (haces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (v.foundations su))
    (hreal : RealizesKingConfig v q k)
    (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile v q su) :
    ∃ u : State, CPReach v u ∧ StateMatchesKingConfig g u q k ∧ (Solvable v ↔ Solvable u) := by
  obtain ⟨u, hreach, hmatch, hsolv⟩ :=
    exists_match_of_depthMatch hwf hb hpm hdm hcount haces
  exact ⟨u, hreach,
    { toMatches := hmatch
      realizes := hreach.realizes hreal
      no_pile := fun su hbit => hreach.noKingPile (hnp su hbit) }, hsolv⟩

/-- **The interface the completeness step uses.**  The critical move lands in a
state that matches the successor position at the middle layer and stands for
`k_t`; exhausting the cell→pile drops turns that into a full match — at `k_t`
itself — without changing solvability either way.

`q` is the game after `SolverMove` and `SolverCleanupPile` and before the
`SolverMoveAces` drain, which is exactly the position whose piles are merged. -/
theorem DepthPlusKingsCfg.exists_cpNormal_match {g : Globals} {v : State}
    {q : SolverPosType} {k : Fin 16} (hwf : WellFormedLayout g) (hb : SolverInvBase g q)
    (hpm : ∀ i : Fin 10, PileMerged g q i (hb.pileDepth_bound i))
    (h : DepthPlusKingsCfg g v q k) :
    ∃ u : State, CPReach v u ∧ StateMatchesKingConfig g u q k ∧ (Solvable v ↔ Solvable u) :=
  exists_matchCfg_of_depthMatch hwf hb hpm h.toDepthPlusKings.depth_match
    h.toDepthPlusKings.cards_count h.toDepthPlusKings.aces_match h.realizes h.no_pile

/-- The same, with the state the play actually reaches named: `Solvable v` is what
the play supplies, and `Solvable u` is what the induction hypothesis at `q`
consumes. -/
theorem DepthPlusKingsCfg.exists_cpNormal_solvable {g : Globals} {v : State}
    {q : SolverPosType} {k : Fin 16} (hwf : WellFormedLayout g) (hb : SolverInvBase g q)
    (hpm : ∀ i : Fin 10, PileMerged g q i (hb.pileDepth_bound i))
    (h : DepthPlusKingsCfg g v q k) (hsolv : Solvable v) :
    ∃ u : State, StateMatchesKingConfig g u q k ∧ Solvable u := by
  obtain ⟨u, -, hmatch, hiff⟩ := h.exists_cpNormal_match hwf hb hpm
  exact ⟨u, hmatch, hiff.1 hsolv⟩
