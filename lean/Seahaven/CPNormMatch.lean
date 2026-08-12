import Seahaven.DepthUnique

/-!
# CP-normalizing after the critical move

Step 3 of the completeness argument.  The state the play reaches after the critical
move need not be CP-normal — cards the solver has already merged back onto their piles
may still be sitting in cells.  `exists_cpNormalForm` (`CPNormal`) exhausts those
drops; this file records that doing so changes nothing the matching cares about:

* the **depth vector** is preserved — a `CPStep` is a drop, and `DepthMatchesV.drop`
  already knows drops never break a depth match;
* the **foundations** are untouched (the drop lands on a column, and the take is from a
  cell), so `aces_match` survives;
* the **card count** is preserved by any move;
* **solvability** is preserved in *both* directions (`CPReach.solvable_iff`), because a
  cell→pile drop is immediately revertible.

Together with `matches_of_depth_match` that is step 4: the CP-normal form matches any
merged position whose depth vector and foundations it agrees with — and by
`canonical_eq_of_matches` that position is unique, hence *is* the solver's child.
-/

/-! ## What a `CPStep` preserves -/

theorem CPStep.foundations {u v : State} (h : CPStep u v) : v.foundations = u.foundations := by
  obtain ⟨i, q, -, hap⟩ := h
  exact foundations_of_nonFoundation_move hap (by simp)

theorem CPStep.cards_count {u v : State} (h : CPStep u v)
    (hc : ∀ c : Card, countState u c = 1) : ∀ c : Card, countState v c = 1 := by
  obtain ⟨i, q, -, hap⟩ := h
  intro c
  rw [← congrFun (movePreservesCards u _ v hap) c]
  exact hc c

theorem CPStep.depthMatchesV {g : Globals} {u v : State} {d : Fin 10 → Fin 6}
    (h : CPStep u v) (hu : DepthMatchesV g u d) : DepthMatchesV g v d := by
  obtain ⟨i, q, -, hap⟩ := h
  rw [applyMove_eq] at hap
  obtain ⟨c, s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨-, rfl⟩ := htake
  exact DepthMatchesV.drop (fun j => by simpa using hu j) hdrop

/-! ## …and therefore what `CPReach` preserves -/

theorem CPReach.foundations {u v : State} (h : CPReach u v) : v.foundations = u.foundations := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [hbc.foundations, ih]

theorem CPReach.cards_count {u v : State} (h : CPReach u v)
    (hc : ∀ c : Card, countState u c = 1) : ∀ c : Card, countState v c = 1 := by
  induction h with
  | refl => exact hc
  | tail _ hbc ih => exact hbc.cards_count ih

theorem CPReach.depthMatchesV {g : Globals} {u v : State} {d : Fin 10 → Fin 6}
    (h : CPReach u v) (hu : DepthMatchesV g u d) : DepthMatchesV g v d := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hbc.depthMatchesV ih

/-! ## Step 3, packaged -/

/-- **The CP-normal form keeps everything the matching reads.**  Depth vector, card
count and foundations are unchanged, no cell card can be dropped any more, and
solvability is unchanged in both directions. -/
theorem exists_cpNormalForm_match {g : Globals} {u : State} {d : Fin 10 → Fin 6}
    (hdm : DepthMatchesV g u d) (hcount : ∀ c : Card, countState u c = 1) :
    ∃ t : State, CPReach u t ∧ (∀ w, ¬ CPStep t w) ∧
      DepthMatchesV g t d ∧ (∀ c : Card, countState t c = 1) ∧
      t.foundations = u.foundations ∧ (Solvable u ↔ Solvable t) := by
  obtain ⟨t, hreach, hnorm⟩ := exists_cpNormalForm u
  exact ⟨t, hreach, hnorm, hreach.depthMatchesV hdm, hreach.cards_count hcount,
    hreach.foundations, hreach.solvable_iff⟩

/-! ## Step 4: the CP-normal form matches the merged position with those depths

`matches_of_depth_match` needs exactly what step 3 delivers.  Uniqueness
(`canonical_eq_of_matches`) then says the position is *the* canonical one, so it is the
child the solver computed — no reasoning about the merge loop is required. -/

/-- **The bridge into step 4.**  A CP-normal state matching a merged position's depths
and foundations matches the position outright. -/
theorem matches_of_cpNormal {g : Globals} {t : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (hdm : DepthMatchesV g t (depthVec p (fun i => by have := hb.pileDepth_bound i; omega)))
    (hcount : ∀ c : Card, countState t c = 1) (hcp : ∀ w, ¬ CPStep t w)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (t.foundations su)) :
    StateMatchesSolverPos g t p :=
  matches_of_depth_match hwf hb hpm _ hdm hcount hcp haces

/-- **Step 3 and step 4 in one go.**  From a state whose depth vector and foundations
are those of a merged position `p`, the play reaches — by cell→pile drops only, so
solvability is untouched in both directions — a state that matches `p` outright. -/
theorem exists_match_of_depthMatch {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (hdm : DepthMatchesV g u (depthVec p (fun i => by have := hb.pileDepth_bound i; omega)))
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    ∃ t : State, CPReach u t ∧ StateMatchesSolverPos g t p ∧ (Solvable u ↔ Solvable t) := by
  obtain ⟨t, hreach, hnorm, hdm', hcount', hfnd, hsolv⟩ :=
    exists_cpNormalForm_match hdm hcount
  refine ⟨t, hreach, matches_of_cpNormal hwf hb hpm hdm' hcount' hnorm ?_, hsolv⟩
  intro su
  rw [hfnd]
  exact haces su
