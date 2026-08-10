import Seahaven.CPNormal

/-!
# Normalizing every pile but one

The completeness step needs a state matching `SolverSpec.movePre` — the position the
core flute move lands at, *before* `SolverCleanupPile` runs.  The play's own
post-critical-move state `t₁` is short of that only in having flute cards parked in
cells, so the match is reached by dropping them back.  But the drops must **skip the
source pile**:

* every other pile is `PileMerged` at `movePre` (`CleanupReady`, from
  `moveDest_cleanupReady`), so its flute is maximal there and no cp drop can push it
  past `pileDepth + pileFlute - 1`;
* the source pile is *exact* already (`|column| = pileDepth`, `pileFlute = 1`), and a cp
  drop onto it is precisely the cleanup's freed-predecessor extension — which belongs to
  `SolverCleanupPile`, not to `movePre`.

So the right normal form exhausts cp moves onto every pile except one.  The measure
argument is unchanged: restricting the step relation only shrinks it, so
`CPStep.measure_lt` still applies.
-/

/-- A cell→pile drop that avoids pile `a`. -/
def CPStepExcept (a : Fin 10) (s t : State) : Prop :=
  ∃ (i : Fin 4) (q : Fin 10), q ≠ a ∧ s.tableau q ≠ [] ∧
    applyMove s ⟨Position.cell i, Position.pile q⟩ = some t

theorem CPStepExcept.toCPStep {a : Fin 10} {s t : State} (h : CPStepExcept a s t) :
    CPStep s t := by
  obtain ⟨i, q, -, hne, hap⟩ := h
  exact ⟨i, q, hne, hap⟩

/-- Reachability by cp moves that avoid pile `a`. -/
abbrev CPReachExcept (a : Fin 10) : State → State → Prop :=
  Relation.ReflTransGen (CPStepExcept a)

theorem CPReachExcept.toCPReach {a : Fin 10} {s t : State} (h : CPReachExcept a s t) :
    CPReach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.toCPStep

/-- **The restricted normal form exists.**  Same measure as `exists_cpNormalForm`; the
conclusion is weaker (moves onto `a` may remain available) and the reach is
correspondingly restricted. -/
theorem exists_cpNormalForm_except (a : Fin 10) (s : State) :
    ∃ t, CPReachExcept a s t ∧ ∀ u, ¬ CPStepExcept a t u := by
  suffices H : ∀ n s, normMeasure s ≤ n →
      ∃ t, CPReachExcept a s t ∧ ∀ u, ¬ CPStepExcept a t u from
    H (normMeasure s) s le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs
    refine ⟨s, Relation.ReflTransGen.refl, fun t hst => ?_⟩
    have := hst.toCPStep.measure_lt
    omega
  | succ n ih =>
    intro s hs
    by_cases hn : ∀ t, ¬ CPStepExcept a s t
    · exact ⟨s, Relation.ReflTransGen.refl, hn⟩
    · obtain ⟨t, hst⟩ : ∃ t, CPStepExcept a s t := by
        by_contra hcon
        exact hn (fun t hst => hcon ⟨t, hst⟩)
      have hlt := hst.toCPStep.measure_lt
      obtain ⟨u, hru, hnu⟩ := ih t (by omega)
      exact ⟨u, Relation.ReflTransGen.head hst hru, hnu⟩

/-- The restricted run is still solvability-neutral in both directions. -/
theorem CPReachExcept.solvable_iff {a : Fin 10} {s t : State} (h : CPReachExcept a s t) :
    Solvable s ↔ Solvable t := h.toCPReach.solvable_iff

/-- **What the restricted normal form says pile by pile.**  For every pile but `a`, no
cell card can be dropped on it — which is the per-pile hypothesis
`no_free_succ_exposed` actually consumes. -/
theorem CPStepExcept.no_drop {a : Fin 10} {t : State} (h : ∀ u, ¬ CPStepExcept a t u)
    {q : Fin 10} (hq : q ≠ a) (hne : t.tableau q ≠ []) (i : Fin 4) (u : State) :
    applyMove t ⟨Position.cell i, Position.pile q⟩ ≠ some u :=
  fun hap => h u ⟨i, q, hq, hne, hap⟩

/-! ## The skipped pile is untouched

Everything the restricted run does happens on other columns, so the source pile's
column is literally unchanged — which is what makes its `flute_match` exact at
`movePre` rather than something to be re-derived. -/

theorem CPStepExcept.tableau_eq {a : Fin 10} {s t : State} (h : CPStepExcept a s t) :
    t.tableau a = s.tableau a := by
  obtain ⟨i, q, hqa, -, hap⟩ := h
  rw [applyMove_eq] at hap
  obtain ⟨c, s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨-, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨-, rfl⟩ := hdrop
  simp only [updateColumn_tableau, updateCell_tableau]
  exact update_diff _ _ _ _ hqa

theorem CPReachExcept.tableau_eq {a : Fin 10} {s t : State} (h : CPReachExcept a s t) :
    t.tableau a = s.tableau a := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [hbc.tableau_eq, ih]
