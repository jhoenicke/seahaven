import Seahaven.CPNormMatch

/-!
# The drain's moves are normalizing moves

Step 5 needs no new construction.  Foundation moves and cell→pile moves are
*solvability-neutral in both directions* — forward by `FMStep.preserves_Solvable` (the
limited-confluence development) and `CPStep.preserves_Solvable`, backward because they
are legal moves — and `Solvable.iff_normReach` packages exactly that.  So the move
sequence the soundness-side simulation already produces can be reused verbatim; the
only thing to check is that every move in it is a foundation move or a cell→pile move,
i.e. that its `Reach` is a `NormReach`.

The two ingredients the drain is built from both convert:

* `PlaysAll` — the foundation run (`SolverMoveAces`' plays) is an `FMReach`;
* `CPReach` — cleanup's freed-predecessor drops are cell→pile moves.

What is *not* here is the re-exposure itself: `Simulates` records `reach : Reach s s'`
(`SoundnessSkeleton`), so the phases have to be restated with `NormReach` before this
bridge can be applied to a whole simulated move.  Everything below is what that
re-exposure will consume.
-/

/-- A foundation run is a normalizing run. -/
theorem PlaysAll.toNormReach {s t : State} {cs : List Card} (h : PlaysAll s cs t) :
    NormReach s t :=
  h.toFMReach.mono (fun _ _ x => Or.inl x)

/-- A cell→pile run is a normalizing run. -/
theorem CPReach.toNormReach {s t : State} (h : CPReach s t) : NormReach s t :=
  h.mono (fun _ _ x => Or.inr x)

/-- **Normalizing runs are solvability-neutral in both directions.**  `Solvable.iff_normReach`,
with the `NoDupState` side condition read off the card count. -/
theorem normReach_solvable_iff {s t : State} (hcount : ∀ c : Card, countState s c = 1)
    (h : NormReach s t) : Solvable s ↔ Solvable t :=
  Solvable.iff_normReach (fun c => le_of_eq (hcount c)) h

/-- **The drain, as step 5 will use it.**  A foundation run followed by a cell→pile run
— the shape `SolverMoveAces` produces, per suit — leaves solvability unchanged. -/
theorem drain_solvable_iff {s t u : State} {cs : List Card}
    (hcount : ∀ c : Card, countState s c = 1)
    (hplays : PlaysAll s cs t) (hcp : CPReach t u) : Solvable s ↔ Solvable u :=
  normReach_solvable_iff hcount (hplays.toNormReach.trans hcp.toNormReach)

/-- The same for a run assembled the other way round (drops first, then plays). -/
theorem drain_solvable_iff' {s t u : State} {cs : List Card}
    (hcount : ∀ c : Card, countState s c = 1)
    (hcp : CPReach s t) (hplays : PlaysAll t cs u) : Solvable s ↔ Solvable u :=
  normReach_solvable_iff hcount (hcp.toNormReach.trans hplays.toNormReach)
