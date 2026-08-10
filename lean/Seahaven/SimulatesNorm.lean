import Seahaven.NormReachBridge

/-!
# `SimulatesNorm`: a simulated phase whose moves are all normalizing

`Simulates` records `reach : Reach s s'` — an arbitrary legal play.  Phases 2 and 3 of
a simulated move (cleanup's freed-predecessor drops and the `SolverMoveAces` drain) use
only *normalizing* moves: foundation plays and cell→pile drops.  `SimulatesNorm` is the
same bundle with that stronger reach, and its point is one line:

> **the entry and exit states are equi-solvable** (`SimulatesNorm.solvable_iff`).

Soundness needed only `Solvable s' → Solvable s`, which any `Reach` gives.  Completeness
needs the forward direction, and *that* is what the normalizing restriction buys — via
`FMStep.preserves_Solvable`'s confluence argument and `CPStep`'s revertibility, packaged
as `Solvable.iff_normReach`.

Note phase 1 — the flute move itself — is **not** normalizing (it moves cards between
piles and cells), so it keeps a plain `Simulates`; `Simulates.transNorm` is the join.

No `NoDupState` hypothesis is needed: card counts are preserved by moves in both
directions (`Reach.countState_eq`), so the count `cfg` provides at `s'` transports back
to `s`.
-/

/-! ## Card counts along a reach -/

/-- Moves neither create nor destroy cards, so the count is a reach invariant — in
particular `NoDupState` transports *backwards* along a reach. -/
theorem Reach.countState_eq {s t : State} (h : Reach s t) :
    ∀ c : Card, countState s c = countState t c := by
  induction h with
  | refl => exact fun _ => rfl
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := hbc
    exact fun c => (ih c).trans (congrFun (movePreservesCards _ m _ hm) c)

theorem Reach.noDup_of_end {s t : State} (h : Reach s t) (hnd : NoDupState t) :
    NoDupState s := fun c => (h.countState_eq c) ▸ hnd c

/-! ## The bundle -/

/-- **A simulated phase built only from normalizing moves.**  Same fields as
`Simulates`, with `reach` strengthened. -/
structure SimulatesNorm (g : Globals) (s : State) (p : SolverPosType) (k : Fin 16)
    (s' : State) (p' : SolverPosType) (k' : Fin 16)
    (FK : Finset Suit) (fk : UInt16) : Prop where
  reach : NormReach s s'
  cfg : StateMatchesKingConfig g s' p' k'
  vacates : KingVacates FK fk
  bound : ∀ su : Suit, ¬ CfgBitSet k' su → ¬ CfgBitSet k su ∨ su ∈ FK

/-- Forgetting the restriction gives an ordinary simulation. -/
theorem SimulatesNorm.toSimulates {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k k' : Fin 16} {FK : Finset Suit} {fk : UInt16}
    (h : SimulatesNorm g s p k s' p' k' FK fk) : Simulates g s p k s' p' k' FK fk where
  reach := h.reach.toReach
  cfg := h.cfg
  vacates := h.vacates
  bound := h.bound

/-- **The point of the bundle**: the entry state is solvable exactly when the exit state
is.  Soundness used only `←`; completeness needs `→`. -/
theorem SimulatesNorm.solvable_iff {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k k' : Fin 16} {FK : Finset Suit} {fk : UInt16}
    (h : SimulatesNorm g s p k s' p' k' FK fk) : Solvable s ↔ Solvable s' :=
  Solvable.iff_normReach
    (h.reach.toReach.noDup_of_end (fun c => le_of_eq (h.cfg.toMatches.cards_count c))) h.reach

/-! ## Building and composing -/

theorem SimulatesNorm.refl {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (h : StateMatchesKingConfig g s p k) : SimulatesNorm g s p k s p k ∅ 0xffff where
  reach := Relation.ReflTransGen.refl
  cfg := h
  vacates := KingVacates.empty
  bound := fun _ hk => Or.inl hk

/-- A configuration-preserving normalizing phase — the shape cleanup's drops and the
drain both have. -/
theorem SimulatesNorm.ofNormReach {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k : Fin 16} (hr : NormReach s s') (h : StateMatchesKingConfig g s' p' k) :
    SimulatesNorm g s p k s' p' k ∅ 0xffff where
  reach := hr
  cfg := h
  vacates := KingVacates.empty
  bound := fun _ hk => Or.inl hk

/-- A foundation run, as a phase (`SolverMoveAces`' plays). -/
theorem SimulatesNorm.ofPlaysAll {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k : Fin 16} {cs : List Card} (hr : PlaysAll s cs s')
    (h : StateMatchesKingConfig g s' p' k) : SimulatesNorm g s p k s' p' k ∅ 0xffff :=
  SimulatesNorm.ofNormReach hr.toNormReach h

/-- A cell→pile run, as a phase (cleanup's freed-predecessor drops). -/
theorem SimulatesNorm.ofCPReach {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k : Fin 16} (hr : CPReach s s') (h : StateMatchesKingConfig g s' p' k) :
    SimulatesNorm g s p k s' p' k ∅ 0xffff :=
  SimulatesNorm.ofNormReach hr.toNormReach h

/-- Normalizing phases compose, discarding the second mask — the `Simulates.extend`
shape, which is what the drain's free joins use. -/
theorem SimulatesNorm.extend {g : Globals} {s w v : State} {p q r : SolverPosType}
    {k kk : Fin 16} {FK FK' : Finset Suit} {fk fk' : UInt16}
    (h : SimulatesNorm g s p k w q kk FK fk) (h' : SimulatesNorm g w q kk v r kk FK' fk') :
    SimulatesNorm g s p k v r kk FK fk where
  reach := h.reach.trans h'.reach
  cfg := h'.cfg
  vacates := h.vacates
  bound := h.bound

/-- **The join with phase 1.**  The flute move is not normalizing, so it stays a plain
`Simulates`; appending a normalizing tail keeps the ordinary bundle, and the tail's own
`solvable_iff` remains available separately. -/
theorem Simulates.transNorm {g : Globals} {s w v : State} {p q r : SolverPosType}
    {k kk : Fin 16} {FK FK' : Finset Suit} {fk fk' : UInt16}
    (h : Simulates g s p k w q kk FK fk) (h' : SimulatesNorm g w q kk v r kk FK' fk') :
    Simulates g s p k v r kk FK fk where
  reach := h.reach.trans h'.reach.toReach
  cfg := h'.cfg
  vacates := h.vacates
  bound := h.bound

/-! ## The cleanup's unpark run is a `CPReach`

`StateMatchesSolverPos.cleanupExtend` (`CleanupSim`) exports not just a `Reach` but the
explicit move list `unparkMoves a cells` that realizes it.  Every move on that list is
`⟨cell i, pile a⟩`, and column `a` only ever *grows* along the run, so each step is a
`CPStep` — the run is a `CPReach`, hence solvability-neutral in both directions.

This is what lets the re-exposure be done from outside: the existing statements need
only have their `Reach` replaced by `CPReach`, with the witness read off the move list
already in their conclusions. -/

/-- A cell→pile drop never empties a column: the take is from a cell and the drop only
pushes a card on top. -/
theorem CPStep.column_ne_nil {u v : State} (h : CPStep u v) {a : Fin 10}
    (hne : u.tableau a ≠ []) : v.tableau a ≠ [] := by
  obtain ⟨i, q, -, hap⟩ := h
  rw [applyMove_eq] at hap
  obtain ⟨c, s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨-, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨-, rfl⟩ := hdrop
  by_cases hqa : q = a
  · subst hqa
    simp [updateColumn_tableau, update]
  · simpa only [updateColumn_tableau, update, if_neg hqa, updateCell_tableau] using hne

theorem CPReach.column_ne_nil {u v : State} (h : CPReach u v) {a : Fin 10}
    (hne : u.tableau a ≠ []) : v.tableau a ≠ [] := by
  induction h with
  | refl => exact hne
  | tail _ hbc ih => exact hbc.column_ne_nil ih

/-- Every move of an unpark run is a cell→pile drop onto a column that stays non-empty,
so the run is a `CPReach`. -/
theorem cpReach_of_unparkMoves {a : Fin 10} :
    ∀ (cells : List (Fin 4)) {s v : State}, s.tableau a ≠ [] →
      List.foldl applyMoveOpt (some s) (unparkMoves a cells) = some v → CPReach s v := by
  intro cells
  induction cells with
  | nil =>
    intro s v _ h
    simp only [unparkMoves, List.foldl_nil, Option.some.injEq] at h
    subst h
    exact Relation.ReflTransGen.refl
  | cons i is ih =>
    intro s v hne h
    rw [unparkMoves, List.foldl_append] at h
    -- the prefix runs the rest of the list …
    cases hmid : List.foldl applyMoveOpt (some s) (unparkMoves a is) with
    | none => rw [hmid] at h; simp [applyMoveOpt] at h
    | some w =>
      rw [hmid] at h
      have hprefix : CPReach s w := ih hne hmid
      -- … and column `a` is still non-empty there (drops only add cards)
      have hwne : w.tableau a ≠ [] := hprefix.column_ne_nil hne
      simp only [List.foldl_cons, List.foldl_nil, applyMoveOpt] at h
      exact hprefix.tail ⟨i, a, hwne, h⟩

/-- **`cleanupExtend`, with its reach upgraded — from outside.**  The lemma already
publishes the move list, so no change to `CleanupSim` is needed to see that its run is
normalizing. -/
theorem StateMatchesSolverPos.cleanupExtend_cp {g : Globals} {s : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) (a : Fin 10)
    {ds rest : Column} {e : Card} {cells : List (Fin 4)}
    (hcol : s.tableau a = e :: rest)
    (hd : 0 < (p.pileDepth.get a).toNat)
    (hnd : cells.Nodup)
    (hhold : HoldsCards s.cells cells ds)
    (hrun : IsRun (ds ++ [e]))
    (hqd : q.pileDepth = p.pileDepth)
    (hqf : (q.pileFlute.get a).toNat = (p.pileFlute.get a).toNat + ds.length)
    (hqfne : ∀ i : Fin 10, i ≠ a → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces) (hqkings : q.kings = p.kings) :
    ∃ v : State, CPReach s v ∧
      (∀ i : Fin 10, i ≠ a → v.tableau i = s.tableau i) ∧
      StateMatchesSolverPos g v q := by
  obtain ⟨v, -, hfold, hframe, hmatch⟩ :=
    h.cleanupExtend a hcol hd hnd hhold hrun hqd hqf hqfne hqaces hqkings
  exact ⟨v, cpReach_of_unparkMoves cells (by rw [hcol]; simp) hfold, hframe, hmatch⟩

/-- Hence the extension is solvability-neutral in both directions — the completeness
direction of cleanup's freed-predecessor absorption. -/
theorem StateMatchesSolverPos.cleanupExtend_solvable_iff {g : Globals} {s v : State}
    {p : SolverPosType} (h : StateMatchesSolverPos g s p) (hr : CPReach s v) :
    Solvable s ↔ Solvable v :=
  normReach_solvable_iff h.cards_count hr.toNormReach
