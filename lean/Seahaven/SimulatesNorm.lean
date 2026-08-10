import Seahaven.NormReachBridge
import Seahaven.CleanupSim

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
  bound : ∀ su : Suit, ¬ CfgBitSet k' su ↔ (¬ CfgBitSet k su ∨ su ∈ FK)

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
  bound := fun su => ⟨Or.inl, fun hc => hc.elim id (fun hm => absurd hm (Finset.notMem_empty su))⟩

/-- A configuration-preserving normalizing phase — the shape cleanup's drops and the
drain both have. -/
theorem SimulatesNorm.ofNormReach {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k : Fin 16} (hr : NormReach s s') (h : StateMatchesKingConfig g s' p' k) :
    SimulatesNorm g s p k s' p' k ∅ 0xffff where
  reach := hr
  cfg := h
  vacates := KingVacates.empty
  bound := fun su => ⟨Or.inl, fun hc => hc.elim id (fun hm => absurd hm (Finset.notMem_empty su))⟩

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

/-- **A lone-king vacate**, normalizing.  Mirrors `Simulates.vacate`; the `NormReach`
is the cleanup extension's cell→pile run (the vacate itself moves no card). -/
theorem SimulatesNorm.vacate {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k k' : Fin 16} {su : Suit} (hr : NormReach s s')
    (h : StateMatchesKingConfig g s' p' k')
    (hk' : ∀ su' : Suit, su' ≠ su → (CfgBitSet k' su' ↔ CfgBitSet k su'))
    (hsu : ¬ CfgBitSet k' su) :
    SimulatesNorm g s p k s' p' k' {su} (kingOnPileMap.get (finOfSuit su)) where
  reach := hr
  cfg := h
  vacates := KingVacates.single su
  bound := (Simulates.vacate (p := p) hr.toReach h hk' hsu).bound

/-- **A suit physically on a solver-empty column is piled by any configuration the
state matches.**  The contrapositive of `no_pile`, and the reason `ofVacated`'s side
condition is never an extra assumption. -/
theorem StateMatchesKingConfig.clear_of_column {g : Globals} {v : State} {p : SolverPosType}
    {k : Fin 16} (h : StateMatchesKingConfig g v p k) {i : Fin 10}
    (hd0 : (p.pileDepth.get i).toNat = 0) {d : Card} (hd : (v.tableau i).getLast? = some d) :
    ¬ CfgBitSet k d.suit :=
  fun hbit => h.no_pile d.suit hbit i hd0 d hd rfl

/-- **Carrying a non-neutral `forcedKings` accumulator across a phase that moves
nothing.**

This does *not* model a vacate — it is used strictly **after** one.  The drain is
entered at the post-cleanup position, where the vacated king is already sitting on the
freed column; the accumulator `SolverRemoveFlute` returned still has to be carried into
the drain's `forcedKings := forcedKings &&& …`, and that is all this provides.  Hence
the configuration is `k` on both sides: nothing changes here, because the change
happened earlier.

The side condition `∀ su ∈ FK, ¬ CfgBitSet k su` is therefore not an extra assumption
but a *consequence* of `h`: the vacated suit's king is physically on a solver-empty
column, so `no_pile` forces its bit clear (`clear_of_column`).  In particular
`piled k = piled k ∪ FK` already, which is why replacing `k` by `k ∪ FK` would be a
no-op.

The vacate itself — where the configuration really does gain a suit, `k' =
clearCfgBit k su` — is `SimulatesNorm.vacate` / `StateMatchesKingConfig.vacatePile`, on
the phase-1 route.  And the *parent's* configuration genuinely lacks that suit: the
column had depth 1 there, so no suit owned it.  That gap is exactly what `forcedKings`
and the `subsetTable` shift across the child's larger `freePiles` block exist to
bridge. -/
theorem SimulatesNorm.ofVacated {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    {FK : Finset Suit} {fk : UInt16} (h : StateMatchesKingConfig g s p k)
    (hvac : KingVacates FK fk) (hFK : ∀ su ∈ FK, ¬ CfgBitSet k su) :
    SimulatesNorm g s p k s p k FK fk where
  reach := Relation.ReflTransGen.refl
  cfg := h
  vacates := hvac
  bound := fun su => ⟨Or.inl, fun hc => hc.elim id (fun hm => hFK su hm)⟩

/-- Normalizing phases compose, unioning the vacated suits and intersecting the masks —
the `Simulates.trans` shape, which is what the drain's `forcedKings` accumulator does. -/
theorem SimulatesNorm.trans {g : Globals} {s s' s'' : State} {p p' p'' : SolverPosType}
    {k k' k'' : Fin 16} {F₁ F₂ : Finset Suit} {fk₁ fk₂ : UInt16}
    (h₁ : SimulatesNorm g s p k s' p' k' F₁ fk₁)
    (h₂ : SimulatesNorm g s' p' k' s'' p'' k'' F₂ fk₂) :
    SimulatesNorm g s p k s'' p'' k'' (F₁ ∪ F₂) (fk₁ &&& fk₂) where
  reach := h₁.reach.trans h₂.reach
  cfg := h₂.cfg
  vacates := h₁.vacates.inter h₂.vacates
  bound := (h₁.toSimulates.trans h₂.toSimulates).bound

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

/-- Hence the extension is solvability-neutral in both directions — the completeness
direction of cleanup's freed-predecessor absorption. -/
theorem StateMatchesSolverPos.cleanupExtend_solvable_iff {g : Globals} {s v : State}
    {p : SolverPosType} (h : StateMatchesSolverPos g s p) (hr : CPReach s v) :
    Solvable s ↔ Solvable v :=
  normReach_solvable_iff h.cards_count hr.toNormReach
