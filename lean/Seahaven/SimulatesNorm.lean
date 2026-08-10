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

/-- **More depth-zero piles.**  A position whose depths are all at most another's has at
least as many free piles.  Composed with `movePre_depth_le` / `removeFlute_depth_le`,
this is what says the child never has *fewer* empty columns than the parent — the column
budget the re-assembly at the child runs on. -/
theorem freePiles_mono {g : Globals} {p q : SolverPosType}
    (hm : SolverInvMerged g p) (hm' : SolverInvMerged g q)
    (h : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat) :
    p.freePiles.toNat ≤ q.freePiles.toNat := by
  rw [← card_empty_piles_eq_freePiles hm, ← card_empty_piles_eq_freePiles hm']
  refine Finset.card_le_card (fun i hi => ?_)
  simp only [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hp0 : (p.pileDepth.get i).toNat = 0 := by rw [hi.2]; rfl
  have hle := h i
  have hq0 : (q.pileDepth.get i).toNat = 0 := by omega
  exact UInt8.toNat_inj.mp (by rw [hq0]; rfl)

/-- **Each vacate buys a free pile.**  If every suit of `FK` can be pointed at a pile
that was occupied at `p` and is empty at `q`, and distinct suits at distinct piles, then
`q` has at least `FK.card` more free piles than `p`.

This is the *arithmetic* half of the column budget the re-assembly at the child needs.
The semantic half — producing `site`, the pile each vacated king was freed from — is not
recorded by `Simulates`/`SimulatesNorm`, whose `FK` is a bare `Finset Suit`. -/
theorem freePiles_add_card_le {g : Globals} {p q : SolverPosType}
    (hm : SolverInvMerged g p) (hm' : SolverInvMerged g q)
    (hle : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat)
    {FK : Finset Suit} (site : Suit → Fin 10)
    (hsite : ∀ su ∈ FK, 0 < (p.pileDepth.get (site su)).toNat ∧
      (q.pileDepth.get (site su)).toNat = 0)
    (hinj : Set.InjOn site ↑FK) :
    p.freePiles.toNat + FK.card ≤ q.freePiles.toNat := by
  classical
  have hz : ∀ (r : SolverPosType) (i : Fin 10),
      r.pileDepth.get i = 0 ↔ (r.pileDepth.get i).toNat = 0 := by
    intro r i
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UInt8.toNat_inj.mp (by rw [h]; rfl)
  set Ep : Finset (Fin 10) := Finset.univ.filter (fun i => p.pileDepth.get i = 0) with hEp
  set Eq : Finset (Fin 10) := Finset.univ.filter (fun i => q.pileDepth.get i = 0) with hEq
  have hsub : Ep ⊆ Eq := by
    intro i hi
    rw [hEp, Finset.mem_filter, hz] at hi
    rw [hEq, Finset.mem_filter, hz]
    exact ⟨Finset.mem_univ _, by have := hle i; omega⟩
  have hSsub : FK.image site ⊆ Eq := by
    intro i hi
    obtain ⟨su, hsu, rfl⟩ := Finset.mem_image.1 hi
    rw [hEq, Finset.mem_filter, hz]
    exact ⟨Finset.mem_univ _, (hsite su hsu).2⟩
  have hdisj : Disjoint Ep (FK.image site) := by
    rw [Finset.disjoint_right]
    intro i hi hiEp
    obtain ⟨su, hsu, rfl⟩ := Finset.mem_image.1 hi
    rw [hEp, Finset.mem_filter, hz] at hiEp
    have := (hsite su hsu).1
    omega
  have hcard : Ep.card + (FK.image site).card ≤ Eq.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hsub hSsub)
  rw [Finset.card_image_of_injOn hinj] at hcard
  rw [← card_empty_piles_eq_freePiles hm, ← card_empty_piles_eq_freePiles hm']
  exact hcard

/-! ## Counting the piles a phase frees

`FK` is a set of *suits*, but the column budget the completeness re-assembly runs on is
about *piles*.  The link is that every vacate empties a pile of its own — and the
cheapest way to record it is to carry the **pile number**: it is right there at the
vacate (`vacatePile`'s `a`, whose depth goes `1 → 0`), and unlike a `freePiles`
inequality it needs no position invariants either to state or to compose.  The
invariants enter only once, at the very end, to turn depth-zero counts back into
`freePiles` (`VacateSites.freePiles_add_card_le`). -/

/-- What a phase does to the pile depths, together with the piles its vacates freed. -/
structure VacateSites (p p' : SolverPosType) (FK : Finset Suit) : Prop where
  /-- Depths never rise, so a solver-empty column stays solver-empty. -/
  depth_le : ∀ i : Fin 10, (p'.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat
  /-- Each vacated suit freed a pile of its own: occupied before, empty after. -/
  sites : ∃ site : Suit → Fin 10, Set.InjOn site ↑FK ∧
    ∀ su ∈ FK, 0 < (p.pileDepth.get (site su)).toNat ∧
      (p'.pileDepth.get (site su)).toNat = 0

/-- A phase that changes nothing. -/
theorem VacateSites.rfl' (p : SolverPosType) : VacateSites p p ∅ where
  depth_le := fun _ => le_rfl
  sites := ⟨fun _ => 0, by simp, by simp⟩

/-- A phase that vacates nothing: only the depths have to fall. -/
theorem VacateSites.of_depth_le {p p' : SolverPosType}
    (h : ∀ i : Fin 10, (p'.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat) :
    VacateSites p p' ∅ where
  depth_le := h
  sites := ⟨fun _ => 0, by simp, by simp⟩

/-- A single vacate, at the pile it freed. -/
theorem VacateSites.single {p p' : SolverPosType} {a : Fin 10} {su : Suit}
    (hle : ∀ i : Fin 10, (p'.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat)
    (hd : 0 < (p.pileDepth.get a).toNat) (hq : (p'.pileDepth.get a).toNat = 0) :
    VacateSites p p' {su} where
  depth_le := hle
  sites := ⟨fun _ => a, by
      intro x hx y hy _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      rw [hx, hy], fun _ _ => ⟨hd, hq⟩⟩

/-- Forgetting some vacates. -/
theorem VacateSites.subset {p p' : SolverPosType} {FK FK' : Finset Suit}
    (h : VacateSites p p' FK) (hsub : FK' ⊆ FK) : VacateSites p p' FK' := by
  obtain ⟨site, hinj, hsite⟩ := h.sites
  exact ⟨h.depth_le, site, hinj.mono (by exact_mod_cast hsub), fun su hsu => hsite su (hsub hsu)⟩

open Classical in
/-- **Composition.**  The two site maps have disjoint ranges for free: the first
phase's piles are already empty at the join, the second phase's are not. -/
theorem VacateSites.trans {p q r : SolverPosType} {F₁ F₂ : Finset Suit}
    (h₁ : VacateSites p q F₁) (h₂ : VacateSites q r F₂) : VacateSites p r (F₁ ∪ F₂) := by
  obtain ⟨s₁, hi₁, hp₁⟩ := h₁.sites
  obtain ⟨s₂, hi₂, hp₂⟩ := h₂.sites
  refine ⟨fun i => le_trans (h₂.depth_le i) (h₁.depth_le i),
    fun su => if su ∈ F₁ then s₁ su else s₂ su, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    by_cases hx1 : x ∈ F₁ <;> by_cases hy1 : y ∈ F₁
    · simp only [if_pos hx1, if_pos hy1] at hxy
      exact hi₁ (by exact_mod_cast hx1) (by exact_mod_cast hy1) hxy
    · simp only [if_pos hx1, if_neg hy1] at hxy
      have h0 := (hp₁ x hx1).2
      have h1 := (hp₂ y (hy.resolve_left hy1)).1
      rw [hxy] at h0
      omega
    · simp only [if_neg hx1, if_pos hy1] at hxy
      have h0 := (hp₁ y hy1).2
      have h1 := (hp₂ x (hx.resolve_left hx1)).1
      rw [← hxy] at h0
      omega
    · simp only [if_neg hx1, if_neg hy1] at hxy
      exact hi₂ (by exact_mod_cast hx.resolve_left hx1) (by exact_mod_cast hy.resolve_left hy1) hxy
  · intro su hsu
    rw [Finset.mem_union] at hsu
    simp only []
    by_cases h1 : su ∈ F₁
    · rw [if_pos h1]
      exact ⟨(hp₁ su h1).1, by have := h₂.depth_le (s₁ su); have := (hp₁ su h1).2; omega⟩
    · rw [if_neg h1]
      exact ⟨by have := h₁.depth_le (s₂ su); have := (hp₂ su (hsu.resolve_left h1)).1; omega,
        (hp₂ su (hsu.resolve_left h1)).2⟩

/-- **The column budget.**  The invariants enter only here, to read `freePiles` off the
depth-zero count. -/
theorem VacateSites.freePiles_add_card_le {g : Globals} {p p' : SolverPosType}
    {FK : Finset Suit} (h : VacateSites p p' FK)
    (hm : SolverInvMerged g p) (hm' : SolverInvMerged g p') :
    p.freePiles.toNat + FK.card ≤ p'.freePiles.toNat := by
  obtain ⟨site, hinj, hsite⟩ := h.sites
  exact _root_.freePiles_add_card_le hm hm' h.depth_le site hsite hinj
