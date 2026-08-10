import Seahaven.CriticalMove
import Seahaven.KingReshuffle

/-!
# The king configuration only moves when a column is empty

This file closes the last gap of the completeness step for one pile: the
recursion establishes the answer bit at the configuration `k_t` the *critical*
state stands for, while the caller asked about the configuration `k` the
*initial* state stands for, and the two need not be equal — the prefix of the
winning play may have shuffled king runs between the cells and the empty
columns.

## The argument

Look at the states of the prefix `s ⟶* t` and ask which of them have a
physically **empty** solver-empty column.

* If none does, the piled suits never change (`prefix_piled_left` /
  `prefix_piled_right`): a column can only start or stop carrying a king run at
  a moment when it is empty.  And with no empty column around, a configuration
  the state *realizes* is the configuration it *is* in — the reservation branch
  of `OwnsPile` needs an empty column (`cfgOf_eq_of_noEmpty`).  Hence `k = k_t`.

* Otherwise, take the **first** such state.  Everything before it has a constant
  configuration, and the move into it can only *drop* a suit, so its piled suits
  are among `k`'s.  Symmetrically the **last** such state has its piled suits
  among `k_t`'s.  Either way both `k` and `k_t` dominate a configuration that
  leaves one column completely unused and still fits in the cells — that is
  `HasSpareSubset`, and `ComponentComplete.lean` turns it into the component bit.

The two directions are proved by one induction each; the "first" and "last"
states never have to be named (`prefix_piled_left` walks the chain and either
gets all the way through or stops at an empty-column state).

## Why the chain and not `Reach`

Every state the argument inspects has to be a middle-layer match: the counting
(`card_piledSet_cfgOf_lt`) reads the piled suits off the *columns*, and the
space bound (`freeCellsOf_cfgOf_nonneg`) needs the card count, the foundations
and `flute_le`.  Bare `Reach s t` says nothing about the states in between,
which is why `exists_critical_move_aces` hands back a `PrefixReach`.
-/

/-! ## Empty columns -/

/-- Some column the solver treats as empty really is empty. -/
def HasEmptyPile (u : State) (p : SolverPosType) : Prop :=
  ∃ i : Fin 10, (p.pileDepth.get i).toNat = 0 ∧ u.tableau i = []

/-- Every column the solver treats as empty carries at least one card. -/
def NoEmptyPile (u : State) (p : SolverPosType) : Prop :=
  ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 → u.tableau i ≠ []

theorem noEmptyPile_of_not {u : State} {p : SolverPosType} (h : ¬ HasEmptyPile u p) :
    NoEmptyPile u p := fun i hd0 hnil => h ⟨i, hd0, hnil⟩

/-! ## One move, one column

`PiledSuit` reads only `getLast?` of the solver-empty columns, and a single move
changes any one column by at most a `cons` or a `tail`.  Neither touches
`getLast?` unless the column is empty on one of the two sides. -/

theorem getLast?_cons_of_ne_nil {c : Card} {rest : Column} (h : rest ≠ []) :
    (c :: rest).getLast? = rest.getLast? := by
  cases rest with
  | nil => exact absurd rfl h
  | cons b l => exact List.getLast?_cons_cons

/-- **What one move can do to one column**: nothing, remove its top card, or add
one.  (Taking from and dropping onto the same column lands in the first case:
the card comes straight back.) -/
theorem move_column_cases {u v : State} {m : Move} (h : applyMove u m = some v) (i : Fin 10) :
    v.tableau i = u.tableau i ∨ (∃ c : Card, u.tableau i = c :: v.tableau i) ∨
      (∃ c : Card, v.tableau i = c :: u.tableau i) := by
  rw [applyMove_eq] at h
  obtain ⟨card, s0, htake, hdrop⟩ := h
  have htk : s0.tableau i = u.tableau i ∨ u.tableau i = card :: s0.tableau i := by
    cases hsrc : m.src with
    | foundation => rw [hsrc, takeFromPosition] at htake; simp at htake
    | cell j =>
      rw [hsrc, takeFromPosition, takeFromCell_eq] at htake
      obtain ⟨-, rfl⟩ := htake
      exact Or.inl rfl
    | pile q =>
      rw [hsrc, takeFromPosition, takeFromCol_eq] at htake
      obtain ⟨rest, hcol, rfl⟩ := htake
      by_cases hiq : i = q
      · subst hiq
        exact Or.inr (by simpa using hcol)
      · exact Or.inl (by simp [update, Ne.symm hiq])
  have hdp : v.tableau i = s0.tableau i ∨ v.tableau i = card :: s0.tableau i := by
    cases hdst : m.dest with
    | foundation =>
      rw [hdst, dropPosition, dropFoundation_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      exact Or.inl rfl
    | cell j =>
      rw [hdst, dropPosition, dropCell_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      exact Or.inl rfl
    | pile r =>
      rw [hdst, dropPosition, dropCol_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      by_cases hir : i = r
      · subst hir
        exact Or.inr (by simp)
      · exact Or.inl (by simp [update, Ne.symm hir])
  rcases htk with htk | htk <;> rcases hdp with hdp | hdp
  · exact Or.inl (hdp.trans htk)
  · exact Or.inr (Or.inr ⟨card, by rw [hdp, htk]⟩)
  · exact Or.inr (Or.inl ⟨card, by rw [htk, hdp]⟩)
  · exact Or.inl (by rw [hdp, ← htk])

/-- **A move out of a state with no empty column can only lose piled suits.**  A
suit's column cannot have been *created* by this move: creating one means
dropping onto an empty column, and there is none. -/
theorem PiledSuit.of_move_src {u v : State} {p : SolverPosType} {m : Move}
    (h : applyMove u m = some v) (hne : NoEmptyPile u p) {su : Suit}
    (hp : PiledSuit v p su) : PiledSuit u p su := by
  obtain ⟨i, hd0, d, hd, hsu⟩ := hp
  refine ⟨i, hd0, d, ?_, hsu⟩
  rcases move_column_cases h i with heq | ⟨c, heq⟩ | ⟨c, heq⟩
  · rw [← heq]; exact hd
  · have hvne : v.tableau i ≠ [] := by
      intro hc
      rw [Option.mem_def, hc] at hd
      simp at hd
    rw [heq, getLast?_cons_of_ne_nil hvne]
    exact hd
  · rw [heq, getLast?_cons_of_ne_nil (hne i hd0)] at hd
    exact hd

/-- **A move into a state with no empty column can only gain piled suits.**  A
suit's column cannot have been *emptied* by this move. -/
theorem PiledSuit.of_move_dst {u v : State} {p : SolverPosType} {m : Move}
    (h : applyMove u m = some v) (hne : NoEmptyPile v p) {su : Suit}
    (hp : PiledSuit u p su) : PiledSuit v p su := by
  obtain ⟨i, hd0, d, hd, hsu⟩ := hp
  refine ⟨i, hd0, d, ?_, hsu⟩
  rcases move_column_cases h i with heq | ⟨c, heq⟩ | ⟨c, heq⟩
  · rw [heq]; exact hd
  · rw [heq, getLast?_cons_of_ne_nil (hne i hd0)] at hd
    exact hd
  · have hune : u.tableau i ≠ [] := by
      intro hc
      rw [Option.mem_def, hc] at hd
      simp at hd
    rw [heq, getLast?_cons_of_ne_nil hune]
    exact hd

/-! ## Along the whole prefix

Two inductions, mirror images of each other.  Each either walks the entire chain
without meeting an empty column — in which case the piled suits only travel in
its direction — or stops at the first (resp. last) state that has one. -/

/-- **Looking backwards.**  Either every suit piled at the far end is piled at
the near end, or some state of the chain has an empty column and *its* piled
suits are all piled at the near end. -/
theorem prefix_piled_left {g : Globals} {p : SolverPosType} {u v : State}
    (hu : DepthPlusKings g u p) (hr : PrefixReach g p u v) :
    (∀ su : Suit, PiledSuit v p su → PiledSuit u p su) ∨
      ∃ w : State, DepthPlusKings g w p ∧ HasEmptyPile w p ∧
        ∀ su : Suit, PiledSuit w p su → PiledSuit u p su := by
  induction hr with
  | refl => exact Or.inl (fun _ h => h)
  | @tail v' v hchain hstep ih =>
    by_cases hemp : HasEmptyPile v' p
    · rcases ih with hl | ⟨w, hw, hwe, hws⟩
      · exact Or.inr ⟨v', PrefixReach.dpk hu hchain, hemp, hl⟩
      · exact Or.inr ⟨w, hw, hwe, hws⟩
    · obtain ⟨m, hm⟩ := hstep.1
      have hstep' : ∀ su : Suit, PiledSuit v p su → PiledSuit v' p su :=
        fun su hsu => PiledSuit.of_move_src hm (noEmptyPile_of_not hemp) hsu
      rcases ih with hl | ⟨w, hw, hwe, hws⟩
      · exact Or.inl (fun su hsu => hl su (hstep' su hsu))
      · exact Or.inr ⟨w, hw, hwe, hws⟩

/-- **Looking forwards.**  The mirror image: either every suit piled at the near
end is piled at the far end, or some state of the chain has an empty column and
*its* piled suits are all piled at the far end. -/
theorem prefix_piled_right {g : Globals} {p : SolverPosType} {u v : State}
    (hr : PrefixReach g p u v) :
    (∀ su : Suit, PiledSuit u p su → PiledSuit v p su) ∨
      ∃ w : State, DepthPlusKings g w p ∧ HasEmptyPile w p ∧
        ∀ su : Suit, PiledSuit w p su → PiledSuit v p su := by
  induction hr with
  | refl => exact Or.inl (fun _ h => h)
  | @tail v' v hchain hstep ih =>
    by_cases hemp : HasEmptyPile v p
    · exact Or.inr ⟨v, hstep.2, hemp, fun _ h => h⟩
    · obtain ⟨m, hm⟩ := hstep.1
      have hstep' : ∀ su : Suit, PiledSuit v' p su → PiledSuit v p su :=
        fun su hsu => PiledSuit.of_move_dst hm (noEmptyPile_of_not hemp) hsu
      rcases ih with hl | ⟨w, hw, hwe, hws⟩
      · exact Or.inl (fun su hsu => hstep' su (hl su hsu))
      · exact Or.inr ⟨w, hw, hwe, fun su hsu => hstep' su (hws su hsu)⟩

/-! ## Realized versus physical

`cfgOf` records the suits that *physically* have a column; a configuration the
state merely `RealizesKingConfig` may in addition reserve an empty column for a
suit whose stack has already reached the foundation.  With no empty column there
is nothing to reserve, so the two agree. -/

theorem piledMaskNat_congr {u v : State} {p : SolverPosType}
    (h : ∀ su : Suit, PiledSuit u p su ↔ PiledSuit v p su) :
    piledMaskNat u p = piledMaskNat v p := by
  unfold piledMaskNat
  rw [h Suit.clubs, h Suit.diamonds, h Suit.hearts, h Suit.spades]

theorem cfgOf_congr {u v : State} {p : SolverPosType}
    (h : ∀ su : Suit, PiledSuit u p su ↔ PiledSuit v p su) : cfgOf u p = cfgOf v p :=
  congrArg cfgOfMask (Fin.ext (piledMaskNat_congr h))

/-- **With no empty column, the realized configuration is the physical one.** -/
theorem cfgOf_eq_of_noEmpty {u : State} {p : SolverPosType} {k : Fin 16}
    (hr : RealizesKingConfig u p k) (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile u p su)
    (hne : ¬ HasEmptyPile u p) : k = cfgOf u p := by
  refine piledSet_inj (Finset.Subset.antisymm ?_ ?_)
  · intro su hsu
    rw [mem_piledSet] at hsu
    rw [mem_piledSet, cfgBitSet_cfgOf, not_not]
    obtain ⟨assign, hown, -, hiff⟩ := hr
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff su).2 hsu)
    obtain ⟨hd0, hcase⟩ := hown su i hi
    rcases hcase with ⟨d, hd, hsuit, -⟩ | ⟨hemp, -⟩
    · exact ⟨i, hd0, d, hd, hsuit⟩
    · exact absurd ⟨i, hd0, hemp⟩ hne
  · intro su hsu
    rw [mem_piledSet, cfgBitSet_cfgOf, not_not] at hsu
    rw [mem_piledSet]
    intro hbit
    obtain ⟨i, hd0, d, hd, hsuit⟩ := hsu
    exact hnp su hbit i hd0 d hd hsuit

/-! ## What an empty-column state witnesses

Two facts, both about the state `w` the chain stopped at:

* it leaves a column completely unused, so it piles fewer suits than the
  position has empty columns, and
* its configuration fits in the cells — it is a real state, and only four cells
  exist. -/

open Classical in
/-- **An empty column is a column no suit is using.**  The piled suits inject
into the *non-empty* solver-empty columns, and the empty one is not among
them. -/
theorem card_piledSet_cfgOf_lt {g : Globals} {w : State} {p : SolverPosType}
    (hm : SolverInvMerged g p) (he : HasEmptyPile w p) :
    (piledSet (cfgOf w p)).card < p.freePiles.toNat := by
  obtain ⟨i₀, hd0, hemp⟩ := he
  set E : Finset (Fin 10) := Finset.univ.filter (fun i => p.pileDepth.get i = 0) with hE
  set K : Finset (Fin 10) :=
    Finset.univ.filter (fun i => p.pileDepth.get i = 0 ∧ w.tableau i ≠ []) with hK
  have hzero : ∀ i : Fin 10, p.pileDepth.get i = 0 ↔ (p.pileDepth.get i).toNat = 0 := by
    intro i
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UInt8.toNat_inj.mp (by rw [h]; rfl)
  -- the piled suits inject into the non-empty solver-empty columns
  have hmapmem : ∀ su ∈ piledSet (cfgOf w p),
      (if hp : PiledSuit w p su then hp.choose else i₀) ∈ K := by
    intro su hsu
    rw [mem_piledSet, cfgBitSet_cfgOf, not_not] at hsu
    rw [dif_pos hsu]
    obtain ⟨hpd0, d, hd, -⟩ := hsu.choose_spec
    rw [hK, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (hzero _).2 hpd0, ?_⟩
    intro hc
    rw [Option.mem_def, hc] at hd
    simp at hd
  have hinj : Set.InjOn (fun su => if hp : PiledSuit w p su then hp.choose else i₀)
      ↑(piledSet (cfgOf w p)) := by
    intro su hsu su' hsu' heq
    rw [Finset.mem_coe, mem_piledSet, cfgBitSet_cfgOf, not_not] at hsu hsu'
    simp only [dif_pos hsu, dif_pos hsu'] at heq
    obtain ⟨-, d, hd, hsuit⟩ := hsu.choose_spec
    obtain ⟨-, d', hd', hsuit'⟩ := hsu'.choose_spec
    rw [Option.mem_def] at hd hd'
    rw [heq] at hd
    rw [← hsuit, ← hsuit', congrArg Card.suit (Option.some.inj (hd.symm.trans hd'))]
  have h1 : (piledSet (cfgOf w p)).card ≤ K.card :=
    Finset.card_le_card_of_injOn _ hmapmem hinj
  -- and one solver-empty column is not used at all
  have hsub : K ⊆ E := by
    intro i hi
    rw [hK, Finset.mem_filter] at hi
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2.1⟩
  have hi₀E : i₀ ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hzero _).2 hd0⟩
  have hi₀K : i₀ ∉ K := by
    rw [hK, Finset.mem_filter]
    rintro ⟨-, -, hne⟩
    exact hne hemp
  have h2 : K.card < E.card :=
    Finset.card_lt_card ⟨hsub, fun hc => hi₀K (hc hi₀E)⟩
  have h3 : E.card = p.freePiles.toNat := card_empty_piles_eq_freePiles hm
  omega

/-- **A real state's configuration fits.**  `usedSpace` is at most what is
physically outside the piles, the cells hold at most four cards, and every king
stack is refunded — so the cell budget at `cfgOf w p` is non-negative. -/
theorem freeCellsOf_cfgOf_nonneg {g : Globals} {w : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hw : DepthPlusKings g w p) :
    0 ≤ freeCellsOf p (cfgOf w p) := by
  have h1 := usedSpace_le_outside hb hw.cards_count hw.aces_match hw.flute_le
  have h2 := kingList_le_kingRefund_of (k := cfgOf w p) hb
    (fun i hi d hd => hw.king_le i hi d hd)
    (fun _ _ hi hj {_ _} hd he hsu => hw.empty_pile_unique hi hj hd he hsu)
    (fun _ hbit => noKingPile_cfgOf hbit)
  have h3 : ((cellList w).length : Int) ≤ 4 := by
    have h := cellList_length_add_freeCells w
    exact_mod_cast (by omega : (cellList w).length ≤ 4)
  unfold freeCellsOf
  linarith

/-- **Every configuration a state stands for is affordable.**  The same count as
`freeCellsOf_cfgOf_nonneg`, at an arbitrary realized configuration rather than the
physical one: `no_pile` is all `kingList_le_kingRefund_of` needs. -/
theorem DepthPlusKingsCfg.freeCellsOf_nonneg {g : Globals} {w : State} {p : SolverPosType}
    {k : Fin 16} (hb : SolverInvBase g p) (hw : DepthPlusKingsCfg g w p k) :
    0 ≤ freeCellsOf p k := by
  have h1 := usedSpace_le_outside hb hw.toDepthPlusKings.cards_count
    hw.toDepthPlusKings.aces_match hw.toDepthPlusKings.flute_le
  have h2 := kingList_le_kingRefund_of (k := k) hb
    (fun i hi d hd => hw.toDepthPlusKings.king_le i hi d hd)
    (fun _ _ hi hj {_ _} hd he hsu => hw.toDepthPlusKings.empty_pile_unique hi hj hd he hsu)
    hw.no_pile
  have h3 : ((cellList w).length : Int) ≤ 4 := by
    have h := cellList_length_add_freeCells w
    exact_mod_cast (by omega : (cellList w).length ≤ 4)
  unfold freeCellsOf
  linarith

/-! ## The conclusion of the physical half -/

/-- **`k` has a feasible subset with a column to spare.**  Some configuration
piling no more than `k` does leaves a solver-empty column completely unused and
still fits in the cells.  This is exactly the semantic content of a
`componentTable` bit (`ComponentComplete.inComponent_of_hasSpareSubset`). -/
def HasSpareSubset (p : SolverPosType) (k : Fin 16) : Prop :=
  ∃ c : Fin 16, piledSet c ⊆ piledSet k ∧ (piledSet c).card < p.freePiles.toNat ∧
    0 ≤ freeCellsOf p c

/-- A state with an empty column, all of whose piled suits `k` piles, witnesses
`HasSpareSubset p k`. -/
theorem hasSpareSubset_of_state {g : Globals} {w : State} {p : SolverPosType} {k : Fin 16}
    (hm : SolverInvMerged g p) (hw : DepthPlusKings g w p) (he : HasEmptyPile w p)
    (hsub : ∀ su : Suit, PiledSuit w p su → ¬ CfgBitSet k su) : HasSpareSubset p k := by
  refine ⟨cfgOf w p, ?_, card_piledSet_cfgOf_lt hm he,
    freeCellsOf_cfgOf_nonneg hm.toSolverInvBase hw⟩
  intro su hsu
  rw [mem_piledSet, cfgBitSet_cfgOf, not_not] at hsu
  rw [mem_piledSet]
  exact hsub su hsu

/-- **The gap, physical half.**  Either the two configurations coincide, or each
of them dominates a feasible configuration with a column to spare.

Note both alternatives are needed: the critical move may itself put a king on an
empty column (`cfgOfPlus`), and then `t` has an empty column, so the second
alternative is the one that fires. -/
theorem cfg_eq_or_spareSubset {g : Globals} {p : SolverPosType} {s t : State} {k kt : Fin 16}
    (hm : SolverInvMerged g p)
    (hs : DepthPlusKingsCfg g s p k) (ht : DepthPlusKingsCfg g t p kt)
    (hr : PrefixReach g p s t) :
    k = kt ∨ (HasSpareSubset p k ∧ HasSpareSubset p kt) := by
  -- a state's piled suits are among the configuration's, by `no_pile`
  have hpk : ∀ su : Suit, PiledSuit s p su → ¬ CfgBitSet k su := by
    intro su ⟨i, hd0, d, hd, hsuit⟩ hbit
    exact hs.no_pile su hbit i hd0 d hd hsuit
  have hpkt : ∀ su : Suit, PiledSuit t p su → ¬ CfgBitSet kt su := by
    intro su ⟨i, hd0, d, hd, hsuit⟩ hbit
    exact ht.no_pile su hbit i hd0 d hd hsuit
  by_cases hes : HasEmptyPile s p
  · refine Or.inr ⟨hasSpareSubset_of_state hm hs.toDepthPlusKings hes hpk, ?_⟩
    rcases prefix_piled_right hr with hl | ⟨w, hw, hwe, hws⟩
    · exact hasSpareSubset_of_state hm hs.toDepthPlusKings hes
        (fun su hsu => hpkt su (hl su hsu))
    · exact hasSpareSubset_of_state hm hw hwe (fun su hsu => hpkt su (hws su hsu))
  by_cases het : HasEmptyPile t p
  · refine Or.inr ⟨?_, hasSpareSubset_of_state hm ht.toDepthPlusKings het hpkt⟩
    rcases prefix_piled_left hs.toDepthPlusKings hr with hl | ⟨w, hw, hwe, hws⟩
    · exact hasSpareSubset_of_state hm ht.toDepthPlusKings het
        (fun su hsu => hpk su (hl su hsu))
    · exact hasSpareSubset_of_state hm hw hwe (fun su hsu => hpk su (hws su hsu))
  -- neither endpoint has an empty column
  rcases prefix_piled_left hs.toDepthPlusKings hr with hl | ⟨w, hw, hwe, hws⟩
  · rcases prefix_piled_right hr with hl' | ⟨w', hw', hwe', hws'⟩
    · left
      rw [cfgOf_eq_of_noEmpty hs.realizes hs.no_pile hes,
        cfgOf_eq_of_noEmpty ht.realizes ht.no_pile het]
      exact cfgOf_congr (fun su => ⟨hl' su, hl su⟩)
    · exact Or.inr ⟨hasSpareSubset_of_state hm hw' hwe' (fun su hsu => hpk su (hl su (hws' su hsu))),
        hasSpareSubset_of_state hm hw' hwe' (fun su hsu => hpkt su (hws' su hsu))⟩
  · rcases prefix_piled_right hr with hl' | ⟨w', hw', hwe', hws'⟩
    · exact Or.inr ⟨hasSpareSubset_of_state hm hw hwe (fun su hsu => hpk su (hws su hsu)),
        hasSpareSubset_of_state hm hw hwe (fun su hsu => hpkt su (hl' su (hws su hsu)))⟩
    · exact Or.inr ⟨hasSpareSubset_of_state hm hw hwe (fun su hsu => hpk su (hws su hsu)),
        hasSpareSubset_of_state hm hw' hwe' (fun su hsu => hpkt su (hws' su hsu))⟩
