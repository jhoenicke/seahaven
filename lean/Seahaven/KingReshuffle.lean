import Seahaven.KingConfigSim
import Seahaven.ComponentKingBits
import Seahaven.SoundnessSkeleton

/-!
# King reshuffling: the component is one mutually reachable class

`computeComponentKingBits` returns a set of king configurations that the solver
treats as interchangeable: `movable'' := movable' ||| component` (`Solver.lean:453`)
adds *every* component bit as soon as *one* of them is solvable.  What justifies
that is `ComponentSound` — from a state standing for one component configuration
one can reach, by legal moves that change nothing else, a state standing for any
other.

This file proves the combinatorial heart of it and reduces the rest to two
physical steps.

## The argument

Write `runLen p su` for the number of cards in suit `su`'s freed king run — what
piling that suit refunds to the cells (`kingRefund`).  A configuration is a set
`S` of piled suits, and it costs the cells `usedSpace - Σ_{su ∈ S} runLen su`, so

> `S` is **feasible** iff `0 ≤ freeCells S`, and `S` is **in the component** iff
> some `x ∈ S` can be unpiled, i.e. `S.erase x` is still feasible.

A *reshuffle step* unpiles one suit and piles another — the only kind of move
available, because inside one block every empty column already carries a king, so
a column must be freed before another suit can claim it.  The step's one side
condition is that the intermediate set `S.erase x` be feasible: its run has to fit
in the cells.  Piling never needs a condition (it only frees cells), which is why
the step is *symmetric*: forward and backward use the same intermediate.

Connectivity is then a greedy argument, and it does **not** work by heading
straight for the target — see below.  It routes through

> `M` := a set of `n` suits with the **largest** total run length,

for which every `y ∈ M` has `runLen y ≥ runLen x` for every `x ∉ M` (else swapping
`x` for `y` would beat `M`).  From any `S` in the component with `|S| = n`:

* unpile `x` := the **shortest** run in `S \ M`, pile any `y ∈ M \ S`;
* the intermediate is feasible: the component witness `x0 ∈ S` has
  `runLen x ≤ runLen x0` either because `x0 ∈ M` (then `key` applies, `x ∉ M`) or
  because `x0 ∈ S \ M` (then minimality of `x` applies) — and unpiling a *shorter*
  run than one that is known to fit, fits;
* the result is again in the component, witnessed by the freshly piled `y`, and it
  is one suit closer to `M`.

So `S ⟶* M`, and by symmetry `M ⟶* T` for the target, giving `S ⟶* T`.

**Why route through `M` and not straight to the target `T`.**  Taking `x` to be the
shortest run in `S \ T` and `y` the longest in `T \ S` — the obvious greedy — can
get stuck: the component witness `x0` may lie in `S ∩ T`, with every run in `S \ T`
strictly longer than `x0`, so no unpiling towards `T` is affordable, and unpiling
`x0` itself makes no progress.  Against `M` that cannot happen, because `M` holds
the *longest* runs: a witness inside `M` bounds every candidate outside it.

## The physical steps

The two card-level facts are isolated as `KingUnpileReachable` and
`KingPileReachable` — moving one suit's freed king run from an empty column into
the cells and back — and **proved in `KingMoveSim`**, which also assembles
`ComponentSound` from them (`componentSound`).  `SubsetSound` needs only the
piling half: its downward closure moves *more* kings onto columns, the direction
with no cell-space side condition at all.
-/

open Finset

/-! ## Configurations as sets of piled suits

`CfgBitSet k su` is "suit `su` has **no** pile", so the piled set is the *clear*
bits.  Everything about the correspondence is decided over the tables: `piledSet`
is a bijection onto `Finset Suit`, and the two bit operations are `erase` and
`insert`. -/

/-- The suits that configuration `k` puts on a pile of their own. -/
def piledSet (k : Fin 16) : Finset Suit := Finset.univ.filter (fun su => ¬ CfgBitSet k su)

theorem mem_piledSet {k : Fin 16} {su : Suit} : su ∈ piledSet k ↔ ¬ CfgBitSet k su := by
  simp [piledSet]

/-- Configuration `k` with suit `su` additionally **un**piled — dual to
`clearCfgBit`.  The `min` clamp never fires (`grlex2bits` values are 4-bit). -/
def setCfgBit (k : Fin 16) (su : Suit) : Fin 16 :=
  ⟨(bits2grlex.get ⟨min ((grlex2bits.get k).toNat ||| 2 ^ suitToNat su) 15, by omega⟩).toNat,
    bits2grlex_lt _⟩

theorem piledSet_inj : Function.Injective piledSet := by decide

theorem piledSet_surj (S : Finset Suit) : ∃ k : Fin 16, piledSet k = S := by
  revert S; decide

theorem piledSet_setCfgBit (k : Fin 16) (su : Suit) :
    piledSet (setCfgBit k su) = (piledSet k).erase su := by revert k su; decide

theorem piledSet_clearCfgBit (k : Fin 16) (su : Suit) :
    piledSet (clearCfgBit k su) = insert su (piledSet k) := by revert k su; decide

/-! ## The cell arithmetic

`kingRefund` is the total run length of the piled suits, so `freeCellsOf` is an
affine function of that sum — which is what makes the whole argument linear. -/

/-- Cards in suit `su`'s freed king run: `kings su` is the deepest card *not* freed,
so the run is `kings su + 1 … K`. -/
def runLen (p : SolverPosType) (su : Suit) : Int :=
  13 - (VALUE (p.kings.get (finOfSuit su))).toNat

/-- Under `SolverInvBase` no suit is over-freed, so runs have nonnegative length.
Not needed for the connectivity argument — feasibility of an intermediate is
always inherited from the component witness — but it is what says that *piling*
never costs cells, which is why the physical pile step has no side condition. -/
theorem runLen_nonneg {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p) (su : Suit) :
    0 ≤ runLen p su := by
  have h := (hb.aces_kings_valid (finOfSuit su)).2.2.2.1
  unfold runLen
  omega

theorem sum_suit (f : Suit → Int) :
    (∑ su : Suit, f su) = f .clubs + f .diamonds + f .hearts + f .spades := by
  simp [Finset.sum, Finset.univ, Fintype.elems]; ring

/-- **The refund is the total run length of the piled suits.** -/
theorem kingRefund_eq_sum (p : SolverPosType) (k : Fin 16) :
    kingRefund p k = ∑ su ∈ piledSet k, runLen p su := by
  have hcfg : ∀ su : Suit, (¬ CfgBitSet k su)
      ↔ ((grlex2bits.get k).toNat / 2 ^ suitToNat su % 2 = 0) := by
    intro su; unfold CfgBitSet; omega
  rw [piledSet, Finset.sum_filter, sum_suit]
  simp only [hcfg, runLen, finOfSuit, suitToNat,
    show (⟨0, by omega⟩ : Fin 4) = 0 from rfl, show (⟨1, by omega⟩ : Fin 4) = 1 from rfl,
    show (⟨2, by omega⟩ : Fin 4) = 2 from rfl, show (⟨3, by omega⟩ : Fin 4) = 3 from rfl]
  rw [kingRefund, show (List.finRange 4) = [0, 1, 2, 3] from by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  ring

/-- `freeCellsOf`, read off the piled set. -/
theorem freeCellsOf_eq (p : SolverPosType) (k : Fin 16) :
    freeCellsOf p k = (4 - p.usedSpace.toInt) + ∑ su ∈ piledSet k, runLen p su := by
  rw [freeCellsOf, kingRefund_eq_sum]
  ring

/-! ## The abstract reshuffle problem

Stated over an arbitrary run-length function and cell budget: nothing below knows
about `SolverPosType`. -/

namespace KingSwap

variable (len : Suit → Int) (B : Int)

/-- The piled set `S` fits in the cells. -/
def Feas (S : Finset Suit) : Prop := 0 ≤ B + ∑ su ∈ S, len su

/-- `S` is in the component: some piled suit can be moved back into the cells,
which is what frees a column for a different suit. -/
def Comp (S : Finset Suit) : Prop := ∃ x ∈ S, Feas len B (S.erase x)

/-- One reshuffle: unpile `x`, pile `y`, with the intermediate set feasible. -/
def Step (S T : Finset Suit) : Prop :=
  ∃ x ∈ S, ∃ y ∉ S, Feas len B (S.erase x) ∧ T = insert y (S.erase x)

variable {len B}

/-- A step's target is again in the component — witnessed by the suit just piled,
whose removal gives back the (feasible) intermediate. -/
theorem Step.comp {S T : Finset Suit} (h : Step len B S T) : Comp len B T := by
  obtain ⟨x, hx, y, hy, hfeas, rfl⟩ := h
  refine ⟨y, Finset.mem_insert_self _ _, ?_⟩
  rwa [Finset.erase_insert (fun hc => hy (Finset.mem_of_mem_erase hc))]

theorem Step.card_eq {S T : Finset Suit} (h : Step len B S T) : T.card = S.card := by
  obtain ⟨x, hx, y, hy, -, rfl⟩ := h
  rw [Finset.card_insert_of_notMem (fun hc => hy (Finset.mem_of_mem_erase hc)),
    Finset.card_erase_of_mem hx]
  have : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hx⟩
  omega

/-- **Steps are symmetric**: undoing a reshuffle passes through the same
intermediate set, so it carries the same feasibility condition. -/
theorem Step.symm {S T : Finset Suit} (h : Step len B S T) : Step len B T S := by
  obtain ⟨x, hx, y, hy, hfeas, rfl⟩ := h
  have hyx : y ∉ S.erase x := fun hc => hy (Finset.mem_of_mem_erase hc)
  have hxne : x ≠ y := fun hc => hy (hc ▸ hx)
  refine ⟨y, Finset.mem_insert_self _ _, x, ?_, ?_, ?_⟩
  · rw [Finset.mem_insert]
    exact fun hc => hc.elim hxne (fun hc' => (Finset.notMem_erase x S) hc')
  · rwa [Finset.erase_insert hyx]
  · rw [Finset.erase_insert hyx, Finset.insert_erase hx]

theorem reachable_symm {S T : Finset Suit}
    (h : Relation.ReflTransGen (Step len B) S T) :
    Relation.ReflTransGen (Step len B) T S := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

/-! ### The greedy target -/

/-- A set of `n` suits of maximal total run length, together with the property
that makes it the right waypoint: every run it holds is at least as long as every
run it does not. -/
private theorem exists_max_set (len : Suit → Int) (n : Nat) {A : Finset Suit} (hAn : A.card = n) :
    ∃ M : Finset Suit, M.card = n ∧
      (∀ S : Finset Suit, S.card = n → ∑ su ∈ S, len su ≤ ∑ su ∈ M, len su) ∧
      (∀ y ∈ M, ∀ x ∉ M, len x ≤ len y) := by
  obtain ⟨M, hMmem, hMmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset Suit).powersetCard n) (fun U => ∑ su ∈ U, len su)
    ⟨A, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hAn⟩⟩
  have hMn : M.card = n := (Finset.mem_powersetCard.1 hMmem).2
  have hmax : ∀ S : Finset Suit, S.card = n → ∑ su ∈ S, len su ≤ ∑ su ∈ M, len su :=
    fun S hS => hMmax S (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩)
  refine ⟨M, hMn, hmax, fun y hy x hx => ?_⟩
  have hxe : x ∉ M.erase y := fun hc => hx (Finset.mem_of_mem_erase hc)
  have hcard : (insert x (M.erase y)).card = n := by
    rw [Finset.card_insert_of_notMem hxe, Finset.card_erase_of_mem hy]
    have : 1 ≤ M.card := Finset.card_pos.2 ⟨y, hy⟩
    omega
  have hsum : ∑ su ∈ insert x (M.erase y), len su = (∑ su ∈ M, len su) - len y + len x := by
    rw [Finset.sum_insert hxe]
    have := Finset.sum_erase_add M len hy
    omega
  have := hmax _ hcard
  omega

/-! ### The descent -/

/-- **Every component set of size `n` reaches the greedy target `M`.**  Induction
on how far `S` is from `M`; each round unpiles the shortest run outside `M` and
piles one of `M`'s. -/
private theorem reachable_max {M : Finset Suit} {n : Nat}
    (hMn : M.card = n) (hkey : ∀ y ∈ M, ∀ x ∉ M, len x ≤ len y) :
    ∀ (m : Nat) (S : Finset Suit), (S \ M).card ≤ m → Comp len B S → S.card = n →
      Relation.ReflTransGen (Step len B) S M := by
  intro m
  induction m with
  | zero =>
    intro S hle _ hSn
    have hsub : S ⊆ M := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (by omega))
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)) ▸ Relation.ReflTransGen.refl
  | succ m ih =>
    intro S hle hS hSn
    by_cases hSM : S = M
    · exact hSM ▸ Relation.ReflTransGen.refl
    -- `S` is not contained in `M`, so there is something to unpile
    have hne : (S \ M).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hc
      exact hSM (Finset.eq_of_subset_of_card_le
        (Finset.sdiff_eq_empty_iff_subset.1 hc) (by omega))
    obtain ⟨x, hxSM, hxmin⟩ := Finset.exists_min_image (S \ M) len hne
    obtain ⟨hxS, hxM⟩ := Finset.mem_sdiff.1 hxSM
    -- and, the cards being equal, something in `M` to pile
    have hcomm : (M \ S).card = (S \ M).card := by
      have h1 := Finset.card_sdiff_add_card_inter S M
      have h2 := Finset.card_sdiff_add_card_inter M S
      rw [Finset.inter_comm] at h2
      omega
    obtain ⟨y, hySM⟩ := Finset.card_pos.1 (by rw [hcomm]; exact Finset.card_pos.2 hne)
    obtain ⟨hyM, hyS⟩ := Finset.mem_sdiff.1 hySM
    -- the intermediate is feasible: `x`'s run is no longer than the witness's
    obtain ⟨x0, hx0S, hx0feas⟩ := hS
    have hlen : len x ≤ len x0 := by
      by_cases hx0M : x0 ∈ M
      · exact hkey x0 hx0M x hxM
      · exact hxmin x0 (Finset.mem_sdiff.2 ⟨hx0S, hx0M⟩)
    have hfeas : Feas len B (S.erase x) := by
      have h1 := Finset.sum_erase_add S len hxS
      have h2 := Finset.sum_erase_add S len hx0S
      unfold Feas at hx0feas ⊢
      omega
    -- one step, then recurse: `S'` is one suit closer to `M`
    have hstep : Step len B S (insert y (S.erase x)) := ⟨x, hxS, y, hyS, hfeas, rfl⟩
    refine Relation.ReflTransGen.head hstep (ih _ ?_ hstep.comp ?_)
    · have hsd : insert y (S.erase x) \ M = (S \ M).erase x := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hax, haS⟩, haM⟩
          · exact absurd hyM haM
          · exact ⟨hax, haS, haM⟩
        · rintro ⟨hax, haS, haM⟩
          exact ⟨Or.inr ⟨hax, haS⟩, haM⟩
      rw [hsd, Finset.card_erase_of_mem hxSM]
      omega
    · rw [hstep.card_eq]; exact hSn

/-- **The component is one mutually reachable class.**  Any two component sets of
the same size are joined by reshuffle steps. -/
theorem reachable {A C : Finset Suit} {n : Nat}
    (hA : Comp len B A) (hAn : A.card = n) (hC : Comp len B C) (hCn : C.card = n) :
    Relation.ReflTransGen (Step len B) A C := by
  obtain ⟨M, hMn, -, hkey⟩ := exists_max_set len n hAn
  exact (reachable_max hMn hkey (A \ M).card A le_rfl hA hAn).trans
    (reachable_symm (reachable_max hMn hkey (C \ M).card C le_rfl hC hCn))

end KingSwap

/-! ## Back to configurations

The abstract development is transported along the bijection `piledSet`.  Note
which side each bit operation lands on: `setCfgBit` (**un**pile) is `erase`, and
`clearCfgBit` (pile) is `insert`. -/

/-- `k` is in the component: one of its piled suits can be moved back into the
cells.  This is the semantic content of a `componentTable` bit — the loop of
`computeComponentKingBits` enumerates exactly the configurations that pile one
suit fewer and still fit (`component_run_eq`). -/
def InComponent (p : SolverPosType) (k : Fin 16) : Prop :=
  ∃ su : Suit, ¬ CfgBitSet k su ∧ 0 ≤ freeCellsOf p (setCfgBit k su)

/-- One reshuffle at configuration level: unpile `x`, pile `y`.  The intermediate
configuration `setCfgBit k x` — one suit fewer piled, hence one spare column — must
leave the cells non-negative, since `x`'s run has to go there. -/
def CfgStep (p : SolverPosType) (k k' : Fin 16) : Prop :=
  ∃ x : Suit, ¬ CfgBitSet k x ∧ ∃ y : Suit, CfgBitSet k y ∧
    0 ≤ freeCellsOf p (setCfgBit k x) ∧ k' = clearCfgBit (setCfgBit k x) y

/-- The cell budget with nothing piled. -/
private def budget (p : SolverPosType) : Int := 4 - p.usedSpace.toInt

private theorem feas_iff (p : SolverPosType) (k : Fin 16) :
    KingSwap.Feas (runLen p) (budget p) (piledSet k) ↔ 0 ≤ freeCellsOf p k := by
  rw [KingSwap.Feas, freeCellsOf_eq, budget]

private theorem inComponent_iff (p : SolverPosType) (k : Fin 16) :
    InComponent p k ↔ KingSwap.Comp (runLen p) (budget p) (piledSet k) := by
  unfold InComponent KingSwap.Comp
  constructor
  · rintro ⟨su, hsu, hfeas⟩
    exact ⟨su, mem_piledSet.2 hsu,
      by rw [← piledSet_setCfgBit]; exact (feas_iff p _).2 hfeas⟩
  · rintro ⟨su, hsu, hfeas⟩
    exact ⟨su, mem_piledSet.1 hsu,
      (feas_iff p _).1 (by rw [piledSet_setCfgBit]; exact hfeas)⟩

private theorem cfgStep_iff (p : SolverPosType) (k k' : Fin 16) :
    CfgStep p k k' ↔ KingSwap.Step (runLen p) (budget p) (piledSet k) (piledSet k') := by
  unfold CfgStep KingSwap.Step
  constructor
  · rintro ⟨x, hx, y, hy, hfeas, rfl⟩
    refine ⟨x, mem_piledSet.2 hx, y, fun hc => (mem_piledSet.1 hc) hy, ?_, ?_⟩
    · rw [← piledSet_setCfgBit]; exact (feas_iff p _).2 hfeas
    · rw [piledSet_clearCfgBit, piledSet_setCfgBit]
  · rintro ⟨x, hx, y, hy, hfeas, heq⟩
    refine ⟨x, mem_piledSet.1 hx, y, by by_contra hc; exact hy (mem_piledSet.2 hc), ?_, ?_⟩
    · exact (feas_iff p _).1 (by rw [piledSet_setCfgBit]; exact hfeas)
    · refine piledSet_inj ?_
      rw [heq, piledSet_clearCfgBit, piledSet_setCfgBit]

/-- Transport of an abstract path back to configurations: `piledSet` is onto, so
every intermediate set is some configuration, and injective, so the endpoints are
pinned. -/
private theorem transport_path (p : SolverPosType) {S T : Finset Suit}
    (h : Relation.ReflTransGen (KingSwap.Step (runLen p) (budget p)) S T)
    (k : Fin 16) (hk : piledSet k = S) :
    ∀ k' : Fin 16, piledSet k' = T → Relation.ReflTransGen (CfgStep p) k k' := by
  induction h with
  | refl =>
    intro k' hk'
    exact piledSet_inj (hk'.trans hk.symm) ▸ Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
    intro k' hk'
    obtain ⟨k1, hk1⟩ := piledSet_surj _
    refine Relation.ReflTransGen.tail (ih k1 hk1) ((cfgStep_iff p k1 k').2 ?_)
    rw [hk1, hk']
    exact hstep

/-- **The component is one class, at configuration level.**  `piledSet` is a
bijection, so the abstract connectivity theorem transports verbatim; the
cardinality hypothesis is what says the two configurations live in the same
`closureInfos` block. -/
theorem cfgStep_reachable_of_component (p : SolverPosType) {k k' : Fin 16}
    (hk : InComponent p k) (hk' : InComponent p k')
    (hcard : (piledSet k).card = (piledSet k').card) :
    Relation.ReflTransGen (CfgStep p) k k' :=
  transport_path p
    (KingSwap.reachable ((inComponent_iff p k).1 hk) rfl ((inComponent_iff p k').1 hk') hcard.symm)
    k rfl k' rfl

/-! ## The two physical steps

These are the only things about *cards* the argument needs, and they are exactly
the two halves of a king reshuffle.  Both are `parkMoves`/`unparkMoves` work: a
freed king run is a descending same-suit run whose deepest card is the king, so it
goes into cells one card at a time and comes back onto an empty column the same
way (`dropCol` accepts a king on an empty column, and each next card on its
successor).

They are stated as named `Prop`s in the style of `SoundnessSkeleton`'s
obligations.  `SubsetSound` needs the same two — its downward closure under "put
fewer kings on piles" is repeated *piling*, i.e. `KingPileReachable` alone. -/

/-- **Unpiling.**  Suit `su` owns a column; move its whole run into the cells.
Affordable exactly when the resulting configuration leaves the cells
non-negative, which is the hypothesis `hfeas`.  The abstract position is
unchanged: the run's cards are not counted by any field of `p` (`usedSpace`
already charges them to the cells — that is what the `kingRefund` of the *other*
configuration says). -/
def KingUnpileReachable : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (k : Fin 16) (su : Suit),
    WellFormedLayout g → SolverInvMerged g p → StateMatchesKingConfig g s p k →
    ¬ CfgBitSet k su → 0 ≤ freeCellsOf p (setCfgBit k su) →
    KingConfigReachable g p s (setCfgBit k su)

/-- **Piling.**  Suit `su`'s run is in the cells; move it onto a spare column.
No affordability condition — piling only *frees* cells (`runLen_nonneg`) — but
there must be a column left over, which is what the cardinality hypothesis says:
fewer suits are piled than the position has empty columns. -/
def KingPileReachable : Prop :=
  ∀ (g : Globals) (p : SolverPosType) (s : State) (k : Fin 16) (su : Suit),
    WellFormedLayout g → SolverInvMerged g p → StateMatchesKingConfig g s p k →
    CfgBitSet k su → (piledSet k).card < p.freePiles.toNat →
    KingConfigReachable g p s (clearCfgBit k su)

/-- A configuration never claims more king piles than the position has empty
columns. -/
theorem card_piledSet_le_freePiles {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hs : StateMatchesKingConfig g s p k) (hm : SolverInvMerged g p) :
    (piledSet k).card ≤ p.freePiles.toNat :=
  hs.realizes.card_clear_le_freePiles hm

/-- **One reshuffle step is physically realizable.**  Unpile, which is what needs
the cells; then pile, which is what needs the column the unpiling just freed. -/
theorem CfgStep.reachable (hU : KingUnpileReachable) (hP : KingPileReachable)
    {g : Globals} {p : SolverPosType} {s : State} {k k' : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hs : StateMatchesKingConfig g s p k) (hstep : CfgStep p k k') :
    KingConfigReachable g p s k' := by
  obtain ⟨x, hx, y, hy, hfeas, rfl⟩ := hstep
  obtain ⟨s1, hr1, hs1⟩ := hU g p s k x hwf hm hs hx hfeas
  -- the unpiled column is the spare one the piling needs
  have hcard : (piledSet (setCfgBit k x)).card < p.freePiles.toNat := by
    have hle := card_piledSet_le_freePiles hs hm
    have hpos : 1 ≤ (piledSet k).card := Finset.card_pos.2 ⟨x, mem_piledSet.2 hx⟩
    rw [piledSet_setCfgBit, Finset.card_erase_of_mem (mem_piledSet.2 hx)]
    omega
  -- `y` is still unpiled after `x` left
  have hy1 : CfgBitSet (setCfgBit k x) y := by
    by_contra hc
    have hmem : y ∈ (piledSet k).erase x := by
      rw [← piledSet_setCfgBit]; exact mem_piledSet.2 hc
    exact (mem_piledSet.1 (Finset.mem_of_mem_erase hmem)) hy
  obtain ⟨s2, hr2, hs2⟩ := hP g p s1 (setCfgBit k x) y hwf hm hs1 hy1 hcard
  exact ⟨s2, hr1.trans hr2, hs2⟩

/-- A whole reshuffle path is physically realizable. -/
theorem cfgPath_reachable (hU : KingUnpileReachable) (hP : KingPileReachable)
    {g : Globals} {p : SolverPosType} {k k' : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hpath : Relation.ReflTransGen (CfgStep p) k k') :
    ∀ s : State, StateMatchesKingConfig g s p k → KingConfigReachable g p s k' := by
  induction hpath with
  | refl => exact fun s hs => ⟨s, Relation.ReflTransGen.refl, hs⟩
  | tail _ hstep ih =>
    intro s hs
    obtain ⟨s1, hr1, hs1⟩ := ih s hs
    obtain ⟨s2, hr2, hs2⟩ := CfgStep.reachable hU hP hwf hm hs1 hstep
    exact ⟨s2, hr1.trans hr2, hs2⟩

/-- **The lemma the `component` widening needs.**  From a state standing for one
component configuration, a state standing for *any* other component configuration
of the same block is reachable by legal moves — and it stands for the *same*
abstract position, since reshuffling king runs between the cells and empty columns
changes no depth, flute or foundation. -/
theorem component_configReachable (hU : KingUnpileReachable) (hP : KingPileReachable)
    {g : Globals} {p : SolverPosType} {s : State} {k k' : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hs : StateMatchesKingConfig g s p k)
    (hk : InComponent p k) (hk' : InComponent p k')
    (hcard : (piledSet k).card = (piledSet k').card) :
    KingConfigReachable g p s k' :=
  cfgPath_reachable hU hP hwf hm (cfgStep_reachable_of_component p hk hk' hcard) s hs

/-! ## Same block, same number of piled suits

The cardinality hypothesis above is free for two configurations of one
`closureInfos` block: the block *is* the set of grlex indices whose piled set has
the block's size (`closureInfo_block`). -/

private theorem card_piledSet_add_popCount (k : Fin 16) :
    (piledSet k).card + popCount4 (grlex2bits.get k).toNat = 4 := by revert k; decide

/-- Every configuration of `p`'s block piles `numPiledKings p` suits. -/
theorem card_piledSet_globalCfg (p : SolverPosType) (i : Nat)
    (hi : i < (closureInfoOf p).numBits.toNat) :
    (piledSet (globalCfg (closureInfoOf p) i)).card = numPiledKings p := by
  have hf : (closureInfoOf p) = closureInfos.get ⟨min p.freePiles.toInt.toNat 10, by omega⟩ := rfl
  have hble : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p.freePiles.toInt.toNat 10, by omega⟩
  have hval : (globalCfg (closureInfoOf p) i).val = (closureInfoOf p).shiftValue.toNat + i :=
    globalCfg_val _ _ (by omega)
  have hblock := (closureInfo_block ⟨min p.freePiles.toInt.toNat 10, by omega⟩
    (globalCfg (closureInfoOf p) i)).1 (by rw [hval, ← hf]; omega)
  have hcard := card_piledSet_add_popCount (globalCfg (closureInfoOf p) i)
  rw [show (↑(⟨min p.freePiles.toInt.toNat 10, by omega⟩ : Fin 11) : Nat)
      = min p.freePiles.toInt.toNat 10 from rfl] at hblock
  rw [hblock] at hcard
  have hmin := numPiledKings_eq p
  omega

/-- **The shape `ComponentSound` asks for.**  Same statement as
`component_configReachable`, but with a *reachable* configuration on the left
instead of a matching state — the two `Reach`es simply compose.  What is still
missing between this and `ComponentSound` itself is the table bridge: a
`componentTable` bit at local index `i` implies `InComponent p (globalCfg ci i)`.
That is `component_run_eq` plus `component_spec_*` (whose `MaskSub … ∧ masks
differ` says precisely that the enumerated block-`f-1` configuration is
`setCfgBit` of the block-`f` one) plus `freeCellsOf_nonneg_iff` for the loop's
`usedSpace ≤ 4` test; the cardinality hypothesis is `card_piledSet_globalCfg`. -/
theorem component_kingConfigReachable (hU : KingUnpileReachable) (hP : KingPileReachable)
    {g : Globals} {p : SolverPosType} {s : State} {k k' : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hreach : KingConfigReachable g p s k)
    (hk : InComponent p k) (hk' : InComponent p k')
    (hcard : (piledSet k).card = (piledSet k').card) :
    KingConfigReachable g p s k' := by
  obtain ⟨s1, hr1, hs1⟩ := hreach
  obtain ⟨s2, hr2, hs2⟩ := component_configReachable hU hP hwf hm hs1 hk hk' hcard
  exact ⟨s2, hr1.trans hr2, hs2⟩

/-! ## The table bridge: a `componentTable` bit means `InComponent`

`component_spec_*` characterizes the table as "`MaskSub` plus the masks differ",
i.e. the enumerated block-`f-1` configuration piles a *strict* subset of the
block-`f` one.  Since the two blocks' configurations pile `f-1` and `f` suits, that
subset misses exactly one suit — so the enumerated configuration *is* `setCfgBit`
of the queried one.  Stated that way, each block is a `decide`. -/

set_option maxRecDepth 100000 in
private theorem comp_sem_98 : ∀ (T : Fin 2) (j : Fin 4),
    (componentAt (98 + T.val)).toNat.testBit j.val = true →
      ∃ il : Fin 1, T.val.testBit il.val = true ∧
        ∃ su : Suit, ¬ CfgBitSet (globalCfg (closureInfos.get (1 : Fin 11)) j.val) su ∧
          setCfgBit (globalCfg (closureInfos.get (1 : Fin 11)) j.val) su
            = globalCfg (closureInfos.get (0 : Fin 11)) il.val := by decide

set_option maxRecDepth 100000 in
private theorem comp_sem_0 : ∀ (T : Fin 16) (j : Fin 6),
    (componentAt (0 + T.val)).toNat.testBit j.val = true →
      ∃ il : Fin 4, T.val.testBit il.val = true ∧
        ∃ su : Suit, ¬ CfgBitSet (globalCfg (closureInfos.get (2 : Fin 11)) j.val) su ∧
          setCfgBit (globalCfg (closureInfos.get (2 : Fin 11)) j.val) su
            = globalCfg (closureInfos.get (1 : Fin 11)) il.val := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private theorem comp_sem_16 : ∀ (T : Fin 64) (j : Fin 4),
    (componentAt (16 + T.val)).toNat.testBit j.val = true →
      ∃ il : Fin 6, T.val.testBit il.val = true ∧
        ∃ su : Suit, ¬ CfgBitSet (globalCfg (closureInfos.get (3 : Fin 11)) j.val) su ∧
          setCfgBit (globalCfg (closureInfos.get (3 : Fin 11)) j.val) su
            = globalCfg (closureInfos.get (2 : Fin 11)) il.val := by decide

private theorem freePiles_bridge (p : SolverPosType) :
    p.freePiles.toInt.toNat = p.freePiles.toNat := rfl

/-- **The three blocks, uniformly.**  A set component bit at local index `j` comes
from a block-`f-1` configuration `il` that is `j`'s configuration with one suit
unpiled. -/
private theorem comp_bit_semantics (p : SolverPosType) (hfp1 : 1 ≤ p.freePiles.toNat)
    (hfp3 : p.freePiles.toNat ≤ 3) (T : Nat) (hT : T < 2 ^ (prevInfo p).numBits.toNat)
    (j : Nat) (hj : j < (closureInfoOf p).numBits.toNat)
    (hbit : (componentAt ((prevInfo p).offset.toNat + T)).toNat.testBit j = true) :
    ∃ il : Nat, il < (prevInfo p).numBits.toNat ∧ T.testBit il = true ∧
      ∃ su : Suit, ¬ CfgBitSet (globalCfg (closureInfoOf p) j) su ∧
        setCfgBit (globalCfg (closureInfoOf p) j) su = globalCfg (prevInfo p) il := by
  have hbr := freePiles_bridge p
  have hcases : p.freePiles.toNat = 1 ∨ p.freePiles.toNat = 2 ∨ p.freePiles.toNat = 3 := by omega
  rcases hcases with h | h | h
  · have hc : closureInfoOf p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toInt.toNat 10 = 1 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (0 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 0 by rw [h]; decide))
    rw [hc, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (0 : Fin 11)).numBits.toNat = 1 from by decide] at hT
    rw [hp, show (closureInfos.get (0 : Fin 11)).offset.toNat = 98 from by decide] at hbit
    rw [hc, hp, show (closureInfos.get (0 : Fin 11)).numBits.toNat = 1 from by decide]
    obtain ⟨il, hilbit, su, hsu, heq⟩ := comp_sem_98 ⟨T, by omega⟩ ⟨j, hj⟩ hbit
    exact ⟨il.val, il.isLt, hilbit, su, hsu, heq⟩
  · have hc : closureInfoOf p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toInt.toNat 10 = 2 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 1 by rw [h]; decide))
    rw [hc, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hj
    rw [hp, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hT
    rw [hp, show (closureInfos.get (1 : Fin 11)).offset.toNat = 0 from by decide] at hbit
    rw [hc, hp, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide]
    obtain ⟨il, hilbit, su, hsu, heq⟩ := comp_sem_0 ⟨T, by omega⟩ ⟨j, hj⟩ hbit
    exact ⟨il.val, il.isLt, hilbit, su, hsu, heq⟩
  · have hc : closureInfoOf p = closureInfos.get (3 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toInt.toNat 10 = 3 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 2 by rw [h]; decide))
    rw [hc, show (closureInfos.get (3 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hT
    rw [hp, show (closureInfos.get (2 : Fin 11)).offset.toNat = 16 from by decide] at hbit
    rw [hc, hp, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide]
    obtain ⟨il, hilbit, su, hsu, heq⟩ := comp_sem_16 ⟨T, by omega⟩ ⟨j, hj⟩ hbit
    exact ⟨il.val, il.isLt, hilbit, su, hsu, heq⟩

/-- **A set component bit means the configuration is in the component.**  The
loop's `usedSpace ≤ 4` test is `freeCellsOf ≥ 0` for the enumerated
one-suit-fewer configuration (`freeCellsOf_nonneg_iff`), which is exactly
`InComponent`'s witness. -/
theorem inComponent_of_component_bit {g : Globals} {p : SolverPosType} {comp : UInt8}
    (hb : SolverInvBase g p) (hfp1 : 1 ≤ p.freePiles.toNat) (hfp3 : p.freePiles.toNat ≤ 3)
    (hrun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hbit : BitSet comp.toUInt16 ⟨min i 15, by omega⟩) :
    InComponent p (globalCfg (closureInfoOf p) i) := by
  obtain ⟨result, hchar, hbound, hcomp⟩ := component_run_eq g p comp hfp1 hfp3 hrun
  have hcb : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p.freePiles.toInt.toNat 10, by omega⟩
  have hpb : (prevInfo p).shiftValue.toNat + (prevInfo p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min (p.freePiles.toNat - 1) 10, by omega⟩
  -- the bit, as a `testBit` of the table entry
  have hbit' : (componentAt ((prevInfo p).offset.toNat + result.toNat)).toNat.testBit i = true := by
    rw [← hcomp]
    have h := (BitSet_toNat comp.toUInt16 ⟨min i 15, by omega⟩).1 hbit
    rwa [UInt8.toNat_toUInt16,
      show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega)] at h
  obtain ⟨il, hil, hilbit, su, hsu, heq⟩ :=
    comp_bit_semantics p hfp1 hfp3 result.toNat hbound i hi hbit'
  -- and the configuration it came from fits in the cells
  refine ⟨su, hsu, ?_⟩
  rw [heq]
  exact (freeCellsOf_nonneg_iff p hb (prevInfo p) il (by omega)).2
    ((hchar il (by omega)).1 hilbit).2

/-- Outside `1 ≤ freePiles ≤ 3` the guard fails and `computeComponentKingBits`
returns `0` — no component bits, so the widening is vacuous there. -/
theorem component_eq_zero_of_range {g : Globals} {p : SolverPosType} {comp : UInt8}
    (hout : p.freePiles.toNat = 0 ∨ 4 ≤ p.freePiles.toNat)
    (hrun : EStateM.run (computeComponentKingBits p) g = .ok comp g) : comp = 0 := by
  have hfi : (p.freePiles.toInt32).toInt = (p.freePiles.toNat : Int) := uint8_toInt32_toInt _
  have hguard : ((p.freePiles.toInt32 ≥ (1 : Int32)) && (p.freePiles.toInt32 ≤ (3 : Int32)))
      = false := by
    rcases hout with h | h
    · have : ¬ ((1 : Int32) ≤ p.freePiles.toInt32) := by
        rw [Int32.le_iff_toInt_le, show ((1 : Int32)).toInt = 1 from by decide, hfi]; omega
      simp [ge_iff_le, this]
    · have : ¬ (p.freePiles.toInt32 ≤ (3 : Int32)) := by
        rw [Int32.le_iff_toInt_le, show ((3 : Int32)).toInt = 3 from by decide, hfi]; omega
      simp [this]
  rw [component_eq_explicit] at hrun
  simp only [componentExplicit, EStateM.run, bind, pure, EStateM.pure,
    hguard, Bool.false_eq_true, reduceIte] at hrun
  exact (EStateM.Result.ok.inj hrun.symm).1

/-- **`ComponentSound`, from the two physical steps.**  Everything else is now in
place: the table bridge turns each set bit into `InComponent`, `card_piledSet_globalCfg`
supplies the same-block cardinality, and out of range the table entry is `0`, so
there is no bit to move. -/
theorem componentSound_of (hU : KingUnpileReachable) (hP : KingPileReachable) :
    ComponentSound := by
  intro g p s comp i j hwf hm hrun hi hj hbi hbj hreach
  by_cases hrange : 1 ≤ p.freePiles.toNat ∧ p.freePiles.toNat ≤ 3
  · refine component_kingConfigReachable hU hP hwf hm hreach
      (inComponent_of_component_bit hm.toSolverInvBase hrange.1 hrange.2 hrun hi hbi)
      (inComponent_of_component_bit hm.toSolverInvBase hrange.1 hrange.2 hrun hj hbj) ?_
    rw [card_piledSet_globalCfg p i hi, card_piledSet_globalCfg p j hj]
  · rw [component_eq_zero_of_range (by omega) hrun,
      show ((0 : UInt8).toUInt16) = (0 : UInt16) from rfl] at hbi
    exact absurd hbi (BitSet_zero _)
