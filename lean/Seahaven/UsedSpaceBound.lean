import Seahaven.SoundnessSkeleton
import Seahaven.SolverSpecCommon

/-!
# `usedSpace` bounds the cards outside the piles

`usedSpace_ge_of_free_above` (`SolverInvariant`) says: any family of distinct real
cards that avoids `usedSpace_def`'s three counted families — resident pile cards,
foundation cards, flute interiors — is no larger than `usedSpace`.

This file discharges those three obligations for the two families a *concrete*
state carries outside the piles proper:

* the cards in cells;
* the cards on piles the solver treats as empty (the king stacks).

Every one of the three exclusions comes from the same source, `cards_count = 1`:
a card is in exactly one place, so a card in a cell or on a king pile is not
resident in a pile (hence free), not on a foundation, and not one of the physical
run cards above some boundary.

The payoff is `freeCells_ge`: at least `4 - (usedSpace - Σ king stacks)` cells are
free — the concrete counterpart of `computeKingSpaces`' refund arithmetic
(`freeCellsOf`), and the fact that discharges the free-cell preconditions of the
`MoveSim` simulation theorems.
-/

/-! ## Counting: one card, one place -/

theorem countColumn_le_countTableau (t : Fin 10 → Column) (d : Card) (i : Fin 10) :
    countColumn (t i) d ≤ countTableau t d := by
  unfold countTableau
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  simp only [List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem countCard_le_countCells (f : Fin 4 → Option Card) (d : Card) (i : Fin 4) :
    countCard (f i) d ≤ countCells f d := by
  unfold countCells
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  simp only [List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem countCells_pair_le {f : Fin 4 → Option Card} {d : Card} {i j : Fin 4} (hij : i ≠ j) :
    countCard (f i) d + countCard (f j) d ≤ countCells f d := by
  unfold countCells
  have hpair := Finset.sum_pair (f := fun k : Fin 4 => countCard (f k) d) hij
  rw [List.sum_ofFn, ← hpair]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem countFoundation_eq_zero_iff (f : Suit → Option Rank) (d : Card) :
    countFoundation f d = 0 ↔ optRankToNat (f d.suit) < rankToNat d.rank := by
  unfold countFoundation
  split <;> simp_all

theorem one_le_countCard {f : Fin 4 → Option Card} {d : Card} {i : Fin 4}
    (h : f i = some d) : 1 ≤ countCard (f i) d := by
  rw [h]; simp [countCard]

/-- A column with no card counted twice has no duplicates.  (Phrased on
`countColumn` rather than `List.count`, which would need `LawfulBEq Card`.) -/
theorem nodup_of_countColumn_le_one : ∀ (xs : List Card),
    (∀ d, countColumn xs d ≤ 1) → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hle => by
    have hsplit : ∀ d, countColumn (x :: xs) d
        = countCard (some x) d + countColumn xs d := by
      intro d; rw [countColumn, List.map_cons, List.sum_cons]; rfl
    have h1 : ∀ d, countColumn xs d ≤ 1 := by
      intro d
      have := hle d
      rw [hsplit d] at this
      omega
    refine List.nodup_cons.2 ⟨?_, nodup_of_countColumn_le_one xs h1⟩
    intro hmem
    have h2 := hle x
    have h3 := one_le_countColumn hmem
    have h4 : countCard (some x) x = 1 := by simp [countCard]
    rw [hsplit x, h4] at h2
    omega

/-- A card in a column is not covered by its foundation. -/
theorem NoDupState.foundation_lt_of_mem_column {s : State} (hnd : NoDupState s) {d : Card}
    {i : Fin 10} (hmem : d ∈ s.tableau i) :
    optRankToNat (s.foundations d.suit) < rankToNat d.rank := by
  have h1 := one_le_countColumn hmem
  have h2 := countColumn_le_countTableau s.tableau d i
  have h3 := hnd d
  unfold countState at h3
  exact (countFoundation_eq_zero_iff _ _).1 (by omega)

/-- A card in a cell is not covered by its foundation. -/
theorem NoDupState.foundation_lt_of_cell {s : State} (hnd : NoDupState s) {d : Card}
    {i : Fin 4} (hc : s.cells i = some d) :
    optRankToNat (s.foundations d.suit) < rankToNat d.rank := by
  have h1 := one_le_countCard hc
  have h2 := countCard_le_countCells s.cells d i
  have h3 := hnd d
  unfold countState at h3
  exact (countFoundation_eq_zero_iff _ _).1 (by omega)

/-- A card in a cell is in no column. -/
theorem NoDupState.not_mem_column_of_cell {s : State} (hnd : NoDupState s) {d : Card}
    {i : Fin 4} (hc : s.cells i = some d) (j : Fin 10) : d ∉ s.tableau j := by
  intro hmem
  have h1 := one_le_countColumn hmem
  have h2 := countColumn_le_countTableau s.tableau d j
  have h3 := one_le_countCard hc
  have h4 := countCard_le_countCells s.cells d i
  have h5 := hnd d
  unfold countState at h5
  omega

/-- One card occupies one cell. -/
theorem NoDupState.cell_unique {s : State} (hnd : NoDupState s) {d : Card} {i j : Fin 4}
    (hi : s.cells i = some d) (hj : s.cells j = some d) : i = j := by
  by_contra hij
  have h1 := one_le_countCard hi
  have h2 := one_le_countCard hj
  have h3 := countCells_pair_le (f := s.cells) (d := d) hij
  have h4 := hnd d
  unfold countState at h4
  omega

/-- No column repeats a card. -/
theorem NoDupState.column_nodup {s : State} (hnd : NoDupState s) (i : Fin 10) :
    (s.tableau i).Nodup := by
  refine nodup_of_countColumn_le_one _ (fun d => ?_)
  have h2 := countColumn_le_countTableau s.tableau d i
  have h3 := hnd d
  unfold countState at h3
  omega

/-! ## Cards outside the piles are free -/

/-- **A card the solver would call "not free" is physically resident**, at its own
dealt slot, in a pile of positive depth.  The contrapositive is what the counting
argument needs. -/
theorem StateMatchesSolverPos.mem_of_not_isFreeCard {g : Globals} {s : State}
    {p : SolverPosType} (hwf : WellFormedLayout g) (h : StateMatchesSolverPos g s p)
    (d : Card) (hnf : ¬ isFreeCard g p (encodeCard d)) :
    ∃ i : Fin 10, d ∈ s.tableau i ∧ 0 < (p.pileDepth.get i).toNat := by
  have hreal : IsRealCard (encodeCard d) := encodeCard_real d
  have hc64 : (encodeCard d).toNat < 64 := IsRealCard_lt64 hreal
  have hp10 : (cardPile g (encodeCard d)).toNat < 10 := hwf.pile_lt _ hreal
  set P : Fin 10 := ⟨(cardPile g (encodeCard d)).toNat, hp10⟩ with hPdef
  have hPeq : (p.pileDepth[(cardPile g (encodeCard d)).toNat]'hp10) = p.pileDepth.get P := rfl
  have hlt : (cardDepth g (encodeCard d)).toNat < (p.pileDepth.get P).toNat := by
    by_contra hge
    refine hnf (SolverSpec.isFree_of_cardDepth_ge g p hwf _ hc64 hp10 ?_)
    rw [hPeq]
    omega
  have hd6 : (p.pileDepth.get P).toNat < 6 := h.depth_lt6 P
  have hd5 : (cardDepth g (encodeCard d)).toNat < 5 := by
    omega
  obtain ⟨pos, hpos⟩ := StateMatchesLayout.card_in_pile (g := g) (s := s)
    P ⟨(cardDepth g (encodeCard d)).toNat, hd5⟩
    ⟨⟨(p.pileDepth.get P).toNat, hd6⟩, h.depth_match P, by
      exact hlt⟩
  have hround := hwf.round_trip (encodeCard d) hreal hd5
  refine ⟨P, ?_, by omega⟩
  have hcode : encodeCard ((s.tableau P).get pos) = encodeCard d := by
    rw [hpos]
    show (g.pos2card.get P).get ⟨(cardDepth g (encodeCard d)).toNat, hd5⟩ = encodeCard d
    exact hround
  rw [← encodeCard_inj hcode]
  exact List.get_mem ..

/-- A card in a cell is free. -/
theorem StateMatchesSolverPos.isFreeCard_of_cell {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : StateMatchesSolverPos g s p) {d : Card} {i : Fin 4}
    (hc : s.cells i = some d) : isFreeCard g p (encodeCard d) := by
  by_contra hnf
  obtain ⟨j, hmem, _⟩ := h.mem_of_not_isFreeCard hwf d hnf
  exact h.noDup.not_mem_column_of_cell hc j hmem

/-- A card on a pile the solver treats as empty is free. -/
theorem StateMatchesSolverPos.isFreeCard_of_empty_pile {g : Globals} {s : State}
    {p : SolverPosType} (hwf : WellFormedLayout g) (h : StateMatchesSolverPos g s p)
    {d : Card} {i : Fin 10} (hd0 : (p.pileDepth.get i).toNat = 0)
    (hmem : d ∈ s.tableau i) : isFreeCard g p (encodeCard d) := by
  by_contra hnf
  obtain ⟨j, hmemj, hdj⟩ := h.mem_of_not_isFreeCard hwf d hnf
  rw [h.noDup.pile_unique hmem hmemj] at hd0
  omega

/-! ## Cards outside the piles outrank their foundation -/

/-- The solver-side reading of "not covered by the foundation". -/
theorem StateMatchesSolverPos.aces_lt {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (d : Card)
    (hlt : optRankToNat (s.foundations d.suit) < rankToNat d.rank)
    (hs : (SUIT (encodeCard d)).toNat < 4) :
    p.aces.get ⟨(SUIT (encodeCard d)).toNat, hs⟩ < encodeCard d := by
  have hsu : suitToNat d.suit < 4 := suitToNat_lt _
  have hsuit : (SUIT (encodeCard d)).toNat = suitToNat d.suit := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat']; omega
  have hidx : (⟨(SUIT (encodeCard d)).toNat, hs⟩ : Fin 4) = finOfSuit d.suit := Fin.ext hsuit
  have hr13 : rankToNat d.rank ≤ 13 := rankBounded _
  have hf13 : optRankToNat (s.foundations d.suit) ≤ 13 := by
    cases hf : s.foundations d.suit with
    | none => simp [optRankToNat]
    | some r => simpa [optRankToNat] using rankBounded r
  rw [hidx, h.aces_match d.suit, UInt8.lt_iff_toNat_lt]
  show (CARD (UInt8.ofNat (suitToNat d.suit))
      (UInt8.ofNat (optRankToNat (s.foundations d.suit)))).toNat
    < (CARD (UInt8.ofNat (suitToNat d.suit)) (UInt8.ofNat (rankToNat d.rank))).toNat
  rw [CARD_toNat (by omega) (by omega), CARD_toNat (by omega) (by omega)]
  omega

/-! ## Cards outside the piles are not flute interiors -/

/-- **A flute-interior code is the code of a card physically in that column.**
`boundary[j] - m`, for `1 ≤ m < pileFlute[j]`, is the `m`-th card above the
boundary — which by `flute_match` is really sitting there. -/
theorem StateMatchesSolverPos.flute_interior_mem {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (j : Fin 10)
    (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidx : (p.pileDepth.get j).toNat - 1 < 5)
    (m : Nat) (hm1 : 1 ≤ m) (hm2 : m < (p.pileFlute.get j).toNat) :
    ∃ d ∈ s.tableau j, encodeCard d
      = (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ - UInt8.ofNat m := by
  obtain ⟨B, hBeq⟩ : ∃ B, (g.pos2card.get j).get
      ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ = B := ⟨_, rfl⟩
  have hfm := h.flute_match j hdj
  have hnL : (p.pileDepth.get j).toNat ≤ (s.tableau j).length := (h.depth_match j).1
  -- the flute card `m` above the boundary sits at index `L - depth - m`
  obtain ⟨idx, hidxeq⟩ : ∃ idx,
      (s.tableau j).length - (p.pileDepth.get j).toNat - m = idx := ⟨_, rfl⟩
  obtain ⟨hs, hv⟩ := flute_elem h j hdj ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ rfl
    idx (by omega) (by omega)
  rw [hBeq] at hs hv
  refine ⟨(s.tableau j)[idx], List.getElem_mem _, ?_⟩
  rw [hBeq]
  -- same suit block, value `m` lower
  have hVd : 1 ≤ (VALUE (encodeCard (s.tableau j)[idx])).toNat := by
    rw [encodeCard_VALUE]; exact rankToNat_pos _
  have hVB : (VALUE (encodeCard (s.tableau j)[idx])).toNat + m = (VALUE B).toNat := by omega
  have hmof : (UInt8.ofNat m).toNat = m := by
    rw [UInt8.toNat_ofNat']
    have := VALUE_toNat B
    omega
  have hBsub : (UInt8.ofNat m) ≤ B := by
    rw [UInt8.le_iff_toNat_le, hmof]
    have := VALUE_toNat B
    omega
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_sub_of_le _ _ hBsub, hmof]
  have h1 := SUIT_toNat (encodeCard (s.tableau j)[idx])
  have h2 := VALUE_toNat (encodeCard (s.tableau j)[idx])
  have h3 := SUIT_toNat B
  have h4 := VALUE_toNat B
  have h5 := congrArg UInt8.toNat hs
  omega

/-! ## The cards outside the piles, as one list

Collected as a `List Card` rather than a `Finset`: the length is then the count we
want by construction (`length_filterMap`/`length_flatMap`), and `Nodup` — which
`cards_count` gives — is exactly the injectivity `usedSpace_ge_of_free_above`
asks for. -/

/-- The cards sitting in cells, in cell order. -/
def cellList (s : State) : List Card := (List.finRange 4).filterMap s.cells

/-- The cards sitting on piles the solver treats as empty (the king stacks). -/
def kingList (s : State) (p : SolverPosType) : List Card :=
  ((List.finRange 10).filter
    (fun i => decide ((p.pileDepth.get i).toNat = 0))).flatMap s.tableau

/-- Everything outside the piles proper. -/
def outsideList (s : State) (p : SolverPosType) : List Card := cellList s ++ kingList s p

@[simp] theorem mem_cellList {s : State} {d : Card} :
    d ∈ cellList s ↔ ∃ i : Fin 4, s.cells i = some d := by
  simp only [cellList, List.mem_filterMap, List.mem_finRange, true_and]

@[simp] theorem mem_kingList {s : State} {p : SolverPosType} {d : Card} :
    d ∈ kingList s p ↔ ∃ i : Fin 10, (p.pileDepth.get i).toNat = 0 ∧ d ∈ s.tableau i := by
  simp only [kingList, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]

/-- **Cells are either free or hold one of `cellList`'s cards.** -/
theorem cellList_length_add_freeCells (s : State) :
    (cellList s).length + (freeCells s).length = 4 := by
  have h1 : (cellList s).length
      = (List.finRange 4).countP (fun i => (s.cells i).isSome) :=
    List.length_filterMap_eq_countP
  have h2 : (freeCells s).length
      = (List.finRange 4).countP (fun i => decide ¬ (s.cells i).isSome = true) := by
    rw [freeCells, ← List.countP_eq_length_filter]
    refine List.countP_congr (fun i _ => ?_)
    cases hc : s.cells i <;> simp
  have h3 := List.length_eq_countP_add_countP (fun i : Fin 4 => (s.cells i).isSome)
    (l := List.finRange 4)
  rw [h1, h2]
  simp only [List.length_finRange] at h3
  omega

/-- `kingList`'s length is the total size of the king stacks. -/
theorem kingList_length (s : State) (p : SolverPosType) :
    (kingList s p).length
      = (((List.finRange 10).filter
          (fun i => decide ((p.pileDepth.get i).toNat = 0))).map
        (fun i => (s.tableau i).length)).sum := by
  rw [kingList, List.length_flatMap]

theorem mem_outsideList {s : State} {p : SolverPosType} {d : Card}
    (hd : d ∈ outsideList s p) :
    (∃ i : Fin 4, s.cells i = some d) ∨
      (∃ i : Fin 10, (p.pileDepth.get i).toNat = 0 ∧ d ∈ s.tableau i) := by
  rw [outsideList, List.mem_append] at hd
  rcases hd with hc | hp
  · exact Or.inl (mem_cellList.1 hc)
  · exact Or.inr (mem_kingList.1 hp)

theorem outsideList_nodup {s : State} (hnd : NoDupState s) (p : SolverPosType) :
    (outsideList s p).Nodup := by
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · refine List.Nodup.filterMap ?_ (List.nodup_finRange 4)
    intro i i' d hd hd'
    exact hnd.cell_unique (Option.mem_def.1 hd) (Option.mem_def.1 hd')
  · refine List.nodup_flatMap.2 ⟨fun i _ => hnd.column_nodup i, ?_⟩
    refine List.Pairwise.imp ?_ ((List.nodup_finRange 10).filter _)
    intro i j hij d hdi hdj
    exact hij (hnd.pile_unique hdi hdj)
  · intro d hd e he hde
    subst hde
    obtain ⟨i, hi⟩ := mem_cellList.1 hd
    obtain ⟨j, _, hj⟩ := mem_kingList.1 he
    exact hnd.not_mem_column_of_cell hi j hj

/-! ## The bound -/

/-- **Every card outside the piles is free, above its foundation, and not a flute
interior** — the three obligations of `usedSpace_ge_of_free_above`, all three from
`cards_count = 1`. -/
theorem StateMatchesSolverPos.usedSpace_ge_outside {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p) :
    ((outsideList s p).length : Int) ≤ p.usedSpace.toInt := by
  have hnd := h.noDup
  have hnodup := outsideList_nodup hnd p
  -- each listed card is in a cell or on an empty pile
  have hcases : ∀ k : Fin (outsideList s p).length,
      (∃ i : Fin 4, s.cells i = some (outsideList s p)[k.val]) ∨
      (∃ i : Fin 10, (p.pileDepth.get i).toNat = 0 ∧
        (outsideList s p)[k.val] ∈ s.tableau i) :=
    fun k => mem_outsideList (List.getElem_mem _)
  refine usedSpace_ge_of_free_above hwf hb
    (fun k : Fin (outsideList s p).length => encodeCard (outsideList s p)[k.val])
    ?_ (fun k => encodeCard_real _) ?_ ?_ ?_
  · -- injective: `Nodup` plus `encodeCard`
    intro k1 k2 heq
    exact Fin.ext ((hnodup.getElem_inj_iff).1 (encodeCard_inj heq))
  · -- free
    intro k
    rcases hcases k with ⟨i, hi⟩ | ⟨i, hd0, hi⟩
    · exact h.isFreeCard_of_cell hwf hi
    · exact h.isFreeCard_of_empty_pile hwf hd0 hi
  · -- above the foundation
    intro k hs
    refine h.aces_lt _ ?_ hs
    rcases hcases k with ⟨i, hi⟩ | ⟨_, _, hi⟩
    · exact hnd.foundation_lt_of_cell hi
    · exact hnd.foundation_lt_of_mem_column hi
  · -- not a flute interior
    intro k j hdj m hm1 hm2 heq
    have hidx : (p.pileDepth.get j).toNat - 1 < 5 := by
      have h6 := h.depth_lt6 j
      omega
    obtain ⟨e, hemem, hecode⟩ := h.flute_interior_mem j hdj hidx m hm1 hm2
    have hcard : e = (outsideList s p)[k.val] := encodeCard_inj (hecode.trans heq)
    rw [hcard] at hemem
    rcases hcases k with ⟨i, hi⟩ | ⟨i, hd0, hi⟩
    · exact hnd.not_mem_column_of_cell hi j hemem
    · rw [hnd.pile_unique hi hemem] at hd0
      omega

/-- **The concrete free-cell bound.**  `usedSpace` pays for the cards in cells and
for the king stacks together, so whatever it does not spend on king stacks bounds
the used cells — i.e. at least `4 - (usedSpace - Σ king stacks)` cells are free.
This is the concrete counterpart of `computeKingSpaces`' refund arithmetic. -/
theorem StateMatchesSolverPos.freeCells_ge {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p) :
    (4 : Int) - (p.usedSpace.toInt - ((kingList s p).length : Int))
      ≤ ((freeCells s).length : Int) := by
  have h1 := h.usedSpace_ge_outside hwf hb
  have h2 := cellList_length_add_freeCells s
  simp only [outsideList, List.length_append] at h1
  omega

/-! ## The king-configuration form

`computeKingSpaces` charges a configuration `kingRefund p k` — for every suit the
configuration puts on a pile, its whole freed stack.  A state realizing `k` really
does carry those cards on columns (`king_pile_contents`), on *distinct* columns
(the assignment is injective), so the refund is at most the total king-stack size
and the bound above applies verbatim. -/

private theorem finOfSuit_natToSuit (su : Fin 4) : finOfSuit (natToSuit su) = su :=
  Fin.ext (suitToNat_natToSuit su)

private theorem kingRefund_eq_sum (p : SolverPosType) (k : Fin 16) :
    kingRefund p k = ∑ su : Fin 4,
      (if ¬ CfgBitSet k (natToSuit su) then ((13 : Int) - (VALUE (p.kings.get su)).toNat)
        else 0) := by
  rw [kingRefund, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl (fun su _ => ?_)
  have hb : (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0 ↔ ¬ CfgBitSet k (natToSuit su) := by
    unfold CfgBitSet
    rw [suitToNat_natToSuit]
    omega
  by_cases hc : (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0
  · rw [if_pos hc, if_pos (hb.1 hc)]
  · rw [if_neg hc, if_neg (fun hn => hc (hb.2 hn))]

/-- **The configuration's refund is really on the columns.** -/
theorem StateMatchesKingConfig.kingRefund_le {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} (hk : StateMatchesKingConfig g s p k) :
    kingRefund p k ≤ ((kingList s p).length : Int) := by
  obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
  have hm := hk.toMatches
  -- per suit: the refund equals the length of the column that suit owns
  have hterm : ∀ su : Fin 4,
      (if ¬ CfgBitSet k (natToSuit su) then ((13 : Int) - (VALUE (p.kings.get su)).toNat)
        else 0)
      = ((if ¬ CfgBitSet k (natToSuit su)
            then (s.tableau ((assign (natToSuit su)).getD 0)).length else 0 : Nat) : Int) := by
    intro su
    by_cases hbit : CfgBitSet k (natToSuit su)
    · rw [if_neg (by simpa using hbit), if_neg (by simpa using hbit)]
      simp
    · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff (natToSuit su)).2 hbit)
      obtain ⟨hd0, hstack⟩ := hown (natToSuit su) i hi
      rw [if_pos hbit, if_pos hbit, hi, Option.getD_some]
      rcases hstack with ⟨d, hd, hdsuit, _⟩ | ⟨hnil, h13⟩
      · have hc := (hm.king_pile_contents i hd0 (Option.mem_def.1 hd)).1
        rw [hdsuit, finOfSuit_natToSuit] at hc
        have h13 : (VALUE (p.kings.get su)).toNat ≤ 13 := by omega
        omega
      · rw [hnil, finOfSuit_natToSuit] at *
        simp only [List.length_nil, Nat.cast_zero]
        omega
  rw [kingRefund_eq_sum, Finset.sum_congr rfl (fun su _ => hterm su), ← Nat.cast_sum]
  refine Nat.cast_le.2 ?_
  -- drop the zero terms, then compare with the sum over all solver-empty piles
  rw [← Finset.sum_filter]
  have hinjOn : Set.InjOn (fun su : Fin 4 => (assign (natToSuit su)).getD 0)
      ↑(Finset.univ.filter (fun su : Fin 4 => ¬ CfgBitSet k (natToSuit su))) := by
    intro su hsu su' hsu' heq
    have h1 : ¬ CfgBitSet k (natToSuit su) :=
      (Finset.mem_filter.1 (Finset.mem_coe.1 hsu)).2
    have h2 : ¬ CfgBitSet k (natToSuit su') :=
      (Finset.mem_filter.1 (Finset.mem_coe.1 hsu')).2
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff (natToSuit su)).2 h1)
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 ((hiff (natToSuit su')).2 h2)
    have hb : (assign (natToSuit su)).getD 0 = (assign (natToSuit su')).getD 0 := heq
    rw [hi, hi', Option.getD_some, Option.getD_some] at hb
    have := hinj (natToSuit su) (natToSuit su') i hi (hb ▸ hi')
    exact Fin.ext (by rw [← suitToNat_natToSuit su, ← suitToNat_natToSuit su', this])
  rw [← Finset.sum_image (f := fun i : Fin 10 => (s.tableau i).length) hinjOn]
  have hsubset : Finset.image (fun su : Fin 4 => (assign (natToSuit su)).getD 0)
      (Finset.univ.filter (fun su : Fin 4 => ¬ CfgBitSet k (natToSuit su)))
      ⊆ Finset.univ.filter (fun i : Fin 10 => (p.pileDepth.get i).toNat = 0) := by
    intro i hi
    obtain ⟨su, hsu, rfl⟩ := Finset.mem_image.1 hi
    have h1 : ¬ CfgBitSet k (natToSuit su) := (Finset.mem_filter.1 hsu).2
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 ((hiff (natToSuit su)).2 h1)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hj, Option.getD_some]
    exact (hown (natToSuit su) j hj).1
  refine le_trans (Finset.sum_le_sum_of_subset hsubset) ?_
  rw [kingList_length]
  refine le_of_eq ?_
  simp [Finset.sum, Finset.filter, Finset.univ, Fintype.elems, Multiset.filter]

/-- **The free cells a realized king configuration guarantees.**  `freeCellsOf` —
the quantity `computeKingSpaces` compares against `fluteLen` — never overstates
the cells actually free.  This is what discharges the free-cell preconditions of
the `MoveSim` phase-1 theorems once `KingSpacesSpec`/`solverGetMovable` supply the
abstract affordability. -/
theorem StateMatchesKingConfig.freeCellsOf_le {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k) :
    freeCellsOf p k ≤ ((freeCells s).length : Int) := by
  have h1 := hk.toMatches.freeCells_ge hwf hb
  have h2 := hk.kingRefund_le
  unfold freeCellsOf
  omega
