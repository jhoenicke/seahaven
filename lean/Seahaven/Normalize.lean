import Seahaven.FoundationMoves

/-!
# Normalizing a position by harmless moves

The solver reasons about a *normalized* position: one in which no card can be
advanced to its foundation and no card sitting in a cell can be dropped back
onto a pile.  `SolverConvertFromPilesKings` performs exactly this normalization
internally, so before any statement relating a `State` to a `SolverPosType` can
be proved, the `State` side needs the same notion.

This file defines the normalizing steps (`NormStep` = foundation move or
cell→pile move), shows that each of them is *harmless* in both directions, and
shows that normalization terminates.

The two harmlessness arguments are wildly asymmetric:

* A foundation move is irreversible, so `Solvable s → Solvable t` needs the full
  limited-confluence development of `Seahaven.FoundationMoves`.
* A cell→pile move is *immediately revertible* — `dropCol` only ever places a
  card on `nextCard card`, and the cell it came from is empty afterwards — so
  `Solvable s → Solvable t` is a single application of `Solvable.step`.

The converse direction, `Solvable t → Solvable s`, is trivial for both: the
normalizing moves are legal moves, so any solution from `t` can be prefixed with
them.
-/

/-! ## A generic reachability layer -/

/-- One arbitrary legal move. -/
def MoveStep (s t : State) : Prop := ∃ m : Move, applyMove s m = some t

/-- `Reach s t` : `t` is reachable from `s` by legal moves. -/
abbrev Reach : State → State → Prop := Relation.ReflTransGen MoveStep

theorem MoveStep.toReach {s t : State} (h : MoveStep s t) : Reach s t :=
  Relation.ReflTransGen.single h

/-- Anything reachable by legal moves can be prefixed onto a solution. -/
theorem Solvable.of_reach {s t : State} (h : Reach s t) : Solvable t → Solvable s := by
  induction h with
  | refl => exact id
  | tail _ hbc ih =>
    intro hc
    obtain ⟨m, hm⟩ := hbc
    exact ih (Solvable.step m hm hc)

theorem reach_of_foldl {s t : State} {ms : List Move}
    (h : List.foldl applyMoveOpt (some s) ms = some t) : Reach s t := by
  induction ms generalizing s with
  | nil => simp at h; subst h; exact Relation.ReflTransGen.refl
  | cons m rest ih =>
    rw [List.foldl_cons] at h
    cases hm : applyMove s m with
    | none =>
      rw [show applyMoveOpt (some s) m = applyMove s m from rfl, hm,
        foldl_applyMoveOpt_none] at h
      simp at h
    | some s2 =>
      rw [show applyMoveOpt (some s) m = applyMove s m from rfl, hm] at h
      exact Relation.ReflTransGen.head ⟨m, hm⟩ (ih h)

theorem foldl_of_reach {s t : State} (h : Reach s t) :
    ∃ ms : List Move, List.foldl applyMoveOpt (some s) ms = some t := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hbc ih =>
    obtain ⟨ms, hms⟩ := ih
    obtain ⟨m, hm⟩ := hbc
    exact ⟨ms ++ [m], by rw [List.foldl_append, hms]; exact hm⟩

theorem NoDupState.reach {s t : State} (h : NoDupState s) (hr : Reach s t) :
    NoDupState t := by
  induction hr with
  | refl => exact h
  | tail _ hbc ih => obtain ⟨m, hm⟩ := hbc; exact ih.applyMove hm

/-! ## Normalizing steps -/

/-- Move a card out of a cell onto a *non-empty* pile.

Cell→empty-pile moves are deliberately excluded: with two empty piles a king in
a cell has two irreconcilable destinations, which would destroy any hope of
unique normal forms.  Nothing downstream needs them — the abstract model counts
a king stack in cells and a king stack on an empty pile identically. -/
def CPStep (s t : State) : Prop :=
  ∃ (i : Fin 4) (q : Fin 10), s.tableau q ≠ [] ∧
    applyMove s ⟨Position.cell i, Position.pile q⟩ = some t

/-- A single normalizing step: advance a foundation, or return a card from a
cell to a pile. -/
def NormStep (s t : State) : Prop := FMStep s t ∨ CPStep s t

abbrev NormReach : State → State → Prop := Relation.ReflTransGen NormStep

/-- A normalized state admits no normalizing step. -/
def Normalized (s : State) : Prop := ∀ t, ¬ NormStep s t

theorem NormStep.toMoveStep {s t : State} (h : NormStep s t) : MoveStep s t := by
  rcases h with ⟨p, hp⟩ | ⟨i, q, _, hq⟩
  · exact ⟨_, hp⟩
  · exact ⟨_, hq⟩

theorem NormReach.toReach {s t : State} (h : NormReach s t) : Reach s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.toMoveStep

/-! ## Harmlessness -/

/-- The key asymmetry: a cell→pile move can always be taken back.  `dropCol`
only ever places a card on `nextCard card`, so the card is on top of the
destination pile afterwards, and the cell it came from is empty. -/
theorem CPStep.revert {s t : State} (h : CPStep s t) :
    ∃ m : Move, applyMove t m = some s := by
  obtain ⟨i, q, _, hm⟩ := h
  refine ⟨⟨Position.pile q, Position.cell i⟩, ?_⟩
  rw [applyMove_eq] at hm ⊢
  obtain ⟨c, s0, htake, hdrop⟩ := hm
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨hcell, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨hhead, rfl⟩ := hdrop
  refine ⟨c, updateCell s i none, ?_, ?_⟩
  · simp only [takeFromPosition, takeFromCol_eq]
    exact ⟨(updateCell s i none).tableau q, by simp, by
      apply State.ext' <;> simp [update2, update_self]⟩
  · simp only [dropPosition, dropCell_eq]
    refine ⟨by simp, ?_⟩
    apply State.ext' <;> simp [update2, ← hcell, update_self]

theorem CPStep.preserves_Solvable {s t : State} (h : CPStep s t) (hs : Solvable s) :
    Solvable t := by
  obtain ⟨m, hm⟩ := h.revert
  exact Solvable.step m hm hs

theorem FMStep.preserves_Solvable {s t : State} (hnd : NoDupState s) (h : FMStep s t)
    (hs : Solvable s) : Solvable t :=
  hs.of_fmReach hnd (Relation.ReflTransGen.single h)

theorem NormStep.preserves_Solvable {s t : State} (hnd : NoDupState s) (h : NormStep s t)
    (hs : Solvable s) : Solvable t := by
  rcases h with h | h
  · exact FMStep.preserves_Solvable hnd h hs
  · exact h.preserves_Solvable hs

theorem NoDupState.normReach {s t : State} (h : NoDupState s) (hr : NormReach s t) :
    NoDupState t :=
  h.reach hr.toReach

theorem NormReach.preserves_Solvable {s t : State} (hnd : NoDupState s)
    (h : NormReach s t) (hs : Solvable s) : Solvable t := by
  induction h with
  | refl => exact hs
  | @tail b c hsb hbc ih => exact hbc.preserves_Solvable (hnd.normReach hsb) ih

/-- The easy converse: normalizing moves are legal moves, so a solution from the
normal form extends to a solution from the original state. -/
theorem NormReach.reflect_Solvable {s t : State} (h : NormReach s t) (ht : Solvable t) :
    Solvable s :=
  Solvable.of_reach h.toReach ht

theorem Solvable.iff_normReach {s t : State} (hnd : NoDupState s) (h : NormReach s t) :
    Solvable s ↔ Solvable t :=
  ⟨h.preserves_Solvable hnd, h.reflect_Solvable⟩

/-! ## Unfolding `Normalized` -/

theorem Normalized.no_fm {s : State} (h : Normalized s) (p : Position) :
    applyMove s ⟨p, Position.foundation⟩ = none := by
  cases hm : applyMove s ⟨p, Position.foundation⟩ with
  | none => rfl
  | some t => exact (h t (Or.inl ⟨p, hm⟩)).elim

theorem Normalized.no_cp {s : State} (h : Normalized s) (i : Fin 4) (q : Fin 10)
    (hne : s.tableau q ≠ []) :
    applyMove s ⟨Position.cell i, Position.pile q⟩ = none := by
  cases hm : applyMove s ⟨Position.cell i, Position.pile q⟩ with
  | none => rfl
  | some t => exact (h t (Or.inr ⟨i, q, hne, hm⟩)).elim

/-- The positive reading of `Normalized`: no card in a cell is ready for its
foundation or droppable on a pile, and no exposed tableau card is ready for its
foundation. -/
theorem normalized_iff {s : State} : Normalized s ↔
    ((∀ (i : Fin 4) (c : Card), s.cells i = some c →
        some c.rank ≠ nextRank (s.foundations c.suit) ∧
        ∀ q : Fin 10, s.tableau q ≠ [] → (s.tableau q).head? ≠ nextCard c) ∧
     (∀ (q : Fin 10) (c : Card) (rest : Column), s.tableau q = c :: rest →
        some c.rank ≠ nextRank (s.foundations c.suit))) := by
  constructor
  · intro h
    refine ⟨fun i c hc => ⟨?_, ?_⟩, ?_⟩
    · intro hready
      have hnf := h.no_fm (Position.cell i)
      unfold applyMove at hnf
      simp only [takeFromPosition, takeFromCell, hc, dropPosition, dropFoundation,
        updateCell_foundations, if_pos hready] at hnf
      simp at hnf
    · intro q hne hhead
      have hnc := h.no_cp i q hne
      unfold applyMove at hnc
      simp only [takeFromPosition, takeFromCell, hc, dropPosition, dropCol,
        updateCell_tableau, if_pos hhead] at hnc
      simp at hnc
    · intro q c rest hcol hready
      have hnf := h.no_fm (Position.pile q)
      unfold applyMove at hnf
      simp only [takeFromPosition, takeFromCol, hcol, dropPosition, dropFoundation,
        updateColumn_foundations, if_pos hready] at hnf
      simp at hnf
  · rintro ⟨hcell, hpile⟩ t hstep
    rcases hstep with ⟨p, hp⟩ | ⟨i, q, hne, hq⟩
    · rw [applyMove_eq] at hp
      obtain ⟨c, s0, htake, hdrop⟩ := hp
      simp only [dropPosition, dropFoundation_eq] at hdrop
      obtain ⟨hready, _⟩ := hdrop
      rw [takeFromPosition_foundations htake] at hready
      cases p with
      | foundation => simp [takeFromPosition] at htake
      | cell i =>
        rw [takeFromPosition, takeFromCell_eq] at htake
        exact (hcell i c htake.1).1 hready
      | pile q =>
        rw [takeFromPosition, takeFromCol_eq] at htake
        obtain ⟨rest, hcol, _⟩ := htake
        exact hpile q c rest hcol hready
    · rw [applyMove_eq] at hq
      obtain ⟨c, s0, htake, hdrop⟩ := hq
      simp only [takeFromPosition, takeFromCell_eq] at htake
      obtain ⟨hc, rfl⟩ := htake
      simp only [dropPosition, dropCol_eq] at hdrop
      obtain ⟨hhead, _⟩ := hdrop
      exact (hcell i c hc).2 q hne (by simpa using hhead)

/-! ## Normalization terminates -/

def cellCount (s : State) : Nat :=
  (List.ofFn fun i : Fin 4 => if s.cells i = none then 0 else 1).sum

def tableauCount (s : State) : Nat :=
  (List.ofFn fun p : Fin 10 => (s.tableau p).length).sum

/-- Every normalizing step strictly decreases this: a card leaving a cell is
worth 2, a card leaving the tableau is worth 1, so cell→pile still loses 1. -/
def normMeasure (s : State) : Nat := 2 * cellCount s + tableauCount s

theorem cellCount_updateCell (s : State) (i : Fin 4) (v : Option Card) :
    cellCount (updateCell s i v) + (if s.cells i = none then 0 else 1)
      = cellCount s + (if v = none then 0 else 1) := by
  unfold cellCount
  have heq : ∀ j : Fin 4, (if (updateCell s i v).cells j = none then 0 else 1)
      = update (fun j => if s.cells j = none then 0 else 1) i
          (if v = none then 0 else 1) j := by
    intro j; simp only [updateCell_cells, update]; split <;> simp_all
  simp only [heq]
  exact updateSum (fun j => if s.cells j = none then 0 else 1) i (if v = none then 0 else 1)

theorem tableauCount_updateColumn (s : State) (p : Fin 10) (col : Column) :
    tableauCount (updateColumn s p col) + (s.tableau p).length
      = tableauCount s + col.length := by
  unfold tableauCount
  have heq : ∀ j : Fin 10, ((updateColumn s p col).tableau j).length
      = update (fun j => (s.tableau j).length) p col.length j := by
    intro j; simp only [updateColumn_tableau, update]; split <;> simp_all
  simp only [heq]
  exact updateSum (fun j => (s.tableau j).length) p col.length

@[simp] theorem cellCount_updateColumn (s : State) (p : Fin 10) (col : Column) :
    cellCount (updateColumn s p col) = cellCount s := rfl
@[simp] theorem tableauCount_updateCell (s : State) (i : Fin 4) (v : Option Card) :
    tableauCount (updateCell s i v) = tableauCount s := rfl
@[simp] theorem cellCount_updateFoundation (s : State) (c : Card) :
    cellCount (updateFoundation s c) = cellCount s := rfl
@[simp] theorem tableauCount_updateFoundation (s : State) (c : Card) :
    tableauCount (updateFoundation s c) = tableauCount s := rfl

theorem FMStep.measure_lt {s t : State} (h : FMStep s t) :
    normMeasure t < normMeasure s := by
  obtain ⟨p, hp⟩ := h
  rw [applyMove_eq] at hp
  obtain ⟨c, s0, htake, hdrop⟩ := hp
  simp only [dropPosition, dropFoundation_eq] at hdrop
  obtain ⟨_, rfl⟩ := hdrop
  unfold normMeasure
  cases p with
  | foundation => simp [takeFromPosition] at htake
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at htake
    obtain ⟨hc, rfl⟩ := htake
    have h1 := cellCount_updateCell s i none
    simp only [hc, cellCount_updateFoundation, tableauCount_updateFoundation,
      tableauCount_updateCell] at h1 ⊢
    simp at h1
    omega
  | pile q =>
    rw [takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest, hcol, rfl⟩ := htake
    have h1 := tableauCount_updateColumn s q rest
    simp only [hcol, cellCount_updateFoundation, tableauCount_updateFoundation,
      cellCount_updateColumn, List.length_cons] at h1 ⊢
    omega

theorem CPStep.measure_lt {s t : State} (h : CPStep s t) :
    normMeasure t < normMeasure s := by
  obtain ⟨i, q, _, hm⟩ := h
  rw [applyMove_eq] at hm
  obtain ⟨c, s0, htake, hdrop⟩ := hm
  simp only [takeFromPosition, takeFromCell_eq] at htake
  obtain ⟨hc, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨_, rfl⟩ := hdrop
  unfold normMeasure
  have h1 := cellCount_updateCell s i none
  have h2 := tableauCount_updateColumn (updateCell s i none) q
    (c :: (updateCell s i none).tableau q)
  simp only [hc, cellCount_updateColumn, tableauCount_updateCell, updateCell_tableau,
    List.length_cons] at h1 h2 ⊢
  simp at h1
  omega

theorem NormStep.measure_lt {s t : State} (h : NormStep s t) :
    normMeasure t < normMeasure s := by
  rcases h with h | h
  · exact h.measure_lt
  · exact h.measure_lt

theorem NormReach.measure_le {s t : State} (h : NormReach s t) :
    normMeasure t ≤ normMeasure s := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (le_of_lt hbc.measure_lt) ih

/-- Every state has a normal form, reachable by harmless moves. -/
theorem exists_normalForm (s : State) : ∃ t, NormReach s t ∧ Normalized t := by
  suffices H : ∀ n s, normMeasure s ≤ n → ∃ t, NormReach s t ∧ Normalized t from
    H (normMeasure s) s le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs
    refine ⟨s, Relation.ReflTransGen.refl, fun t hst => ?_⟩
    have := hst.measure_lt
    omega
  | succ n ih =>
    intro s hs
    by_cases hn : Normalized s
    · exact ⟨s, Relation.ReflTransGen.refl, hn⟩
    · obtain ⟨t, hst⟩ : ∃ t, NormStep s t := by
        by_contra hcon
        exact hn (fun t hst => hcon ⟨t, hst⟩)
      have hlt := hst.measure_lt
      obtain ⟨u, hru, hnu⟩ := ih t (by omega)
      exact ⟨u, Relation.ReflTransGen.head hst hru, hnu⟩

/-- **Normalization is free.**  Any solvable position has a normalized position
reachable from it that is still solvable. -/
theorem Solvable.normalize {s : State} (hnd : NoDupState s) (hs : Solvable s) :
    ∃ t, NormReach s t ∧ Normalized t ∧ Solvable t := by
  obtain ⟨t, hr, hn⟩ := exists_normalForm s
  exact ⟨t, hr, hn, hr.preserves_Solvable hnd hs⟩

/-! ## A decidable twin, for `#eval` sanity checks -/

def cellOK (s : State) (i : Fin 4) : Bool :=
  match s.cells i with
  | none => true
  | some c =>
      (!(decide (some c.rank = nextRank (s.foundations c.suit)))) &&
      ((List.finRange 10).all fun q =>
        match s.tableau q with
        | [] => true
        | top :: _ => !(decide (some top = nextCard c)))

def pileOK (s : State) (q : Fin 10) : Bool :=
  match s.tableau q with
  | [] => true
  | c :: _ => !(decide (some c.rank = nextRank (s.foundations c.suit)))

def normalizedB (s : State) : Bool :=
  ((List.finRange 4).all (cellOK s)) && ((List.finRange 10).all (pileOK s))

theorem cellOK_iff (s : State) (i : Fin 4) : cellOK s i = true ↔
    ∀ c : Card, s.cells i = some c →
      some c.rank ≠ nextRank (s.foundations c.suit) ∧
      ∀ q : Fin 10, s.tableau q ≠ [] → (s.tableau q).head? ≠ nextCard c := by
  unfold cellOK
  cases hc : s.cells i with
  | none => simp
  | some c =>
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
      Bool.not_eq_true', decide_eq_false_iff_not, Option.some.injEq, forall_eq']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q hne => ?_⟩
      have hq2 := h2 q
      cases hq : s.tableau q with
      | nil => exact absurd hq hne
      | cons top rest => rw [hq] at hq2; simpa using hq2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q => ?_⟩
      cases hq : s.tableau q with
      | nil => simp
      | cons top rest =>
        have := h2 q (by rw [hq]; simp)
        rw [hq] at this
        simpa using this

theorem pileOK_iff (s : State) (q : Fin 10) : pileOK s q = true ↔
    ∀ (c : Card) (rest : Column), s.tableau q = c :: rest →
      some c.rank ≠ nextRank (s.foundations c.suit) := by
  unfold pileOK
  cases hq : s.tableau q with
  | nil => simp
  | cons c rest =>
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · intro h c' rest' hc'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hc'
      exact h
    · intro h; exact h c rest rfl

theorem normalizedB_iff (s : State) : normalizedB s = true ↔ Normalized s := by
  rw [normalized_iff]
  simp only [normalizedB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, cellOK_iff, pileOK_iff]

instance : DecidablePred Normalized :=
  fun s => decidable_of_iff _ (normalizedB_iff s)
