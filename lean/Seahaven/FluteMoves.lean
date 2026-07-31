import Seahaven.Normalize

/-!
# Moving a flute

The solver moves an entire *flute* — a maximal accessible descending same-suit
run — in a single abstract step, charging `fluteLen - 1` free cells for a
pile-to-pile move.  The rules of the game only ever move one card at a time, so
one abstract move has to be realized by `2L - 1` concrete moves: park the `L-1`
cards above the boundary card into free cells, move the boundary card, then drop
the parked cards back on top of it.

This file builds exactly that move list and proves it runs.  It is deliberately
independent of the solver's layout tables: everything is phrased on
`Rules.State`.

Orientation reminder: the *head* of a `Column` is the accessible top card, and
`dropCol` places a card `x` only on `nextCard x`.  So values increase as you go
deeper, and a run reads `[c-(L-1), …, c-1, c]` from top to bottom — the boundary
card `c` is the deepest and highest.
-/

/-! ## Runs -/

/-- Consecutive cards ascend by one — the shape `dropCol` builds and the shape a
flute has. -/
def IsRun : List Card → Prop
  | [] => True
  | x :: l => (∀ y ∈ l.head?, nextCard x = some y) ∧ IsRun l

theorem IsRun.tail {x : Card} {l : List Card} (h : IsRun (x :: l)) : IsRun l := h.2

theorem IsRun.head {x : Card} {l : List Card} (h : IsRun (x :: l)) :
    ∀ y ∈ l.head?, nextCard x = some y := h.1

theorem head?_append_cons (l : List Card) (c : Card) (r : Column) :
    (l ++ c :: r).head? = (l ++ [c]).head? := by
  cases l <;> simp

/-! ## Free cells -/

def freeCells (s : State) : List (Fin 4) :=
  (List.finRange 4).filter (fun i => s.cells i = none)

theorem freeCells_nodup (s : State) : (freeCells s).Nodup :=
  (List.nodup_finRange 4).filter _

@[simp] theorem mem_freeCells {s : State} {i : Fin 4} :
    i ∈ freeCells s ↔ s.cells i = none := by
  simp [freeCells]

/-- Pick `k` distinct free cells, whenever there are at least `k` of them. -/
theorem exists_free_cells {s : State} {k : Nat} (h : k ≤ (freeCells s).length) :
    ∃ cells : List (Fin 4), cells.Nodup ∧ cells.length = k ∧
      ∀ i ∈ cells, s.cells i = none := by
  refine ⟨(freeCells s).take k, (freeCells_nodup s).sublist (List.take_sublist _ _), ?_, ?_⟩
  · simp [h]
  · intro i hi
    exact mem_freeCells.1 (List.mem_of_mem_take hi)

/-! ## Cells holding a list of cards -/

/-- `HoldsCards f cells cards`: the listed cells hold exactly `cards`, in order.
Phrased on the cell function rather than the whole `State` so that it can be
rewritten along `u.cells = t.cells`. -/
def HoldsCards (f : Fin 4 → Option Card) : List (Fin 4) → List Card → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | i :: is, x :: xs => f i = some x ∧ HoldsCards f is xs

theorem HoldsCards.length {f : Fin 4 → Option Card} :
    ∀ {cells : List (Fin 4)} {cards : List Card}, HoldsCards f cells cards →
      cells.length = cards.length
  | [], [], _ => rfl
  | _ :: _, [], h => h.elim
  | [], _ :: _, h => h.elim
  | _ :: is, _ :: xs, h => by simpa using HoldsCards.length h.2

/-! ## The move lists -/

/-- Park the top `cells.length` cards of pile `a`, one per cell, in order. -/
def parkMoves (a : Fin 10) : List (Fin 4) → List Move
  | [] => []
  | i :: is => ⟨Position.pile a, Position.cell i⟩ :: parkMoves a is

/-- Return the parked cards onto pile `b`.  The *first* cell was parked first and
so must be returned last, hence the recursion appends. -/
def unparkMoves (b : Fin 10) : List (Fin 4) → List Move
  | [] => []
  | i :: is => unparkMoves b is ++ [⟨Position.cell i, Position.pile b⟩]

/-- The full realization of one abstract flute move from pile `a` to pile `b`. -/
def fluteMoves (a b : Fin 10) (cells : List (Fin 4)) : List Move :=
  parkMoves a cells ++ ⟨Position.pile a, Position.pile b⟩ :: unparkMoves b cells

@[simp] theorem parkMoves_length (a : Fin 10) (cells : List (Fin 4)) :
    (parkMoves a cells).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons i is ih => simp [parkMoves, ih]

@[simp] theorem unparkMoves_length (b : Fin 10) (cells : List (Fin 4)) :
    (unparkMoves b cells).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons i is ih => simp [unparkMoves, ih]

@[simp] theorem fluteMoves_length (a b : Fin 10) (cells : List (Fin 4)) :
    (fluteMoves a b cells).length = 2 * cells.length + 1 := by
  simp [fluteMoves]; omega

/-! ## Parking -/

theorem run_parkMoves {s : State} {a : Fin 10} {cells : List (Fin 4)} {top rest : Column}
    (hcol : s.tableau a = top ++ rest)
    (hlen : cells.length = top.length)
    (hnd : cells.Nodup)
    (hfree : ∀ i ∈ cells, s.cells i = none) :
    ∃ t : State,
      List.foldl applyMoveOpt (some s) (parkMoves a cells) = some t ∧
      t.tableau a = rest ∧
      (∀ q, q ≠ a → t.tableau q = s.tableau q) ∧
      t.foundations = s.foundations ∧
      HoldsCards t.cells cells top ∧
      (∀ i, i ∉ cells → t.cells i = s.cells i) := by
  induction cells generalizing s top with
  | nil =>
    cases top with
    | nil =>
      exact ⟨s, rfl, by simpa using hcol, fun q _ => rfl, rfl, trivial, fun i _ => rfl⟩
    | cons x xs => simp at hlen
  | cons i is ih =>
    cases top with
    | nil => simp at hlen
    | cons x xs =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hi, hnd⟩ := hnd
      have hcell : s.cells i = none := hfree i (by simp)
      have hstep : applyMove s ⟨Position.pile a, Position.cell i⟩
          = some (updateCell (updateColumn s a (xs ++ rest)) i (some x)) := by
        rw [applyMove_eq]
        refine ⟨x, updateColumn s a (xs ++ rest), ?_, ?_⟩
        · simp only [takeFromPosition, takeFromCol_eq]
          exact ⟨xs ++ rest, by simpa using hcol, rfl⟩
        · simp only [dropPosition, dropCell_eq]
          exact ⟨by simpa using hcell, trivial⟩
      obtain ⟨t, hfold, hta, htq, htf, hhold, hoth⟩ :=
        ih (s := updateCell (updateColumn s a (xs ++ rest)) i (some x)) (top := xs)
          (by simp) (by simpa using hlen) hnd
          (fun i' hi' => by
            have hne : i ≠ i' := fun h => hi (h ▸ hi')
            simpa [hne] using hfree i' (List.mem_cons_of_mem _ hi'))
      refine ⟨t, ?_, hta, ?_, ?_, ⟨?_, hhold⟩, ?_⟩
      · rw [parkMoves, List.foldl_cons,
          show applyMoveOpt (some s) ⟨Position.pile a, Position.cell i⟩
            = applyMove s ⟨Position.pile a, Position.cell i⟩ from rfl, hstep]
        exact hfold
      · intro q hq; rw [htq q hq]; simp [Ne.symm hq]
      · rw [htf]; rfl
      · rw [hoth i hi]; simp
      · intro i' hi'
        rw [hoth i' (fun h => hi' (List.mem_cons_of_mem _ h))]
        have hne : i ≠ i' := fun h => hi' (h ▸ List.mem_cons_self ..)
        simp [hne]

/-! ## Unparking -/

theorem run_unparkMoves {u : State} {b : Fin 10} {cells : List (Fin 4)}
    {top restb : Column} {c : Card}
    (hnd : cells.Nodup)
    (hhold : HoldsCards u.cells cells top)
    (hcol : u.tableau b = c :: restb)
    (hrun : IsRun (top ++ [c])) :
    ∃ v : State,
      List.foldl applyMoveOpt (some u) (unparkMoves b cells) = some v ∧
      v.tableau b = top ++ c :: restb ∧
      (∀ q, q ≠ b → v.tableau q = u.tableau q) ∧
      (∀ i ∈ cells, v.cells i = none) ∧
      (∀ i, i ∉ cells → v.cells i = u.cells i) ∧
      v.foundations = u.foundations := by
  induction cells generalizing u top with
  | nil =>
    cases top with
    | nil => exact ⟨u, rfl, by simpa using hcol, fun q _ => rfl, by simp, fun i _ => rfl, rfl⟩
    | cons x xs => exact hhold.elim
  | cons i is ih =>
    cases top with
    | nil => exact hhold.elim
    | cons x xs =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hi, hnd⟩ := hnd
      obtain ⟨hci, hhold'⟩ := hhold
      simp only [List.cons_append] at hrun
      obtain ⟨v', hfold, hvb, hvq, hvempty, hvoth, hvf⟩ :=
        ih (u := u) (top := xs) hnd hhold' hcol hrun.tail
      obtain ⟨y, hy⟩ : ∃ y, (xs ++ [c]).head? = some y := by
        cases h : xs ++ [c] with
        | nil => simp at h
        | cons y ys => exact ⟨y, by simp⟩
      have hcelli : v'.cells i = some x := by rw [hvoth i hi]; exact hci
      have hhead : (v'.tableau b).head? = nextCard x := by
        rw [hvb, head?_append_cons, hy]
        exact (hrun.head y (Option.mem_def.2 hy)).symm
      have hstep : applyMove v' ⟨Position.cell i, Position.pile b⟩
          = some (updateColumn (updateCell v' i none) b (x :: v'.tableau b)) := by
        rw [applyMove_eq]
        refine ⟨x, updateCell v' i none, ?_, ?_⟩
        · simp only [takeFromPosition, takeFromCell_eq]
          exact ⟨hcelli, trivial⟩
        · simp only [dropPosition, dropCol_eq, updateCell_tableau]
          exact ⟨hhead, trivial⟩
      refine ⟨updateColumn (updateCell v' i none) b (x :: v'.tableau b), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [unparkMoves, List.foldl_append, hfold,
          show List.foldl applyMoveOpt (some v') [⟨Position.cell i, Position.pile b⟩]
            = applyMove v' ⟨Position.cell i, Position.pile b⟩ from rfl]
        exact hstep
      · simp [hvb]
      · intro q hq; simp [Ne.symm hq, hvq q hq]
      · intro i' hi'
        rcases List.mem_cons.1 hi' with rfl | hi'
        · simp
        · have hne : i ≠ i' := fun h => hi (h ▸ hi')
          simpa [hne] using hvempty i' hi'
      · intro i' hi'
        have hne : i ≠ i' := fun h => hi' (h ▸ List.mem_cons_self ..)
        rw [← hvoth i' (fun h => hi' (List.mem_cons_of_mem _ h))]
        simp [hne]
      · simpa using hvf

/-! ## One abstract flute move -/

/-- **The realization of one solver flute move.**  A flute of length
`top.length + 1` moves from pile `a` to pile `b` in `2L - 1` concrete moves,
using `L - 1` free cells, and the cells are all free again afterwards.

The destination hypothesis `hdst` covers both solver destinations that land on a
column: a genuine pile (whose exposed card is `nextCard c`) and an empty king
pile (where `nextCard c = none = [].head?`, i.e. `c` is a king). -/
theorem run_fluteMoves {s : State} {a b : Fin 10} {cells : List (Fin 4)}
    {top rest : Column} {c : Card}
    (hab : a ≠ b)
    (hcol : s.tableau a = top ++ c :: rest)
    (hrun : IsRun (top ++ [c]))
    (hlen : cells.length = top.length)
    (hnd : cells.Nodup)
    (hfree : ∀ i ∈ cells, s.cells i = none)
    (hdst : (s.tableau b).head? = nextCard c) :
    ∃ v : State,
      List.foldl applyMoveOpt (some s) (fluteMoves a b cells) = some v ∧
      v.tableau a = rest ∧
      v.tableau b = top ++ c :: s.tableau b ∧
      (∀ q, q ≠ a → q ≠ b → v.tableau q = s.tableau q) ∧
      v.cells = s.cells ∧
      v.foundations = s.foundations := by
  obtain ⟨t, hpark, hta, htq, htf, hthold, htoth⟩ :=
    run_parkMoves (a := a) (top := top) (rest := c :: rest) hcol hlen hnd hfree
  have htb : t.tableau b = s.tableau b := htq b (Ne.symm hab)
  have hmid : applyMove t ⟨Position.pile a, Position.pile b⟩
      = some (updateColumn (updateColumn t a rest) b (c :: s.tableau b)) := by
    rw [applyMove_eq]
    refine ⟨c, updateColumn t a rest, ?_, ?_⟩
    · simp only [takeFromPosition, takeFromCol_eq]
      exact ⟨rest, hta, rfl⟩
    · simp only [dropPosition, dropCol_eq, updateColumn_tableau,
        update_diff _ _ _ _ hab, htb]
      exact ⟨hdst, trivial⟩
  set u := updateColumn (updateColumn t a rest) b (c :: s.tableau b) with hu
  have hub : u.tableau b = c :: s.tableau b := by simp [hu]
  have hua : u.tableau a = rest := by simp [hu, Ne.symm hab]
  have hucells : u.cells = t.cells := rfl
  obtain ⟨v, hunpark, hvb, hvq, hvempty, hvoth, hvf⟩ :=
    run_unparkMoves (u := u) (top := top) (restb := s.tableau b) hnd
      (by rw [hucells]; exact hthold)
      hub hrun
  refine ⟨v, ?_, ?_, hvb, ?_, ?_, ?_⟩
  · rw [fluteMoves, List.foldl_append, hpark, List.foldl_cons,
      show applyMoveOpt (some t) ⟨Position.pile a, Position.pile b⟩
        = applyMove t ⟨Position.pile a, Position.pile b⟩ from rfl, hmid]
    exact hunpark
  · rw [hvq a hab, hua]
  · intro q hqa hqb
    rw [hvq q hqb]
    simp [hu, Ne.symm hqa, Ne.symm hqb, htq q hqa]
  · funext i
    by_cases hi : i ∈ cells
    · rw [hvempty i hi]; exact (hfree i hi).symm
    · rw [hvoth i hi, hucells, htoth i hi]
  · rw [hvf]
    simp [hu, htf]

/-- Packaged for use with `Solvable`: the whole flute move is a `Reach` step. -/
theorem reach_fluteMoves {s v : State} {a b : Fin 10} {cells : List (Fin 4)}
    (h : List.foldl applyMoveOpt (some s) (fluteMoves a b cells) = some v) : Reach s v :=
  reach_of_foldl h

/-- Moving a flute into the cells (the solver's `EXTRA` destination) is just the
parking phase: `L` moves costing `L` cells. -/
theorem run_fluteToCells {s : State} {a : Fin 10} {cells : List (Fin 4)}
    {top rest : Column}
    (hcol : s.tableau a = top ++ rest)
    (hlen : cells.length = top.length)
    (hnd : cells.Nodup)
    (hfree : ∀ i ∈ cells, s.cells i = none) :
    ∃ t : State,
      List.foldl applyMoveOpt (some s) (parkMoves a cells) = some t ∧
      t.tableau a = rest ∧
      (∀ q, q ≠ a → t.tableau q = s.tableau q) ∧
      t.foundations = s.foundations ∧
      HoldsCards t.cells cells top ∧
      (∀ i, i ∉ cells → t.cells i = s.cells i) :=
  run_parkMoves hcol hlen hnd hfree
