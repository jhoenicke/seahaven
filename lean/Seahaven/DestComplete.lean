import Seahaven.CriticalMove

/-!
# The critical move's destination is forced

The solver explores one destination per pile — `solverGetDestination`'s walk — while
a winning play may send the boundary card anywhere the rules allow.  Completeness
has to know the two agree.  They do, and the reason splits into three small facts,
none of which needs the solver side:

* **The destination never moves a depth.**  Only the *source* column loses a card;
  a drop never breaks a depth match (`DepthMatchesV.drop`).  Since a merged position
  is determined by its depth vector (`matches_of_depth_match`), the child position
  the play reaches is the same whatever the destination was.
* **Parking and then dropping is the direct move** (`cell_park_then_drop`): moving a
  card to a cell and later dropping it on a column is, as a state transformation,
  *literally* the one-step move onto that column.  So a play that parks the boundary
  card where the solver drops it is CP-equivalent to the solver's move — which is
  what lets `CPReach.solvable_iff` transport solvability across the difference.
* **A column destination is unique** (`pile_dest_unique`): a non-king card fits on
  exactly one column, the one holding its successor on top; a king fits only on
  *empty* columns, which is the king-relabelling freedom the abstract state
  deliberately does not record.

`critical_child_depthMatch` then reads off the child's depth match, and
`dest_ne_source` rules out the degenerate "put it straight back" move.
-/

/-! ## Parking is the direct move -/

/-- **Park, then drop, is drop.**  Moving `c` from a column into a cell and then
from that cell onto a column produces exactly the state the direct column-to-column
move produces — the intermediate cell is restored to `none`, which is what it was.

This is why the play's choice of destination is immaterial: the cell detour is a
`CPStep`, and `CPReach.solvable_iff` transports solvability across it. -/
theorem cell_park_then_drop {u v w : State} {a q : Fin 10} {j : Fin 4}
    (hv : applyMove u ⟨Position.pile a, Position.cell j⟩ = some v)
    (hw : applyMove v ⟨Position.cell j, Position.pile q⟩ = some w) :
    applyMove u ⟨Position.pile a, Position.pile q⟩ = some w := by
  rw [applyMove_eq] at hv hw ⊢
  obtain ⟨c, s0, htake, hdrop⟩ := hv
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest, hcol, rfl⟩ := htake
  simp only [dropPosition, dropCell_eq] at hdrop
  obtain ⟨hnone, rfl⟩ := hdrop
  obtain ⟨c', v0, htake', hdrop'⟩ := hw
  simp only [takeFromPosition, takeFromCell_eq] at htake'
  obtain ⟨hcell, rfl⟩ := htake'
  -- the parked card is the one we parked, and undoing the park is the identity
  have hcj : (updateCell (updateColumn u a rest) j (some c)).cells j = some c := by
    simp [updateCell, update]
  rw [hcj] at hcell
  rw [show c' = c from (Option.some.inj hcell).symm] at hdrop'
  have hv0 : updateCell (updateCell (updateColumn u a rest) j (some c)) j none
      = updateColumn u a rest := by
    refine State.ext' ?_ rfl rfl
    show update (update (updateColumn u a rest).cells j (some c)) j none
      = (updateColumn u a rest).cells
    funext i
    by_cases hij : j = i
    · subst hij
      simp only [update]
      exact hnone.symm
    · simp [update, hij]
  rw [hv0] at hdrop'
  refine ⟨c, updateColumn u a rest, ?_, hdrop'⟩
  simp only [takeFromPosition, takeFromCol_eq]
  exact ⟨rest, hcol, rfl⟩

/-- The park itself is a legal move out of `u`, and the drop that follows it is a
`CPStep` — so the two-step detour is `CPReach`-equivalent to the direct move. -/
theorem cpStep_of_park_drop {v w : State} {q : Fin 10} {j : Fin 4}
    (hw : applyMove v ⟨Position.cell j, Position.pile q⟩ = some w) (hne : v.tableau q ≠ []) :
    CPStep v w := ⟨j, q, hne, hw⟩

/-! ## A column destination is unique -/

/-- **At most one column can accept a non-king card.**  Its successor is a single
card, and no card is in two columns. -/
theorem pile_dest_unique {u : State} (hnd : NoDupState u) {c e : Card}
    (hnext : nextCard c = some e) {q q' : Fin 10}
    (hq : (u.tableau q).head? = nextCard c) (hq' : (u.tableau q').head? = nextCard c) :
    q = q' := by
  rw [hnext] at hq hq'
  exact hnd.pile_unique (List.mem_of_mem_head? (Option.mem_def.2 hq))
    (List.mem_of_mem_head? (Option.mem_def.2 hq'))

/-- **A king fits only on an empty column.**  `nextCard` of a king is `none`, and
`dropCol` then demands `head? = none`.  Which empty column it goes to is exactly
the freedom the abstract state does not record (king relabelling). -/
theorem king_dest_empty {u : State} {c : Card} (hking : nextCard c = none)
    {q : Fin 10} (hq : (u.tableau q).head? = nextCard c) : u.tableau q = [] := by
  rw [hking] at hq
  exact List.head?_eq_none_iff.1 hq

/-- The destination column of a legal column-to-column move holds the moved card's
successor on top — read off `dropCol`, in the pre-move state when `q ≠ a`. -/
theorem dest_head_of_move {u v : State} {a q : Fin 10} {c : Card} {rest : Column}
    (hne : q ≠ a) (hcol : u.tableau a = c :: rest)
    (hv : applyMove u ⟨Position.pile a, Position.pile q⟩ = some v) :
    (u.tableau q).head? = nextCard c := by
  rw [applyMove_eq] at hv
  obtain ⟨c', s0, htake, hdrop⟩ := hv
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest', hcol', rfl⟩ := htake
  rw [hcol] at hcol'
  obtain ⟨hc, hr⟩ : c = c' ∧ rest = rest' := by simpa using hcol'
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨hhead, -⟩ := hdrop
  rw [← hc] at hhead
  simpa only [updateColumn_tableau, update, if_neg (Ne.symm hne)] using hhead

/-! ## The degenerate destination -/

/-- **Putting the card straight back is a no-op.**  A column-to-itself move rebuilds
the very same state, so it cannot be the move that breaks the depth match.  (For a
lone king on a depth-1 pile this move *is* legal — the column empties and the king
returns — which is why the critical move has to be identified by the break rather
than by legality.) -/
theorem self_move_id {u v : State} {a : Fin 10}
    (hv : applyMove u ⟨Position.pile a, Position.pile a⟩ = some v) : v = u := by
  rw [applyMove_eq] at hv
  obtain ⟨c, s0, htake, hdrop⟩ := hv
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest, hcol, rfl⟩ := htake
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨-, rfl⟩ := hdrop
  refine State.ext' rfl rfl ?_
  show update (update u.tableau a rest) a (c :: (updateColumn u a rest).tableau a) = u.tableau
  funext i
  by_cases hia : a = i
  · subst hia
    simp only [update, updateColumn_tableau]
    exact hcol.symm
  · simp [update, hia]

/-- **The critical move leaves its own pile.**  Its destination is neither the
foundation (no foundation move is available, `no_fmStep_of_depthMatch`) nor the
source column (that move changes nothing, `self_move_id`). -/
theorem dest_ne_source {g : Globals} {t₀ t₁ : State} {p : SolverPosType} {m : Move}
    {a : Fin 10} (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : DepthMatchesV g t₀ (depthVec p hd6))
    (hbreak : ¬ DepthMatchesV g t₁ (depthVec p hd6))
    (hsrc : m.src = Position.pile a) (hap : applyMove t₀ m = some t₁) :
    m.dest ≠ Position.pile a := by
  intro hdst
  have hm : (⟨Position.pile a, Position.pile a⟩ : Move) = m := by
    obtain ⟨src, dest⟩ := m
    simp only at hsrc hdst
    rw [hsrc, hdst]
  have hid : t₁ = t₀ := self_move_id (u := t₀) (v := t₁) (a := a) (by rw [hm]; exact hap)
  rw [hid] at hbreak
  exact hbreak hdm

/-! ## The child's depth match

The destination contributes nothing: whatever column receives the card only *gains*
a card on top, which `DepthMatchesV.drop` already knows preserves a match.  The
whole content is on the source side, where the new depth is any `d'` the shortened
column still matches — and `merge_complete` makes the solver's choice the least
such, which is what `MatchesDepth.matches_of_depth_match` needs. -/

/-- **The state after the critical move matches the child's depth vector.**  Given
any candidate child depth `d'` that agrees with `d` off the source pile and that the
shortened source column still matches, the post-move state matches `d'`. -/
theorem critical_child_depthMatch {g : Globals} {t₀ t₁ : State} {d d' : Fin 10 → Fin 6}
    {m : Move} {a : Fin 10} {c : Card} {rest : Column}
    (hdm : DepthMatchesV g t₀ d) (hcol : t₀.tableau a = c :: rest)
    (hsrc : m.src = Position.pile a) (hdst : m.dest ≠ Position.pile a)
    (hap : applyMove t₀ m = some t₁)
    (hoff : ∀ i : Fin 10, i ≠ a → d' i = d i)
    (hsrc' : PileMatches g rest a (d' a)) :
    DepthMatchesV g t₁ d' := by
  rw [applyMove_eq, hsrc] at hap
  obtain ⟨c', s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest', hcol', rfl⟩ := htake
  rw [hcol] at hcol'
  obtain ⟨-, hr⟩ : c = c' ∧ rest = rest' := by simpa using hcol'
  rw [hr] at hsrc'
  -- the shortened state matches `d'` …
  have hmid : DepthMatchesV g (updateColumn t₀ a rest') d' := by
    intro i
    by_cases hia : i = a
    · subst hia
      simpa [update] using hsrc'
    · have := hdm i
      rw [← hoff i hia] at this
      simpa only [updateColumn_tableau, update, if_neg (Ne.symm hia)] using this
  -- … and dropping the card somewhere else cannot break it
  exact hmid.drop hdrop

/-- **The destination is irrelevant to the child position.**  Two legal critical
moves out of the same state, with the same source, reach states that match the same
depth vectors — so they stand for the same abstract child. -/
theorem child_depthMatch_dest_irrelevant {g : Globals} {t₀ v w : State} {d' : Fin 10 → Fin 6}
    {a : Fin 10} {dst dst' : Position} {c : Card} {rest : Column}
    (hcol : t₀.tableau a = c :: rest)
    (hv : applyMove t₀ ⟨Position.pile a, dst⟩ = some v)
    (hw : applyMove t₀ ⟨Position.pile a, dst'⟩ = some w)
    (hdst : dst ≠ Position.pile a) (hdst' : dst' ≠ Position.pile a)
    (hsrc' : PileMatches g rest a (d' a))
    (hdm : DepthMatchesV g t₀ (fun i => if i = a then d' a else d' i)) :
    DepthMatchesV g v d' ∧ DepthMatchesV g w d' := by
  refine ⟨critical_child_depthMatch hdm hcol rfl hdst hv ?_ hsrc',
          critical_child_depthMatch hdm hcol rfl hdst' hw ?_ hsrc'⟩ <;>
    exact fun i hia => by simp [hia]

/-! ## A cell destination witnesses a free cell

If the play parks the boundary card, the cell it used was free *before* the move, so
the critical state has at least one free cell.  Combined with
`DepthPlusKingsCfg.flute_add_freeCells_le_freeCellsOf` this upgrades the
affordability bound from `fluteLen - 1` to `fluteLen` — exactly the index
`solverGetMovable` reads for an `EXTRA` (or cell-bound king) destination. -/

/-- A move into cell `j` needs `j` free in the source state (the take does not touch
the cells). -/
theorem freeCell_of_cell_dest {u v : State} {a : Fin 10} {j : Fin 4}
    (hv : applyMove u ⟨Position.pile a, Position.cell j⟩ = some v) : u.cells j = none := by
  rw [applyMove_eq] at hv
  obtain ⟨c, s0, htake, hdrop⟩ := hv
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest, -, rfl⟩ := htake
  simp only [dropPosition, dropCell_eq] at hdrop
  exact hdrop.1

/-- Hence the source state has a free cell to spare. -/
theorem one_le_freeCells_of_cell_dest {u v : State} {a : Fin 10} {j : Fin 4}
    (hv : applyMove u ⟨Position.pile a, Position.cell j⟩ = some v) :
    1 ≤ (freeCells u).length := by
  have hmem : j ∈ freeCells u := mem_freeCells.2 (freeCell_of_cell_dest hv)
  exact List.length_pos_iff_ne_nil.2 (fun hnil => by rw [hnil] at hmem; simp at hmem)

/-! ## "It fits nowhere, so it went to a cell"

The step that pays for the higher `possibleKings` index.  When the solver's
destination is `EXTRA`, or a king pile whose suit the configuration does **not**
pile, the boundary card fits on no column and cannot go to the foundation — so the
play's critical move was a park, and the cell it used was free beforehand.  That is
the extra cell `possibleKings[fluteLen]` asks for.

The one exception is a **king moved onto an empty column**: `nextCard` of a king is
`none`, so an empty column does accept it.  There the configuration must be chosen to
*claim* that column for the suit (`OwnsPile`'s second disjunct, available because
`kings su` is then still the king), which moves the case into the king-pile branch
that only needs `fluteLen - 1`.  See `king_dest_empty`. -/

/-- **A move that fits nowhere is a park.**  Neither the foundation (no `FMStep`) nor
any column (`hother`/`hself`) accepts the card, so the destination is a cell — and
that cell was free before the move. -/
theorem cell_dest_of_no_fit {u v : State} {m : Move} {a : Fin 10} {c : Card} {rest : Column}
    (hcol : u.tableau a = c :: rest) (hsrc : m.src = Position.pile a)
    (hap : applyMove u m = some v) (hnf : ∀ t, ¬ FMStep u t)
    (hother : ∀ q : Fin 10, q ≠ a → (u.tableau q).head? ≠ nextCard c)
    (hself : rest.head? ≠ nextCard c) :
    ∃ j : Fin 4, m.dest = Position.cell j ∧ u.cells j = none := by
  cases hdst : m.dest with
  | foundation =>
    exact absurd ⟨m.src, by rw [Move.foundation_eta hdst]; exact hap⟩ (hnf v)
  | cell j =>
    refine ⟨j, rfl, ?_⟩
    refine freeCell_of_cell_dest (a := a) (v := v) ?_
    have hm : (⟨Position.pile a, Position.cell j⟩ : Move) = m := by
      obtain ⟨src, dest⟩ := m
      simp only at hsrc hdst
      rw [hsrc, hdst]
    rw [hm]; exact hap
  | pile q =>
    exfalso
    rw [applyMove_eq, hsrc] at hap
    obtain ⟨c', s0, htake, hdrop⟩ := hap
    simp only [takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest', hcol', rfl⟩ := htake
    rw [hcol] at hcol'
    obtain ⟨hc, hr⟩ : c = c' ∧ rest = rest' := by simpa using hcol'
    rw [hdst] at hdrop
    simp only [dropPosition, dropCol_eq] at hdrop
    obtain ⟨hhead, -⟩ := hdrop
    rw [← hc] at hhead
    by_cases hqa : q = a
    · subst hqa
      rw [← hr] at hhead
      exact hself (by simpa [update] using hhead)
    · exact hother q hqa (by
        simpa only [updateColumn_tableau, update, if_neg (Ne.symm hqa)] using hhead)

/-- Hence a free cell is available at the critical state. -/
theorem one_le_freeCells_of_no_fit {u v : State} {m : Move} {a : Fin 10} {c : Card}
    {rest : Column} (hcol : u.tableau a = c :: rest) (hsrc : m.src = Position.pile a)
    (hap : applyMove u m = some v) (hnf : ∀ t, ¬ FMStep u t)
    (hother : ∀ q : Fin 10, q ≠ a → (u.tableau q).head? ≠ nextCard c)
    (hself : rest.head? ≠ nextCard c) :
    1 ≤ (freeCells u).length := by
  obtain ⟨j, -, hnone⟩ := cell_dest_of_no_fit hcol hsrc hap hnf hother hself
  have hmem : j ∈ freeCells u := mem_freeCells.2 hnone
  exact List.length_pos_iff_ne_nil.2 (fun hnil => by rw [hnil] at hmem; simp at hmem)

/-- `cell_dest_of_no_fit`, with the source column excluded by `dest_ne_source`
instead of by an explicit hypothesis on the shortened column. -/
theorem cell_dest_of_no_fit' {u v : State} {m : Move} {a : Fin 10} {c : Card} {rest : Column}
    (hcol : u.tableau a = c :: rest) (hsrc : m.src = Position.pile a)
    (hap : applyMove u m = some v) (hnf : ∀ t, ¬ FMStep u t)
    (hdst : m.dest ≠ Position.pile a)
    (hother : ∀ q : Fin 10, q ≠ a → (u.tableau q).head? ≠ nextCard c) :
    ∃ j : Fin 4, m.dest = Position.cell j ∧ u.cells j = none := by
  cases hd : m.dest with
  | foundation =>
    exact absurd ⟨m.src, by rw [Move.foundation_eta hd]; exact hap⟩ (hnf v)
  | cell j =>
    refine ⟨j, rfl, ?_⟩
    refine freeCell_of_cell_dest (a := a) (v := v) ?_
    have hm : (⟨Position.pile a, Position.cell j⟩ : Move) = m := by
      obtain ⟨src, dest⟩ := m
      simp only at hsrc hd
      rw [hsrc, hd]
    rw [hm]; exact hap
  | pile q =>
    exfalso
    by_cases hqa : q = a
    · exact hdst (by rw [hd, hqa])
    · rw [applyMove_eq, hsrc] at hap
      obtain ⟨c', s0, htake, hdrop⟩ := hap
      simp only [takeFromPosition, takeFromCol_eq] at htake
      obtain ⟨rest', hcol', rfl⟩ := htake
      rw [hcol] at hcol'
      obtain ⟨hc, -⟩ : c = c' ∧ rest = rest' := by simpa using hcol'
      rw [hd] at hdrop
      simp only [dropPosition, dropCol_eq] at hdrop
      obtain ⟨hhead, -⟩ := hdrop
      rw [← hc] at hhead
      exact hother q hqa (by
        simpa only [updateColumn_tableau, update, if_neg (Ne.symm hqa)] using hhead)

/-- The destination column of a legal move, in the *pre-move* state (`q ≠ a`). -/
theorem dest_head_of_move' {u v : State} {m : Move} {a q : Fin 10} {c : Card} {rest : Column}
    (hcol : u.tableau a = c :: rest) (hsrc : m.src = Position.pile a)
    (hd : m.dest = Position.pile q) (hqa : q ≠ a) (hap : applyMove u m = some v) :
    (u.tableau q).head? = nextCard c := by
  rw [applyMove_eq, hsrc] at hap
  obtain ⟨c', s0, htake, hdrop⟩ := hap
  simp only [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest', hcol', rfl⟩ := htake
  rw [hcol] at hcol'
  obtain ⟨hc, -⟩ : c = c' ∧ rest = rest' := by simpa using hcol'
  rw [hd] at hdrop
  simp only [dropPosition, dropCol_eq] at hdrop
  obtain ⟨hhead, -⟩ := hdrop
  rw [← hc] at hhead
  simpa only [updateColumn_tableau, update, if_neg (Ne.symm hqa)] using hhead
