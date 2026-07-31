import Mathlib.Tactic
import Mathlib.Logic.Relation
import Seahaven.Rules
import Seahaven.CountProofs

/-!
# Foundation moves are never harmful

A *foundation move* is a `Move` whose destination is `Position.foundation`.

This file proves that playing a foundation move can never turn a solvable
position into an unsolvable one (`foundationMove_preserves_Solvable`).

Note that foundation moves are *not* confluent in the naive sense: a move
`src → cell` and the move `src → foundation` do not commute, because they take
the very same card.  What is true is a *limited* confluence
(`fm_commute` / `fm_absorb`): every move of a reference solution either still
works after the foundation move (and the foundation move can be replayed
afterwards), or it is the move that ships the very same card, in which case it
can simply be skipped.

All results need the hypothesis `NoDupState`: the state must not contain a card
twice, where a card also counts as present once its foundation has passed it.
Without it the statement is plainly false — a second copy of the card below `c`
could still want to be stacked onto `c`, which is impossible once `c` has left
for the foundation.  `NoDupState` is invariant under *every* move
(`NoDupState.applyMove`), so it only has to be established once, for the deal.
-/

/-! ## Extensionality and field simp lemmas -/

theorem State.ext' {s t : State}
    (hc : s.cells = t.cells) (hf : s.foundations = t.foundations)
    (ht : s.tableau = t.tableau) : s = t := by
  cases s; cases t; simp_all

@[simp] theorem updateColumn_cells (s : State) (p : Fin 10) (col : Column) :
    (updateColumn s p col).cells = s.cells := rfl
@[simp] theorem updateColumn_foundations (s : State) (p : Fin 10) (col : Column) :
    (updateColumn s p col).foundations = s.foundations := rfl
@[simp] theorem updateColumn_tableau (s : State) (p : Fin 10) (col : Column) :
    (updateColumn s p col).tableau = update s.tableau p col := rfl

@[simp] theorem updateCell_cells (s : State) (i : Fin 4) (v : Option Card) :
    (updateCell s i v).cells = update s.cells i v := rfl
@[simp] theorem updateCell_foundations (s : State) (i : Fin 4) (v : Option Card) :
    (updateCell s i v).foundations = s.foundations := rfl
@[simp] theorem updateCell_tableau (s : State) (i : Fin 4) (v : Option Card) :
    (updateCell s i v).tableau = s.tableau := rfl

@[simp] theorem updateFoundation_cells (s : State) (c : Card) :
    (updateFoundation s c).cells = s.cells := rfl
@[simp] theorem updateFoundation_foundations (s : State) (c : Card) :
    (updateFoundation s c).foundations = update s.foundations c.suit c.rank := rfl
@[simp] theorem updateFoundation_tableau (s : State) (c : Card) :
    (updateFoundation s c).tableau = s.tableau := rfl

/-- Rewriting an already-present value is a no-op. -/
theorem update_self [DecidableEq T1] (f : T1 → T2) (i : T1) :
    update f i (f i) = f := by
  funext j; simp [update]; intro h; simp [h]

/-! ## Characterising `takeFromPosition` and `dropPosition` -/

theorem takeFromCol_eq {s : State} {col : Fin 10} {card : Card} {s' : State} :
    takeFromCol s col = some (card, s') ↔
      ∃ rest, s.tableau col = card :: rest ∧ s' = updateColumn s col rest := by
  unfold takeFromCol
  cases h : s.tableau col with
  | nil => simp
  | cons x xs =>
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨xs, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨rest, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩

theorem takeFromCell_eq {s : State} {i : Fin 4} {card : Card} {s' : State} :
    takeFromCell s i = some (card, s') ↔
      s.cells i = some card ∧ s' = updateCell s i none := by
  unfold takeFromCell
  cases h : s.cells i with
  | none => simp
  | some x => simp only [Option.some.injEq, Prod.mk.injEq, eq_comm]

theorem dropCol_eq {s : State} {dst : Fin 10} {card : Card} {s' : State} :
    dropCol s dst card = some s' ↔
      (s.tableau dst).head? = nextCard card ∧
        s' = updateColumn s dst (card :: s.tableau dst) := by
  unfold dropCol
  by_cases h : (s.tableau dst).head? = nextCard card <;> simp [h, eq_comm]

theorem dropCell_eq {s : State} {dst : Fin 4} {card : Card} {s' : State} :
    dropCell s dst card = some s' ↔
      s.cells dst = none ∧ s' = updateCell s dst (some card) := by
  unfold dropCell
  by_cases h : s.cells dst = none <;> simp [h, eq_comm]

theorem dropFoundation_eq {s : State} {card : Card} {s' : State} :
    dropFoundation s card = some s' ↔
      some card.rank = nextRank (s.foundations card.suit) ∧
        s' = updateFoundation s card := by
  unfold dropFoundation
  by_cases h : some card.rank = nextRank (s.foundations card.suit) <;> simp [h, eq_comm]

theorem applyMove_eq {s s' : State} {m : Move} :
    applyMove s m = some s' ↔
      ∃ card s0, takeFromPosition s m.src = some (card, s0) ∧
        dropPosition s0 m.dest card = some s' := by
  unfold applyMove
  cases h : takeFromPosition s m.src with
  | none => simp
  | some pair =>
    obtain ⟨card, s0⟩ := pair
    constructor
    · intro hd; exact ⟨card, s0, rfl, hd⟩
    · rintro ⟨card', s0', h', hd⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact hd

/-- `takeFromPosition` never reads or writes the foundations. -/
theorem takeFromPosition_foundations {s : State} {p : Position}
    {card : Card} {s0 : State} (h : takeFromPosition s p = some (card, s0)) :
    s0.foundations = s.foundations := by
  cases p with
  | pile i => rw [takeFromPosition, takeFromCol_eq] at h; obtain ⟨rest, _, rfl⟩ := h; rfl
  | cell i => rw [takeFromPosition, takeFromCell_eq] at h; obtain ⟨_, rfl⟩ := h; rfl
  | foundation => simp [takeFromPosition] at h

/-! ## Foundation moves, reachability, solvability -/

/-- A *foundation move* is a move whose destination is the foundation. -/
def IsFoundationMove (m : Move) : Prop := m.dest = Position.foundation

instance (m : Move) : Decidable (IsFoundationMove m) := by
  unfold IsFoundationMove; infer_instance

theorem Move.foundation_eta {m : Move} (h : IsFoundationMove m) :
    (⟨m.src, Position.foundation⟩ : Move) = m := by
  cases m with
  | mk src dest => simp only [IsFoundationMove] at h; subst h; rfl

/-- `FMStep s t` : `t` is obtained from `s` by playing one foundation move. -/
def FMStep (s t : State) : Prop :=
  ∃ p : Position, applyMove s ⟨p, Position.foundation⟩ = some t

/-- `FMReach s t` : `t` is obtained from `s` by playing zero or more
foundation moves.  Read it as "`t` is at least as far advanced as `s`". -/
abbrev FMReach : State → State → Prop := Relation.ReflTransGen FMStep

theorem FMStep.toReach {s t : State} (h : FMStep s t) : FMReach s t :=
  Relation.ReflTransGen.single h

/-- A state has no duplicated cards.  A card counts as present when it sits in
a cell, in the tableau, or when it is already covered by its foundation. -/
def NoDupState (s : State) : Prop := ∀ c : Card, countState s c ≤ 1

theorem NoDupState.applyMove {s s' : State} {m : Move}
    (h : NoDupState s) (hm : applyMove s m = some s') : NoDupState s' := by
  intro c
  have := congrFun (movePreservesCards s m s' hm) c
  rw [← this]
  exact h c

/-- Solvability, phrased as an inductive reachability predicate. -/
inductive Solvable : State → Prop
  | done {s : State} (h : isGoal s = true) : Solvable s
  | step {s s' : State} (m : Move) (h : applyMove s m = some s') (hs : Solvable s') :
      Solvable s

/-! ### Bridge to `isSolution` -/

theorem foldl_applyMoveOpt_none (l : List Move) :
    List.foldl applyMoveOpt none l = none := by
  induction l with
  | nil => rfl
  | cons m ms ih => simpa [applyMoveOpt] using ih

theorem solvable_of_run {s : State} {sol : List Move} {s1 : State}
    (h : List.foldl applyMoveOpt (some s) sol = some s1) (hg : isGoal s1 = true) :
    Solvable s := by
  induction sol generalizing s with
  | nil => simp at h; subst h; exact Solvable.done hg
  | cons m ms ih =>
    rw [List.foldl_cons] at h
    cases hm : applyMove s m with
    | none =>
      rw [show applyMoveOpt (some s) m = applyMove s m from rfl, hm,
        foldl_applyMoveOpt_none] at h
      simp at h
    | some s2 =>
      rw [show applyMoveOpt (some s) m = applyMove s m from rfl, hm] at h
      exact Solvable.step m hm (ih h)

theorem solvable_of_isSolution {s : State} {sol : List Move}
    (h : isSolution s sol = true) : Solvable s := by
  unfold isSolution at h
  cases hr : List.foldl applyMoveOpt (some s) sol with
  | none => rw [hr] at h; simp at h
  | some s1 => rw [hr] at h; exact solvable_of_run hr h

theorem exists_solution_of_solvable {s : State} (h : Solvable s) :
    ∃ sol : List Move, isSolution s sol = true := by
  induction h with
  | done hg => exact ⟨[], by simp [isSolution, hg]⟩
  | step m hm _ ih =>
    obtain ⟨sol, hsol⟩ := ih
    refine ⟨m :: sol, ?_⟩
    unfold isSolution at hsol ⊢
    rw [List.foldl_cons, show applyMoveOpt (some _) m = applyMove _ m from rfl, hm]
    exact hsol

/-! ## Commuting independent updates -/

theorem update_comm [DecidableEq T1] (f : T1 → T2) {i j : T1} (h : i ≠ j) (v w : T2) :
    update (update f i v) j w = update (update f j w) i v := by
  funext k
  by_cases hik : i = k <;> by_cases hjk : j = k <;> simp_all [update]

theorem updateColumn_comm (s : State) {i j : Fin 10} (h : i ≠ j) (a b : Column) :
    updateColumn (updateColumn s i a) j b = updateColumn (updateColumn s j b) i a := by
  apply State.ext' <;> simp [update_comm _ h]

theorem updateCell_comm (s : State) {i j : Fin 4} (h : i ≠ j) (a b : Option Card) :
    updateCell (updateCell s i a) j b = updateCell (updateCell s j b) i a := by
  apply State.ext' <;> simp [update_comm _ h]

theorem updateFoundation_comm (s : State) {c d : Card} (h : c.suit ≠ d.suit) :
    updateFoundation (updateFoundation s c) d = updateFoundation (updateFoundation s d) c := by
  apply State.ext' <;> simp [update_comm _ h]

/-! ## Independent take / drop operations commute -/

/-- Advancing a foundation does not disturb taking a card. -/
theorem take_updateFoundation {s : State} {p : Position} {d : Card} {s' : State} (c : Card)
    (h : takeFromPosition s p = some (d, s')) :
    takeFromPosition (updateFoundation s c) p = some (d, updateFoundation s' c) := by
  cases p with
  | pile i =>
    rw [takeFromPosition, takeFromCol_eq] at h
    obtain ⟨rest, hcol, rfl⟩ := h
    rw [takeFromPosition, takeFromCol_eq]
    exact ⟨rest, hcol, rfl⟩
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at h
    obtain ⟨hc, rfl⟩ := h
    rw [takeFromPosition, takeFromCell_eq]
    exact ⟨hc, rfl⟩
  | foundation => simp [takeFromPosition] at h

/-- Taking from two different positions commutes. -/
theorem take_take_comm {s : State} {p q : Position} {c d : Card} {sp sq : State}
    (hpq : p ≠ q)
    (hp : takeFromPosition s p = some (c, sp))
    (hq : takeFromPosition s q = some (d, sq)) :
    ∃ spq, takeFromPosition sp q = some (d, spq) ∧ takeFromPosition sq p = some (c, spq) := by
  cases p with
  | foundation => simp [takeFromPosition] at hp
  | pile i =>
    rw [takeFromPosition, takeFromCol_eq] at hp
    obtain ⟨ri, hi, rfl⟩ := hp
    cases q with
    | foundation => simp [takeFromPosition] at hq
    | pile j =>
      have hij : i ≠ j := fun h => hpq (by subst h; rfl)
      rw [takeFromPosition, takeFromCol_eq] at hq
      obtain ⟨rj, hj, rfl⟩ := hq
      refine ⟨updateColumn (updateColumn s i ri) j rj, ?_, ?_⟩
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨rj, by simpa [update_diff _ _ _ _ hij] using hj, rfl⟩
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨ri, by simpa [update_diff _ _ _ _ (Ne.symm hij)] using hi,
          updateColumn_comm s hij ri rj⟩
    | cell j =>
      rw [takeFromPosition, takeFromCell_eq] at hq
      obtain ⟨hj, rfl⟩ := hq
      refine ⟨updateCell (updateColumn s i ri) j none, ?_, ?_⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa using hj, rfl⟩
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨ri, by simpa using hi, rfl⟩
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at hp
    obtain ⟨hi, rfl⟩ := hp
    cases q with
    | foundation => simp [takeFromPosition] at hq
    | pile j =>
      rw [takeFromPosition, takeFromCol_eq] at hq
      obtain ⟨rj, hj, rfl⟩ := hq
      refine ⟨updateColumn (updateCell s i none) j rj, ?_, ?_⟩
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨rj, by simpa using hj, rfl⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa using hi, rfl⟩
    | cell j =>
      have hij : i ≠ j := fun h => hpq (by subst h; rfl)
      rw [takeFromPosition, takeFromCell_eq] at hq
      obtain ⟨hj, rfl⟩ := hq
      refine ⟨updateCell (updateCell s i none) j none, ?_, ?_⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa [update_diff _ _ _ _ hij] using hj, rfl⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa [update_diff _ _ _ _ (Ne.symm hij)] using hi,
          updateCell_comm s hij none none⟩

/-- Advancing a foundation for suit `c.suit` does not disturb any drop, provided
the drop itself is not a foundation drop of the very same suit. -/
theorem drop_updateFoundation {s : State} {dst : Position} {d : Card} {s' : State} {c : Card}
    (h : dropPosition s dst d = some s')
    (hsuit : dst = Position.foundation → c.suit ≠ d.suit) :
    dropPosition (updateFoundation s c) dst d = some (updateFoundation s' c) := by
  cases dst with
  | pile j =>
    rw [dropPosition, dropCol_eq] at h
    rw [dropPosition, dropCol_eq]
    obtain ⟨hh, rfl⟩ := h
    exact ⟨hh, rfl⟩
  | cell j =>
    rw [dropPosition, dropCell_eq] at h
    rw [dropPosition, dropCell_eq]
    obtain ⟨hh, rfl⟩ := h
    exact ⟨hh, rfl⟩
  | foundation =>
    have hs := hsuit rfl
    rw [dropPosition, dropFoundation_eq] at h
    rw [dropPosition, dropFoundation_eq]
    obtain ⟨hh, rfl⟩ := h
    exact ⟨by simpa [update_diff _ _ _ _ hs] using hh, (updateFoundation_comm s hs).symm⟩

/-- Dropping at `dst` and taking at `p` commute whenever `dst ≠ p`. -/
theorem drop_take_comm {s : State} {p dst : Position} {c d : Card} {sp s' : State}
    (hne : dst ≠ p)
    (hp : takeFromPosition s p = some (c, sp))
    (hd : dropPosition s dst d = some s') :
    ∃ s'', dropPosition sp dst d = some s'' ∧ takeFromPosition s' p = some (c, s'') := by
  cases dst with
  | foundation =>
    rw [dropPosition, dropFoundation_eq] at hd
    obtain ⟨hready, rfl⟩ := hd
    refine ⟨updateFoundation sp d, ?_, take_updateFoundation d hp⟩
    rw [dropPosition, dropFoundation_eq]
    exact ⟨by rw [takeFromPosition_foundations hp]; exact hready, rfl⟩
  | pile j =>
    rw [dropPosition, dropCol_eq] at hd
    obtain ⟨hhead, rfl⟩ := hd
    cases p with
    | foundation => simp [takeFromPosition] at hp
    | pile k =>
      have hjk : j ≠ k := fun h => hne (by subst h; rfl)
      rw [takeFromPosition, takeFromCol_eq] at hp
      obtain ⟨rk, hk, rfl⟩ := hp
      refine ⟨updateColumn (updateColumn s k rk) j (d :: s.tableau j), ?_, ?_⟩
      · rw [dropPosition, dropCol_eq]
        refine ⟨by simpa [update_diff _ _ _ _ (Ne.symm hjk)] using hhead, ?_⟩
        simp [update_diff _ _ _ _ (Ne.symm hjk)]
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨rk, by simpa [update_diff _ _ _ _ hjk] using hk,
          (updateColumn_comm s hjk (d :: s.tableau j) rk).symm⟩
    | cell k =>
      rw [takeFromPosition, takeFromCell_eq] at hp
      obtain ⟨hk, rfl⟩ := hp
      refine ⟨updateColumn (updateCell s k none) j (d :: s.tableau j), ?_, ?_⟩
      · rw [dropPosition, dropCol_eq]
        exact ⟨by simpa using hhead, rfl⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa using hk, rfl⟩
  | cell i =>
    rw [dropPosition, dropCell_eq] at hd
    obtain ⟨hempty, rfl⟩ := hd
    cases p with
    | foundation => simp [takeFromPosition] at hp
    | pile k =>
      rw [takeFromPosition, takeFromCol_eq] at hp
      obtain ⟨rk, hk, rfl⟩ := hp
      refine ⟨updateCell (updateColumn s k rk) i (some d), ?_, ?_⟩
      · rw [dropPosition, dropCell_eq]
        exact ⟨by simpa using hempty, rfl⟩
      · rw [takeFromPosition, takeFromCol_eq]
        exact ⟨rk, by simpa using hk, rfl⟩
    | cell k =>
      have hik : i ≠ k := fun h => hne (by subst h; rfl)
      rw [takeFromPosition, takeFromCell_eq] at hp
      obtain ⟨hk, rfl⟩ := hp
      refine ⟨updateCell (updateCell s k none) i (some d), ?_, ?_⟩
      · rw [dropPosition, dropCell_eq]
        exact ⟨by simpa [update_diff _ _ _ _ (Ne.symm hik)] using hempty, rfl⟩
      · rw [takeFromPosition, takeFromCell_eq]
        exact ⟨by simpa [update_diff _ _ _ _ hik] using hk,
          (updateCell_comm s hik (some d) none).symm⟩

/-! ## Consequences of `NoDupState` -/

theorem countState_foundation_le (s : State) (c : Card) :
    countFoundation s.foundations c ≤ countState s c := by
  simp [countState]
  omega

/-- In a duplicate-free state, two different positions cannot hold the same card. -/
theorem no_dup_two_positions {s : State} {p q : Position} {c : Card} {sp sq : State}
    (hnd : NoDupState s) (hpq : p ≠ q)
    (hp : takeFromPosition s p = some (c, sp))
    (hq : takeFromPosition s q = some (c, sq)) : False := by
  obtain ⟨spq, _, hts⟩ := take_take_comm hpq hp hq
  have h1 := takePreservesCards s q c sq hq c
  have h2 := takePreservesCards sq p c spq hts c
  have h3 := hnd c
  simp [countCard] at h1 h2
  omega

/-- In a duplicate-free state, a card that is already covered by its foundation
cannot be lying around in the layout. -/
theorem no_dup_covered {s : State} {q : Position} {d : Card} {sq : State}
    (hnd : NoDupState s)
    (hcov : countFoundation s.foundations d = 1)
    (hq : takeFromPosition s q = some (d, sq)) : False := by
  have h1 := takePreservesCards s q d sq hq d
  have h2 : countFoundation sq.foundations d ≤ countState sq d := countState_foundation_le sq d
  rw [takeFromPosition_foundations hq] at h2
  have h3 := hnd d
  simp [countCard] at h1
  omega

/-! ## Small arithmetic facts about ranks and foundations -/

theorem nextCard_eq {d c : Card} (h : nextCard d = some c) :
    c.suit = d.suit ∧ rankToNat c.rank = rankToNat d.rank + 1 := by
  unfold nextCard at h
  cases hr : nextRank d.rank with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, by simpa [optRankToNat] using nextRankNat (some d.rank) r hr⟩

/-- If `c` is playable onto its foundation, the foundation is exactly one below `c`. -/
theorem foundation_of_ready {f : Suit → Option Rank} {c : Card}
    (h : some c.rank = nextRank (f c.suit)) :
    optRankToNat (f c.suit) + 1 = rankToNat c.rank :=
  (nextRankNat (f c.suit) c.rank h.symm).symm

/-- Playable cards are unique per suit. -/
theorem ready_unique {f : Suit → Option Rank} {c d : Card} (hs : d.suit = c.suit)
    (hc : some c.rank = nextRank (f c.suit)) (hd : some d.rank = nextRank (f d.suit)) :
    d = c := by
  rw [hs] at hd
  have : d.rank = c.rank := by
    have := hd.trans hc.symm
    exact (Option.some.inj this)
  exact Card.ext hs this

theorem nextRank_king : nextRank (some Rank.king) = none := by decide

theorem drop_foundations_ne {s s' : State} {dst : Position} {d : Card} {suit : Suit}
    (h : dropPosition s dst d = some s') (hne : dst = Position.foundation → suit ≠ d.suit) :
    s'.foundations suit = s.foundations suit := by
  cases dst with
  | pile j => rw [dropPosition, dropCol_eq] at h; obtain ⟨_, rfl⟩ := h; rfl
  | cell j => rw [dropPosition, dropCell_eq] at h; obtain ⟨_, rfl⟩ := h; rfl
  | foundation =>
    have hs := hne rfl
    rw [dropPosition, dropFoundation_eq] at h
    obtain ⟨_, rfl⟩ := h
    simp [update_diff _ _ _ _ (Ne.symm hs)]

@[simp] theorem updateCell_self (s : State) (i : Fin 4) : updateCell s i (s.cells i) = s := by
  apply State.ext' <;> simp [update_self]

@[simp] theorem updateColumn_self (s : State) (i : Fin 10) :
    updateColumn s i (s.tableau i) = s := by
  apply State.ext' <;> simp [update_self]

/-! ## Limited confluence

The two lemmas below are the heart of the development.  Consider a foundation
move `s → t` taking card `c` off position `p`, and an arbitrary other move `m`
that is legal in `s`, leading to `s1`.

* If `m` takes its card from somewhere other than `p` (`fm_commute`), then `m`
  is still legal in `t`, and the foundation move can be replayed afterwards:
  the two moves genuinely commute.
* If `m` takes its card from `p` (`fm_absorb`), it moves the very same card `c`.
  Either `m` *is* the foundation move (then `s1 = t`), or `m` parks `c` in a
  cell or on a pile, and a single foundation move from `s1` still reaches `t`.
-/

/-- A foundation move commutes with every other legal move that does not take
the same card.  This needs `NoDupState`: it rules out a reference move that
wants to drop a card *onto* `c`, or onto `c`'s foundation slot. -/
theorem fm_commute {s t s1 : State} {p : Position} {m : Move}
    (hnd : NoDupState s)
    (hfm : applyMove s ⟨p, Position.foundation⟩ = some t)
    (hm : applyMove s m = some s1)
    (hsrc : m.src ≠ p) :
    ∃ t1, applyMove t m = some t1 ∧ applyMove s1 ⟨p, Position.foundation⟩ = some t1 := by
  simp only [applyMove_eq] at hfm hm
  obtain ⟨c, sp, htp, hdf⟩ := hfm
  obtain ⟨d, sq, htq, hdd⟩ := hm
  simp only [dropPosition, dropFoundation_eq] at hdf
  obtain ⟨hready, rfl⟩ := hdf
  have hfsp : sp.foundations = s.foundations := takeFromPosition_foundations htp
  have hfsq : sq.foundations = s.foundations := takeFromPosition_foundations htq
  rw [hfsp] at hready
  obtain ⟨spq, htsp, hts1⟩ := take_take_comm (Ne.symm hsrc) htp htq
  -- the reference move cannot target the position `p` we just emptied
  have hdestp : m.dest ≠ p := by
    intro heq
    cases hp : p with
    | foundation => rw [hp, takeFromPosition] at htp; simp at htp
    | cell k =>
      rw [heq, hp, dropPosition, dropCell_eq] at hdd
      rw [hp, takeFromPosition, takeFromCell_eq] at hts1
      rw [hts1.1] at hdd
      simp at hdd
    | pile k =>
      rw [heq, hp, dropPosition, dropCol_eq] at hdd
      rw [hp, takeFromPosition, takeFromCol_eq] at hts1
      obtain ⟨rest, hcol, _⟩ := hts1
      rw [hcol] at hdd
      obtain ⟨hhead, _⟩ := hdd
      simp only [List.head?_cons] at hhead
      obtain ⟨hsuit, hrank⟩ := nextCard_eq hhead.symm
      have hf := foundation_of_ready hready
      have hcov : countFoundation s.foundations d = 1 := by
        unfold countFoundation
        rw [← hsuit]
        have hlt : ¬ (optRankToNat (s.foundations c.suit) < rankToNat d.rank) := by omega
        simp [hlt]
      exact no_dup_covered hnd hcov htq
  -- the reference move cannot be a foundation move of the same suit
  have hsuit : m.dest = Position.foundation → c.suit ≠ d.suit := by
    intro hdest hsq
    rw [hdest, dropPosition, dropFoundation_eq] at hdd
    obtain ⟨hreadyd, _⟩ := hdd
    rw [hfsq] at hreadyd
    have hdc : d = c := ready_unique hsq.symm hready hreadyd
    subst hdc
    exact no_dup_two_positions hnd (Ne.symm hsrc) htp htq
  obtain ⟨s'', hdrop, htake⟩ := drop_take_comm hdestp hts1 hdd
  refine ⟨updateFoundation s'' c, ?_, ?_⟩
  · rw [applyMove_eq]
    exact ⟨d, updateFoundation spq c, take_updateFoundation c htsp,
      drop_updateFoundation hdrop hsuit⟩
  · rw [applyMove_eq]
    refine ⟨c, s'', htake, ?_⟩
    simp only [dropPosition, dropFoundation_eq]
    refine ⟨?_, trivial⟩
    rw [takeFromPosition_foundations htake, drop_foundations_ne hdd hsuit, hfsq]
    exact hready

/-- Limited confluence, stated directly on moves: after a legal foundation move
`s → t`, every move that was legal in `s` is still legal in `t`, unless it takes
its card from the position the foundation move just emptied. -/
theorem foundationMove_keeps_moves_legal {s t s1 : State} {mf m : Move}
    (hnd : NoDupState s) (hdest : IsFoundationMove mf)
    (hfm : applyMove s mf = some t) (hm : applyMove s m = some s1)
    (hsrc : m.src ≠ mf.src) :
    ∃ t1, applyMove t m = some t1 := by
  obtain ⟨t1, ht1, _⟩ :=
    fm_commute hnd (p := mf.src) ((Move.foundation_eta hdest).symm ▸ hfm) hm hsrc
  exact ⟨t1, ht1⟩

/-- If the reference move takes the very same card, it can be absorbed: either it
*is* our foundation move, or the card is parked somewhere and can be shipped to
the foundation from there. -/
theorem fm_absorb {s t s1 : State} {p : Position} {m : Move}
    (hfm : applyMove s ⟨p, Position.foundation⟩ = some t)
    (hm : applyMove s m = some s1)
    (hsrc : m.src = p) :
    t = s1 ∨ applyMove s1 ⟨m.dest, Position.foundation⟩ = some t := by
  simp only [applyMove_eq] at hfm hm
  obtain ⟨c, sp, htp, hdf⟩ := hfm
  obtain ⟨d, sq, htq, hdd⟩ := hm
  rw [hsrc, htp] at htq
  simp only [Option.some.injEq, Prod.mk.injEq] at htq
  obtain ⟨rfl, rfl⟩ := htq
  simp only [dropPosition, dropFoundation_eq] at hdf
  obtain ⟨hready, rfl⟩ := hdf
  cases hdest : m.dest with
  | foundation =>
    left
    rw [hdest] at hdd
    simp only [dropPosition, dropFoundation_eq] at hdd
    exact hdd.2.symm
  | cell i =>
    right
    rw [hdest] at hdd
    simp only [dropPosition, dropCell_eq] at hdd
    obtain ⟨hnone, rfl⟩ := hdd
    have hback : update sp.cells i (none : Option Card) = sp.cells := by
      rw [← hnone]; exact update_self _ _
    rw [applyMove_eq]
    refine ⟨c, sp, ?_, ?_⟩
    · simp only [takeFromPosition, takeFromCell_eq]
      refine ⟨by simp, ?_⟩
      apply State.ext' <;> simp [update2, hback]
    · simp only [dropPosition, dropFoundation_eq]
      exact ⟨hready, trivial⟩
  | pile j =>
    right
    rw [hdest] at hdd
    simp only [dropPosition, dropCol_eq] at hdd
    obtain ⟨hhead, rfl⟩ := hdd
    rw [applyMove_eq]
    refine ⟨c, sp, ?_, ?_⟩
    · simp only [takeFromPosition, takeFromCol_eq]
      refine ⟨sp.tableau j, by simp, ?_⟩
      apply State.ext' <;> simp [update2, update_self]
    · simp only [dropPosition, dropFoundation_eq]
      exact ⟨hready, trivial⟩

/-! ## Foundation moves never undo progress -/

theorem FMStep.king {s t : State} (h : FMStep s t) (suit : Suit)
    (hs : s.foundations suit = some Rank.king) :
    t.foundations suit = some Rank.king := by
  obtain ⟨p, hp⟩ := h
  simp only [applyMove_eq] at hp
  obtain ⟨c, sp, htp, hdf⟩ := hp
  simp only [dropPosition, dropFoundation_eq] at hdf
  obtain ⟨hready, rfl⟩ := hdf
  have hfsp : sp.foundations = s.foundations := takeFromPosition_foundations htp
  rw [hfsp] at hready
  have hne : c.suit ≠ suit := by
    intro heq
    rw [heq, hs, nextRank_king] at hready
    simp at hready
  simp only [updateFoundation_foundations, update_diff _ _ _ _ hne, hfsp, hs]

theorem beq_king_iff (x : Option Rank) :
    (x == some Rank.king) = true ↔ x = some Rank.king := by
  cases x with
  | none => simp
  | some r => cases r <;> simp <;> decide

theorem isGoal_iff {s : State} :
    isGoal s = true ↔ ∀ suit : Suit, s.foundations suit = some Rank.king := by
  simp only [isGoal, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_king_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ suit; cases suit <;> assumption
  · intro h; exact ⟨h _, h _, h _, h _⟩

theorem FMReach.isGoal {s t : State} (h : FMReach s t) (hg : isGoal s = true) :
    isGoal t = true := by
  induction h with
  | refl => exact hg
  | tail _ hst ih =>
    rw [isGoal_iff] at ih ⊢
    exact fun suit => hst.king suit (ih suit)

theorem NoDupState.fmReach {s t : State} (h : NoDupState s) (hr : FMReach s t) :
    NoDupState t := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => obtain ⟨p, hp⟩ := hst; exact ih.applyMove hp

/-! ## The simulation lemma -/

/-- Having played a run of foundation moves `s ⇝ t`, any move `m` that is legal
in `s` can be answered from `t`: either `m` itself is still legal in `t` and the
foundation moves can be caught up afterwards, or `m` has already been subsumed
by the foundation moves, and `t` is still reachable from `s1` by foundation
moves alone. -/
theorem fm_simulate {s t s1 : State} {m : Move}
    (hnd : NoDupState s) (hreach : FMReach s t) (hm : applyMove s m = some s1) :
    (∃ t1, applyMove t m = some t1 ∧ FMReach s1 t1) ∨ FMReach s1 t := by
  induction hreach with
  | refl => exact Or.inl ⟨s1, hm, Relation.ReflTransGen.refl⟩
  | @tail u t hsu hut ih =>
    have hndu : NoDupState u := hnd.fmReach hsu
    rcases ih with ⟨u1, hu1, hru1⟩ | hru
    · obtain ⟨p, hp⟩ := hut
      by_cases hsrc : m.src = p
      · rcases fm_absorb hp hu1 hsrc with heq | hstep
        · exact Or.inr (heq ▸ hru1)
        · exact Or.inr (hru1.tail ⟨m.dest, hstep⟩)
      · obtain ⟨t1, ht1, hback⟩ := fm_commute hndu hp hu1 hsrc
        exact Or.inl ⟨t1, ht1, hru1.tail ⟨p, hback⟩⟩
    · exact Or.inr (hru.tail hut)

/-! ## Main results -/

/-- Playing foundation moves never destroys solvability. -/
theorem Solvable.of_fmReach {s : State} (hs : Solvable s) :
    ∀ {t : State}, NoDupState s → FMReach s t → Solvable t := by
  induction hs with
  | done hg => intro t _ hr; exact Solvable.done (FMReach.isGoal hr hg)
  | @step s s1 m hm _ ih =>
    intro t hnd hr
    rcases fm_simulate hnd hr hm with ⟨t1, ht1, hr1⟩ | hr1
    · exact Solvable.step m ht1 (ih (hnd.applyMove hm) hr1)
    · exact ih (hnd.applyMove hm) hr1

/-- **A foundation move is never harmful.**  If a duplicate-free position is
solvable, then so is the position obtained by playing an arbitrary move onto
the foundation. -/
theorem foundationMove_preserves_Solvable {s t : State} {m : Move}
    (hnd : NoDupState s) (hdest : IsFoundationMove m)
    (hm : applyMove s m = some t) (hs : Solvable s) : Solvable t := by
  exact hs.of_fmReach hnd
    (Relation.ReflTransGen.single ⟨m.src, (Move.foundation_eta hdest).symm ▸ hm⟩)

/-- The same statement in terms of `isSolution`. -/
theorem foundationMove_preserves_isSolution {s t : State} {m : Move} {sol : List Move}
    (hnd : NoDupState s) (hdest : IsFoundationMove m)
    (hm : applyMove s m = some t) (hsol : isSolution s sol = true) :
    ∃ sol' : List Move, isSolution t sol' = true :=
  exists_solution_of_solvable
    (foundationMove_preserves_Solvable hnd hdest hm (solvable_of_isSolution hsol))
