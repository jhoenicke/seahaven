import Seahaven.FluteMoves

/-!
# Playing a run of cards to the foundation

`SolverMoveAces` ships a *consecutive run of one suit* to the foundation in a
single call: starting just above `aces[suit]`, it walks upwards for as long as
the next card is either already free or exposed at its pile's boundary.

This file is the `Rules.State` counterpart.  `PlaysTo s c t` says that card `c`
is played onto its foundation from wherever it currently sits, and `PlaysAll`
iterates that over a list of cards.  The headline results are

* `ready_tail` — readiness propagates along a run, so a caller only ever has to
  supply *accessibility* of the next card, never readiness;
* `playsAll_column` — a run exposed on top of a pile plays off completely, which
  is exactly the `cardDepth == 0` cascade of `SolverMoveAces`;
* the transfer lemmas to `FMReach` and hence to `Solvable`, in both directions.

Everything here is independent of the solver's layout tables.
-/

/-! ## One card to its foundation -/

/-- `PlaysTo s c t`: the card `c` is taken from wherever it is accessible in `s`
and dropped on its foundation, giving `t`. -/
def PlaysTo (s : State) (c : Card) (t : State) : Prop :=
  ∃ (pos : Position) (s0 : State),
    takeFromPosition s pos = some (c, s0) ∧ dropFoundation s0 c = some t

theorem PlaysTo.toFMStep {s t : State} {c : Card} (h : PlaysTo s c t) : FMStep s t := by
  obtain ⟨pos, s0, ht, hd⟩ := h
  exact ⟨pos, by rw [applyMove_eq]; exact ⟨c, s0, ht, hd⟩⟩

theorem PlaysTo.ready {s t : State} {c : Card} (h : PlaysTo s c t) :
    some c.rank = nextRank (s.foundations c.suit) := by
  obtain ⟨pos, s0, ht, hd⟩ := h
  obtain ⟨hready, _⟩ := dropFoundation_eq.1 hd
  rwa [takeFromPosition_foundations ht] at hready

theorem PlaysTo.foundations {s t : State} {c : Card} (h : PlaysTo s c t) :
    t.foundations = update s.foundations c.suit c.rank := by
  obtain ⟨pos, s0, ht, hd⟩ := h
  obtain ⟨_, rfl⟩ := dropFoundation_eq.1 hd
  rw [updateFoundation_foundations, takeFromPosition_foundations ht]

/-- The card came either from a cell or from the top of a pile, and the
resulting state is completely determined. -/
theorem PlaysTo.cases {s t : State} {c : Card} (h : PlaysTo s c t) :
    (∃ i : Fin 4, s.cells i = some c ∧ t = updateFoundation (updateCell s i none) c) ∨
    (∃ (q : Fin 10) (rest : Column), s.tableau q = c :: rest ∧
      t = updateFoundation (updateColumn s q rest) c) := by
  obtain ⟨pos, s0, ht, hd⟩ := h
  obtain ⟨_, rfl⟩ := dropFoundation_eq.1 hd
  cases pos with
  | foundation => simp [takeFromPosition] at ht
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at ht
    obtain ⟨hc, rfl⟩ := ht
    exact Or.inl ⟨i, hc, rfl⟩
  | pile q =>
    rw [takeFromPosition, takeFromCol_eq] at ht
    obtain ⟨rest, hcol, rfl⟩ := ht
    exact Or.inr ⟨q, rest, hcol, rfl⟩

theorem PlaysTo.of_cell {s : State} {i : Fin 4} {c : Card}
    (hc : s.cells i = some c) (hready : some c.rank = nextRank (s.foundations c.suit)) :
    PlaysTo s c (updateFoundation (updateCell s i none) c) := by
  refine ⟨Position.cell i, updateCell s i none, ?_, ?_⟩
  · simp only [takeFromPosition, takeFromCell_eq]; exact ⟨hc, trivial⟩
  · rw [dropFoundation_eq]; exact ⟨by simpa using hready, rfl⟩

theorem PlaysTo.of_pile {s : State} {q : Fin 10} {c : Card} {rest : Column}
    (hcol : s.tableau q = c :: rest)
    (hready : some c.rank = nextRank (s.foundations c.suit)) :
    PlaysTo s c (updateFoundation (updateColumn s q rest) c) := by
  refine ⟨Position.pile q, updateColumn s q rest, ?_, ?_⟩
  · simp only [takeFromPosition, takeFromCol_eq]; exact ⟨rest, hcol, rfl⟩
  · rw [dropFoundation_eq]; exact ⟨by simpa using hready, rfl⟩

/-- A card is *accessible* when it can be taken: it sits in a cell or on top of
a pile.  This is the only thing a caller has to establish — readiness comes free
along a run, see `ready_tail`. -/
def Accessible (s : State) (c : Card) : Prop :=
  (∃ i : Fin 4, s.cells i = some c) ∨ (∃ q : Fin 10, (s.tableau q).head? = some c)

theorem PlaysTo.of_accessible {s : State} {c : Card} (hacc : Accessible s c)
    (hready : some c.rank = nextRank (s.foundations c.suit)) : ∃ t, PlaysTo s c t := by
  rcases hacc with ⟨i, hc⟩ | ⟨q, hq⟩
  · exact ⟨_, PlaysTo.of_cell hc hready⟩
  · cases hcol : s.tableau q with
    | nil => rw [hcol] at hq; simp at hq
    | cons x xs =>
      rw [hcol] at hq
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst hq
      exact ⟨_, PlaysTo.of_pile hcol hready⟩

/-- **Readiness propagates along a run.**  Having played `c`, the next card of
the run is ready for the same foundation. -/
theorem ready_tail {s t : State} {c c' : Card}
    (hn : nextCard c = some c') (h : PlaysTo s c t) :
    some c'.rank = nextRank (t.foundations c'.suit) := by
  obtain ⟨hsuit, hrank⟩ := nextCard_eq hn
  rw [h.foundations, hsuit, update_same, nextRank]
  have : optRankToNat (some c.rank) + 1 = rankToNat c'.rank := by
    simp [optRankToNat, hrank]
  rw [this]
  exact (rankToNatToRank (some c'.rank)).symm

/-! ## A whole run -/

/-- `PlaysAll s cs t`: the cards `cs` are played to their foundations, in order. -/
inductive PlaysAll : State → List Card → State → Prop
  | nil (s : State) : PlaysAll s [] s
  | cons {s t u : State} {c : Card} {cs : List Card} :
      PlaysTo s c t → PlaysAll t cs u → PlaysAll s (c :: cs) u

theorem PlaysAll.toFMReach {s t : State} {cs : List Card} (h : PlaysAll s cs t) :
    FMReach s t := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons hc _ ih => exact Relation.ReflTransGen.head hc.toFMStep ih

theorem PlaysAll.toReach {s t : State} {cs : List Card} (h : PlaysAll s cs t) : Reach s t :=
  (NormReach.toReach (h.toFMReach.mono fun _ _ x => Or.inl x))

theorem PlaysAll.preserves_Solvable {s t : State} {cs : List Card}
    (hnd : NoDupState s) (h : PlaysAll s cs t) (hs : Solvable s) : Solvable t :=
  hs.of_fmReach hnd h.toFMReach

theorem PlaysAll.reflect_Solvable {s t : State} {cs : List Card}
    (h : PlaysAll s cs t) (ht : Solvable t) : Solvable s :=
  Solvable.of_reach h.toReach ht

theorem PlaysAll.append {s t u : State} {cs ds : List Card}
    (h1 : PlaysAll s cs t) (h2 : PlaysAll t ds u) : PlaysAll s (cs ++ ds) u := by
  induction h1 with
  | nil => exact h2
  | cons hc _ ih => exact PlaysAll.cons hc (ih h2)

theorem PlaysAll.foundations_of_forall_ne {s t : State} {cs : List Card}
    (h : PlaysAll s cs t) (v : Suit) (hv : ∀ c ∈ cs, c.suit ≠ v) :
    t.foundations v = s.foundations v := by
  induction h with
  | nil => rfl
  | @cons s t u c cs hc _ ih =>
    rw [ih (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc')), hc.foundations]
    exact update_diff _ _ _ _ (hv c (List.mem_cons_self ..))

theorem PlaysAll.foundations_getLast {s t : State} {cs : List Card} (h : PlaysAll s cs t) :
    ∀ c, cs.getLast? = some c → t.foundations c.suit = some c.rank := by
  induction h with
  | nil => simp
  | @cons s t u c cs hc hall ih =>
    intro d hd
    cases cs with
    | nil =>
      cases hall
      have hcd : c = d := by
        have h1 : ([c] : List Card).getLast? = some c := rfl
        rw [h1] at hd
        exact Option.some.inj hd
      subst hcd
      rw [hc.foundations, update_same]
    | cons e es => exact ih d (by simpa using hd)

/-- **A run exposed on top of a pile plays off completely.**  This is the
`cardDepth == 0` cascade of `SolverMoveAces`, on the `Rules` side. -/
theorem playsAll_column {s : State} {q : Fin 10} {cs rest : Column}
    (hcol : s.tableau q = cs ++ rest)
    (hrun : IsRun cs)
    (hready : ∀ c ∈ cs.head?, some c.rank = nextRank (s.foundations c.suit)) :
    ∃ t : State, PlaysAll s cs t ∧
      t.tableau q = rest ∧
      (∀ p, p ≠ q → t.tableau p = s.tableau p) ∧
      t.cells = s.cells := by
  induction cs generalizing s with
  | nil => exact ⟨s, PlaysAll.nil s, by simpa using hcol, fun p _ => rfl, rfl⟩
  | cons c cs' ih =>
    have hc : PlaysTo s c (updateFoundation (updateColumn s q (cs' ++ rest)) c) :=
      PlaysTo.of_pile (by simpa using hcol) (hready c (by simp))
    obtain ⟨t, hall, hta, htp, htc⟩ :=
      ih (s := updateFoundation (updateColumn s q (cs' ++ rest)) c) (by simp) hrun.tail
        (fun c' hc' => ready_tail (hrun.head c' hc') hc)
    exact ⟨t, PlaysAll.cons hc hall, hta,
      fun p hp => by rw [htp p hp]; simp [Ne.symm hp],
      by rw [htc]; rfl⟩

/-- The single-card counterpart, for a card sitting in a cell. -/
theorem playsAll_cell {s : State} {i : Fin 4} {c : Card}
    (hc : s.cells i = some c)
    (hready : some c.rank = nextRank (s.foundations c.suit)) :
    ∃ t : State, PlaysAll s [c] t ∧
      t.cells = update s.cells i none ∧
      t.tableau = s.tableau :=
  ⟨_, PlaysAll.cons (PlaysTo.of_cell hc hready) (PlaysAll.nil _), rfl, rfl⟩

/-! ## The run that `SolverMoveAces` plays

`SolverMoveAces` walks upwards from `aces[suit] + 1`.  On the `Rules` side that
start card is `nextFoundationCard`, and the run it walks is `runFrom`.  The
solver therefore only has to contribute a *count* — the `aces` delta — never the
cards themselves, which keeps the eventual bridge free of card decoding. -/

/-- The card currently playable on suit `su`'s foundation, if any. -/
def nextFoundationCard (s : State) (su : Suit) : Option Card :=
  (nextRank (s.foundations su)).map fun r => ({ suit := su, rank := r } : Card)

/-- The `n` cards starting at `oc` and ascending within the suit; shorter if the
suit runs out at the king. -/
def runFrom : Option Card → Nat → List Card
  | _, 0 => []
  | none, _ + 1 => []
  | some c, n + 1 => c :: runFrom (nextCard c) n

@[simp] theorem runFrom_zero (oc : Option Card) : runFrom oc 0 = [] := rfl
@[simp] theorem runFrom_none (n : Nat) : runFrom none n = [] := by cases n <;> rfl
@[simp] theorem runFrom_some (c : Card) (n : Nat) :
    runFrom (some c) (n + 1) = c :: runFrom (nextCard c) n := rfl

theorem head?_runFrom : ∀ (oc : Option Card) (n : Nat), ∀ y ∈ (runFrom oc n).head?, oc = some y
  | _, 0 => by simp
  | none, _ + 1 => by simp
  | some c, n + 1 => by
      intro y hy
      simp only [runFrom_some, List.head?_cons] at hy
      exact Option.mem_def.1 hy

theorem isRun_runFrom : ∀ (oc : Option Card) (n : Nat), IsRun (runFrom oc n)
  | _, 0 => by simp [IsRun]
  | none, _ + 1 => by simp [IsRun]
  | some c, n + 1 => ⟨head?_runFrom (nextCard c) n, isRun_runFrom (nextCard c) n⟩

theorem length_runFrom : ∀ (oc : Option Card) (n : Nat), (runFrom oc n).length ≤ n
  | _, 0 => by simp
  | none, _ + 1 => by simp
  | some c, n + 1 => by simpa using length_runFrom (nextCard c) n

theorem suit_runFrom {su : Suit} : ∀ (oc : Option Card) (n : Nat),
    (∀ c ∈ oc, c.suit = su) → ∀ c ∈ runFrom oc n, c.suit = su
  | _, 0 => by simp
  | none, _ + 1 => by simp
  | some c, n + 1 => by
    intro hoc d hd
    have hc : c.suit = su := hoc c rfl
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc
    · refine suit_runFrom (nextCard c) n ?_ d hd
      intro e he
      rw [(nextCard_eq he).1]
      exact hc

theorem nextFoundationCard_spec {s : State} {su : Suit} {c : Card}
    (h : nextFoundationCard s su = some c) :
    c.suit = su ∧ some c.rank = nextRank (s.foundations c.suit) := by
  unfold nextFoundationCard at h
  cases hr : nextRank (s.foundations su) with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, by rw [hr]⟩

/-- The head of the run the solver walks is ready for its foundation — so a
caller only ever has to establish *accessibility*, using `PlaysTo.of_accessible`
and `ready_tail` to step along. -/
theorem ready_head_runFrom {s : State} {su : Suit} {n : Nat} :
    ∀ c ∈ (runFrom (nextFoundationCard s su) n).head?,
      some c.rank = nextRank (s.foundations c.suit) := by
  intro c hc
  exact (nextFoundationCard_spec (head?_runFrom _ n c hc)).2

/-- Playing the whole run advances exactly one foundation, and only that one. -/
theorem PlaysAll.runFrom_foundations {s t : State} {su : Suit} {n : Nat}
    (h : PlaysAll s (runFrom (nextFoundationCard s su) n) t) (v : Suit) (hv : v ≠ su) :
    t.foundations v = s.foundations v := by
  refine h.foundations_of_forall_ne v (fun c hc hcv => hv ?_)
  rw [← hcv]
  exact suit_runFrom (su := su) _ n
    (fun d hd => (nextFoundationCard_spec hd).1) c hc

/-- After playing the suit's next card, the suit's next card is the successor. -/
theorem nextFoundationCard_playsTo {s t : State} {su : Suit} {c : Card}
    (hsu : c.suit = su) (h : PlaysTo s c t) : nextFoundationCard t su = nextCard c := by
  have hf : t.foundations su = some c.rank := by
    rw [h.foundations, ← hsu, update_same]
  unfold nextFoundationCard nextCard
  rw [hf, ← hsu]
  cases nextRank (some c.rank) <;> simp

/-- **The whole run plays, driven by an accessibility invariant.**

`P` is whatever the caller knows about the state — in the eventual bridge it will
be derived from a `Rules.State ↔ SolverPosType` matching relation.  All the
caller must supply is that `P` makes the suit's next card accessible and is
preserved by playing it; readiness and the shape of the run come for free. -/
theorem exists_playsAll_runFrom {su : Suit} (P : State → Prop)
    (hstep : ∀ (u : State) (c : Card), P u → nextFoundationCard u su = some c →
      Accessible u c ∧ ∀ t, PlaysTo u c t → P t) :
    ∀ (n : Nat) (s : State), P s →
      ∃ t, PlaysAll s (runFrom (nextFoundationCard s su) n) t ∧ P t := by
  intro n
  induction n with
  | zero => intro s hs; exact ⟨s, PlaysAll.nil s, hs⟩
  | succ n ih =>
    intro s hs
    cases hnf : nextFoundationCard s su with
    | none => exact ⟨s, by rw [runFrom_none]; exact PlaysAll.nil s, hs⟩
    | some c =>
      obtain ⟨hacc, hpres⟩ := hstep s c hs hnf
      obtain ⟨hsu, hready⟩ := nextFoundationCard_spec hnf
      obtain ⟨t1, hplay⟩ := PlaysTo.of_accessible hacc hready
      obtain ⟨t, hall, hPt⟩ := ih t1 (hpres t1 hplay)
      rw [nextFoundationCard_playsTo hsu hplay] at hall
      exact ⟨t, by rw [runFrom_some]; exact PlaysAll.cons hplay hall, hPt⟩
