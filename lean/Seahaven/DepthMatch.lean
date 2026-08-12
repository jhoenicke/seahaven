import Seahaven.MatchesDepth
import Seahaven.DeckCount

/-!
# Matching a depth vector, and the critical move

The completeness argument follows a winning play until the first move that changes
a pile's (merged) depth — the *critical move*.  The clean way to say "the depths
have not changed yet" is to match only the depth vector, ignoring `pileFlute` and
`kings`:

* `DepthMatchesV g u d` — for every pile, the bottom `d i` cards are the dealt ones
  and everything above them continues the boundary's run.

This is exactly the hypothesis `matches_of_depth_match` needs, so no separate
"loose match" notion (a flute split between its column and the cells) is required:
the pre-critical state's `DepthMatchesV` *is* the loose match.

The extraction then needs no invariance lemma at all.  A solved state does **not**
match a depth vector with a positive entry, so along any winning play the property
must fail somewhere; taking the first failure defines the critical move, and every
earlier state matches by construction.  What is needed instead is only

* the two endpoints — `not_depthMatchesV_of_goal` here, and
* the classification of a *breaking* move: since drops always preserve the match
  (`PileMatches_cons`) and takes preserve it while the depth still fits
  (`PileMatches_tail_same`), the breaking move must remove some pile's boundary card,
  which also pins `|tableau a| = d a` — precisely the `hcol` hypothesis of
  `DeckCount.usedSpace_add_flute_le`.
-/

/-- `u`'s columns match the depth vector `d`, ignoring `pileFlute` and `kings`. -/
def DepthMatchesV (g : Globals) (u : State) (d : Fin 10 → Fin 6) : Prop :=
  ∀ i : Fin 10, PileMatches g (u.tableau i) i (d i)

/-- The depth vector a position's `pileDepth` denotes. -/
def depthVec (p : SolverPosType) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (i : Fin 10) : Fin 6 :=
  ⟨(p.pileDepth.get i).toNat, hd6 i⟩

theorem depthMatchesV_iff_depth_match {g : Globals} {u : State} {p : SolverPosType}
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6) :
    DepthMatchesV g u (depthVec p hd6)
      ↔ ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩ :=
  Iff.rfl

/-! ## Removing the top card -/

private theorem IsSameSuitDescending_prefix {su : UInt8} {sv : Nat} {l l' : List UInt8}
    (h : IsSameSuitDescending su sv (l ++ l')) : IsSameSuitDescending su sv l := by
  intro i
  have hi : i.val < (l ++ l').length := by
    simp only [List.length_append]
    omega
  obtain ⟨hs, hv⟩ := h ⟨i.val, hi⟩
  simp only [List.get_eq_getElem, List.getElem_append_left i.isLt] at hs hv
  exact ⟨hs, hv⟩

/-- **Taking the top card off a column preserves the match**, as long as the depth
still fits — i.e. as long as the card taken was *not* the boundary. -/
theorem PileMatches_tail_same {g : Globals} {rest : Column} {a : Fin 10} {n : Fin 6} {c : Card}
    (hm : PileMatches g (c :: rest) a n) (hle : n.val ≤ rest.length) :
    PileMatches g rest a n := by
  obtain ⟨hlen, hbot, hflute⟩ := hm
  have hrevlen : n.val ≤ rest.reverse.length := by simpa using hle
  have hsplit : ((c :: rest).reverse.drop n.val).map encodeCard
      = ((rest.reverse.drop n.val).map encodeCard) ++ [encodeCard c] := by
    rw [List.reverse_cons, List.drop_append_of_le_length hrevlen, List.map_append]
    rfl
  refine ⟨hle, ?_, ?_⟩
  · intro k
    have hk := hbot k
    rw [List.reverse_cons, List.getElem?_append_left (by simpa using k.isLt.trans_le hle)] at hk
    exact hk
  · simp only [] at hflute ⊢
    rw [hsplit] at hflute
    by_cases hn : n.val > 0
    · rw [dif_pos hn] at hflute ⊢
      exact IsSameSuitDescending_prefix hflute
    · rw [dif_neg hn] at hflute ⊢
      obtain ⟨su, hsu⟩ := hflute
      exact ⟨su, IsSameSuitDescending_prefix hsu⟩

/-! ## A solved state matches no positive depth -/

theorem foundations_king_of_goal {u : State} (hgoal : isGoal u = true) (su : Suit) :
    u.foundations su = some Rank.king := by
  have h : ∀ v : Option Rank, (v == some Rank.king) = true → v = some Rank.king := by
    intro v hv
    cases v with
    | none => revert hv; decide
    | some r => cases r <;> revert hv <;> decide
  simp only [isGoal, List.all_cons, List.all_nil, Bool.and_eq_true] at hgoal
  cases su
  · exact h _ hgoal.1
  · exact h _ hgoal.2.1
  · exact h _ hgoal.2.2.2.1
  · exact h _ hgoal.2.2.1

theorem tableau_eq_nil_of_goal {u : State} (hcount : ∀ c : Card, countState u c = 1)
    (hgoal : isGoal u = true) (i : Fin 10) : u.tableau i = [] := by
  rcases hcol : u.tableau i with _ | ⟨c, cs⟩
  · rfl
  · exfalso
    have hmem : c ∈ u.tableau i := by rw [hcol]; exact List.mem_cons_self ..
    have h1 := one_le_countColumn hmem
    have h2 := countColumn_le_countTableau u.tableau c i
    have h3 : countFoundation u.foundations c = 1 := by
      unfold countFoundation
      refine if_neg ?_
      rw [foundations_king_of_goal hgoal c.suit,
        show optRankToNat (some Rank.king) = 13 from rfl]
      have := rankBounded c.rank
      omega
    have h4 := hcount c
    unfold countState at h4
    omega

/-- **The goal does not match a depth vector with a positive entry.**  Every column
is empty in a solved state, and `PileMatches` demands `d i ≤ |tableau i|`. -/
theorem not_depthMatchesV_of_goal {g : Globals} {u : State} {d : Fin 10 → Fin 6}
    (hcount : ∀ c : Card, countState u c = 1) (hgoal : isGoal u = true)
    {i : Fin 10} (hpos : 0 < (d i).val) : ¬ DepthMatchesV g u d := by
  intro h
  have h1 := (h i).1
  rw [tableau_eq_nil_of_goal hcount hgoal i] at h1
  simp only [List.length_nil] at h1
  omega

/-! ## Classifying the move that breaks the match

A *drop* never breaks it, and a *take* breaks it only by removing a boundary card.
So the first failure along a play is a move whose source pile has its boundary on
top — which is the critical move, and gives `hcol` for free. -/

/-- Dropping a card never breaks a depth match. -/
theorem DepthMatchesV.drop {g : Globals} {s0 v : State} {d : Fin 10 → Fin 6}
    (h : DepthMatchesV g s0 d) {dst : Position} {c : Card}
    (hd : dropPosition s0 dst c = some v) : DepthMatchesV g v d := by
  cases dst with
  | foundation =>
    rw [dropPosition, dropFoundation_eq] at hd
    obtain ⟨-, rfl⟩ := hd
    intro i
    simpa using h i
  | cell j =>
    rw [dropPosition, dropCell_eq] at hd
    obtain ⟨-, rfl⟩ := hd
    intro i
    simpa using h i
  | pile q =>
    rw [dropPosition, dropCol_eq] at hd
    obtain ⟨hhead, rfl⟩ := hd
    intro i
    by_cases hiq : i = q
    · subst hiq
      simpa using PileMatches_cons (h i) hhead
    · simpa [update, Ne.symm hiq] using h i

/-- **The breaking move takes a boundary card off a pile.** -/
theorem exists_boundary_of_break {g : Globals} {u v : State} {d : Fin 10 → Fin 6} {m : Move}
    (hm : applyMove u m = some v) (hu : DepthMatchesV g u d) (hv : ¬ DepthMatchesV g v d) :
    ∃ (a : Fin 10) (c : Card) (rest : Column),
      m.src = Position.pile a ∧ u.tableau a = c :: rest ∧ rest.length + 1 = (d a).val := by
  rw [applyMove_eq] at hm
  obtain ⟨c, s0, htake, hdrop⟩ := hm
  cases hsrc : m.src with
  | foundation =>
    rw [hsrc, takeFromPosition] at htake
    simp at htake
  | cell i =>
    exact absurd (DepthMatchesV.drop (by
      rw [hsrc, takeFromPosition, takeFromCell_eq] at htake
      obtain ⟨-, rfl⟩ := htake
      intro j
      simpa using hu j) hdrop) hv
  | pile a =>
    rw [hsrc, takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest, hcol, rfl⟩ := htake
    refine ⟨a, c, rest, rfl, hcol, ?_⟩
    have hlen : (d a).val ≤ (c :: rest).length := hcol ▸ (hu a).1
    by_contra hne
    refine hv (DepthMatchesV.drop (fun j => ?_) hdrop)
    by_cases hja : j = a
    · subst hja
      have h1 : PileMatches g (c :: rest) j (d j) := hcol ▸ hu j
      simpa using PileMatches_tail_same h1 (by
        simp only [List.length_cons] at hlen
        omega)
    · simpa [update, Ne.symm hja] using hu j

/-! ## The extraction

No invariance lemma is needed: the first failure along the play *defines* the
critical move, and every earlier state matches by construction. -/

/-- **Splitting a winning play at the critical move.**  If `u` matches a depth
vector with a positive entry and a play from `u` wins, then the play passes through
a state `t₀` that still matches, and its next move takes a boundary card off some
pile `a` (`|tableau a| = d a`, i.e. the flute is already parked). -/
theorem exists_critical_move {g : Globals} {d : Fin 10 → Fin 6} {i₀ : Fin 10}
    (hpos : 0 < (d i₀).val) :
    ∀ (ms : List Move) (u w : State), (∀ c : Card, countState u c = 1) →
      DepthMatchesV g u d → List.foldl applyMoveOpt (some u) ms = some w → isGoal w = true →
      ∃ (t₀ t₁ : State) (m : Move) (a : Fin 10) (c : Card) (rest : Column),
        Reach u t₀ ∧ DepthMatchesV g t₀ d ∧ applyMove t₀ m = some t₁ ∧ Reach t₁ w ∧
        t₀.tableau a = c :: rest ∧ rest.length + 1 = (d a).val := by
  intro ms
  induction ms with
  | nil =>
    intro u w hcount hd hrun hgoal
    simp only [List.foldl_nil, Option.some.injEq] at hrun
    subst hrun
    exact absurd hd (not_depthMatchesV_of_goal hcount hgoal hpos)
  | cons m rest ih =>
    intro u w hcount hd hrun hgoal
    rw [List.foldl_cons] at hrun
    cases hmv : applyMove u m with
    | none =>
      rw [show applyMoveOpt (some u) m = applyMove u m from rfl, hmv,
        foldl_applyMoveOpt_none] at hrun
      simp at hrun
    | some u' =>
      rw [show applyMoveOpt (some u) m = applyMove u m from rfl, hmv] at hrun
      by_cases hd' : DepthMatchesV g u' d
      · have hcount' : ∀ c : Card, countState u' c = 1 := by
          intro c
          rw [← congrFun (movePreservesCards u m u' hmv) c]
          exact hcount c
        obtain ⟨t₀, t₁, m', a, c, rst, hr, hdm, hap, hr2, hcol, hlen⟩ :=
          ih u' w hcount' hd' hrun hgoal
        exact ⟨t₀, t₁, m', a, c, rst, Relation.ReflTransGen.head ⟨m, hmv⟩ hr, hdm, hap, hr2,
          hcol, hlen⟩
      · obtain ⟨a, c, rst, -, hcol, hlen⟩ := exists_boundary_of_break hmv hd hd'
        exact ⟨u, u', m, a, c, rst, Relation.ReflTransGen.refl, hd, hmv,
          reach_of_foldl hrun, hcol, hlen⟩

/-! ## The middle layer: depths, king stacks, foundations — but not flute lengths

A state whose flutes are partly parked in cells satisfies every clause of
`StateMatchesSolverPos` *except* `flute_match`, whose equality degrades to `≤`.
That is exactly the layer the space count and the king refund need, and exactly
what the pre-critical state `exists_critical_move` returns provides.

Three layers, in increasing strength:

* `DepthMatchesV` — the depth vector only; what the prefix preserves by
  construction, and what `matches_of_depth_match` takes as `hdm`.
* `DepthPlusKings` — adds the king stacks, the foundations, and `flute_le`.
* `StateMatchesSolverPos` — recovered from the middle layer by CP-normality,
  which is what turns `flute_le` back into an equality (`DepthPlusKings.upgrade`).
-/

/-- **`StateMatchesSolverPos` without `flute_match`.**  The flute clause is weakened
to the inequality a parked state satisfies: a column never holds *more* than its
flute, but it may hold less, the difference sitting in cells. -/
structure DepthPlusKings (g : Globals) (u : State) (p : SolverPosType) : Prop where
  cards_count : ∀ c : Card, countState u c = 1
  depth_lt6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6
  depth_match : ∀ i : Fin 10,
    PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, depth_lt6 i⟩
  /-- A column the solver treats as empty carries *at most* its suit's king stack;
      it may hold less, the rest sitting in cells mid-reshuffle. -/
  king_le : ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 →
    ∀ c ∈ (u.tableau i).getLast?,
      (u.tableau i).length + (VALUE (p.kings.get (finOfSuit c.suit))).toNat ≤ 13
  aces_match : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)
  /-- The physical run above a boundary is at most the recorded flute; the
      difference is what has been parked into cells. -/
  flute_le : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
    (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat

/-- The same, together with a king configuration — the shape the refund bound
(`DeckCount.kingList_le_kingRefund`) consumes. -/
structure DepthPlusKingsCfg (g : Globals) (u : State) (p : SolverPosType) (k : Fin 16) : Prop where
  toDepthPlusKings : DepthPlusKings g u p
  realizes : RealizesKingConfig u p k
  no_pile : ∀ su : Suit, CfgBitSet k su → NoKingPile u p su

/-! ### Between the layers -/

theorem DepthPlusKings.toDepthMatchesV {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) : DepthMatchesV g u (depthVec p h.depth_lt6) :=
  h.depth_match

theorem DepthPlusKings.noDup {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) : NoDupState u :=
  fun c => le_of_eq (h.cards_count c)

/-- A full match is a middle-layer match: `flute_match`'s equality gives `flute_le`. -/
theorem StateMatchesSolverPos.toDepthPlusKings {g : Globals} {u : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g u p) : DepthPlusKings g u p where
  cards_count := h.cards_count
  depth_lt6 := h.depth_lt6
  depth_match := h.depth_match
  king_le := fun i hi c hc => le_of_eq (h.king_pile i hi c hc)
  aces_match := h.aces_match
  flute_le := fun i hi => by rw [h.flute_match i hi]

theorem StateMatchesKingConfig.toDepthPlusKingsCfg {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (h : StateMatchesKingConfig g u p k) :
    DepthPlusKingsCfg g u p k where
  toDepthPlusKings := h.toMatches.toDepthPlusKings
  realizes := h.realizes
  no_pile := h.no_pile

/-- **CP-normality upgrades the middle layer to a full match.**  This is
`matches_of_depth_match` read as "parking is the only difference": once no cell card
can be dropped, `flute_le` is an equality and the king stacks are exactly as tall as
`kings` says. -/
theorem DepthPlusKings.upgrade {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (h : DepthPlusKings g u p) (hcp : ∀ t, ¬ CPStep u t) :
    StateMatchesSolverPos g u p :=
  matches_of_depth_match hwf hb hpm h.depth_lt6 h.depth_match h.cards_count hcp h.aces_match

theorem DepthPlusKingsCfg.upgrade {g : Globals} {u : State} {p : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (h : DepthPlusKingsCfg g u p k) (hcp : ∀ t, ¬ CPStep u t) :
    StateMatchesKingConfig g u p k where
  toMatches := h.toDepthPlusKings.upgrade hwf hb hpm hcp
  realizes := h.realizes
  no_pile := h.no_pile

/-! ### The space count, over the middle layer

`DeckCount`'s bound needs only `cards_count`, `aces_match` and `flute_le`, all of
which the middle layer has — so it applies to the pre-critical state directly. -/

theorem DepthPlusKings.usedSpace_add_flute_le {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (h : DepthPlusKings g u p)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    p.usedSpace.toInt + ((p.pileFlute.get a).toNat : Int) - 1
      ≤ 4 + ((kingList u p).length : Int) :=
  _root_.usedSpace_add_flute_le hb h.cards_count h.aces_match h.flute_le a hda hcol

/-- **The middle layer needs no extra assumptions.**  Both `≤` clauses are
*derived* — `flute_le_of_depth` from `flute_maximal`, `king_le_of_depth` from
`king_frontier` — so the depth match, the card count and the foundations are all the
input there is.  CP-normality is what turns the two `≤` into `=`
(`DepthPlusKings.upgrade`). -/
theorem DepthPlusKings.of_depthMatch {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hb.pileDepth_bound i))
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    DepthPlusKings g u p where
  cards_count := hcount
  depth_lt6 := hd6
  depth_match := hdm
  king_le := fun i hi => king_le_of_depth hwf hb hd6 hdm hcount haces i hi
  aces_match := haces
  flute_le := fun i hi => flute_le_of_depth hwf hb hd6 hdm hcount haces i (hpm i) hi

/-! ## The prefix, as a chain

`exists_critical_move_aces` walks the winning play until the depth vector breaks.
Plain `Reach` forgets what happened in between, but the king-configuration argument
(`EmptyPileCfg`) has to look at *every* state of that prefix — it asks where a
column first became physically empty.  So the extraction hands back a chain whose
every state is still a middle-layer match.

`DepthPlusKings` is carried on the *target* of each step; the source of the whole
chain has to be supplied separately, which is exactly how the caller has it. -/

/-- One move of the prefix: a legal move whose target still matches `p` at the
middle layer. -/
def PrefixStep (g : Globals) (p : SolverPosType) (u v : State) : Prop :=
  MoveStep u v ∧ DepthPlusKings g v p

/-- Reachability through states that all still match `p` at the middle layer. -/
abbrev PrefixReach (g : Globals) (p : SolverPosType) : State → State → Prop :=
  Relation.ReflTransGen (PrefixStep g p)

theorem PrefixStep.toMoveStep {g : Globals} {p : SolverPosType} {u v : State}
    (h : PrefixStep g p u v) : MoveStep u v := h.1

theorem PrefixReach.toReach {g : Globals} {p : SolverPosType} {u v : State}
    (h : PrefixReach g p u v) : Reach u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toMoveStep

/-- **Every state of the chain matches**, the far end included. -/
theorem PrefixReach.dpk {g : Globals} {p : SolverPosType} {u v : State}
    (hu : DepthPlusKings g u p) (h : PrefixReach g p u v) : DepthPlusKings g v p := by
  induction h with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2

/-! ## The king configuration a state *is* in

Nothing has to choose a configuration: the piled suits are a function of the
state, so the configuration is too.  `CfgBitSet` has the opposite polarity (a set
bit means "no pile of its own"), so the mask is the complement of the piled set,
and `bits2grlex` turns it into the grlex index the solver's blocks are indexed by. -/

/-- Suit `su` owns a pile in `u`: some solver-empty column's deepest card is its. -/
def PiledSuit (u : State) (p : SolverPosType) (su : Suit) : Prop :=
  ∃ i : Fin 10, (p.pileDepth.get i).toNat = 0 ∧ ∃ d ∈ (u.tableau i).getLast?, d.suit = su

theorem noKingPile_of_not_piled {u : State} {p : SolverPosType} {su : Suit}
    (h : ¬ PiledSuit u p su) : NoKingPile u p su := by
  intro i hd0 d hd hsu
  exact h ⟨i, hd0, d, hd, hsu⟩

/-- The grlex index of a mask. -/
def cfgOfMask (m : Fin 16) : Fin 16 := ⟨(bits2grlex.get m).toNat, bits2grlex_lt m⟩

theorem cfgBitSet_cfgOfMask (m : Fin 16) (su : Suit) :
    CfgBitSet (cfgOfMask m) su ↔ m.val / 2 ^ (suitToNat su) % 2 = 1 := by
  unfold CfgBitSet cfgOfMask
  rw [grlex_bits_inv m]

open Classical in
/-- The internal mask of the configuration `u` realizes: bit set = *no* pile. -/
noncomputable def piledMaskNat (u : State) (p : SolverPosType) : Nat :=
  (if PiledSuit u p Suit.clubs then 0 else 1)
    + (if PiledSuit u p Suit.diamonds then 0 else 2)
    + (if PiledSuit u p Suit.hearts then 0 else 4)
    + (if PiledSuit u p Suit.spades then 0 else 8)

theorem piledMaskNat_lt (u : State) (p : SolverPosType) : piledMaskNat u p < 16 := by
  unfold piledMaskNat
  split_ifs <;> omega

theorem piledMaskNat_bit (u : State) (p : SolverPosType) (su : Suit) :
    piledMaskNat u p / 2 ^ (suitToNat su) % 2 = 1 ↔ ¬ PiledSuit u p su := by
  unfold piledMaskNat
  cases su <;> simp only [suitToNat_clubs, suitToNat_diamonds, suitToNat_hearts,
    suitToNat_spades] <;> split_ifs <;> simp_all

/-- **The configuration `u` realizes**, as a function of the state. -/
noncomputable def cfgOf (u : State) (p : SolverPosType) : Fin 16 :=
  cfgOfMask ⟨piledMaskNat u p, piledMaskNat_lt u p⟩

theorem cfgBitSet_cfgOf (u : State) (p : SolverPosType) (su : Suit) :
    CfgBitSet (cfgOf u p) su ↔ ¬ PiledSuit u p su := by
  rw [cfgOf, cfgBitSet_cfgOfMask]
  exact piledMaskNat_bit u p su

theorem noKingPile_cfgOf {u : State} {p : SolverPosType} {su : Suit}
    (h : CfgBitSet (cfgOf u p) su) : NoKingPile u p su :=
  noKingPile_of_not_piled ((cfgBitSet_cfgOf u p su).1 h)

open Classical in
/-- **Every middle-layer state realizes the configuration it *is* in.**  The
assignment is "the column that suit's stack sits on", unique by `getLast?`; the
deepest card of a solver-empty column is a king by `PileMatches.king_run`, which is
what `OwnsPile` asks for. -/
theorem DepthPlusKings.toCfg {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) : DepthPlusKingsCfg g u p (cfgOf u p) where
  toDepthPlusKings := h
  no_pile := fun _ hbit => noKingPile_cfgOf hbit
  realizes := by
    refine ⟨fun s' => if hp : PiledSuit u p s' then some hp.choose else none, ?_, ?_, ?_⟩
    · intro su i hassign
      simp only [] at hassign
      have hp : PiledSuit u p su := by
        by_contra hn
        rw [dif_neg hn] at hassign
        simp at hassign
      rw [dif_pos hp] at hassign
      have hi : hp.choose = i := Option.some.inj hassign
      obtain ⟨hd0, d, hd, hsu⟩ := hp.choose_spec
      rw [hi] at hd0 hd
      refine ⟨hd0, Or.inl ⟨d, hd, hsu, ?_⟩⟩
      have hr0l : 0 < (u.tableau i).reverse.length := by
        cases hcol : u.tableau i with
        | nil => rw [Option.mem_def, hcol] at hd; simp at hd
        | cons x xs => simp
      have hdeep : (u.tableau i).reverse[0]'hr0l = d := by
        have h1 : (u.tableau i).reverse.head? = some d := by
          rw [List.head?_reverse]; exact hd
        have h2 : (u.tableau i).reverse.head? = (u.tableau i).reverse[0]? :=
          List.head?_eq_getElem?
        rw [h1, List.getElem?_eq_getElem hr0l] at h2
        exact (Option.some.inj h2).symm
      obtain ⟨su', hrun⟩ := (h.depth_match i).king_run hd0
      obtain ⟨-, hv⟩ := hrun 0 hr0l
      rw [hdeep, encodeCard_VALUE] at hv
      exact rank_king_of_13 (by omega)
    · intro su su' i h1 h2
      simp only [] at h1 h2
      have hp : PiledSuit u p su := by
        by_contra hn; rw [dif_neg hn] at h1; simp at h1
      have hp' : PiledSuit u p su' := by
        by_contra hn; rw [dif_neg hn] at h2; simp at h2
      rw [dif_pos hp] at h1
      rw [dif_pos hp'] at h2
      obtain ⟨-, d, hd, hsu⟩ := hp.choose_spec
      obtain ⟨-, d', hd', hsu'⟩ := hp'.choose_spec
      rw [Option.some.inj h1, Option.mem_def] at hd
      rw [Option.some.inj h2, Option.mem_def] at hd'
      rw [← hsu, ← hsu', congrArg Card.suit (Option.some.inj (hd.symm.trans hd'))]
    · intro su
      simp only []
      rw [cfgBitSet_cfgOf]
      by_cases hp : PiledSuit u p su
      · simp [hp]
      · simp [hp]

/-! ## Buried cards stay buried

`aces_match` is threaded along the prefix by a single fact about the *initial*
position: each suit's next foundation card is strictly below its boundary, and a
card strictly below a boundary is inaccessible at *every* depth-matching state.  So
while the depth vector is unchanged no foundation move is possible, and the
foundations — hence `aces_match` — are constant. -/

/-- **A card strictly below its boundary is neither in a cell nor on top of a
column.**  It sits at its own dealt slot, with the dealt cards above it still in
place; needs nothing but the depth match. -/
theorem buried_inaccessible {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) {c : Card}
    (hp10 : (cardPile g (encodeCard c)).toNat < 10)
    (hbur : (cardDepth g (encodeCard c)).toNat + 1
      < (p.pileDepth.get ⟨(cardPile g (encodeCard c)).toNat, hp10⟩).toNat) :
    (∀ i : Fin 4, u.cells i ≠ some c) ∧ (∀ q : Fin 10, (u.tableau q).head? ≠ some c) := by
  have hnd : NoDupState u := fun d => le_of_eq (hcount d)
  have hreal : IsRealCard (encodeCard c) := encodeCard_real c
  set P : Fin 10 := ⟨(cardPile g (encodeCard c)).toNat, hp10⟩ with hP
  have hd5 : (cardDepth g (encodeCard c)).toNat < 5 := by have := hd6 P; omega
  have hnL : (p.pileDepth.get P).toNat ≤ (u.tableau P).length := (hdm P).1
  have hnval : (⟨(p.pileDepth.get P).toNat, hd6 P⟩ : Fin 6).val
      = (p.pileDepth.get P).toNat := rfl
  have hrev : (cardDepth g (encodeCard c)).toNat < (u.tableau P).reverse.length := by
    simp only [List.length_reverse]; omega
  have hslot : (u.tableau P).reverse[(cardDepth g (encodeCard c)).toNat]'hrev = c :=
    encodeCard_inj (by
      rw [(hdm P).resident_code (by omega) hrev]
      exact hwf.round_trip (encodeCard c) hreal hd5)
  have hmemP : c ∈ u.tableau P := by
    rw [← hslot]; exact List.mem_reverse.mp (List.getElem_mem ..)
  refine ⟨fun i hi => hnd.not_mem_column_of_cell hi P hmemP, fun q hq => ?_⟩
  have hqP : q = P := hnd.pile_unique (List.mem_of_mem_head? (Option.mem_def.2 hq)) hmemP
  subst hqP
  have hrl : (u.tableau P).length - 1 < (u.tableau P).reverse.length := by
    simp only [List.length_reverse]; omega
  have hhead := head?_reverse_last (show 0 < (u.tableau P).length by omega) hrl
  rw [hq] at hhead
  have hnodup : (u.tableau P).reverse.Nodup := List.nodup_reverse.mpr (hnd.column_nodup P)
  have := hnodup.getElem_inj_iff.1 (hslot.trans (Option.some.inj hhead))
  omega
