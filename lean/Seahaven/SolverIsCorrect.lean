import Seahaven.SolveCorrect
import Seahaven.ConvertMatch
import Seahaven.ReachableMatch
import Seahaven.CleanupLax
import Seahaven.KingPileMax
import Seahaven.DealMatches
import Seahaven.SolverCorrectness

/-!
# `solver_is_correct`

The end-to-end statement `Correctness` (`SolverCorrectness`), discharged.

The two global invariants are:

* `inv0 g` — the two `Globals` bounds `initcard` needs to be *entered* with.  It
  says nothing about the deal, only that `card2pile`/`card2depth` are in range, so
  it holds of `emptyGlobals` and is implied by everything stronger.
* `inv1 sh g` — `WellFormedLayout g` (the deal arrays are a consistent layout),
  `HashmapCorrect g` (the memo table is two-sidedly right), and `InitInv sh 52 g`
  read *modulo the memo table*, which is what pins the layout to *this* shuffle.
  The `{ g with hashmap := … }` in `InitInv52` is not a trick to weaken the
  invariant: `InitInv`'s `memo_zero` clause is about a freshly cleared table and is
  false after the first `solve`, while its other four clauses never look at the
  hashmap at all.

This file is organized as

1. **the deal bridge** — `Shuffle.vector` really is a deal, and the state
   `Rules.init` builds from a `Shuffle` is the one `DealMatches` reasons about;
2. **the invariants** — `inv0`/`inv1` and the `initcard` obligation;
3. **the query** — `solve (pilesKingsFromState s)` on a reachable `s`.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## 1. The deal bridge

`Shuffle.vector` writes card `c` as `13 * suit + rank`, which is exactly
`encodeShuffle (encodeCard c)`; so `decodeShuffle` recovers the solver's card code
and `dealCards` recovers the `Rules` card. -/

theorem cardToNat_eq (c : Card) : cardToNat c = 13 * suitToNat c.suit + rankToNat c.rank := by
  rw [cardToNat, suit_idxOf]

theorem cardToNat_bounds (c : Card) : 1 ≤ cardToNat c ∧ cardToNat c ≤ 52 := by
  rw [cardToNat_eq]
  have h1 : suitToNat c.suit ≤ 3 := by cases c.suit <;> decide
  have h2 : 1 ≤ rankToNat c.rank := by cases c.rank <;> decide
  have h3 : rankToNat c.rank ≤ 13 := rankBounded c.rank
  omega

theorem cardToNat_inj {c d : Card} (h : cardToNat c = cardToNat d) : c = d := by
  rw [cardToNat_eq, cardToNat_eq] at h
  have h1 : suitToNat c.suit ≤ 3 := by cases c.suit <;> decide
  have h2 : suitToNat d.suit ≤ 3 := by cases d.suit <;> decide
  have h3 : 1 ≤ rankToNat c.rank ∧ rankToNat c.rank ≤ 13 := ⟨by cases c.rank <;> decide,
    rankBounded c.rank⟩
  have h4 : 1 ≤ rankToNat d.rank ∧ rankToNat d.rank ≤ 13 := ⟨by cases d.rank <;> decide,
    rankBounded d.rank⟩
  have hs : suitToNat c.suit = suitToNat d.suit := by omega
  have hr : rankToNat c.rank = rankToNat d.rank := by omega
  refine Card.ext ?_ (rankInj _ _ hr)
  revert hs; cases c.suit <;> cases d.suit <;> decide

/-- The shuffle vector's entry is the solver's `13 * suit + value` encoding. -/
theorem decodeShuffle_cardToNat (c : Card) :
    decodeShuffle (UInt8.ofNat (cardToNat c)) = encodeCard c := by
  rw [cardToNat_eq]
  unfold encodeCard
  cases c with
  | mk su rk => cases su <;> cases rk <;> decide

theorem shuffle_vector_get (sh : Shuffle) (i : Fin 52) :
    (sh.vector)[i.val]'i.isLt = UInt8.ofNat (cardToNat (sh.perm i)) := by
  show (Vector.ofFn (fun i : Fin 52 => UInt8.ofNat (cardToNat (sh.perm i))))[i.val] = _
  simp

theorem shuffle_vector_toNat (sh : Shuffle) (i : Fin 52) :
    ((sh.vector)[i.val]'i.isLt).toNat = cardToNat (sh.perm i) := by
  rw [shuffle_vector_get, UInt8.toNat_ofNat']
  have := (cardToNat_bounds (sh.perm i)).2
  omega

/-- **A shuffle deals.** -/
theorem shuffle_isDeal (sh : Shuffle) : IsDeal sh.vector := by
  constructor
  · intro i h
    rw [show (sh.vector[i]'h) = (sh.vector[(⟨i, h⟩ : Fin 52).val]'h) from rfl,
      shuffle_vector_toNat]
    exact cardToNat_bounds _
  · intro i j hi hj h
    have h' : cardToNat (sh.perm ⟨i, hi⟩) = cardToNat (sh.perm ⟨j, hj⟩) := by
      rw [← shuffle_vector_toNat sh ⟨i, hi⟩, ← shuffle_vector_toNat sh ⟨j, hj⟩]
      exact congrArg UInt8.toNat h
    exact congrArg Fin.val (sh.inj _ _ (cardToNat_inj h'))

/-- **The deal is the shuffle.**  `DealMatches`' `dealCards` reconstruction of the
    deal from the vector gives back the shuffle's own permutation. -/
theorem dealCards_shuffle (sh : Shuffle) : dealCards sh.vector = sh.perm := by
  funext i
  unfold dealCards
  rw [dealCard, dif_pos i.isLt, shuffle_vector_get, decodeShuffle_cardToNat,
    decodeCard_encodeCard]
  rfl

/-- Hence the state `Rules.init` builds is `DealMatches`' `dealState`. -/
theorem dealState_shuffle (sh : Shuffle) : dealState sh.vector = _root_.init sh.perm := by
  rw [dealState, dealCards_shuffle]

/-! ## 2. The invariants -/

/-- What `initcard` must be entered with: the two array bounds it does not
    re-establish itself.  Nothing about the deal. -/
def Inv0 (g : Globals) : Prop :=
  (∀ (n : Nat) (h : n < 64), (g.card2pile[n]'h).toNat < 10) ∧
  (∀ (n : Nat) (h : n < 64), (g.card2depth[n]'h).toNat ≤ 5)

/-- `InitInv` with its `memo_zero` clause discarded: the four clauses that pin the
    layout to the shuffle, none of which reads the memo table. -/
def InitInv52 (sh : Vector UInt8 52) (g : Globals) : Prop :=
  InitInv sh 52 { g with hashmap := mkVector BIG_HASH_SIZE 0 }

/-- What holds after `initcard` and is preserved by every `solve`. -/
def Inv1 (sh : Shuffle) (g : Globals) : Prop :=
  WellFormedLayout g ∧ HashmapCorrect g ∧ InitInv52 sh.vector g

theorem Inv1.toInv0 {sh : Shuffle} {g : Globals} (h : Inv1 sh g) : Inv0 g :=
  ⟨fun n hn => h.2.2.pile_lt n hn, fun n hn => h.2.2.depth_le n hn⟩

theorem inv0_emptyGlobals : Inv0 emptyGlobals := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · show ((mkVector 64 (0 : UInt8))[n]'hn).toNat < 10
    rw [mkVector_getElem _ _ n hn]; decide
  · show ((mkVector 64 (0 : UInt8))[n]'hn).toNat ≤ 5
    rw [mkVector_getElem _ _ n hn]; decide

/-- `InitInv52` only reads `card2pile`, `card2depth` and `pos2card`, so a memo-table
    write cannot break it. -/
theorem InitInv52.set_hashmap {sh : Vector UInt8 52} {g : Globals}
    (h : InitInv52 sh g) (hm : Vector UInt16 BIG_HASH_SIZE) :
    InitInv52 sh { g with hashmap := hm } := h

/-- **`initcard` establishes `Inv1`.** -/
theorem inv1_of_initcard (sh : Shuffle) {g : Globals} (h : Inv0 g) :
    ∃ g' : Globals, EStateM.run (initcard sh.vector) g = .ok () g' ∧ Inv1 sh g' := by
  obtain ⟨g', hrun, hwf, hcor, -, hinv⟩ := initcard_ok' (shuffle_isDeal sh) g h.1 h.2
  exact ⟨g', hrun, hwf, hcor,
    { pile_lt := hinv.pile_lt, depth_le := hinv.depth_le, located := hinv.located,
      placed := hinv.placed,
      memo_zero := fun n hn => mkVector_getElem _ _ n hn }⟩

/-- **`Inv1` is preserved by a memo-table write** — which, by the frame
    `solve_correct` reports, is the only thing a query does. -/
theorem Inv1.set_hashmap {sh : Shuffle} {g : Globals} (h : Inv1 sh g)
    (hm : Vector UInt16 BIG_HASH_SIZE) (hcor : HashmapCorrect { g with hashmap := hm }) :
    Inv1 sh { g with hashmap := hm } :=
  ⟨h.1.set_hashmap hm, hcor, h.2.2.set_hashmap hm⟩

/-! ## 3. What a reachable state is

Two facts about `isReachable (init sh.perm) s` that the query needs and that are
available now: the state still matches the *layout* (`pos2card`'s piles are still
prefixes of the columns, for some depth), and it is still a full deck. -/

theorem reach_of_isReachable {s t : State} (h : isReachable s t) : Reach s t := by
  obtain ⟨sol, hsol⟩ := h
  exact reach_of_foldl hsol

/-- The dealt state matches the layout `initcard` recorded. -/
theorem dealState_matchesLayout {sh : Vector UInt8 52} (hdeal : IsDeal sh) {g : Globals}
    (hinv : InitInv sh 52 g) : StateMatchesLayout g (dealState sh) where
  piles_match := fun i => ⟨⟨5, by omega⟩, dealState_pileMatches hdeal hinv i⟩
  cards_count := dealState_cards_count hdeal

/-- **And every reachable state does.**  `StateMatchesLayout.applyMove` along the
    play. -/
theorem matchesLayout_of_reach {g : Globals} {s t : State}
    (h : StateMatchesLayout g s) (hr : Reach s t) : StateMatchesLayout g t := by
  induction hr with
  | refl => exact h
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := hbc
    exact ih.applyMove hm

/-- `StateMatchesLayout` reads only `pos2card`, so a memo-table write cannot break it. -/
theorem StateMatchesLayout.set_hashmap {g : Globals} {hm : Vector UInt16 BIG_HASH_SIZE}
    {s : State} (h : StateMatchesLayout { g with hashmap := hm } s) :
    StateMatchesLayout g s :=
  ⟨h.piles_match, h.cards_count⟩

/-- **Every reachable state matches the layout `initcard` recorded.**  The dealt state
does (`dealState_matchesLayout`), and `StateMatchesLayout.applyMove` carries it along the
play. -/
theorem matchesLayout_of_reachable {sh : Shuffle} {g : Globals} (hinv : Inv1 sh g)
    {s : State} (hreach : isReachable (_root_.init sh.perm) s) : StateMatchesLayout g s := by
  have hdeal : StateMatchesLayout g (dealState sh.vector) :=
    StateMatchesLayout.set_hashmap (dealState_matchesLayout (shuffle_isDeal sh) hinv.2.2)
  rw [dealState_shuffle sh] at hdeal
  exact matchesLayout_of_reach hdeal (reach_of_isReachable hreach)

/-! ### The king bitmap is a nibble

`kingBit` sets at most one of the four low bits, so `pk[10] < 16` — the side
condition `kingCfgOf` needs. -/

theorem uint8_or_lt16 {x y : UInt8} (hx : x.toNat < 16) (hy : y.toNat < 16) :
    (x ||| y).toNat < 16 := by
  rw [UInt8.toNat_or]
  exact Nat.or_lt_two_pow (n := 4) hx hy

theorem kingBit_lt16 (col : Column) : (kingBit col).toNat < 16 := by
  unfold kingBit
  cases col with
  | nil => decide
  | cons c rest =>
    dsimp only
    split
    · have h : allSuits.idxOf c.suit < 4 := by cases c.suit <;> decide
      interval_cases h4 : (allSuits.idxOf c.suit) <;> decide
    · decide

theorem kingBitmap_lt16 (s : State) : (kingBitmap s).toNat < 16 := by
  unfold kingBitmap
  simp only [Fin.foldl_succ, Fin.foldl_zero]
  exact uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16
    (uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16 (uint8_or_lt16
      (by decide) (kingBit_lt16 _)) (kingBit_lt16 _)) (kingBit_lt16 _)) (kingBit_lt16 _))
      (kingBit_lt16 _)) (kingBit_lt16 _)) (kingBit_lt16 _)) (kingBit_lt16 _)) (kingBit_lt16 _))
    (kingBit_lt16 _)

/-- Hence the encoding's slot 10 is always a legal `kingCfgOf` argument. -/
theorem pilesKings_get10_lt16 (s : State) :
    ((pilesKingsFromState s).get ⟨10, by omega⟩).toNat < 16 := by
  show ((Vector.ofFn (fun pile : Fin 11 =>
    if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s)).get
      ⟨10, by omega⟩).toNat < 16
  rw [show (Vector.ofFn (fun pile : Fin 11 =>
      if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s)).get
        ⟨10, by omega⟩ = kingBitmap s from by
      show (Vector.ofFn (fun pile : Fin 11 =>
        if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s))[10] = _
      rw [Vector.getElem_ofFn]
      exact dif_neg (by decide)]
  exact kingBitmap_lt16 s

/-! ## 4. The query

Everything above is assembly.  What is left is the query itself: that
`solve (pilesKingsFromState s)` on a reachable `s` runs at all, and that its answer
is about `s`.  Stated as a named `Prop` — house style (`SolvableBits`) for an
obligation not yet discharged — so that nothing in this file is `sorry`d. -/

/-- **Obligation 1: the encoding is legal.**  `pilesKingsFromState` reports
`|removeFlute (tableau i)|` as pile `i`'s depth, and the solver's tables only run to
depth `5`.  True because a move either pushes onto a column — extending its top run,
so `removeFlute` is unchanged — or pops from it, and `removeFlute` never grows; the
dealt columns start at five.  (The `pk[10] < 16` half is `pilesKings_get10_lt16`.) -/
def ReachableValidDepths : Prop :=
  ∀ (sh : Shuffle) (s : State), isReachable (_root_.init sh.perm) s →
    ValidDepths (pilesKingsFromState s)

/-- **Obligation 1, discharged** (`ReachableMatch`).  There is no `Globals` in the
statement, so one is produced: `initcard` on the shuffle records the layout the state is
being measured against. -/
theorem reachableValidDepths : ReachableValidDepths := by
  intro sh s hreach
  obtain ⟨g, -, hinv⟩ := inv1_of_initcard sh inv0_emptyGlobals
  exact validDepths_pilesKings hinv.1 (matchesLayout_of_reachable hinv hreach)

/-- **Obligation 2: the answer is about `s`.**  Everything else a query needs — that
it returns at all (`solve_runs`), that it returns one of the two codes and writes
nothing but the memo table (`solve_frame`) — is now proved, so this is the whole
remaining content of `Correctness`.

It is no longer a monolith: `ConvertMatch` splits it into three, and
`reachableAnswer_of` below is the assembly.  What used to make it hard was that
`solve_correct` matched the state against `convertPre g pk` — a position with all
flutes at `1` and the *maximal* foundation, i.e. one no state of an ongoing game
matches.  `solve_correct_lax` matches against a position with the queried depths and
the state's *own* flutes and foundations (`CvEntry`), leaving convert's own loops to
close the gap; what is left over are the two simulation obligations `CvPrologueSim`
(loop 2) and `CvCleanupSim` (loop 3), and `ReachableEntry` below. -/
def ReachableAnswer : Prop :=
  ∀ (sh : Shuffle) (g : Globals), Inv1 sh g →
    ∀ s : State, isReachable (_root_.init sh.perm) s →
      ∀ (r : UInt8) (g' : Globals),
        EStateM.run (_root_.solve (pilesKingsFromState s)) g = .ok r g' →
        (r = UInt8.ofNat SUCCESS ↔ isSolvable s)

/-- **Obligation 2a: a reachable state matches its own encoding.**  The `Rules`-side
half, and all that is left of Obligation 2 once the convert call is read at the
entry state (`CvEntry`):

* `pileDepth s i = |removeFlute (tableau i)|` is a legal boundary — the column is a
  prefix of its dealt column with one same-suit descending run stacked on it, and
  `removeFlute` strips exactly that run, so `PileMatches` holds at that depth;
* the flutes are then the run lengths, and the foundations the state's own, so both
  clauses hold by construction;
* the configuration `kingBitmap s` names is realized: a column `removeFlute` empties
  is a run bottoming out at a king (`nextCard king = none` is what lets the recursion
  reach `[]`), which is exactly a king pile for the suit whose bit is set. -/
def ReachableEntry : Prop :=
  ∀ (sh : Shuffle) (g : Globals), Inv1 sh g →
    ∀ s : State, isReachable (_root_.init sh.perm) s →
      ∃ game' : SolverPosType,
        CvEntry g (pilesKingsFromState s) s game'
          (kingCfgOf (pilesKingsFromState s) (pilesKings_get10_lt16 s))

/-- **Obligation 2a, discharged** (`ReachableMatch`). -/
theorem reachableEntry : ReachableEntry := fun _ _ hinv s hreach =>
  exists_cvEntry hinv.1 (matchesLayout_of_reachable hinv hreach) (pilesKings_get10_lt16 s)

/-- **Obligation 2, assembled.**  `solve_correct_lax` answers about the state the
caller handed in, so nothing has to be normalized before the query. -/
theorem reachableAnswer_of (hvd : ReachableValidDepths) (hA : CvPrologueSim)
    (hE : ReachableEntry) : ReachableAnswer := by
  intro sh g hinv s hreach r g' hrun
  obtain ⟨game', hentry⟩ := hE sh g hinv s hreach
  obtain ⟨-, hcase⟩ := solve_correct_lax hA cvCleanupSim hinv.1 hinv.2.1 (hvd sh s hreach)
    (pilesKings_get10_lt16 s) hentry hrun
  rcases hcase with ⟨hr, hns⟩ | ⟨hr, hs⟩
  · exact ⟨fun h => absurd (h.symm.trans hr) (by decide), fun h => absurd h hns⟩
  · exact ⟨fun _ => hs, fun _ => hr⟩

/-! ## The theorem -/

/-- **The solver is correct**, given the two query obligations. -/
theorem solver_is_correct_of (hvd : ReachableValidDepths) (hans : ReachableAnswer) :
    Correctness := by
  refine ⟨Inv0, Inv1, inv0_emptyGlobals, fun sh g => ⟨Inv1.toInv0, ?_, ?_⟩⟩
  · exact fun h => inv1_of_initcard sh h
  · intro hinv s hreach
    have hpk : ValidDepths (pilesKingsFromState s) := hvd sh s hreach
    have hs10 := pilesKings_get10_lt16 s
    obtain ⟨r, g', hrun⟩ := solve_runs hinv.1 hinv.2.1 hpk hs10
    obtain ⟨hcode, hcor', hm, rfl⟩ := solve_frame hinv.1 hinv.2.1 hpk hs10 hrun
    refine ⟨_, r, hrun, hinv.set_hashmap hm hcor', ?_⟩
    have hiff := hans sh g hinv s hreach r _ hrun
    rcases hcode with h | h
    · exact Or.inr ⟨h, hiff.1 h⟩
    · refine Or.inl ⟨h, fun hsol => ?_⟩
      exact absurd (h.symm.trans (hiff.2 hsol)) (by decide)

/-- **The solver is correct**, in the three-obligation form: the encoding is legal
(`ReachableValidDepths`), a reachable state matches it (`ReachableEntry`), and convert's
loop 2 is simulated (`CvPrologueSim`). -/
theorem solver_is_correct_of' (hvd : ReachableValidDepths) (hA : CvPrologueSim)
    (hE : ReachableEntry) : Correctness :=
  solver_is_correct_of hvd (reachableAnswer_of hvd hA hE)

/-- **The solver is correct**, given only convert's loop-2 simulation.  The encoding is
legal and a reachable state matches it (`ReachableMatch`), and the cleanup loop is
simulated (`CleanupLax`), so all that is left of `Correctness` is that loop 2's writes —
the maximal foundation and the completed king piles — are realized by normalizing
moves. -/
theorem solver_is_correct_of_prologue (hA : CvPrologueSim) : Correctness :=
  solver_is_correct_of' reachableValidDepths hA reachableEntry

/-- **The solver is correct.**  Loop 2's simulation is `KingPileMax.cvPrologueSim`: the
maximal foundations are reached by foundation plays (`FoundationMax`) and the king piles by
cell-to-pile drops, so every position convert writes is reachable from the queried state by
solvability-preserving moves. -/
theorem solver_is_correct : Correctness :=
  solver_is_correct_of_prologue cvPrologueSim

end SolverSpec
