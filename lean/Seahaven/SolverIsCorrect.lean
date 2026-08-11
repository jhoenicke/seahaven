import Seahaven.SolveCorrect
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

theorem idxOf_suit (su : Suit) : allSuits.idxOf su = suitToNat su := by
  cases su <;> rfl

theorem cardToNat_eq (c : Card) : cardToNat c = 13 * suitToNat c.suit + rankToNat c.rank := by
  rw [cardToNat, idxOf_suit]

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

/-- **What a query on a reachable state does.**  The frame (`HashmapCorrect` plus
"only the memo table changed") is what carries `Inv1` across; the disjunction is the
answer.

Three things go into it, none of which is in the tree yet:

1. **totality** — `solve` is `partial_fixpoint` and every existing theorem about it
   is conditional on a successful run (`recCheck_run_loop_inv`, `recLoop_all`, …).
   Needs the `DepthSum` induction of `recCheck_spec` run in the *constructing*
   direction, with a "this step runs" lemma per array read and for `SolverMove`.
2. **the `Rules`-side bridge** — that `pilesKingsFromState s` is a legal encoding of
   a reachable `s` (depths `≤ 5`; `kingBitmap < 16`) and that `s` normalizes, by
   solvability-preserving moves, to a state matching the position convert computes
   for it, at the configuration `kingBitmap s` names.
3. **the canonical two-sided interface** — `solve_correct` matches against
   `convertPre`, whose flutes are all `1`, so it only speaks about states with no
   run on any pile; a normalized state has runs.  The reading that matches the
   position convert *returns* exists for soundness (`solve_sound_canonical`) but
   its completeness half additionally needs `BitSet fk (kingCfgOf pk h)` — that
   every king convert vacated is one the queried configuration piles. -/
def SolveQuery : Prop :=
  ∀ (sh : Shuffle) (g : Globals), Inv1 sh g →
    ∀ s : State, isReachable (_root_.init sh.perm) s →
      ∃ (g' : Globals) (res : UInt8),
        EStateM.run (_root_.solve (pilesKingsFromState s)) g = .ok res g' ∧
        HashmapCorrect g' ∧ (∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
        ((res = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨
          (res = UInt8.ofNat SUCCESS ∧ isSolvable s))

/-! ## The theorem -/

/-- **The solver is correct**, given the query obligation. -/
theorem solver_is_correct_of (hq : SolveQuery) : Correctness := by
  refine ⟨Inv0, Inv1, inv0_emptyGlobals, fun sh g => ⟨Inv1.toInv0, ?_, ?_⟩⟩
  · exact fun h => inv1_of_initcard sh h
  · intro hinv s hreach
    obtain ⟨g', res, hrun, hcor', ⟨hm, rfl⟩, hans⟩ := hq sh g hinv s hreach
    exact ⟨_, res, hrun, hinv.set_hashmap hm hcor', hans⟩

end SolverSpec
