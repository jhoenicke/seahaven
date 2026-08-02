import Seahaven.EStateMTail
import Seahaven.SolverInvariant

/-!
# `solverGetDestination`: explicit-loop twin and fuel model

`solverGetDestination` is the last loop-bearing solver function without a spec.

Its loop *used* to contain an early `return` (a king-frontier test) as well as a
`break`.  That test turned out to be dead — see "Where the walk stops" below —
and has been removed from both this model and `solver/solver.c`, so the loop is
now `break`-only and the twin below uses the simple accumulator.  The notes on
the early-`return` desugaring are kept because they are the general recipe, and
because the other direction was what made the dead code visible in the first
place.

## How `repeat` with `break` and `return` is translated

A `repeat` whose body only `break`s becomes `forIn Loop.mk acc body` with the
accumulator being just the tuple of mutable variables; `break` is
`ForInStep.done`, falling off the end is `ForInStep.yield`.

Adding an early `return` changes two things:

* the accumulator gains a leading `Option α` (α = the function's return type),
  giving `MProd (Option α) «mutables»`.  `return v` becomes
  `ForInStep.done ⟨some v, «mutables»⟩`; every other exit carries `none`;
* after the loop the function matches on that component —
  `match r.fst with | none => «code after the loop» | some a => pure a`.

Inside the body, an `if` *without* an `else` followed by more code becomes a
**join point**: `have jp := fun «mutables» (y : PUnit) => «continuation»`, and
the `if` reads
`if c then pure (.done ⟨some v, …⟩) else do let y ← pure PUnit.unit; jp «mutables» y`.

The practical consequences for writing a `rfl`-equal twin — all three were
needed to make `getDest_eq_explicit` go through:

1. destructure the accumulator with `have`, not `let`;
2. write the branch as an explicit `if … then … else …` with the continuation
   *inside* the `else`, rather than `if … then return …` followed by the
   continuation;
3. rebind updated mutables with `have` too.
-/

open Lean

/-- Accumulator of the `solverGetDestination` walk: `⟨card, posFromTop, toPile⟩`.

Now that the in-loop king test is gone (see below) the loop has no early
`return`, so the accumulator is just the mutables — no leading `Option`. -/
abbrev DestAcc := MProd CardType (MProd Int32 UInt8)

/-- Body of the `solverGetDestination` `repeat` loop. -/
def destBody (game : SolverPosType) (globals : Globals) :
    Unit → DestAcc → EStateM Error Globals (ForInStep DestAcc) :=
  fun _ r =>
    have card := r.fst
    have posFromTop := r.snd.fst
    have toPile := r.snd.snd
    do
      have card := card + 1
      let toPile ← globals.card2pile.getE card.toUInt32
      let pd ← game.pileDepth.getE toPile.toUInt32
      let cd ← globals.card2depth.getE card.toUInt32
      have posFromTop : Int32 := pd.toInt32 - cd.toUInt32.toInt32
      if posFromTop > 0 then pure (.done ⟨card, posFromTop, toPile⟩)
      else pure (.yield ⟨card, posFromTop, toPile⟩)

def getDestExplicit (game : SolverPosType) (pile : UInt32) : EStateM Error Globals UInt8 := do
  let globals ← get
  let depth ← game.pileDepth.getE pile
  let card ← (← globals.pos2card.getE pile).getE (depth.toInt32 - 1).toUInt32
  have suit : UInt8 := SUIT card
  let k ← game.kings.getE suit.toUInt32
  if (card.toInt8 == k) = true then pure (10 + suit)
  else do
    let r ← Loop.forIn Loop.mk (⟨card, 0, 0⟩ : DestAcc) (destBody game globals)
    pure (if (r.snd.fst == 1) = true then r.snd.snd else 14)

/-- The explicit-loop twin is definitionally the real function. -/
theorem getDest_eq_explicit : solverGetDestination = getDestExplicit := rfl

/-! ## Fuel model

The walk increments `card` every iteration and stops no later than
`kings[suit] ≤ CARD suit 13`, so `13 - VALUE card` iterations bound it. -/

/-- Run the loop for at most `fuel` iterations; `none` means fuel ran out. -/
def destFuel (game : SolverPosType) (globals : Globals) :
    Nat → DestAcc → EStateM Error Globals (Option DestAcc)
  | 0, _ => pure none
  | fuel + 1, acc => do
      match ← destBody game globals () acc with
      | .done a => pure (some a)
      | .yield a => destFuel game globals fuel a

/-- **Exact run.**  Whenever the fuel model finishes, the real loop agrees. -/
theorem destLoop_eq_of_fuel (game : SolverPosType) (globals : Globals) :
    ∀ (fuel : Nat) (acc res : DestAcc) (g g' : Globals),
      EStateM.run (destFuel game globals fuel acc) g = .ok (some res) g' →
      EStateM.run (Loop.forIn Loop.mk acc (destBody game globals)) g = .ok res g' := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc res g g' h
    simp [destFuel, EStateM.run, pure, EStateM.pure] at h
  | succ n ih =>
    intro acc res g g' h
    rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals) (l := Loop.mk) (b := acc)
      (f := destBody game globals)]
    rw [destFuel] at h
    cases hb : destBody game globals () acc g with
    | error e s => simp [EStateM.run, bind, EStateM.bind, hb] at h
    | ok st gm =>
      cases st with
      | done a =>
        simp only [EStateM.run, bind, EStateM.bind, hb, pure, EStateM.pure,
          EStateM.Result.ok.injEq, Option.some.injEq] at h ⊢
        exact h
      | yield a =>
        simp only [EStateM.run, bind, EStateM.bind, hb] at h ⊢
        exact ih a res gm g' h

/-! ## Where the walk stops

`SuitClean.king_frontier` (`SolverInvariant.lean:180`) pins this down, and it
makes the in-loop king test **dead code** under `IsCanonicalPos`.  Its two
disjuncts:

* `aces[s] < kings[s] ∧ ¬ isFreeCard kings[s]` — the normal case.  The walk
  advances to `B+k` only after finding `B+k` *free*, so it can never arrive at
  `kings[s]`; it breaks there (or earlier) via `posFromTop > 0` instead.
* `kings[s] = aces[s] ∧ (VALUE aces[s] = 13 ∨ busyAces bit set)`.  In a canonical
  position `busyAces = 0`, so `VALUE aces[s] = 13`: the whole suit is on the
  foundation, hence every card of `s` is free (`foundation_cards_free`) — so no
  pile boundary has suit `s` (`boundary_not_free`), and the walk never starts.

So the in-loop `card == kings[suit]` test can only fire at `k = 0`, where it
duplicates the pre-loop test.  Every other exit is the `break`, at the first
un-freed card above the boundary, which by `king_frontier`'s second conjunct is
at or below `kings[suit]` — giving both the destination and the `13 - VALUE B`
fuel bound. -/

/-- `posFromTop` of a card, as the loop computes it (clamped to stay total). -/
def posFromTopOf (g : Globals) (game : SolverPosType) (c : UInt8) : Int :=
  (game.pileDepth.get ⟨(cardPile g c).toNat % 10, Nat.mod_lt _ (by omega)⟩).toInt
    - (cardDepth g c).toNat

/-- **What `solverGetDestination` computes.**  Either the boundary card *is* the
king frontier and the answer is the king pile, or the walk stops at the first
un-freed card `B + n` above the boundary and the answer is that card's pile when
it is exposed, `EXTRA` otherwise. -/
def GetDestSpec : Prop :=
  ∀ (g : Globals) (game : SolverPosType) (pile : UInt32) (B : UInt8) (r : UInt8)
    (hp : pile.toNat < 10),
    WellFormedLayout g → IsCanonicalPos g game →
    0 < (game.pileDepth.get ⟨pile.toNat, hp⟩).toInt.toNat →
    -- `B` is pile `pile`'s flute boundary (depth clamped; under the invariant
    -- `pileDepth ≤ 5`, so the clamp never fires)
    B = (g.pos2card.get ⟨pile.toNat, hp⟩).get
          ⟨min ((game.pileDepth.get ⟨pile.toNat, hp⟩).toInt.toNat - 1) 4, by omega⟩ →
    EStateM.run (solverGetDestination game pile) g = .ok r g →
      (B.toInt8 = game.kings.get ⟨(SUIT B).toNat % 4, Nat.mod_lt _ (by omega)⟩ ∧
        r = 10 + SUIT B) ∨
      (∃ n : Nat, 1 ≤ n ∧
        (∀ j : Nat, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j)) ∧
        ¬ isFreeCard g game (B + UInt8.ofNat n) ∧
        (VALUE (B + UInt8.ofNat n)).toNat
          ≤ (VALUE (game.kings.get ⟨(SUIT B).toNat % 4, Nat.mod_lt _ (by omega)⟩).toUInt8).toNat ∧
        r = (if posFromTopOf g game (B + UInt8.ofNat n) = 1
             then cardPile g (B + UInt8.ofNat n) else 14))
