# A Verified Seahaven Towers Solver

This directory contains a Lean 4 proof that the Seahaven Towers solver in
[`../solver/solver.c`](../solver/solver.c) is correct: when asked about a game
position, it answers `SUCCESS` if and only if the position is solvable.

The final theorem is `solver_is_correct : Correctness` in
[`Seahaven/SolverIsCorrect.lean`](Seahaven/SolverIsCorrect.lean), proved
without any `sorry` or extra axioms.  Build with

```
lake build
```

## The main files

* **[`Seahaven/Rules.lean`](Seahaven/Rules.lean)** — the rules of the game.
  A `State` has ten tableau columns, four free cells and four foundations.
  A `Move` takes the top card of a column or a cell and drops it on a column
  (only on the next-higher card of the same suit, or a king on an empty
  column), a free cell, or the foundation.  `isSolvable s` says there is a
  sequence of moves from `s` that sends every card to the foundations;
  `isReachable` describes the states a player can reach from the initial deal.
  This file is the *trusted specification*: everything else is proved against
  these definitions.

* **[`Seahaven/Solver.lean`](Seahaven/Solver.lean)** — a Lean implementation
  of the solving algorithm, written to mirror the C implementation as closely
  as possible: the same global arrays (`pos2card`, `card2pile`, `card2depth`,
  the hash table), the same position representation (`SolverPosType`), and the
  same functions (`initcard`, `solve`, `solverRecCheckSolvable`,
  `SolverMove`, `SolverCleanupPile`, …), written in a state monad
  (`EStateM Error Globals`) so that array accesses and assertions can fail
  the way C array accesses would be out of bounds.  The recursive search is
  defined by `partial_fixpoint`, which gives a one-step unfolding equation to
  reason with without needing a termination proof up front.

* **[`Seahaven/SolverCorrectness.lean`](Seahaven/SolverCorrectness.lean)** —
  the correctness specification.  It defines the encoding
  `pilesKingsFromState : State → Vector UInt8 11` that the solver is queried
  with (the ten *merged* pile depths plus a bitmap of king-topped empty
  columns), and the statement `Correctness`: there are invariants on the
  solver's global state such that after `initcard` with the shuffle, calling
  `solve` on the encoding of **any** reachable state returns `SUCCESS` if the
  state is solvable and `NOMOVE` if it is not — and preserves the invariant,
  so the solver can be queried repeatedly.

* **[`Seahaven/SolverIsCorrect.lean`](Seahaven/SolverIsCorrect.lean)** — the
  final assembly `solver_is_correct : Correctness`, gluing the deal bridge
  (a `Shuffle` really deals the deck `initcard` records) to the invariants
  and the two directions of the query proof.

## Why the proof is hard

The solver does not search the game tree of `Rules.lean` moves.  For
performance it works on a heavily *normalized* abstraction of the game, and
the whole proof is about justifying that abstraction.

* **Normalization.**  The solver assumes cards are moved to the foundation as
  soon as possible, and it merges each column's top run of same-suit
  consecutive cards (a *flute*) into the card below it.  A single solver
  position therefore stands for many concrete game states.

* **Flute-level moves.**  One solver move relocates an entire flute: park the
  run's upper cards in free cells, move the boundary card to its destination,
  and re-merge.  Concretely that is a whole sequence of `Rules.lean` moves,
  and it is only legal if enough free cells are available — the solver checks
  this with a space count (`usedSpace`, `computeKingSpaces`).

* **King moves can cause cycles.**  Moving a king run between empty columns
  changes nothing measurable and can be undone, so a naive search loops.  The
  solver never makes such moves.  Instead it tracks *king configurations* —
  which suits own a dedicated empty column — as a bitmask, and its
  memoization table stores, per position, a bitmask of configurations under
  which the position is solvable.  Precomputed tables (`subsetTable`,
  `componentTable`, `computeComponentKingBits`) account for the reshuffling of
  king runs between cells and empty columns without ever searching it.  As a
  consequence every solver move strictly decreases the total merged depth
  `Σ pileDepth`, which gives termination and makes the position hash (a
  weighted sum of depths, injective on valid depth vectors) a safe
  memoization key.

## Structure of the proof

The central relation is a matching predicate (`StateMatchesSolverPos`, …)
between a concrete `State` and a solver position under a king configuration.
The two directions of the correctness theorem are proved separately.

### Soundness — if the solver says `SUCCESS`, the game is solvable

The solver's search is *replayed on the original game*.  Each abstract move
the solver makes is simulated by a sequence of `Rules.lean` moves on a
matching concrete state (park the flute interior in cells, move the boundary
card, drop the parked cards back, then drain the pending foundation moves),
ending in a concrete state that matches the solver's child position.
Induction along the recursion turns the solver's `SUCCESS` at the leaf (all
depths zero, i.e. the game is won) into an actual winning play.  On top of
this sits the memoization argument: hash injectivity guarantees a cached
bitmask is the answer for exactly the queried position.

Key files: `MoveSim`/`Phase1Sim`/`MoveAcesSim`/`CleanupSim` (the move
simulation), `KingConfigSim`/`SubsetTransport`/`ComponentKingBits` (the
king-configuration tables), `SolverInvariant`/`UsedSpaceBound` (position
invariants and the space count), `RecStepSound`/`RecLoopSound`/`RecCheckSound`/
`SolveSound` (the recursion and the memo table).

### Completeness — if the game is solvable, the solver finds it

Here an arbitrary winning play must be turned into one the solver considers.

1. **Normalizing moves do not change solvability.**  Foundation advances and
   dropping parked flute cards back onto their column are shown to be
   solvability-preserving (the latter because a cell→pile drop can be
   undone), so any state may be replaced by its normal form
   (`Normalize`, `CPNormal`, `SimulatesNorm`).
2. **Find the critical move.**  A winning play from a normalized state is
   split at its *critical move* — the first move that decreases a merged pile
   depth.  Everything before it only parks flute cards and reshuffles king
   runs, so the position's depth vector is unchanged up to that point
   (`DepthMatch`, `CriticalMove`).
3. **The solver tries an equivalent move.**  The critical move's destination
   is essentially forced (`DestComplete`), the play itself proves the free
   cells needed to afford the move exist (`DeckCount`, `DestAfford`), and the
   king-configuration reached before the critical move lies in the same
   reachability component as the queried one (`MaximalCfg`, `EmptyPileCfg`,
   `ComponentComplete`).  So the solver's move loop examines a move whose
   child position the post-critical state matches after normalization
   (`CriticalChild`, `CriticalIteration`), and induction on `Σ pileDepth`
   closes the recursion (`RecCheckComplete`, `RecCheckSpec`).

### Gluing

`SolveCorrect` combines both directions into `solve_correct` (the returned
code is `SUCCESS` iff the position is solvable), and the `Convert*` files
handle the entry point: `SolverConvertFromPilesKings` normalizes the queried
encoding (maximal foundations, completed king piles) before the search, and
`ConvertMatch`/`FoundationMax`/`KingPileMax` show these normalizations are
themselves realized by solvability-preserving moves from the queried state.
`ReachableMatch` shows every reachable state matches its own encoding, and
`DealMatches`/`InitCard` connect the initial deal to the layout `initcard`
records.  `SolverIsCorrect.lean` assembles all of this into
`solver_is_correct`.

A more detailed (historical) account of the proof plan and its milestones is
in [`Seahaven/VerificationPlan.md`](Seahaven/VerificationPlan.md).
