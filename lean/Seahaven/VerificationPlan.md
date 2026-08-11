# Solver Correctness: Proof Architecture

This document describes how the correctness proof is organized.  It started as
the working plan for the verification; the proof is now complete
(`solver_is_correct` in `SolverIsCorrect.lean`, no `sorry`s), and the document
has been rewritten to describe what was actually proved.  For the high-level
overview see [../README.md](../README.md).

## The statement

`Correctness` (`SolverCorrectness.lean`) exhibits invariants on the solver's
global state such that

- `initcard shuffle.vector` establishes the invariant from any well-bounded
  starting globals;
- for every state `s` reachable from the deal, `solve (pilesKingsFromState s)`
  runs without error, preserves the invariant (so the solver can be queried
  repeatedly), and returns `SUCCESS` if `s` is solvable and `NOMOVE` if not.

The query encoding `pilesKingsFromState s` is ten *merged* pile depths
(`|removeFlute (tableau i)|` — the column with its accessible same-suit run
stripped) plus a bitmap of the suits whose king run occupies a whole column.

---

## The abstraction: solver positions vs. game states

The solver does not track full game states.  Everything below exists to relate
its abstract positions to `Rules.lean` states.

### The layout (`WellFormedLayout`)

`initcard` records the deal in three global arrays.  `WellFormedLayout` states
that `card2pile`/`card2depth` are left inverses of `pos2card` and that
`pos2card` is injective.  The two cards dealt to the cells (deal positions
50–51) get `card2depth = 5`, one more than any live pile depth, so the freeness
test `card2depth[c] ≥ pileDepth[card2pile[c]]` always counts them as freed.

### The abstract position (`SolverPosType`)

For a position matching a concrete state:

- `pileDepth[i]` — number of not-yet-freed cards in pile `i`;
- `pileFlute[i]` — length of the same-suit consecutive run accessible on top
  of pile `i`, *including* freed predecessors currently parked in cells;
- `aces[s]` — the foundation frontier; `kings[s]` — first un-freed card
  counting down from the king;
- `usedSpace` — cards held outside the counted columns (cells + king stacks);
- `hash` — `Σ pileDepth[i] · 6^i`;
- `busyAces = 0` in canonical positions (pending foundation moves drained).

### One position, many states (`StateMatchesSolverPos`)

Matching is many-to-one.  The three sources of non-uniqueness, each bridged by
*normalizing* moves that preserve solvability in both directions:

1. **Foundation lag** — the abstract position assumes foundation moves are
   played eagerly; a concrete state may still have them pending.
2. **Parked flute cards** — `pileFlute` counts run cards whether they sit on
   the pile or in cells; moving them back and forth is free.
3. **King pile assignment** — the position records *which suits* own an empty
   column, never *which* column.  Relocating a king run between empty columns
   (via the cells) is reversible.

`DepthUnique.lean` proves the converse direction: a state determines the
canonical position it matches — `pileDepth[i]` is the *least* depth at which
`PileMatches` holds (`merge_complete` pins it), so two canonical positions
matching the same state are equal.  One corner is genuinely ambiguous: at
depth `≤ 1` a column whose single dealt card is a king with its run above it
matches depth `1` and depth `0` alike.  The solver never emits such a position
(cleanup's lone-king branch vacates the pile), and the uniqueness lemmas carry
that as the explicit hypothesis `NoLoneKing`, discharged from the cleanup
development where they are used.

### King configurations

Filling empty columns with kings is the one move family that makes *no*
progress: it is reversible and cycles.  The solver therefore never searches
king relocations.  Instead each position is judged under a **king
configuration** — a 4-bit mask, bit `su` set iff suit `su` has *no* dedicated
king pile — and `solverRecCheckSolvable` returns a *bitmask over
configurations* rather than a Boolean.  The payoff: every move the solver does
make strictly decreases `DepthSum = Σ pileDepth` (`move_merged`), which is the
induction measure everywhere and what makes the hash a sound memo key.

The bit-level machinery (`SolvableBits.lean` is the reference):

- configurations are indexed in graded-lexicographic order (`bits2grlex` /
  `grlex2bits`), so the configurations with the same number of piled kings are
  contiguous; `closureInfos[freePiles]` names that block (`shiftValue`,
  `numBits`), and the function's answer is a *local* mask over it;
- `subsetTable` closes a local set downwards under "put fewer kings on piles"
  and expands it back to a global 16-bit mask;
- `forcedKings` accounts for lone-king vacates that *add* a king pile
  mid-move; `componentTable` / `computeComponentKingBits` connect
  configurations reachable from each other by physical king reshuffles.

### The memo table

`hash` determines the depth vector (base-6 digits), and
`IsCanonicalPos_hash_inj` makes it injective on canonical positions.  A slot
stores the 7-bit local answer next to a 9-bit tag of the hash's high part, so
a read either misses or is about exactly the queried position.  The invariant
`HashmapCorrect` says every non-free slot holds the exact two-sided answer
(`SolvableBits`), and it is threaded through the recursion as a parameter.

---

## Soundness: replaying the solver's moves

*If the solver's bit for configuration `k` is set, a state matching the
position at `k` is solvable.*

### Simulating one abstract move

`Simulates.move` (assembled in `SolverMoveSim.lean` from `Phase1Sim`,
`CleanupSim`, `MoveAcesSim`): given a matched state and a `SolverMove` the
solver considers, produce `Rules` moves to a state matching the child
position.  The move plays out in the order of the C code:

1. park the flute's interior cards in cells (the space check
   `solverGetMovable` guarantees the cells exist);
2. move the boundary card to its destination (`SolverRemoveFlute`'s
   `depth--`);
3. cleanup: drop freed predecessors back onto the pile
   (`SolverCleanupPile`'s freed loop), vacate a lone king if one is exposed;
4. drain `busyAces` (`SolverMoveAces`): the walk counts already-free cards
   without touching the state, so the `Rules` plays are *deferred* to the sync
   points, where the whole pending run is played at once.

### The recursion

`solverRecCheckSolvable` is defined by `partial_fixpoint`, giving the one-step
unfolding `recCheck_eq`.  Every theorem about it takes the successful run as a
*hypothesis* (`EStateM.run … = .ok r g'`), so no totality proof is ever
needed; the induction is on a `Nat` bound of `DepthSum`, decreasing by
`move_merged`.

The pile loop reduces to a per-contribution obligation because the
`subsetTable` expansion is additive in the local mask (`subsetAt_or`).  What
remains are semantic obligations, discharged by the simulation:
`MoveSimulated` (the move really is playable) and `SubsetSound` /
`ComponentSound` (a covered configuration really is reachable by king
reshuffles).  One subtlety is load-bearing: intersecting the child's answer
with `forcedKings` is *required* for soundness, not an optimization — after a
lone-king vacate the child stands for a different configuration block, and the
intersection deletes exactly the configurations the child state does not
realize (`kingStep_transport`; see `SoundnessSkeleton.lean` for the refuted
shortcut).

At the `hash = 0` leaf every pile is empty and canonicity forces all four
foundations to the king: the state is already the goal.

---

## Completeness: the solver finds every win

*If a matched state is solvable, the solver's bit for its configuration is
set.*  An arbitrary winning play must be converted into one the solver tries.

### The critical move

Split the winning play at the **critical move** — the first move that
decreases a merged pile depth.  `DepthMatch.lean` provides the matching
hierarchy this runs on: `DepthMatchesV` (depths only) < `DepthPlusKings`
(physical ≤ recorded) < full match, with the `≤` clauses derived, not assumed.
Before the critical move:

- no foundation move is even available — each suit's next foundation card is
  strictly buried (`CriticalMove.no_fmStep_of_depthMatch`), so the prefix only
  parks flute cards in cells and reshuffles king runs;
- consequently the critical state still matches the depth vector, has its
  flute physically parked (`|tableau a| = pileDepth a`), and its foundations
  unchanged.

### The move the solver tries instead

- **Destination** (`DestComplete.lean`): parking the boundary card and
  dropping it later composes to the direct move (`cell_park_then_drop`); a
  column destination is unique; a king fits only on an empty column.  So the
  play's choice is equivalent to the solver's `solverGetDestination`.
- **Affordability** (`DeckCount.lean`, `DestAfford.lean`): the play itself
  parked `fluteLen − 1` cards, and the full-deck partition
  `Σ foundations + #cells + Σ |tableau i| = 52` turns that into the exact
  space bound `solverGetMovable` checks against `possibleKings`.  The
  configuration this happens at is `k_t` — the *physically piled* suits of the
  critical state, plus the moved king when the critical move is
  king-to-empty-column — affordable by construction, no guessing.
- **Bit transfer**: `k_t` usually has no bit of its own in the block
  (`closureInfos` stores only maximal assignments); `MaximalCfg` supplies a
  covering block configuration through `subsetTable`, and the gap between the
  queried configuration `k` and `k_t` is closed by the component argument
  (`EmptyPileCfg`, `ComponentComplete`): they differ only by reversible king
  reshuffles, and `KingAssemble` shows cell→pile king drops undo themselves.

### After the critical move

CP-normalize the child (`CPNormal.lean`; cell→pile drops are revertible, so
solvability is unchanged) and identify the result with the solver's own child:
by depth uniqueness the canonical position the child state matches *is* the
one `SolverMove` + `SolverCleanupPile` computed (`matches_of_depth_match`,
`CriticalChild`).  The induction hypothesis at the child (smaller `DepthSum`)
then yields the bit, transported back up through `subsetTable` and
`forcedKings` read in the completeness direction (`SubsetTransport`).

### The loop invariant

Completeness through the pile loop is a *persistence* property, not an
additive one (`CompleteBits.or_left`): one particular iteration contributes
the bit, and every later `|||` preserves it.  This is also why the loop's
early `break` and its `movable &&& ~~~solvable == 0` skip are harmless.

---

## One induction, two directions

`RecCheckSound` proves the soundness half alone; a standalone completeness
induction would repeat it verbatim.  `RecCheckSpec.lean` therefore runs a
**single** induction at the two-sided memo invariant `HashmapCorrect`: both
loop developments are parameterized over the invariant they carry, and
instantiating both at `HashmapCorrect` lets one induction hypothesis feed
both directions (`recCheckSolvableSpec`, hypothesis-free, in
`RecCheckComplete.lean`).  Only the `hash = 0` leaf and the memo hit are
direction-specific.

---

## Entry and assembly

- **Convert** (`SolverConvertFromPilesKings`): read at the caller's state via
  the lax entry `CvEntry` (`ConvertMatch.lean`) — the queried depths with the
  state's *own* flutes and foundations.  Convert's own loops close the gap to
  the canonical position, and their writes are realized by normalizing moves:
  maximal foundations by foundation plays (`FoundationMax`), completed king
  piles by cell→pile drops (`KingPileMax`), the cleanup loop by
  `CleanupLax`.
- **The query is legal and about the right state** (`ReachableMatch.lean`):
  every reachable state has merged depths `≤ 5` (`removeFlute` never grows
  along a play) and matches its own encoding, realizing the configuration
  `kingBitmap` names.
- **The deal** (`InitCard.lean`, `DealMatches.lean`): `initcard` on a shuffle
  establishes `WellFormedLayout`, both memo invariants, and the layout of the
  dealt state.
- **`solve`** (`SolveCorrect.lean`): joins the two-sided recursion spec with
  the convert simulation; `SolverIsCorrect.lean` packages the invariants
  (`Inv0`/`Inv1`) and discharges `Correctness`.

---

## Design decisions worth remembering

- **No totality proof.**  Every spec takes the successful run as a
  hypothesis, so `partial_fixpoint` never has to be shown terminating; the
  induction measure lives in the theorems.
- **`forcedKings` is a soundness ingredient**, not a pruning heuristic — the
  "intersection only shrinks, so soundness is free" shortcut is wrong (twice
  refuted; `SoundnessSkeleton.lean`).
- **The specification must pin the configuration down.**  `SolvableBits` is
  stated over `StateMatchesKingConfig`, whose negative clause `no_pile` is
  load-bearing: with bare `RealizesKingConfig` the specification is
  unsatisfiable (recorded in `SolvableBits.lean`).
- **`k_t` is constructed, not guessed** — the physically piled suits of the
  critical state (plus the moved king); an earlier plan to guess a maximal
  extension of the queried configuration was superseded.
- **King pile numbering** exists only in concrete states; all abstract-level
  statements are modulo the assignment of king suits to specific columns, and
  the reversibility of the reassignment is a proved lemma, not a convention.
