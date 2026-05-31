# Verification Plan: Solver Correctness

## Goal

Show that `solverRecCheckSolvable` is sound and complete:

- **Soundness**: if bit `i` is set in the return value, the game is solvable under king configuration `grlex2bits[shiftValue + i]`.
- **Completeness**: if the game is solvable under some king configuration, the corresponding bit is set.

The return value is a local bitmask (shifted by `closureInfo.shiftValue`) over the relevant king configurations for the current `freePiles` count.

---

## Setting Up the Correspondence

### 1. Well-formed `pos2card` / `card2pile` / `card2depth` maps

Define a predicate `WellFormedLayout` on the global arrays stating:
- `card2pile` and `card2depth` are left inverses of `pos2card`:
  `pos2card[card2pile[c]][card2depth[c]] = c` for all cards `c` that appear in a pile.
- `pos2card` is injective within each pile.
- Cards at positions 50–51 (extra cards) have `card2depth = 5`, which is ≥ any valid pile depth, so they always appear "freed".

### 2. Abstract game state `SolverPosType` from a concrete game

Given a concrete `Rules.GameState` and a `WellFormedLayout`, define a function
```
toSolverPos : Rules.GameState → SolverPosType
```
or show that `SolverConvertFromPilesKings` produces the canonical abstract state.

The key invariants to establish on the resulting `SolverPosType`:
- `pileDepth[i]` = number of cards not yet freed in pile `i` (above-flute count + 1).
- `pileFlute[i]` = length of the maximal same-suit consecutive run accessible at the top of pile `i`, extended by freed predecessor cards.
- `aces[s]` = highest card of suit `s` on the foundation (sentinel `CARD(s,0)` if none).
- `kings[s]` = first un-freed card counting down from the king.
- `usedSpace` = cards in extra slots + cards in king piles.
- `hash` = Σ `pileDepth[i] * pileHashes[i]`.
- `busyAces = 0` (normalised after `SolverConvertFromPilesKings`).

### 3. Many-to-one relationship

Multiple concrete `Rules.GameState` values map to the same `SolverPosType`.  The
three sources of non-uniqueness are:

**a) Foundation not fully advanced.**
The abstract state is always normalised: `SolverMoveAces` has been run to
exhaustion, so any card whose predecessor is on the foundation and which is
itself free (in extra or at the top of a pile) has already been moved.
A concrete state may lag behind: those cards are still in extra or on top of a
pile.  The concrete game can reach the normalised form by zero-cost foundation
moves (`busyAces` drain).

**b) Flute cards still occupying extra cells.**
The abstract `pileFlute[i]` counts *all* cards that belong to the accessible
run of pile `i`, including freed predecessors currently sitting in extra space.
In the concrete state those cards are in extra (counted in `usedSpace`); in the
canonical concrete state they have been moved back onto the pile.
Concretely: a sequence of at most `fluteLen - 1` pile-to-pile moves (parking
the individual cards back) reaches the canonical form without changing any pile
depth or foundation, but reducing `usedSpace` accordingly.  The abstract state
treats them as already merged; both forms are equivalent for solvability.

**c) No notion of which empty pile a king occupies.**
The abstract state records, per king configuration, *which* suits have a
dedicated empty pile, but not *which* empty pile each king occupies.  Two
concrete states that differ only in the assignment of king suits to specific
empty pile slots correspond to the same abstract state under the same king
configuration.  Moving a king stack from one empty pile to another is always
possible (requires one free extra slot and one empty pile, i.e. `freePiles ≥ 2`)
and does not change the abstract state.

**Key lemma (canonical form)**: From any concrete game state, there exists a
sequence of zero or more *free* moves (foundation advances, flute-card returns
to pile, king-stack relabelling) that reaches a canonical concrete state whose
direct encoding equals the `SolverPosType` produced by
`SolverConvertFromPilesKings`.

---

## Simulation: SolverMove → Sequence of Rules Moves

For the soundness proof the simulation runs in **one direction only**: given a
normalized concrete state `S` matching abstract state `sp`, and an abstract
`SolverMove(pile, toPile)` that the solver considers, produce a sequence of
`Rules.move`s that transforms `S` into a new normalized concrete state `S'`
matching the child abstract state `sp'`.

### Normalization lemma (separate, reusable)

**Lemma** (`normalize`): Given any `Rules.GameState` `S` matching layout, there
exists a finite sequence of `Rules.move`s — each either a foundation move or an
extra-to-pile move — that reaches a normalized state `S_norm` with
`toSolverPos S_norm = toSolverPos S` (same abstract state).

This lemma is proved independently and is needed in two places:
1. Inside the simulation lemma below, to re-normalize after a solver move.
2. Potentially for completeness, where the starting concrete state may not be
   normalized.

The sequence mirrors `SolverMoveAces`: for each suit flagged in `busyAces`,
advance the foundation, then collapse freed predecessors back onto piles.

### Main simulation lemma

**Lemma** (`simulate_SolverMove`): Let `S` be normalized and `Matches layout S sp kc`.
If `SolverMove(pile, toPile)` is valid for `sp` (i.e. the king-configuration
bit for `kc` is set in `movable`), then there exists a sequence of `Rules.move`s
transforming `S` to a state `S'` such that `Matches layout S' sp' kc'` where
`sp'` is the child abstract state produced by `SolverMove`.

**Proof sketch** — the sequence of concrete moves, following exactly the order
of operations in `SolverRemoveFlute` / `SolverMoveAces`:

1. **Park flute interior cards into extra.**
   The abstract flute of length `L` at `pile` may include up to `L - 1`
   freed predecessor cards that in the canonical form are already on the pile,
   but in a general normalized state are in extra.  Since `S` is normalized,
   those cards are already in extra or on the pile; if on the pile, move them
   to extra one by one (each is a `Rules.move` from pile top to extra cell).
   After this step, only the top card of the abstract flute boundary is on
   the pile.

2. **Move the flute boundary card to its destination.**
   This is a single `Rules.move`: move `pos2card[pile][pileDepth-1]` to
   `toPile` (or to extra / king pile).  This corresponds to the `depth--` and
   `hash -= pilehash` step of `SolverRemoveFlute`.

3. **Re-form the new flute by moving freed predecessors back onto the pile.**
   `SolverCleanupPile` absorbs freed predecessors into the new flute by
   recognising them as free (`card2depth >= pileDepth`).  Concretely, move
   each such freed card from extra back onto the pile top, one by one.  Each
   is a `Rules.move` from extra to pile, and each decrements `usedSpace` by 1
   — matching the `usedSpace--` in the freed-predecessor loop.

4. **Drain `busyAces` (apply the `normalize` lemma).**
   `SolverRemoveFlute` and `SolverMoveAces` advance the foundation and update
   `aces` / `kings` / `freePiles`.  Apply the `normalize` lemma to produce the
   sequence of foundation moves, arriving at `S'` which is again normalized
   and matches the resulting `sp'`.

At each step the invariant `Matches layout (current_state) (current_abstract_state) kc`
is maintained, with `kc` possibly updated by the `forcedKings` mask when a
lone-king pile is exposed.

---

## Invariant Maintenance

After each simulation step, show that the resulting `SolverPosType` satisfies the invariants above. Key points:

- `SolverRemoveFlute` correctly updates `pileDepth`, `pileFlute`, `hash`, `usedSpace`.
- The freed-predecessor check `card2depth[c] >= pileDepth[card2pile[c]]` correctly identifies cards no longer in their original pile.
- The lone-king case correctly transitions a pile with only a king flute to an empty pile.

---

## Hashmap Soundness

The memoisation stores a bitmask per hash value. To use cached results:

- **Collision safety**: the hash function `Σ pileDepth[i] * pileHashes[i]` with bases `6^i` is injective on valid pile-depth vectors (depths 0..5), so distinct abstract states have distinct hashes. No false cache hits.
- **Monotonicity**: the stored bitmask is the exact result for that state; re-using it is valid regardless of the order states are visited.

---

## Soundness Proof Strategy

### Normalized states

Define a `Rules.GameState` to be **normalized** if neither of the following
moves is available:
- Moving a card from a pile top or from extra to the foundation (i.e. no
  `busyAces`-style advance is possible).
- Moving a card from extra onto a non-empty pile (i.e. no freed flute-interior
  card can be placed back onto its pile).

Concretely, `S` is normalized when:
1. For every suit `s` and card `c = aces[s] + 1`, `c` is still buried in its pile
   (not at the top and not in extra).
2. For every card `c` in extra, the pile `card2pile[c]` is either empty or its
   current top card is not `c - 1` in suit (so `c` cannot extend any pile's top run).

A normalized state corresponds *exactly* to the `SolverPosType` produced by
`SolverConvertFromPilesKings`: the pileFlute, aces, kings, and usedSpace fields
are determined without ambiguity.

### Matching predicate

Define `Matches (layout : Layout) (S : Rules.GameState) (sp : SolverPosType)`:
- `layout.pos2card`, `card2pile`, `card2depth` satisfy `WellFormedLayout`.
- `S` is normalized with respect to `layout`.
- `sp.pileDepth[i]` equals the number of non-freed cards in pile `i` under `S`.
- `sp.pileFlute[i]`, `sp.aces`, `sp.kings`, `sp.usedSpace`, `sp.hash` are
  exactly what `SolverConvertFromPilesKings` computes from `S`.
- The king configuration index `kingConfig` (passed separately) identifies which
  suits have a dedicated empty pile in `S`.

### Unmemoized solver

Define `solverRecCheckSolvable_pure` that is identical to
`solverRecCheckSolvable` but **never reads from or writes to the hashmap** —
every call recomputes its result from scratch.  This function has the same
logic and the same termination argument (hash decreases) but is easier to
reason about because there is no memoization state to track.

### Inductive soundness theorem

**Theorem** (`soundness_pure`): For all `h : Nat` and all `sp : SolverPosType`
with `sp.hash ≤ h`, if `Matches layout S sp kingConfig` and
`solverRecCheckSolvable_pure sp` has bit `kingConfig` set, then `S` is solvable
under `Rules`.

**Proof**: by strong induction on `sp.hash` (which equals `h`).

- **Base case** `hash = 0`: all piles are empty, `S` is the winning state.
  The function returns `1`, which always has the relevant bit set.  Trivially
  solvable.

- **Inductive step**: assume the theorem holds for all states with hash < `sp.hash`.
  `solverRecCheckSolvable_pure` iterates over piles, calls `SolverMove` to
  produce a child state `sp'` with strictly smaller hash, and recurses.  If the
  returned bitmask has the bit set, the inductive hypothesis gives a winning
  play from the child abstract state.  By the simulation lemma (Section 3),
  the `SolverMove` in the abstract world corresponds to a concrete `Rules.Move`
  from `S` to some `S'` with `Matches layout S' sp' kingConfig'`.  Prepending
  that move to the winning play from `S'` yields a winning play from `S`.

  The `forcedKings` mask and the `subsetTable` translation handle the king-
  configuration bookkeeping across the move.

### Lifting soundness to the memoized solver

Once `soundness_pure` is established, lift it to `solverRecCheckSolvable`:

**Lemma** (`memo_agrees`): For every `sp`, if the hashmap entry for `sp.hash`
is not `FREESLOT`, its value equals `solverRecCheckSolvable_pure sp`.

This holds because:
- The hashmap is initialized to all-FREESLOT (`SolverInit`).
- The only writes are `setSlot(game.hash, solvable)` at the end of
  `solverRecCheckSolvable`, where `solvable` is the result computed (without
  the cache hit) in that same call — matching `solverRecCheckSolvable_pure`.
- Hash injectivity (no collisions) ensures no other state's write can
  corrupt the entry.

`soundness_pure` + `memo_agrees` immediately give soundness of the memoized
`solverRecCheckSolvable`.

---

## Completeness Proof Strategy

Completeness says: if `S` is a `Rules.GameState` that has a winning play, then
`solverRecCheckSolvable_pure (toAbstract S)` has the corresponding king-configuration
bit set.

The proof is again by strong induction on `sp.hash` (= sum of pile depths), but
now starting from an **arbitrary** (possibly non-normalized) concrete state.

### Core extra-space lemma

**Lemma** (`extra_space_bound`): Let `S` be any `Rules.GameState` and `sp` its
associated abstract state (after normalization of `S`).  Then:

> The number of free extra slots in `S` is **at most** the number of free extra
> slots in `sp` (i.e. `4 - sp.usedSpace - king_pile_space`).

Intuition: the abstract state is normalized, so all cards that can be on the
foundation are there, and all freed predecessors are "collapsed" into flutes
(reducing `usedSpace`).  A non-normalized `S` may have some of those cards
still in extra, consuming slots that the abstract state regards as free.

This lemma is the bridge that lets us transfer move feasibility from the
concrete to the abstract level.

### Case analysis on the next winning `Rules.Move`

Assume `S` has a winning play whose first move is `m`.

**Case A: pile-to-nonempty-pile move.**
`m` moves a flute of length `L` from `pile` to a non-empty `toPile`.
This requires `L - 1` free extra slots in `S`.
By `extra_space_bound`, `sp` also has at least `L - 1` free extra slots.
The solver therefore considers a pile-to-pile `SolverMove(pile, toPile)` with
`fluteLen = L`, which is feasible.  The solver does iterate over `toPile`
because `solverGetDestination` returns it (it is the next card's home pile, at
position-from-top 1).  The resulting child abstract state `sp'` matches the
abstract state of `S` after `m` (up to normalization), and the inductive
hypothesis applies.

**Case B: pile-to-extra move.**
`m` moves a flute of length `L` from `pile` to extra, requiring `L` free extra
slots in `S`.  By `extra_space_bound`, `sp` has at least `L` free extra slots.
The solver may consider one of two sub-cases depending on whether a pile target
exists:

- *No target pile exists* (`solverGetDestination` returns `EXTRA`): the solver
  calls `SolverMove(pile, EXTRA)`, which is feasible.  The child abstract state
  matches the abstract state after `m` (up to normalization).
- *A target pile exists* (`solverGetDestination` returns some `toPile`): the
  solver considers `SolverMove(pile, toPile)` first.  Since the target pile is
  the natural home of the next card, the winning play can route through that
  same abstract transition — the concrete move in `S` to extra is a detour that
  the abstract move to `toPile` subsumes.  In either case the resulting child
  abstract state has strictly smaller hash and the inductive hypothesis applies.

**Case C: pile-to-foundation (or extra-to-foundation) move.**
`m` moves a card to the foundation.  This does not change any pile depth, so
`sp.hash` is unchanged.  The abstract state before and after `m` (once
normalized) is **the same**: `toAbstract(S after m) = toAbstract(S)`.  The
winning play from `S after m` witnesses that `sp` is solvable, so no new
inductive step is needed — the same bit was already going to be set.

**Case D: king shuffling (rearranging stacks among empty piles).**
`m` moves a king stack from one empty pile to another.  This leaves all pile
depths and the foundation unchanged; only the assignment of king suits to
concrete empty piles changes.  In the abstract world this corresponds to moving
between king configurations in the same reachability component (as captured by
`computeComponentKingBits`).  The proof obligation is:

- If the current king configuration is `kc` and after `m` it is `kc'`, and `kc'`
  is reachable from `kc` via the component graph, and `kc'` leads to a winning
  play, then `kc` also leads to a winning play — because the solver propagates
  solvability across the entire component via `movable |= component`.

This requires the component table to be proven correct (see Open Questions §2).

### Inductive step conclusion

In all four cases, after the first `Rules.move` the winning play continues from
a state whose abstract hash is either smaller (cases A, B) or equal (cases C,
D).  Cases C and D terminate without needing the inductive hypothesis; cases A
and B apply it.  This closes the induction.

---

## Open Questions / Harder Parts

1. **Termination of `solverRecCheckSolvable`**: the hash strictly decreases with each recursive call (at least one `pileDepth` decreases), so the recursion terminates. Formalising this requires a well-founded measure on `SolverPosType`.  We can also
use the sum of depths as measure, which shows the max 50 moves limit.

2. **King-configuration component closure**: the `computeComponentKingBits` / `componentTable` logic encodes reachability between king configurations. A separate proof that the component table is correct (matching `kingOnPileMap` and the reachability relation) would be needed.  There is something started in BitmapProofs, but it needs more work.

3. **Completeness vs. soundness**: soundness (solver says solvable → it is) is the easier direction. Completeness (game is solvable → solver finds it) requires showing no solvable path is missed, which needs the simulation to be surjective in the right sense.

4. **Extra-card sentinel convention**: cards at deal positions 50–51 have `card2depth = 5`, always ≥ any pile depth. This should be established as part of `WellFormedLayout` and propagated through the freed-predecessor checks.

5. **King Pile numbering**: The concrete state assigns the kings to specific empty piles.  The abstract state via the king configuration only says which kings are dedicated to a pile, but not to which.  If we want to show that the "canonic" concrete state for the abstract state is reachable, this only holds modulo the right assignment of kings to piles.
