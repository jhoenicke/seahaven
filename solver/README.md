# Seahaven Towers Solver

This document describes the algorithm used in `solver.c` to determine whether
a Seahaven Towers game position is solvable.

## Game Rules (Brief)

Seahaven Towers is a solitaire card game with 10 column piles, 4 free cells
(extra slots), and 4 foundation piles.  Cards are dealt 5 per column (50 cards)
with the remaining 2 going to free cells.  The goal is to move all cards to the
foundations, built up by suit from Ace to King.  Within columns, cards may only
be stacked same-suit in descending order.  A King may be moved to an empty column
to start a "king pile" (a column reserved for building a suit from King downward).

## What the Solver Does

The solver answers **"is this position solvable?"**, not "what is the optimal
sequence of moves."  It uses a memoised depth-first search over an abstracted
game state and returns a bitmask of which *king configurations* lead to a solution.

---

## State Abstraction

### Pile Depth and the Flute

Rather than tracking every card's exact position, the solver uses two values per pile:

- **`pileDepth[i]`**: the number of cards in the *above-flute section* plus 1.
  `pileDepth=0` means the pile is empty; `pileDepth=1` means only the flute
  remains (no blocking cards above it).

- **`pileFlute[i]`**: the length of the *flute* — a consecutive same-suit
  descending sequence sitting at the accessible top of the pile.

Cards are stored in `pos2card[pile][pos]` where `pos=0` is the physically deepest
card (dealt first, covered by others, highest value in a properly stacked sequence)
and higher `pos` means more accessible / lower value.  The flute occupies positions
`pileDepth-1` upward; the boundary card at `pos2card[pile][pileDepth-1]` has the
highest value in the flute.

**The flute is the unit of movement.**  Moving a flute of length L to another pile
requires L−1 temporarily free extra slots (to park the interior cards while the
boundary card slides onto the destination).  Moving a flute to extra slots costs L
slots.  It is never useful to move only part of a flute: doing so would consume
extra space without exposing a new card below.

### Why Pile Depths Determine the Full Game State

Given the **fixed initial card layout** (`pos2card`, `card2pile`, `card2depth` —
set once from the shuffled deck and never changed), the 10 pile depths fully
determine the game state:

- Which cards are still in each pile (those with `card2depth[c] < pileDepth[card2pile[c]]`).
- Which cards have been freed (moved to extra, foundation, or king pile).
- The flute of each pile (the accessible top sequence, computable from pile depths).
- The foundation level per suit (walkable from the Ace upward).
- The king frontier per suit (walkable from the King downward).

This means **two positions with identical pile depths are equivalent**, enabling
memoisation keyed solely on the depth vector.

### The Hash

```c
hash = sum(pileDepth[i] * pileHashes[i])   // pileHashes[i] = 6^i
```

Powers of 6 are used because pile depths are bounded by 0–5, so the mapping
`depth_vector → polynomial` is injective and the values fit in `uint32_t`.

---

## usedSpace and Free Extra Slots

`usedSpace` counts cards that occupy extra slots or king piles (i.e., cards not in
column piles and not yet on the foundation).  Initially it equals the number of
free-cell cards placed during dealing (typically 2).

It is computed as:
```
usedSpace = 52 − Σ(pileDepth[i] + pileFlute[i] − 1)  − Σ foundation_cards_per_suit
```

The term `pileDepth + pileFlute − 1` equals the total number of cards in that
pile (above-flute cards + flute cards).

**Free extra slots = 4 − usedSpace.**  A move is legal only when there are enough
free extra slots.  Pile-to-pile moves do not permanently change `usedSpace` (the
temporarily parked cards return to a pile at the end of the move).

---

## King Configurations

### Why They Are Tracked Separately

Kings can move to any empty pile.  It sometimes can be beneficial to move a king
from an empty pile to the extra cells to make space for a different king on that
pile.  These moves can lead to cycles and make the reasoning more difficult.
Therefore we track the king configuration (which kings are on piles and which on
extra cells) separately.

The game state tracks how many cards from king downwards are free.
Each of the king sequences is considered in `usedSpace` even if the king is possibly piled, since the game state does not know whether the king is piled.  The solver hypothetically
considers reassigning up to `freePiles` of the kings to dedicated empty
piles (moving them out of `usedSpace`), giving each such sequence an extra slot
budget.  The constraint is: number of dedicated king piles ≤ freePiles.

When by chance a king flute resided at the top of a dealt pile and becomes accessible,
it is processed by `SolverRemoveFlute` and the king is "virtually" moved to a free pile
without physically moving it (the free pile is the pile the king just resided on). 
This means that `usedSpace` must now account for the king flute and the column 
becomes empty (`freePiles++`).

Each hypothetical assignment is a **king configuration**.  When checking how much extra
space is available it differs for any king configuration as we need to subtract from
`usedSpace` the number of cards in the king flutes dedicated to empty piles. 
We compute for every number of empty cells the king configurations that lead to at
least this number of empty cells.  Thus if a move is performed we can quickly find
the king configurations that have enough empty cells to perform this move.


### Grlex Bitmask

The 16 possible king configurations are indexed in **grlex (graded lexicographic)
order**, ranked first by the number of suits whose kings are in extra slots, then
lexicographically:

```
Index  Bitmask  Suits in extra  (others are in dedicated piles)
  0    0b0000   {}              all 4 kings in dedicated empty piles
  1    0b0001   {0}
  2    0b0010   {1}
  3    0b0100   {2}
  4    0b1000   {3}
  5    0b0011   {0,1}
  ...
 15    0b1111   {0,1,2,3}       all kings in extra, no dedicated piles
```

In the bitmask, **bit k SET means suit k's king is in extra slots** (not occupying
a dedicated pile).  This is the convention used internally; the external interface
(`stacks[10]`) uses the opposite — bit k SET means the king is in a regular column
pile (not yet freed).

The `bits2grlex` / `grlex2bits` lookup tables convert between raw 4-bit bitmasks
and grlex indices.

### The Solvable Bitmask

`solverRecCheckSolvable` returns a *local* bitmask over the C(4, freePiles)
relevant king configurations for the current `freePiles` count.  The assumption
is that all empty piles are used for king piles.

`closureInfos[k]` encodes the encoding for `freePiles = k`:

| freePiles (k) | dedicated piles | SET bits | shiftValue | numBits=C(4,k) | offset |
|--------------|-----------------|----------|------------|----------------|--------|
| 0            | 0               | 4        | 15         | 1              | 98     |
| 1            | 1               | 3        | 11         | 4              | 0      |
| 2            | 2               | 2        | 5          | 6              | 16     |
| 3            | 3               | 1        | 1          | 4              | 80     |
| 4+           | 4               | 0        | 0          | 1              | 96     |

With freePiles=k, exactly k suits have dedicated empty piles (UNSET bits in grlex),
so 4−k suits are in extra (SET bits).  The shiftValue is the grlex start index for
configs with 4−k SET bits (k dedicated piles), and numBits = C(4,k).

- **shiftValue**: global grlex index of local bit 0.
- **offset**: base index into both `subsetTable` and `componentTable`.

Local bit `i` corresponds to global grlex index `shiftValue + i`.

---

## Space Feasibility per King Configuration

`computeKingSpaces` populates `possibleKings[k]` — the local-bitmask of king
configurations where at least `k` extra slots are free.

For each configuration, it adjusts `usedSpace` by subtracting the number of freed
king-sequence cards for any suit whose king is in a dedicated pile (those cards are
not occupying extra slots).  Then it fills `possibleKings[0..4−usedSpace]`.

`possibleKings[k]` is used by `solverGetMovable` to check move feasibility:

| Move type              | Extra slots needed |
|------------------------|--------------------|
| Pile → pile            | fluteLen − 1       |
| Pile → extra           | fluteLen           |
| Pile → king pile (new) | fluteLen           |
| Pile → king pile (existing) | fluteLen − 1  |

An existing king pile absorbs the flute boundary card directly, saving one slot.
`kingOnPileMap[s]` is the precomputed 16-bit grlex mask of configurations where
suit s's king IS in a dedicated pile (bit s UNSET in `grlex2bits[i]`).

A subtle point here is that a king can be dedicated to a pile, even though the
king is not yet freed.  This is useful when moving a king to a new empty pile,
as we can dedicate that pile to the king before moving and only need fluteLen-1
extra slots per the table above.  It's also useful as we can simply assume that
all freed king piles up to the forth are always dedicated, even if we have no
kings to fill them.

---

## King Component Closure (componentTable)

Not all king configurations are independently reachable from each other.  However,
**all configurations with one genuinely free pile** are mutually reachable: the
empty pile can be used to shuttle a king sequence out, swap which suit occupies a
dedicated pile, and fill the pile back in.

This implies: **all k-dedicated-pile configurations that are supersets (in dedicated
suits) of any feasible (k−1)-dedicated-pile configuration form a single reachable
component.**  If the game is solvable for one configuration in this component, it
is solvable for all of them.

`computeComponentKingBits` computes this component:

1. Evaluate which (k−1)-dedicated configurations are feasible (freed king cards
   fit in 4 extra slots) — this is the input bitmask.
2. Look up `componentTable[closureInfos[k−1].offset + feasibleMask]` to get
   the component bitmask (which k-dedicated configs belong to the component).

**componentTable algorithm** (see `gen_tables.py`):

```python
# output config C is in the component iff
# some feasible input config P covers C:  bits_C is a submask of bits_P
output_bit[j] = 1  if  ∃ feasible P: (grlex2bits[C_j] & grlex2bits[P]) == grlex2bits[C_j]
```

`bits_C` being a submask of `bits_P` means every suit C has in extra is also in
extra in P, i.e., C's dedicated piles are a superset of P's.  So C is reachable
from P by filling the empty pile with the one extra dedicated suit.

Some input combinations are unreachable in practice (e.g., only complementary
pairs like {suits 0,1} and {suits 2,3} being feasible simultaneously, but not
any single-suit config — this is ruled out by the monotonicity of freed-king
counts).  The formula produces a valid result (typically all-bits-set = full
component) for these unreachable inputs anyway.

---

## Child-to-Parent State Translation (subsetTable)

After making a move (transitioning from parent to child state), the child's
solvable bitmask must be translated back to the parent's king-configuration space.
This is needed for moves that free piles.  In that case the child has more dedicated
kings than the parent.  All kings dedicated in the parent must still be dedicated in
the child, though.

**subsetTable algorithm** (see `gen_tables.py`):

```python
# parent config P is solvable if some solvable child config C covers P:
parent_bit[P] = 1  if  ∃ solvable C: (grlex2bits[C] & grlex2bits[P]) == grlex2bits[C]
```

The same submask predicate: if child config C is solvable and C's extra-slot suits
are a subset of P's extra-slot suits, then the parent is solvable under config P
(C is a tighter constraint that P can relax by putting fewer suits in extra).

Indexed as `subsetTable[closureInfos[child.freePiles].offset + childSolvable]`;
the result is a full 16-bit grlex mask, shifted right by `closureInfos[parent.freePiles].shiftValue`
to extract the parent's local bits.

---

## Recursive Solver

`solverRecCheckSolvable(game)`:

1. **Base case**: `hash == 0` means all piles are empty → return 1 (solvable).
2. **Cache check**: look up `game->hash` in the hash map; return cached value if found.
3. **Compute feasibility**: call `computeKingSpaces` to populate `possibleKings`.
4. **Compute component**: call `computeComponentKingBits` to find the big component.
5. **Try each move**: for each non-empty pile, determine its flute's destination
   (`solverGetDestination`) and the king configs under which the move is affordable
   (`solverGetMovable`).  If any new config might become solvable:
   - Copy the game state to the next DFS stack frame.
   - Apply the move (`SolverMove`), which also returns `forcedKings` — the set
     of king configurations that are still valid given any kings uncovered during
     this move (see *Forced King Constraints* below).
   - Recurse; mask child's solvable bitmask with `forcedKings` (in local bit
     space) to restrict to physically valid configurations.
   - Translate the masked child result to parent space via `subsetTable`.
   - Propagate through the component: if any component member is solvable,
     all members are.
   - Accumulate into the parent's `solvable` bitmask.
   - Early-exit if `solvable == allkings` (all feasible configs solved).
6. **Cache and return** the solvable bitmask.

The DFS stack is an array (`gameStack[MAX_MOVES]`); `game[1]` is the child frame,
avoiding heap allocation during recursion.

### Move Destinations (solverGetDestination)

A flute's destination is determined by its boundary card (highest-value card,
at `pos2card[pile][pileDepth-1]`):

- If this card equals the suit's king frontier (`kings[suit]`): move to `KINGPILE+suit`.
- Otherwise: scan upward through the suit's card sequence to find the next card
  still in a pile.  If that card is at the top of its pile (`posFromTop == 1`):
  move there (pile-to-pile).  If it is buried: return `EXTRA` (=14), meaning park
  the flute in extra slots until the blocking cards above it are cleared.

### Foundation Auto-Move (SolverMoveAces / busyAces)

Since king moves are handled by the king configuration, we only need to consider
moves from a pile.  This adds the cards to the destination (extending the flute
in another pile, the king flute, or accounting it as extra cells) and then calls
`SolverRemoveFlute` to remove the cards from the starting pile.  This function
will normalize the pile, e.g. merge uncovered flutes that were put by chance in 
the initial tableaux, move free cards from extra cells to the flute and check
if the flute can be moved to foundations. `SolverMoveAces` then walks up
the suit sequence, advancing the foundation as far as possible automatically.

The `found` counter accumulates cards that are already freed from their piles
(in `usedSpace`) and lie above the current foundation level.  It is **reset to
zero each time a pile-top card is moved to foundation** (via `SolverRemoveFlute`),
because those cards were counted in `pileDepth` (not in `usedSpace`), so no
`usedSpace` adjustment is needed for them.  Only when the walk stalls on a buried
card is `found` subtracted from `usedSpace`, accounting for the freed cards that
are now going to the foundation from extra slots.

When a king is uncovered we convert the pile into a king pile.  This increases
the number of free piles and marks the king as `usedSpace`.  In that case we only
consider successor states that have the king dedicated to a pile, since this is
what the resulting state does.  See *Forced King Constraints* below.

### Forced King Constraints

When `SolverRemoveFlute` exposes a lone king at the bottom of a pile, it converts
that pile to a king pile (`freePiles++`, king sequence goes to `usedSpace`).
This king is now physically sitting in that specific column — the column cannot be
used for any other suit's king sequence, even though the abstract state treats it
as a generic free pile.

**The bug this prevents**: suppose during a move a King of Diamond that sat at the
top of the pile gets exposed.  Further assume that after the move `usedSpace > 4`
(exceeds the 4 extra-cell capacity).  We need to find a solvable configuration
that is Diamond-dedicated.  If only a Heart-dedicated configuration is solvable,
in paraticular the Diamond-dedicated configuration cannot reach it, the solver
must not conclude that the parent is solvable — the freed column *is* the Diamond
column and cannot be repurposed for Heart because there is not enough extra space.

**The fix**: `SolverRemoveFlute` returns a 16-bit `forcedKings` mask (in global
grlex space).  Normally `forcedKings = 0xffff` (no constraint).  When a uncovered
king fires for suit S, it ANDs in `kingOnPileMap[S]`, retaining only configurations
where suit S IS in a dedicated pile (bit S UNSET).  `SolverMoveAces` and
`SolverMove` propagate this mask upward via AND, accumulating constraints from
every king uncovered during the move chain.

In the recursive call site, `recursiveSolvable` is masked before the
`subsetTable` lookup:

```c
uint8_t recursiveSolvable = solverRecCheckSolvable(game + 1)
                          & (forcedKings >> nextClosureInfo->shiftValue);
```

The shift aligns `forcedKings` (global grlex space) with the child's local bit
numbering.  This only retains the solvable king configuration where the uncovered
kings are dedicated to their pile.

If after dedicating a king to a pile it is later moved to the foundations, the
king is still forced.  However, that is no problem as the king suit is empty.
The solver figures out that the king configuration is solvable because it can
reach any other king configuration by rededicating the empty king pile.

---

## Hash Map

A single-probe open-addressing map of 1M `uint16_t` entries.  Each entry stores:
- **7 bits**: the cached solvable value.
- **9 bits**: a tag derived from `key / BIG_HASH_SIZE`.

Misses are detected by tag mismatch; collisions silently evict the old entry.
The entry index is computed as `((high * 0x10001) ^ key) & (BIG_HASH_SIZE − 1)`.

---

## External Interface

`initcard(shuffle, 52)`: one-time setup from the shuffled deck.  Records
`pos2card`, `card2pile`, `card2depth` from the dealing order.

`solve(stacks, 11)`: query for a specific game state.

- `stacks[0..9]`: current pile depths (above-flute cards + 1 per pile, 0 if empty).
- `stacks[10]`: king bitmap where **bit k SET = suit k's king is still in a
  regular column pile** (not yet freed).  XOR with `0xf` converts to the internal
  convention (bit SET = king in extra).

Result written to `result[11]`: `SUCCESS` (0) if solvable, `NOMOVE` (2) if not.

---

## Table Generation

`gen_tables.py` computes both `subsetTable` and `componentTable` from first
principles and verifies them against the values in `solver.c`.  Both tables share
the same core predicate:

```python
def covers(bits_C, bits_P):
    return (bits_C & bits_P) == bits_C   # bits_C is a submask of bits_P
```
