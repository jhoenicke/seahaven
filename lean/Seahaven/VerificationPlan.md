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
- Hash injectivity (for same extra key) ensures no other state's write can
  corrupt the entry, if it overwrites the other state is FREESLOT again.

`soundness_pure` + `memo_agrees` immediately give soundness of the memoized
`solverRecCheckSolvable`.

---

## Completeness Proof Strategy

Completeness says: if the concrete state `s` is solvable, then
`solverRecCheckSolvable` sets the bit for the king configuration `s` realizes.
It is the `→` half of `SolvableBits` (`SolvableBits` is already stated as an iff),
so no new interfaces are needed:

```
CompleteBits g p v := ∀ s k, StateMatchesKingConfig g s p k → Solvable s →
                        BitSet (subsetAt ((closureInfoOf p).offset + v)) k
```

Two structural remarks:

- **No totality proof is needed.**  Stated as in `SolveSpec` (`run (solve pk) g =
  .ok r g' → …`) the successful run is a *hypothesis*, so the child's run is
  extracted from the parent's exactly the way `recCheck_sound_of_body` already
  does.  The `partial_fixpoint` is not an obstacle.
- **The memo needs only `CompleteBits`.**  A cached read is only ever used in the
  completeness direction, so `∀ slot, FREESLOT ∨ CompleteBits …` is a
  self-maintaining invariant; completeness need not be entangled with soundness.

Induction is on `DepthSum` (`Σ pileDepth`), which `move_merged` proves strictly
decreases per child.

### The chain for one inductive step

Let `s` be normalized, solvable, matching the canonical `p` at configuration `k`.
Split the winning play as *shuffle\* · critical move · rest*, where the **critical
move** is the first move that decreases a pile's (merged) depth — the first move
of a pile card that neither continues the card below it nor is a lone king.

1. **The prefix moves no depth.**  Formally: `DepthMatchesV g u d` (`DepthMatch.lean`)
   matches only the depth vector, ignoring `pileFlute`/`kings` — which is exactly
   `matches_of_depth_match`'s hypothesis, so no separate "loose match" predicate is
   needed.  A solved state matches no positive depth
   (`not_depthMatchesV_of_goal`), drops never break the match
   (`DepthMatchesV.drop`) and takes break it only by removing a boundary card
   (`exists_boundary_of_break`), so `exists_critical_move` splits any winning play
   at the first failure — which also pins `|tableau a| = d a`, i.e. the flute is
   already parked.  Rigidity below is then only needed to know *where* the parked
   cards are (cells), not to find the move.  By rigidity, a non-boundary flute card's
   successor sits directly beneath it, so such a card can only be parked in a
   *cell*; and no foundation move is available before the critical move
   (`CPNormal.no_fmStep` at `s`).  So the prefix only parks/unparks flute cards
   and reshuffles king runs between cells and truly empty columns.
2. **After the critical move** we have a solvable `t`.
3. **CP-normalize `t` to `t'`.**  `exists_cpNormalForm` produces `t'`, and
   `CPReach.solvable_iff` gives `Solvable t ↔ Solvable t'` because `CPStep` is
   revertible.  (Only cell→pile moves — foundation moves must stay pending, since
   `busyAces ≠ 0` at this point.)
4. **`t'` matches the game after the `SolverMove` core and `SolverCleanupPile`**,
   i.e. the position `movePre` cleaned up, whose invariant is
   `removeFlute_merged`'s `SolverInvMerged`.  This is `matches_of_depth_match`:
   supply the depth vector and the foundations and the flute lengths and king
   stacks are *forced*.  The depths agree without any merge counting because
   `merge_complete` pins `pileDepth` as the **least** `PileMatches` witness.
5. **Run the drain's moves** (`SolverMoveAces`), which are exactly foundation
   plays plus the per-card cleanup's cell→pile drops — `PlaysAll.preserves_Solvable`
   and `CPStep.preserves_Solvable`, so solvability is unchanged.  The resulting
   state matches the child's canonical position.
6. **Apply the induction hypothesis** at the child, and transport the bit back up.

### The bit-level argument (step 6)

Work with `k_t`, the configuration of the state *just before* the critical move,
rather than with `k`: `k_t` is affordable **by construction**, because the play
really did park `fluteLen - 1` cards in cells.  (An earlier version of this plan
guessed a maximal extension `i₀` of `k` instead; `k_t` supersedes it.)

- `bit k_t ∈ movable` — the space-counting lemma below.
- `bit k_t ∈ subsetTable[childOffset + childSolvable']` — the converse of
  `SubsetSound`: the child configuration `k'` that `t'` realizes lies in the
  child's answer (induction hypothesis), and `k_t ⟶ k'` is a legal reshuffle.
- `bit k' ∈ forcedKings >>> shift` — the converse of `kingStep_transport`; this is
  where `KingVacates` / `Simulates.bound` is consumed in the other direction.

Then `k` and `k_t` differ only by depth-preserving king reshuffles (a run moving
between the cells and a truly empty column), and both directions are legal in
`Rules`, so they lie in the same reshuffle class.  `movable'' := if movable' &&&
component ≠ 0 then movable' ||| component` therefore fires and carries the bit
from `k_t` down to `k`.  The case split closes exactly where the code computes the
component:

- `freePiles = 0` — no empty column exists, so no reshuffle is possible and
  `k = k_t`;
- `freePiles ≥ 4` — the closure block holds a single configuration, so `k = k_t`;
- `freePiles ∈ [1,3]` — the only range where they can differ, and precisely where
  `computeComponentKingBits` returns a nonzero mask.

The loop guards need no separate argument: the early `break` is fine because a
realizable configuration is in `allkings`, and the `movable &&& ~~~solvable == 0`
skip is fine because it says `movable ⊆ solvable`.

### Core extra-space lemma (space counting)

For a matched state, `usedSpace` is *exactly* the number of cards physically
outside the counted parts of the columns.  Writing `physFlute i` for the physical
run above pile `i`'s boundary (`|tableau i| + 1 - pileDepth i`) and
`parked := Σ (pileFlute i - physFlute i)`:

> `#cells = usedSpace - #kingStacks + parked`

and `#kingStacks = refund(k)` for the configuration `k` the state realizes.  Since
`#cells ≤ 4`, affordability follows: `usedSpace - refund(k_t) ≤ 4 - (fluteLen-1)`,
which is exactly the bit `solverGetMovable` reads from
`possibleKings[fluteLen-1]`.

Note the direction: soundness only needed `#outside ≤ usedSpace`
(`usedSpace_ge_outside`, an *injection* into the counted families).  Completeness
needs the converse, so it needs the full deck partition
`Σ_su optRank + #cells + Σ_i |tableau i| = 52` — the one genuinely new counting
ingredient; the rest is `usedSpace_def` arithmetic.

**Done** in `DeckCount.lean`, up to `freeCellsOf`: `deck_partition'`, then
`usedSpace_eq_outside` (`usedSpace + Σ parked = #cells + #kingStacks`), then
`usedSpace_le_outside` / `usedSpace_add_parked_le` / `usedSpace_add_flute_le`, and
`kingList_le_kingRefund` (every king stack is refunded — the *columns → suits*
converse of `UsedSpaceBound`'s `kingRefund_le`).  Composed:

```
StateMatchesKingConfig.flute_sub_one_le_freeCellsOf :
  (pileFlute a) - 1 ≤ freeCellsOf p k
```

given `hflute` ("no column holds more than its flute") and `hcol` (pile `a`'s column
is exactly its dealt part, i.e. the flute is parked) — the two facts the prefix
classification supplies.  This is the completeness counterpart of `freeCellsOf_le`.
What remains on the affordability line is only reading `freeCellsOf` off
`possibleKings`, i.e. the `←` direction of `KingSpacesSpec`.

### SolverRecCheckSolvable loop invariant

The invariant is that once the winning move is examined, the solvable bit for the
king configuration is set to 1 and will stay 1 for all following iterations.

### Status (2026-08-08)

Proved, no `sorry`s:

- `CPNormal.lean` — `StateMatchesSolverPos.normalized`: a state matching an
  `IsCanonicalPos` position is already `Normalized` (`no_cpStep` + `no_fmStep`).
  This is step 1's "no foundation move first" and the "CP-normalization adds
  nothing" half.  Also `congr_of_tableau`: matching reads only the tableau and the
  foundations, so the cell *assignment* is irrelevant.
- `DeckCount.lean` — the deck partition and the space count (see above), the
  ingredient affordability needs.
- `DepthMatch.lean` — the step-1 skeleton (`DepthMatchesV`, `PileMatches_tail_same`,
  `not_depthMatchesV_of_goal`, `DepthMatchesV.drop`, `exists_boundary_of_break`,
  `exists_critical_move`) and the **three-layer** matching hierarchy:
  `DepthMatchesV` (depths only) < `DepthPlusKings` / `DepthPlusKingsCfg`
  (`StateMatchesSolverPos` with `flute_match` and `king_pile` weakened from `=` to
  `≤`, which is what a *parked* state satisfies) < `StateMatchesSolverPos`, with
  `toDepthPlusKings` down and `DepthPlusKings.upgrade` (CP-normality) back up.
  **Both `≤` clauses are derived, not assumed** (`DepthPlusKings.of_depthMatch`):
  `flute_le_of_depth` from `flute_maximal`, `king_le_of_depth` from `king_frontier`,
  neither needing CP-normality.  So the picture is symmetric — *physical ≤ recorded*
  always, *equality* exactly when no cell card can be dropped — and the middle
  layer's real content is just the depth match, the card count and the foundations.
  `DepthPlusKings.usedSpace_add_flute_le` restates the space bound over the middle
  layer, i.e. over the state `exists_critical_move` returns.  The king
  configuration is a *function of the state*, not a choice: `PiledSuit`, `cfgOf`,
  `cfgBitSet_cfgOf` (bit set ↔ not piled) and `DepthPlusKings.toCfg`, which
  produces `DepthPlusKingsCfg g u p (cfgOf u p)` — so `k_t` needs no guessing.
- `MatchesDepth.lean` — `matches_of_depth_match`, the converse: merged position +
  depth agreement + CP-normal + foundations ⟹ full match.  Together with
  `no_cpStep` this makes the depth vector a complete invariant of merged
  positions, which is what makes step 4 depth arithmetic.
- Reusable from soundness: `Solvable.iff_normReach`, `PlaysAll.preserves_Solvable`,
  `CPStep.preserves_Solvable`, `move_merged` (`DepthSum` drops),
  `removeFlute_merged`, `MoveSim.movePre_*` (which also export the resulting
  columns), `Simulates.ofRemoveFlute`, `cleanupRunResult_sim` (its inserted
  `Reach` is only cell→pile drops, so it transfers solvability both ways).

### Status (2026-08-09)

**Step 1 is closed**, and so is the destination question.  Three new files, no
`sorry`s:

- `CriticalMove.lean` — the rest of step 1.  `next_foundation_buried`: at a canonical
  position each suit's next foundation card is *strictly* below its boundary
  (`foundation_maximal_weak` + `busyAces = 0` gives "not free"; equality with the
  boundary would force `pileFlute = 1` via `flute_not_aces` and then
  `busyAces_complete` contradicts `busyAces = 0` again).  Hence
  `no_fmStep_of_depthMatch`: **no foundation move is available at any state that
  still matches the depth vector and the foundations** — the card that would have to
  move is buried, and `buried_inaccessible` puts a buried card out of reach.  So
  along the prefix every move's destination is a cell or a column, the foundations
  are constant, and `exists_critical_move_aces` carries `cards_count` *and*
  `aces_match` to the critical state.  `exists_critical_state` packages it
  (`DepthPlusKings` + `Solvable` + `|tableau a| = pileDepth a`), and
  `exists_critical_state_affordable` reads the space bound off it — so `k_t` is
  affordable **by construction**, which is what `solverGetMovable` needs.
- `DeckCount.lean` (amended) — `kingList_le_kingRefund_of` /
  `flute_sub_one_le_freeCellsOf_of`, the space count over *hypotheses* instead of a
  full match, so the middle layer can use it (`king_pile`'s `=` degrades to `≤`
  harmlessly).  The full-match versions remain as corollaries.
- `DestComplete.lean` — the destination is forced, in three pieces.  **The
  destination never moves a depth** (only the source column loses a card;
  `DepthMatchesV.drop` handles the rest), so it cannot change which child position
  the play reaches.  **Parking then dropping *is* the direct move**
  (`cell_park_then_drop`: the cell detour restores the cell to `none`, so the
  composite is literally `applyMove … ⟨pile a, pile q⟩`), which is what makes the
  play's choice CP-equivalent to the solver's.  **A column destination is unique**
  (`pile_dest_unique`; a king fits only on *empty* columns — the relabelling freedom
  the abstract state deliberately does not record, `king_dest_empty`).  Plus
  `self_move_id`/`dest_ne_source` for the degenerate "put it straight back" move and
  `critical_child_depthMatch` for the child's depth match.
- `CompletenessSkeleton.lean` — the spec layer.  `CompleteBits` (the `→` half of
  `SolvableBits`), `HashmapComplete`, `RecCheckSolvableComplete`, and the
  recombination lemmas (`solvableBits_iff`, `hashmapCorrect_of`,
  `recCheckSolvableSpec_of`: soundness ⊕ completeness ⟹ `RecCheckSolvableSpec`).
  The load-bearing structural lemma is `CompleteBits.or_left` — **completeness is a
  *persistence* property, not an additive one**: one particular iteration carries the
  bit and every later `|||` must preserve it, which is also why the loop's `break`
  and its `movable &&& ~~~solvable == 0` skip are harmless.  The `hash = 0` leaf is
  done (`subsetAt_one_ten`, decided: at ten free piles the mask `1` expands to
  everything).  `SubsetComplete` / `ComponentComplete` are stated so the recursion
  can be built against them.

#### What `k_t` is, exactly

`k_t` = **the physically piled suits of the critical position, plus the moved king in
the king-to-empty-column case.**  The base is `cfgOf t₀ p` (`PiledSuit`: a
solver-empty column whose deepest card is that suit's).  The extension is
well-defined *because* the base is physical: every suit `cfgOf` assigns sits on a
**non-empty** column, so the empty column the king is about to move onto is
unclaimed, and adding `su₀ ↦ i₀` keeps the assignment injective.  `OwnsPile`'s second
disjunct licenses the claim (`tableau i₀ = []` and `VALUE kings[su₀] = 13`, which
holds because the moved card is the suit's king and pile boundaries are never free).

The extension costs nothing and buys the right branch:

* refund: `su₀` contributes `13 - VALUE kings[su₀] = 0`, so `freeCellsOf` is
  unchanged (and `freeCellsOf_mono`/`kingRefund_mono` cover the general `MaskSub`
  case anyway);
* branch: with `su₀` piled, `solverGetMovable`'s king-pile mask fires through
  `possibleKings[fluteLen-1] &&& kingOnPile`, which is the bound already proved.

#### Which `possibleKings` index each case needs, and where it comes from

`solverGetMovable` indexes at `fluteLen-1` for a column destination and at `fluteLen`
for `EXTRA` / a king pile whose suit the configuration does not pile.  The extra cell
is supplied by the play itself:

> if the destination is `EXTRA`, or a king pile for a suit unpiled in `k_t`, the
> boundary card fits on **no** column and cannot go to the foundation, so the critical
> move was a park — and the cell it used was free beforehand.

`DestComplete.cell_dest_of_no_fit` / `one_le_freeCells_of_no_fit` prove the step from
"fits nowhere" to "one more free cell", and
`DeckCount.flute_sub_one_add_freeCells_le_freeCellsOf_of` keeps the free-cell count as
slack, giving `fluteLen - 1 + #freeCells ≤ freeCellsOf p k_t`.  The exception —
`nextCard` of a king is `none`, so an empty column *does* accept a king
(`king_dest_empty`) — is exactly what the `k_t` extension above absorbs.

The `EXTRA` half of "fits nowhere" is **proved** — `ExtraDest.no_column_accepts_of_extra`,
taking `DestValid`'s `EXTRA` branch verbatim.  The argument is the walk's own: if some
column `q` accepted `B`, its top would be `B + 1`; `free_above_boundary` says every card
physically above a column's boundary is free (a non-free card sits at its own dealt
slot, which is at or below its *own* boundary, and a card is in one column only), and
`above_code` says the run above the boundary descends by one — so `B+1 … B+n₀-1` are
exactly the cards above `q`'s boundary and `B + n₀` **is** that boundary, never free
(`boundary_not_free`).  Hence the walk stops at `n = n₀` on a boundary card and the
destination is `q`, not `EXTRA`.  The two degenerate shapes close the same way: with
nothing above the boundary the top *is* the boundary and `n = 1`; a solver-empty column
is a king run whose cards are all free, so the walk would have to run past the king,
against `VALUE B + n ≤ 13`.

The king-frontier half is **proved** too — `ExtraDest.empty_of_accepts_king_frontier`:
when `B = kings[su]`, *only an empty column* can accept it.  A positive-depth column
would need a same-suit card above `kings[su]` at or above its boundary, and boundaries
are never free while `king_frontier` says every such card *is* free; a solver-empty
column that took it would be carrying `su`'s own run, i.e. `su` would be piled.

And the dispatch is assembled: `DestAfford.critical_dest_affordable` takes `DestValid`
and the play's critical move and returns a configuration the state realizes together
with the disjunction `solverGetMovable`'s mask *is* — either `fluteLen` cells are free,
or `fluteLen - 1` are and the destination is a column or a piled king.  `k_t` itself is
`CriticalMove.cfgOfPlus` (`cfgOf` plus the moved king), realized by
`DepthPlusKings.toCfgPlus`; `maskSub_cfgOfPlus` + `freeCellsOf_mono` carry the space
bound to it.  `DestAfford.head_eq_boundary` identifies the abstract boundary card with
the column's head, and step 1 now exports `m.src` and the depth-match break so
`dest_ne_source` applies.

#### From `k_t` to a bit the loop actually iterates over

`closureInfo_block` says a block holds exactly the **maximal** assignments —
`min(freePiles,4)` suits piled — so `k_t` itself usually has no bit; it enters through
the `subsetTable` expansion.  `MaximalCfg.exists_block_cfg_maskSub` supplies the
covering configuration (`MaskSub d k_t` with `d` in the block, decided against the
tables from `card_clear_le_freePiles`), and `exists_block_cfg_afford` carries the space
bound to it via `freeCellsOf_mono`.  `GetMovableSpec.getMovable_bitSet` — the converse
of `getMovable_cells`, cheap because `KingInfoCorrect` and `bitSet_kingOnPileMap` are
both `↔` — then turns that budget into `BitSet movable i`.  So the chain

> play parks `fluteLen-1` cards ⟹ affordability at `k_t` ⟹ affordability at a block
> configuration `d ⊇ k_t` ⟹ the solver's `movable` has `d`'s bit

is closed.  What is *not* closed is the physical half: that the state can be brought
into configuration `d` (moving king runs from the cells onto empty columns), which is
what `SubsetComplete` needs beyond the counting.

#### Step 4 is depth arithmetic

`DepthUnique.lean` proves the minimality the plan assumed: `merge_complete` read through
`PileMatches` says `pileDepth i` is the **least** depth the physical column matches
(`le_of_pileMatches_of_mergeCond`, via `PileMatches.succ_below` — a smaller match would
extend the descent down to `pos2card[i][m-2], pos2card[i][m-1]` and make them
consecutive).  Hence `pileDepth_eq_of_matches`: two merged positions matching the same
state have the same depth vector, and `canonical_eq_of_matches`: **a state determines
the canonical position it matches** (`IsCanonicalPos_unique` supplies the rest).

So step 4 needs no reasoning about the merge loop's history: whatever canonical position
the post-move state matches *is* the one `SolverMove` + `SolverCleanupPile` computed.

One corner is isolated rather than proved: `merge_complete` is vacuous at depth `≤ 1`,
so the argument does not separate depth `1` from depth `0` when the single dealt card is
a king with its run above it — such a column genuinely matches both.  Cleanup's
lone-king branch vacates that pile to depth `0`, so the solver never emits one, but that
is not recorded in `PileMerged`; it is carried as the hypothesis `NoLoneKing`.
**Discharging `NoLoneKing` from the cleanup development is a small open item.**

Open, in rough risk order:

1. **the recursion assembly** — the mirror of `RecStepSound` + `RecLoopSound` +
   `RecCheckSound` + `SolveSound` (~2 500 lines of `forIn`/memo/`partial_fixpoint`
   plumbing) against `RecCheckSolvableComplete`.  Low risk, high volume; the loop
   invariant is the persistence one above rather than `SoundBits.union`;
2. steps 3–5 of the chain: CP-normalize after the critical move and identify the
   result with the solver's child (`matches_of_depth_match` + `merge_complete` pins
   the depth; `critical_child_depthMatch` supplies the depth match), then run the
   drain;
3. `subsetTable` / `forcedKings` completeness (`SubsetComplete`) — the physical half
   only: the tables are already characterized as `↔` (`subsetAt_spec_pos`,
   `KingVacates`, `component_run_eq`);
4. component completeness (`ComponentComplete`), same remark;
5. small pieces: re-exposing phases 2–3 of the simulation with `NormReach`
   instead of `Reach`.  (The CP-only normal form is done — `exists_cpNormalForm`
   in `CPNormal.lean`, with `CPReach.solvable_iff`.)

---

## Open Questions / Harder Parts

1. ~~**Termination of `solverRecCheckSolvable`**~~ *(resolved)*: `move_merged` exports
`DepthSum p' < DepthSum p`, and both the soundness and the completeness statements take
the successful run as a hypothesis, so the `partial_fixpoint` never has to be shown total.

2. **King-configuration component closure**: the `computeComponentKingBits` / `componentTable` logic encodes reachability between king configurations. A separate proof that the component table is correct (matching `kingOnPileMap` and the reachability relation) would be needed.  There is something started in BitmapProofs, but it needs more work.

3. **Completeness vs. soundness**: soundness (solver says solvable → it is) is the easier direction. Completeness (game is solvable → solver finds it) requires showing no solvable path is missed, which needs the simulation to be surjective in the right sense.

4. **Extra-card sentinel convention**: cards at deal positions 50–51 have `card2depth = 5`, always ≥ any pile depth. This should be established as part of `WellFormedLayout` and propagated through the freed-predecessor checks.

5. **King Pile numbering**: The concrete state assigns the kings to specific empty piles.  The abstract state via the king configuration only says which kings are dedicated to a pile, but not to which.  If we want to show that the "canonic" concrete state for the abstract state is reachable, this only holds modulo the right assignment of kings to piles.
