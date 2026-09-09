# Seahaven Lean Proof — File Layout & Theorem Index

Generated 2026-09-09 by surveying all 89 files under `lean/Seahaven/`. This is a map, not
a tutorial: for each file it gives the one-line purpose, the headline theorem(s)/defs a
reader would actually search for, and cross-references to siblings. A "Cleanup notes"
section at the end collects every naming/duplication issue found, for anyone doing a
tidy-up pass.

## Status

- **89 `.lean` files, ~47,400 lines total, zero `sorry`s.** Every occurrence of the string
  "sorry" left in the tree is inside a doc comment, not a proof.
- **The project is fully proved.** The headline theorem is
  `SolverSpec.solver_is_correct : Correctness` in `SolverIsCorrect.lean`, unconditional
  (only the standard `propext`/`Classical.choice`/`Quot.sound` axioms plus the pre-existing
  `native_decide` axioms of the card-encoding tables).
- `Correctness` itself is defined in `SolverCorrectness.lean` — the user's own file,
  described elsewhere as "do not edit." It says: two invariants `Inv0`/`Inv1` exist such
  that `Inv0` holds of `emptyGlobals`, `Inv1 → Inv0`, `initcard` establishes `Inv1` from
  `Inv0`, and under `Inv1` every reachable state's `solve` call succeeds, preserves `Inv1`,
  and answers `SUCCESS`/`NOMOVE` exactly according to solvability.
- No file is dead/unimported: every `.lean` file is reachable from the root `Seahaven.lean`
  import list, directly or transitively (checked explicitly for the 6 files `Seahaven.lean`
  doesn't import directly: `EStateMOrder`, `MathlibImports`, `MoveAcesSim`, `RecCheckRuns`,
  `Rules`, `SolverRealSpec` — all are imported by something else in the tree).
- One file, **`SolverModel.lean`, is a strong candidate for removal** — see Cleanup notes.

## How this map is organized

The 89 files fall into eight roughly dependency-ordered clusters. Within each cluster the
files are listed in the order you'd actually want to read them (base definitions first,
assembly theorems last).

1. [Foundations](#1-foundations) — the game rules, the solver's Lean model, and the bridge between them
2. [SolverSpec\* — per-function specs of the imperative solver](#2-solverspec--per-function-specs-of-the-imperative-solver)
3. [King-configuration bit machinery & recursion soundness](#3-king-configuration-bit-machinery--recursion-soundness)
4. [Move simulation (Rules-side realization of solver moves)](#4-move-simulation-rules-side-realization-of-solver-moves)
5. [recCheck / solve top-level correctness](#5-reccheck--solve-top-level-correctness)
6. [Convert / normalize (dealt state → canonical position)](#6-convert--normalize-dealt-state--canonical-position)
7. [Completeness argument: critical move & depth matching](#7-completeness-argument-critical-move--depth-matching)
8. [Cleanup/king-assembly & the CPNorm family](#8-cleanupking-assembly--the-cpnorm-family)

Then: [Cleanup notes](#cleanup-notes) (naming issues, duplication, dead code, all in one place).

---

## 1. Foundations

The game itself, its Lean-model transliteration of the C solver, and the bridge predicates
tying a `Rules.State` to the solver's arrays. No file here imports anything from clusters 2–8.

### `Rules.lean` (224) — `namespace Rules`
The game: `Suit`, `Rank`, `Card`, `State`, `Move`, `Position`, `applyMove`, `init` (deal),
`isSolvable`/`isReachable`/`isSolution`/`isGoal`, `Shuffle`. No imports — the base of the
whole project.

### `MathlibImports.lean` (27)
Pure import aggregator: one curated Mathlib import list every proof file pulls in instead
of `Mathlib.Tactic`, to cut `.olean` load time. No declarations.

### `EStateMOrder.lean` (68) — `namespace Seahaven`
Supplies the `CCPO`/`MonoBind`/`MonadTail` instances for `EStateM` that Lean 4.31 doesn't
ship by default — this is what lets `recCheckSolvable` be a `partial_fixpoint` (real
unfolding equation) and lets `while` loops unfold via `Lean.Loop.forIn_eq_of_monadTail`.

### `Solver.lean` (536) — `namespace Solver`
Line-by-line transliteration of `solver.c`: `PosType`/`Globals`, the lookup tables
(`pileHashes`, `bits2grlex`, `closureInfos`, `componentTable`, `subsetTable`,
`kingOnPileMap`), every solver primitive (`cleanupPile`, `removeFlute`, `moveAces`, `move`,
`getDestination`, `computeKingSpaces`, `computeComponentKingBits`), the recursive search
`recCheckSolvable`, and the entry point `solve`. This is "ground truth" — everything else
reasons about *this* file's definitions.

### `SolverModel.lean` (318) — `namespace SolverModel` — **see Cleanup notes**
Fuel-bounded structural-recursion re-implementations of `Solver.lean`'s loops
(`cleanupPile`, `removeFlute`, `getDestination`, `moveAces`, `move`,
`convertFromPilesKings`), historically needed before `while` loops were unfoldable. The
file's own comment says that need is gone; only `#eval` sanity checks remain live.

### `LayoutProofs.lean` (701)
Bridges `Rules.State` ↔ `Solver.Globals`: `encodeCard`/`decodeCard` (the `Card ↔ UInt8`
bijection), `StateMatchesLayout`, and the headline `StateMatchesLayout.applyMove` (a legal
move preserves the match).

### `FoundationMoves.lean` (711)
Proves playing a card to the foundation never breaks solvability
(`foundationMove_preserves_Solvable`), via a limited-confluence argument (`fm_commute`,
`fm_absorb`, `fm_simulate`) under a no-duplicate-cards invariant `NoDupState`. Defines its
own inductive `Solvable : State → Prop` — see Cleanup notes for the `Solvable`/`isSolvable`
naming collision with `Rules.lean`.

### `UInt8Lemmas.lean` (110)
`UInt8.toInt` and its arithmetic (wraparound `+`/`-`, `toInt32` promotion), plus the card
codec accessors `VALUE_toNat`/`SUIT_toNat`/`CARD_toNat` as plain `Nat` arithmetic.

### `CountProofs.lean` (265)
`countCard`/`countCells`/`countColumn`/`countTableau`/`countState` and the headline
`movePreservesCards` — a legal move preserves the total count of every card.

### `DeckCount.lean` (707)
Turns per-card counting into a whole-deck partition (`deck_partition`), then proves the
*converse* direction of `usedSpace` accounting (`usedSpace_eq_outside`/`_le_outside`) and
the affordability bounds (`usedSpace_add_flute_le`, etc.) the **completeness** side of
`getMovable`'s space test needs (contrasted with the soundness-side bound in
`SolverInvariant.lean`).

---

## 2. SolverSpec\* — per-function specs of the imperative solver

Result of a 2026-08-04 split of one 8733-line `SolverSpec.lean` into one file per solver
function, plus a shared common file. All 9 of the per-function files declare inside
`namespace SolverSpec`; `SolverRealSpec.lean` and `SolverInvariant.lean` (the two files this
cluster is built on) do **not** — see Cleanup notes.

### `SolverInvariant.lean` (2447, 74 declarations) — no namespace wrapper
The canonical-form invariant tower: `WellFormedLayout`, `PileBase`/`PileMerged`/
`PileClean`/`SuitClean`, `SolverInvBase`/`SolverInvLocal`/`SolverInvMerged`/
`IsCanonicalPos`, `MergedUpTo`; the `usedSpace` counting-argument family
(`usedSpace_ge_of_free_above`, `usedSpace_ge_of_disjoint_free`, …); and uniqueness
(`IsCanonicalPos_unique`, `IsCanonicalPos_hash_inj`). By far the largest single file in the
project — see Cleanup notes for a 4-way split proposal.

### `SolverRealSpec.lean` (770) — no namespace wrapper
The foundational "no fuel model needed" layer: specs proved directly against the real
`while`-loop functions, explicit-loop twins (`cleanupPileExplicit`, `moveAcesExplicit`,
`moveExplicit`), and — notably — the actual **definitions** of `cleanupRunResult`,
`preCleanupPile`, `kingMove`, `removeFlutePre` that the per-function spec files below
reason about (see Cleanup notes: these defs are *not* in the eponymous spec files).

### `SolverSpecCommon.lean` (604)
Shared preconditions (`ValidDepths`, `MoveValid`, `CleanupReady`, `fluteNorm`) and helper
lemmas reused by every function-spec file below.

### `SolverSpecKingMove.lean` (940)
Spec for `kingMove`: `kingMove_pileClean_self`, `kingMove_pileBase_ne`/`_pileMerged_ne`,
`kingMove_suitClean`.

### `SolverSpecPreCleanupPile.lean` (2388)
Spec for `preCleanupPile` (the non-king cleanup tail): `preCleanupPile_pileBase_self`/
`_pileMerged_self`/`_pileClean_self`, `preCleanupPile_suitClean` (the hardest clause),
`preCleanupPile_hash_def`/`_usedSpace_def`.

### `SolverSpecCleanupPile.lean` (1158)
Spec for `cleanupPile` (dispatches `kingMove` vs. `preCleanupPile`): `cleanupPile_eq` (the
shared exact-run preamble), `cleanupPile_base`, `cleanupPile_merged`. Needs
`set_option maxHeartbeats 4000000` — a known, documented build-time hotspot.

### `SolverSpecRemoveFlute.lean` (238)
Spec for `removeFlute`, reduced to `cleanupPile`'s spec via `removeFlute_eq`. Defines the
termination measure `DepthLe`/`DepthSum`. Deliberately has no `Simulates` lemma (documented:
"removing the flute as a card operation would be wrong").

### `SolverSpecSolverCleanupPile.lean` (350)
Spec for one iteration of the monadic convert-time cleanup loop: `solverCleanupPile_step`
(carries the `MergedUpTo` loop invariant across one pile).

### `SolverSpecMoveAces.lean` (2771 — largest split file)
Spec for `moveAcesLoop`/`moveAces`: `ctz_*` bit-twiddling lemmas, `MoveAcesInv`,
`moveAcesLoop_run` (exact symbolic run), `moveAces_merged`.

### `SolverSpecMove.lean` (1845)
Spec for the composed `move` step: `moveDestPre`, `DestValid`, and the headline
`move_merged` (canonical → canonical, strictly decreasing `DepthSum`).

### `SolverSpecDrain.lean` (190)
Spec for the `busyAces` drain loop: termination measure `rank`, `drain_canonical`
(merged → fully canonical), `drain_canonical_of` (predicate-carrying version).

---

## 3. King-configuration bit machinery & recursion soundness

Two interleaved threads: (a) soundness of `recCheckSolvable`'s recursion itself
(`SoundnessSkeleton`→`RecStepSound`→`RecLoopSound`, a clean 3-layer non-overlapping stack),
and (b) the king-configuration bit-encoding machinery both the soundness *and* completeness
directions read (`KingReshuffle`/`KingMoveSim`/`ComponentKingBits`/`OrConsistentTable`/
`ComputeKingSpaces`/`UsedSpaceBound`), plus two small completeness-direction mirror files
(`SubsetTransport`, `MovableBit`).

### `SoundnessSkeleton.lean` (745)
Defines the vocabulary (`Simulates`, `SoundBits`, `MaskSub`) and proves the one deep
transport lemma, **`kingStep_transport`** (`Simulates.transport`) — the crux of why
querying the child at the *parent's* configuration is sound. States (as `Prop`s, proved
elsewhere) the three semantic obligations `SubsetSound`, `ComponentSound`, `MoveSimulated`.

### `RecStepSound.lean` (121)
Discharges the `movable'` step of one pile-loop iteration from a `Simulates` package:
`recStep_sound_of_sim`, `recStep_sound`.

### `RecLoopSound.lean` (437)
Assembles the whole 10-pile loop: `LoopInv`, `contribution_sound`, and (identifying the
loop with the real `partial_fixpoint` body via `recCheck_eq`) the payoff
**`recLoop_body_sound`**.

### `KingReshuffle.lean` (831) — `namespace KingSwap`
The combinatorial heart of `ComponentSound`/`SubsetSound`: an abstract greedy-reachability
argument over sets of piled suits (`KingSwap.reachable`), reduced to two physical
obligations `KingUnpileReachable`/`KingPileReachable`, and assembled into
**`componentSound_of`**/**`subsetSound_of`**.

### `KingMoveSim.lean` (722)
Discharges `KingReshuffle`'s two physical obligations with actual card moves
(`kingUnpileReachable`, `kingPileReachable`), closing **`componentSound`**/**`subsetSound`**.

### `KingConfigSim.lean` (919)
`Simulates`/`SimulatesNorm` instances and frame lemmas carrying `StateMatchesKingConfig`
through `cleanupPile`'s phases and through phase-1 flute moves
(`SimulatesNorm.preCleanupPile`/`.kingMove`/`.cleanupPile`). Also home to `clearCfgBit` —
see Cleanup notes for its split from `KingReshuffle`'s `setCfgBit`. The most eclectic file
in this cluster; mixes in generic column/flute facts (`free_above_boundary`, `isRun_take`).

### `ComponentKingBits.lean` (405)
What `computeComponentKingBits` computes, structurally parallel to `ComputeKingSpaces.lean`:
**`component_bit_iff`**-style per-block table specs, **`component_run_eq`**.

### `OrConsistentTable.lean` (127)
Small generic bit-combinatorics library (`or_consistent`, `or_consistent_spec`) used by
exactly two consumers: `subsetTable` (`SoundnessSkeleton`) and `componentTable`
(`ComponentKingBits`).

### `SubsetTransport.lean` (85)
The **completeness-direction mirror** of `kingStep_transport`:
`kingStep_transport_complete`. Deliberately paired, documented in its own docstring.

### `MovableBit.lean` (106)
Completeness-side counterpart to `RecStepSound`: `exists_movable_bit_of_critical`,
`bitSet_allkings_of_cfg` (the loop's early break never discards a realizable configuration).

### `ComputeKingSpaces.lean` (661)
Proves `KingSpacesSpec` — full correctness of the three-nested-loop `computeKingSpaces`.
Headline: **`kingSpaces_spec`**.

### `UsedSpaceBound.lean` (494)
Proves `usedSpace` really bounds all cards physically outside the piles (the
**soundness**-direction counterpart of `DeckCount.lean`'s completeness-direction bound);
headline: `StateMatchesKingConfig.freeCellsOf_le`.

---

## 4. Move simulation (Rules-side realization of solver moves)

Shows every solver step (`move`, `moveAces`, `cleanupPile`) is realized by legal `Rules`
moves on a matching concrete state. Two confusable-name pairs live here — see Cleanup notes.

### `MoveSim.lean` (1422) — `namespace SolverSpec` wraps only `movePre`
Realizes/matches phase 1 of `move` (the flute move) for all four `getDestination`
outcomes: `FluteMoveAbs`/`ParkMoveAbs`, `movePre`, `StateMatchesSolverPos.fluteMove`/
`.parkMove`, `StateMatchesKingConfig.movePre_run*`.

### `MoveSimulatedReduce.lean` (73)
Reduces `MoveSimulated` to a single remaining hypothesis `Phase1Simulated`:
`moveSimulated_of_phase1`.

### `Phase1Sim.lean` (332)
Closes `Phase1Simulated` unconditionally, hence **`moveSimulated : MoveSimulated`** and
**`recCheckSolvableSound : RecCheckSolvableSound`** — the soundness capstone of this whole
cluster (despite the modest file size — point here, not to `SolverMoveSim.lean`, when
looking for "is `move` sound").

### `GetMovableSpec.lean` (329)
Specs `getMovable`: `getMovable_cells`/`_freeCells` (soundness), `getMovable_bitSet`
(completeness converse).

### `SolverMoveSim.lean` (202)
Simulates phases 2+3 of `move` (removeFlute + drain) *given phase 1 as a hypothesis*:
`Simulates.move`, `exists_child_match_of_movePre`.

### `MoveAcesSim.lean` (850)
**Top-level assembly** for a whole `moveAces` call (despite the plain name — see Cleanup
notes on naming vs. `SimulateMoveAces.lean`): runs `moveAcesLoop_run`, composes
`SimulateMoveAces.lean`'s ingredients, produces the 0-sorry `SimulatesNorm.moveAces`.

### `SimulateMoveAces.lean` (1118)
**Low-level ingredients** for the `moveAces` drain (despite the more elaborate name): the
"sync" step (`SimulatesNorm.syncPlays`) and the walk's "tail" (`SimulatesNorm.tailPlays`),
at the `StateMatchesSolverPos` level only.

### `CleanupSim.lean` (1719)
Simulates `cleanupPile` at the `StateMatchesSolverPos` (not yet king-config) level: merge/
vacate are pure bookkeeping, the freed-predecessor extension is the only real card motion
(`StateMatchesSolverPos.cleanupPileSim`/`.cleanupPileSimKing`).

### `GetDestination.lean` (578)
Explicit-loop twin + fuel model for `getDestination`; headline `getDest_spec`. Documents
(not a live issue) that an old in-loop dead-code early-return was removed from both this
model and `solver.c` together.

### `NormReachBridge.lean` (54)
Tiny bridge: `PlaysAll.toNormReach`, `CPReach.toNormReach`, `drain_solvable_iff`.

### `SimulatesNorm.lean` (356)
Defines `SimulatesNorm` (a `Simulates` bundle with equi-solvability, `.solvable_iff`) and
its composition lemmas (`.refl`/`.trans`/`.vacate`/…), plus `VacateSites`.

---

## 5. recCheck / solve top-level correctness

Soundness *and* completeness of the memoized recursion itself, then lifted through `solve`.
Files split by top-level namespace: `RecCheckSound`/`RecCheckSpec`/`RecCheckRuns`/
`RecCheckComplete`/`InitCard` declare at the root; `SolveSound`/`SolveCorrect`/
`DealMatches`/`SolverIsCorrect` wrap in `namespace SolverSpec` — see Cleanup notes.

### `RecCheckSound.lean` (1654)
Soundness of `recCheckSolvable` (the memo wrapper): `hash == 0` leaf
(`solvable_of_hash_zero`), memo slot-tag arithmetic, and the top theorem
**`recCheck_sound_of_semantics`**.

### `RecCheckSpec.lean` (213)
The **two-sided** spec, one merged induction: **`recCheck_spec`** (serves soundness and
completeness at once, leaving `RecLoopComplete` open).

### `RecCheckRuns.lean` (163)
Totality: `recCheckSolvable` actually returns (`forIn_exists`, `recBodyRuns`).

### `RecCheckComplete.lean` (120)
Discharges the last obligation `RecLoopComplete`, closing
**`recCheckSolvableSpec : RecCheckSolvableSpec`** unconditionally.

### `SolveSound.lean` (322) — `namespace SolverSpec`
`solve`'s soundness: `solveTail_bits`, **`solve_sound`**/`solve_sound_canonical`.

### `SolveCorrect.lean` (381) — `namespace SolverSpec`
`solve`'s two-sided correctness: `solveTail_spec_bits`, `solveTail_runs`,
**`solve_correct`**, `solve_correct_of_normReach`.

### `SolverCorrectness.lean` (87) — **the user's file, do not edit**
Only `Correctness : Prop` (the target spec) and the small glue defs it needs
(`pilesKingsFromState`, `Rules.Shuffle.vector`).

### `SolverIsCorrect.lean` (372) — `namespace SolverSpec`
**`solver_is_correct : Correctness`** — the final unconditional theorem, assembled from
`Inv0`/`Inv1`, the deal bridge, `initcard_ok'`, and `ReachableMatch`/`CleanupLax`/
`KingPileMax`.

### `DealMatches.lean` (333) — `namespace SolverSpec`
The fresh-deal-only entry point: `dealCards`/`dealState`, `fullPk`, `dealState_matches`,
`solve_deal_sound`.

### `InitCard.lean` (495) — nested `namespace IsDeal`
`initcard` establishes `WellFormedLayout ∧ HashmapCorrect ∧ HashmapSound`: `IsDeal`,
`InitInv`, headline **`initcard_ok`**/`initcard_ok'`.

---

## 6. Convert / normalize (dealt state → canonical position)

`convertFromPilesKings`'s four loops, proved pure/closed-form, then simulated by legal
moves at increasing generality. A clean one-theme-per-file split.

### `Normalize.lean` (444)
Defines normalizing moves (`CPStep`, `NormStep`, `NormReach`) and proves normalization is
solvability-neutral and terminating: `Solvable.iff_normReach`, `exists_normalForm`.

### `FluteMoves.lean` (297)
The concrete `2L-1`-move realization of one abstract flute move: `fluteMoves`,
`run_fluteMoves` (headline), `reach_fluteMoves`.

### `ConvertPre.lean` (1085 — largest of the Convert family; split candidate, see Cleanup notes)
`rfl`-twin of all four convert loops, the per-suit walk theory (`runLen`, `cvAceVal`,
`cvKingVal`), and the closed-form position **`convertPre`** + **`convert_run_eq`**.

### `ConvertCount.lean` (195)
Proves the counting bound `CvCountBound` via a cardinality injection into the 52-card deck:
**`cvCountBound`**.

### `ConvertInv.lean` (341)
`convertPre` satisfies `MergedUpTo g · 0`: **`convertPre_mergedUpTo_zero`**.

### `ConvertSound.lean` (79)
Pure top-level fact: `convertFromPilesKings` returns a canonical position:
**`convert_canonical`**.

### `ConvertSim.lean` (116)
Rules-side: a matching state's convert call is realized by legal moves, ending matched:
**`convert_simulates`**.

### `ConvertMatch.lean` (541)
Generalizes to an *unnormalized* caller: `CvEntry`, the two remaining obligations
`CvPrologueSim`/`CvCleanupSim`, and **`convert_simulates_lax`**/**`solve_correct_lax`** —
the version `SolverIsCorrect` actually calls.

### `ReachableMatch.lean` (748) — mixed: root namespace, then `namespace SolverSpec` from line ~457
The Rules-side obligations about a state's *own* encoding: **`validDepths_pilesKings`**,
**`exists_cvEntry`**.

### `CleanupLax.lean` (475) — `namespace SolverSpec`
Discharges `CvCleanupSim`: **`cvCleanupSim`** (generalizes `SimulatesNorm.ofCleanupPile` to
a pile already carrying part of its flute extension).

### `FoundationMax.lean` (428) — `namespace SolverSpec`
First half of `CvPrologueSim`: every suit's foundation playable up to `cvAceVal`:
**`exists_maximal_foundations`**.

### `KingPileMax.lean` (763) — `namespace SolverSpec`
Second half of `CvPrologueSim` (king piles completed) plus the assembly:
**`cvPrologueSim`**.

---

## 7. Completeness argument: critical move & depth matching

Extracts, from a winning play, the first move that breaks a depth match ("the critical
move"), and shows the solver's own search considers it — the completeness mirror of
cluster 3's soundness argument.

### `MatchesPos.lean` (393)
Base relation: **`StateMatchesSolverPos`** (deliberately many-to-many), plus foundation
readout and king-pile content facts.

### `DepthMatch.lean` (555) — see Cleanup notes for disambiguation vs. the next two files
Defines `DepthMatchesV` (depth-only match) and the middle layers `DepthPlusKings`/
`DepthPlusKingsCfg`; extracts the critical move: **`exists_critical_move`**.

### `MatchesDepth.lean` (770 — largest in this cluster)
Proves depth match + CP-normal + merged + foundations ⟹ the **full** match (flute/king
fields are *forced*, not assumed): **`matches_of_depth_match`**.

### `DepthUnique.lean` (167)
Proves a state determines the unique canonical position it matches:
**`canonical_eq_of_matches`**.

### `CriticalMove.lean` (571)
Step 1: extends the critical-move extraction with card-count/foundation invariance and the
affordability bound: **`exists_critical_state`**/**`exists_critical_state_affordable`**.

### `DestComplete.lean` (354)
The chosen destination is irrelevant to which canonical child is reached:
`child_depthMatch_dest_irrelevant`, `cell_dest_of_no_fit`.

### `ExtraDest.lean` (402)
`getDestination = EXTRA` really means no column accepts the card:
**`no_column_accepts_of_extra`**, **`empty_of_accepts_king_frontier`**.

### `DestAfford.lean` (272)
Assembles the destination trichotomy into the affordability disjunction `getMovable`'s
mask actually reads: **`critical_dest_affordable`**.

### `MaximalCfg.lean` (84 — smallest file in the project)
Pure counting: every realized configuration is covered by some block-stored one:
**`exists_block_cfg_maskSub`**.

### `CompletenessSkeleton.lean` (369)
Completeness-side mirror of `RecCheckSound`: `CompleteBits`, `HashmapComplete`,
`ChildSpecComplete`. Contains one explicitly-superseded declaration
(`recCheckSolvableSpec_of`) — see Cleanup notes.

### `CriticalChild.lean` (322)
The critical move, physically simulated through `movePre`/cp-normalization/cleanup:
**`exists_child_of_critical`**.

### `CriticalIteration.lean` (493)
The pile-loop iteration at the critical index sets the bit; assembles the whole loop:
**`critical_iteration_bitSet`**, **`critical_loop_bitSet`**.

---

## 8. Cleanup/king-assembly & the CPNorm family

Closes the remaining gaps between the *initial* king configuration of a completeness
prefix and the *critical* state's own configuration, and normalizes cell→pile drops. The
four `CPNorm*.lean` files have easily-confused names — clarified below, renamed in Cleanup
notes.

### `CPNormal.lean` (449)
**"CP" = cell→pile** (`Rules.CPStep`), **not Lean's `Except` monad**. A merged/canonical
match is already `Normalized`: `no_cpStep`, `no_fmStep`; defines `CPReach` and
`exists_cpNormalForm`.

### `CPNormExcept.lean` (107)
The same normal form **excluding one designated pile `a`** (needed because the critical
move's source pile is handled separately): `CPStepExcept`, `exists_cpNormalForm_except`.
"Except" = "except pile `a`", an exclusion — again unrelated to Lean's `Except`.

### `CPNormMatch.lean` (114)
CP-normalizing preserves everything `StateMatchesSolverPos` cares about, at the plain
(no king-config) layer: **`exists_match_of_depthMatch`**.

### `CPNormCfg.lean` (173)
The same one layer up, adding **king-configuration** invariance (cp-drops never change
`OwnsPile`/`cfgOf`): **`exists_matchCfg_of_depthMatch`**.

### `EmptyPileCfg.lean` (408)
Closes the gap between the prefix's initial king config `k` and the critical state's `k_t`:
either they're equal, or both dominate a `HasSpareSubset`: **`cfg_eq_or_spareSubset`**.

### `ComponentComplete.lean` (181)
The converse component-table reading needed to transport an answer bit across that gap:
**`cfg_eq_or_component_bits`**. Tightly paired with `EmptyPileCfg.lean` (physical half +
bit-table half of one argument).

### `KingAssemble.lean` (153)
Completing a sparser config up to a covering "block" config is **reversible**
(`KingConfigEquiv`, strictly stronger than one-directional reachability):
**`exists_block_match`**.

### `MovePreMatch.lean` (142)
"Route B phase 1": the critical move's target matches `movePre`'s depth vector (depth-only,
deliberately): **`critical_depthMatchesV_movePre`**.

### `CleanupDepth.lean` (448)
Depth-vector-only match survives `cleanupPile`/`removeFlute`'s merge/vacate:
**`cleanupPile_depth`**, **`removeFlute_depth_le`**, `kingVacates_removeFlute`.

### `SolvableBits.lean` (422)
The central spec vocabulary: `closureInfoOf`/`subsetAt`/`BitSet`, `OwnsPile`/`CfgBitSet`/
`RealizesKingConfig`/**`StateMatchesKingConfig`**, **`SolvableBits`**, `HashmapCorrect`,
`RecCheckSolvableSpec`/`SolveSpec`. Read this first — it's used by name throughout clusters
7–8.

### `FoundationRun.lean` (319)
The one **solver-independent** (pure `Rules`) file in this cluster: `PlaysTo`/`PlaysAll`,
`runFrom`/`nextFoundationCard`, headline `playsAll_column`/`exists_playsAll_runFrom`.

---

## Cleanup notes

Everything below was flagged while surveying; ranked roughly by how much it's worth acting
on.

### Likely dead code

- **`SolverModel.lean`** — its own doc comment (lines 106–111) says the original purpose
  (proving specs against a fuel-bounded model instead of the real `while`-based solver) was
  dropped once Lean 4.31 made the real loops non-opaque, and that a model = real equality
  would now be **false as written** (`freedLoop`'s hard-coded fuel of 60 caps a loop the
  real `while` can run further). All that's left is `#eval`-only sanity checks
  (`runConvert`, `convertMatches`, `sampleShuffle`), which are not proofs. Checked: the only
  other file that imports it is `SolverSpecCommon.lean` (`import Seahaven.SolverModel`,
  `open SolverModel`), but every occurrence there of a `SolverModel`-defined name
  (`cleanupPile`, `removeFlute`, `move`, `moveAces`) is inside a *doc comment*, not an
  actual term — no proof anywhere in the tree calls a `SolverModel.*` declaration. So both
  the file and its one import site's `open SolverModel` look safe to delete.
- **`CompletenessSkeleton.recCheckSolvableSpec_of`** — its own doc comment says outright:
  *"Superseded by `RecCheckSpec.recCheck_spec`, which runs one merged induction instead —
  and which also proves the call *returns*, something neither half supplies."* Left in the
  file as historical scaffolding; the rest of the file (`CompleteBits`, `HashmapComplete`,
  `ChildSpecComplete`, the monotonicity lemmas) is still load-bearing for
  `CriticalIteration.lean`.
- **`SolverInvariant.depth_card_not_free`** — its own docstring says "the invariant
  argument of the original spelling was already unused." A harmless dead-parameter shim,
  kept only so call sites don't need to change.

### Genuine duplicate theorem (only one found)

- **`ConvertInv.cvAceVal_le`** and **`FoundationMax.cvAceVal_le_13`** are the exact same
  statement (`cvAceVal g d su ≤ 13`), independently proved by the same one-line
  `runLen_le` call, under different names, in two different files —
  `FoundationMax.lean` already (transitively) imports `ConvertInv.lean`, so it should just
  reuse `cvAceVal_le` instead of restating it.

### Same argument proved multiple times at increasing generality (not duplicates, but consolidatable)

- The convert loop-3 (cleanup-loop) induction is written out **three times**, each
  necessary for its file's stronger invariant: `cvCleanupLoop_run` (`ConvertSound.lean`,
  position-only), `cvCleanupLoop_sim` (`ConvertSim.lean`, + simulation witness),
  `cvCleanupLoop_lax` (`ConvertMatch.lean`, + the caller's own flute vector). A shared
  induction scheme parameterized over "what extra invariant survives one iteration" could
  collapse these to one.
- `solve`'s tail read-chain (`pk10[10]` → `bits2grlex` → `closureInfos` →
  `recCheckSolvable` → `subsetTable`) is re-derived **three times**: `SolveSound.solveTail_bits`,
  `SolveCorrect.solveTail_spec_bits`, `SolveCorrect.solveTail_runs`. A shared "the tail's
  four reads succeed with these values" lemma could replace all three.
- `RecCheckSound.hashmapSound_slotWrite` ↔ `RecCheckSpec.hashmapCorrect_slotWrite`, and
  `RecCheckSound.recBodyStep` ↔ `RecCheckRuns.recBodyRuns` — both pairs are explicitly
  documented in their own docstrings as "verbatim, with X in place of Y" / "this proof with
  the inversion deleted." Deliberate, not a bug, but a maintenance risk (edit one, forget
  the other) worth a shared-lemma refactor if anyone touches this area again.
- `SolverSpecPreCleanupPile.preCleanupPile_not_free_of_lt_boundary` is documented as
  subsumed by the more general `preCleanupPile_not_free_of_ne_absorbed`, yet both remain and
  the older one is still called once (line 1096) — trivial to delete in favor of the general
  form.

### Deliberate, documented mirror pairs — NOT duplicates, just easy to mistake for some

- `SoundnessSkeleton.kingStep_transport` ↔ `SubsetTransport.kingStep_transport_complete`
  (soundness direction / completeness direction of the same transport argument).
- `RecStepSound.recStep_sound` ↔ `MovableBit.exists_movable_bit_of_critical` (same "the
  solver really considers this move" fact, opposite logical direction).
- `MoveAcesSim.lean` / `SimulateMoveAces.lean` — not duplicates: `SimulateMoveAces.lean` is
  the low-level `StateMatchesSolverPos`-only ingredients file, `MoveAcesSim.lean` is the
  top-level assembly that lifts to `StateMatchesKingConfig` and runs the real loop. **The
  naming is inverted** relative to the sibling pattern elsewhere in the project (e.g.
  `MoveSim.lean` = low-level, `SolverMoveSim.lean` = higher assembly) — a reader would
  expect it the other way around. The two files even share one identifier name
  (`tailPlaysComplete`), which compounds the confusion.

### Naming worth improving

- **The four `CPNorm*.lean` files** are all about cell→pile move normalization, not Lean's
  `Except` monad, but the names alone don't convey that:
  - `CPNormal.lean` → base normalization (define + prove existence)
  - `CPNormExcept.lean` → the same, excluding one named pile
  - `CPNormMatch.lean` → + full `StateMatchesSolverPos` match
  - `CPNormCfg.lean` → + king-configuration match

  Suggested rename: `CPNormalize.lean` / `CPNormalizeExceptPile.lean` /
  `CPNormalizeMatch.lean` / `CPNormalizeKingCfg.lean` (or similar) so the "cell→pile" and
  "except a designated pile"/"king-config layer" readings are legible from the filename
  alone.
- **`DepthMatch.lean` / `MatchesDepth.lean` / `DepthUnique.lean`** are three genuinely
  distinct layers of one pipeline, but their names give no hint of the direction split:
  - `DepthMatch` = the depth-only match relation **+** critical-move extraction
  - `MatchesDepth` = depth match **⟹** full match (the CP-normality "forcing" step)
  - `DepthUnique` = merged position **⟹** the depth (hence the position) is **unique**

  A future rename (e.g. `DepthMatchRelation.lean` / `DepthMatchForcesFull.lean` /
  `DepthDeterminesPosition.lean`) would make the direction explicit.
- **`Solvable` (inductive, `FoundationMoves.lean`) vs. `isSolvable` (def, `Rules.lean`)** —
  deliberately bridged (`solvable_of_isSolution`, `exists_solution_of_solvable`) but the
  near-identical names across two files is exactly the kind of thing worth a comment or
  rename if either file is touched again.
- **`clearCfgBit` (`KingConfigSim.lean`) / `setCfgBit` (`KingReshuffle.lean`)** — the
  pile/unpile config-bit-toggle primitives are split across two files by which direction
  each file happened to need first. Someone looking for "the" toggle definitions would
  naturally check one file and miss the other.
- **`SolverRealSpec.lean`** actually contains the `def`s of `preCleanupPile`/`kingMove`
  (not just specs about them) — a reader searching for `def preCleanupPile` would first
  check `SolverSpecPreCleanupPile.lean` and not find it there.
- **`SolverSpecSolverCleanupPile.lean`** is named after the monadic *loop step*, not a bare
  solver function like its siblings — accurate but inconsistent with the "spec for X"
  pattern the other 8 split files follow.

### Namespace inconsistency

Roughly two-thirds of the `SolverSpec*`/`Solve*`/`Convert*`/`RecCheck*` cluster declares
inside `namespace SolverSpec … end SolverSpec`; the rest declares at the top level with no
namespace wrapper. No actual collisions were found, but it's inconsistent enough to be
worth normalizing (or at least documenting) in one pass:

- **Has `namespace SolverSpec`:** `SolverSpecCommon`, `SolverSpecKingMove`,
  `SolverSpecPreCleanupPile`, `SolverSpecCleanupPile`, `SolverSpecRemoveFlute`,
  `SolverSpecSolverCleanupPile`, `SolverSpecMoveAces`, `SolverSpecMove`, `SolverSpecDrain`,
  `ConvertCount`, `ConvertInv`, `ConvertMatch`, `ConvertPre`, `ConvertSim`, `ConvertSound`,
  `FoundationMax`, `KingPileMax`, `CleanupLax`, `DealMatches`, `ReachableMatch` (partially —
  only from line ~457), `SolveCorrect`, `SolveSound`, `SolverIsCorrect`, plus `MoveSim.lean`
  (only around its `movePre` definitions).
- **No namespace wrapper (top-level):** `SolverInvariant`, `SolverRealSpec`,
  `RecCheckSound`, `RecCheckSpec`, `RecCheckRuns`, `RecCheckComplete`,
  `SolverCorrectness`, and essentially everything in clusters 3, 4, 7, 8 above.
- A few files use a namespace for a different purpose entirely: `KingReshuffle`
  (`namespace KingSwap`, for the abstract graph theory only), `InitCard`
  (`namespace IsDeal`, for that one structure's projections).

### Documented cross-file coupling (informational, not action items)

- `LayoutProofs.lean` explicitly disables three `@[simp]` lemmas
  (`update_same`/`update_diff`/`update2`) defined in `CountProofs.lean`
  (`attribute [-simp] …`) because they interfere with proofs there — a real but
  intentional and already-documented cross-file interaction.
- `GetDestination.lean` documents that an old in-loop king-frontier early-return was
  deliberately removed from *both* this Lean model and `solver/solver.c` together — a
  place where model and C code were cleaned up in lockstep, not a residual bug.

### Split candidates (files doing more than one thing)

- **`SolverInvariant.lean`** (2447 lines, 74 declarations) already carries four internal
  section-banner comments and separates cleanly into: (1) the core invariant tower
  (`WellFormedLayout`…`MergedUpTo`), (2) derived arithmetic/disjointness facts, (3) the
  `usedSpace` counting/cardinality machinery (over half the file, and already self-contained
  enough to stand alone), (4) uniqueness/hash-injectivity. This is exactly the kind of split
  already successfully applied to the old 8733-line `SolverSpec.lean` — just not yet applied
  here.
- **`ConvertPre.lean`** (1085 lines, largest of the Convert family) does noticeably more
  than its "closed form of loops 1+2" name suggests: it also holds the `rfl`-twin for *all
  four* convert loops and the full per-suit walk theory (`runLen`/`cvAceVal`/`cvKingVal`). A
  split into loop-mechanics / walk-theory / closed-form-assembly would match the one-theme-
  per-file pattern the rest of the Convert family follows.
- **`KingConfigSim.lean`** (919 lines) mixes king-config simulation proper with generic
  column/flute structural facts (`free_above_boundary`, `column_above`, `isRun_take`,
  `PileMatches_drop_flute`) that arguably belong in a more general "column facts" file.

### Bottom line

**No large-scale duplication or dead subsystem was found.** The project's file-per-theme
discipline mostly holds up under scrutiny — several apparent duplicates turned out on
inspection to be deliberate, documented soundness/completeness mirror pairs. The one file
worth actually deleting is `SolverModel.lean`; the one theorem worth actually deleting is
one of the two `cvAceVal ≤ 13` copies; everything else above is either a naming
clarification or an optional "collapse N similar proofs into one" refactor, not a
correctness or dead-code problem.
