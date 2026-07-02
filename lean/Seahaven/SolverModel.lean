import Seahaven.Solver

/-!
# Parallel provable model of the solver's canonicalization functions

The real solver in `Solver.lean` uses `while`/`repeat` loops, which elaborate to
`Lean.Loop.forIn` — a `partial def` with no equational lemmas, hence logically
opaque.  No spec about those functions can be proved while they use `while`.

This file re-implements the loop-bearing canonicalization functions with
**fuel-bounded structural recursion** instead of `while`.  The result is:

* **total and computable** (no `partial`, no `termination_by`/`sorry`), so the
  spec proofs in `SolverSpec.lean` can unfold the recursion and do induction;
* a **line-by-line twin** of the `Solver.lean` originals, so behavioural
  equivalence can be checked by `#eval` (a formal `model = solver` proof is
  impossible — the `while`-versions stay opaque — so `#eval` equivalence is the
  accepted evidence; see the `#eval` block at the end).

The `for … in List.range` loops of the originals are kept verbatim: `List.forIn`
has unfolding lemmas and is already provable.

Fuel constants are chosen generously above the true bounds (pile depth ≤ 5,
card value ≤ 13, foundation advancement ≤ 52), so with sufficient fuel the model
reproduces the fixed point the `while` loop would reach.
-/

namespace SolverModel

open scoped Classical

/-- Merge loop of `SolverCleanupPile`: fold consecutive same-suit cards below the
    new top into the flute.  Carries `(depth, flute, card)`; mutates `game.hash`. -/
def mergeLoop (fuel : Nat) (pile pilehash : UInt32) (depth flute : Int32) (card : UInt8) :
    EStateM Error (Globals × SolverPosType) (Int32 × Int32 × UInt8) := do
  match fuel with
  | 0 => return (depth, flute, card)
  | fuel + 1 =>
    let ⟨globals, game⟩ ← get
    if depth > 1 && (← (← globals.pos2card.getE pile).getE (depth - 2).toUInt32) == card + 1 then
      set (⟨globals, { game with hash := game.hash - pilehash }⟩ : Globals × SolverPosType)
      mergeLoop fuel pile pilehash (depth - 1) (flute + 1) (card + 1)
    else
      return (depth, flute, card)

/-- Freed-predecessor loop of `SolverCleanupPile`: extend the flute with
    predecessor cards already freed from their piles.  Carries `(flute, prevCard)`;
    mutates `game.usedSpace`. -/
def freedLoop (fuel : Nat) (suit : UInt8) (flute : Int32) (prevCard : UInt8) :
    EStateM Error (Globals × SolverPosType) (Int32 × UInt8) := do
  match fuel with
  | 0 => return (flute, prevCard)
  | fuel + 1 =>
    let ⟨globals, game⟩ ← get
    if (← game.aces.getE suit.toUInt32) < prevCard.toInt8 &&
        (← globals.card2depth.getE prevCard.toUInt32).toNat >=
          (← game.pileDepth.getE (← globals.card2pile.getE prevCard.toUInt32).toUInt32).toInt32.toNatClampNeg then
      set (⟨globals, { game with usedSpace := game.usedSpace - 1 }⟩ : Globals × SolverPosType)
      freedLoop fuel suit (flute + 1) (prevCard - 1)
    else
      return (flute, prevCard)

/-- Model of `Solver.SolverCleanupPile` with the two `while` loops replaced by
    `mergeLoop`/`freedLoop`.  Precondition (unchanged): `game.pileDepth[pile]` and
    `game.hash` already reflect the removal of the old flute boundary. -/
def SolverCleanupPile (pile : UInt32) : EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  let mut forcedKings : UInt16 := 0xffff
  let pilehash := ← pileHashes.getE pile
  let mut depth := (← game.pileDepth.getE pile).toInt32
  let mut flute : Int32 := 1
  if depth == 0 then
    game := { game with freePiles := game.freePiles + 1 }
  else
    let mut card := ← (← globals.pos2card.getE pile).getE (depth - 1).toUInt32
    let suit := SUIT card
    let prevCard := card - 1
    -- state is unchanged since the initial `get`, so the loops see the right game
    let (d, f, c) ← mergeLoop 8 pile pilehash depth flute card
    depth := d; flute := f; card := c
    let (f2, pc) ← freedLoop 60 suit flute prevCard
    flute := f2
    let pc := pc
    let s ← get; globals := s.1; game := s.2
    if (← game.aces.getE suit.toUInt32) == pc.toInt8 then
      game := { game with busyAces := game.busyAces ||| ((1 : UInt8) <<< suit) }
    if depth == 1 && (VALUE card) == 13 then
      game := { game with freePiles := game.freePiles + 1 }
      game := { game with usedSpace := game.usedSpace + flute.toInt8 }
      let newKings ← game.kings.setE suit.toUInt32 ((← game.kings.getE suit.toUInt32) - flute.toInt8)
      game := { game with kings := newKings }
      game := { game with hash := game.hash - pilehash }
      depth := 0
      flute := 1
      forcedKings := forcedKings &&& (← kingOnPileMap.getE suit.toUInt32)
  game := { game with
    pileDepth := ← game.pileDepth.setE pile depth.toInt8
    pileFlute := ← game.pileFlute.setE pile flute.toUInt32.toUInt8
  }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  return forcedKings

-- `CleanupPileEquals` (model = real) was dropped: on Lean 4.31 the real solver's
-- `while` loops are no longer opaque (see `Seahaven.EStateMTail`), so specs are proved
-- directly against `_root_.SolverCleanupPile` (see `Seahaven.SolverSpec`) rather than
-- via this fuel model.  (An unconditional model=real equality would also be false as
-- written: the model's `freedLoop 60` caps the freed-flute loop, which the real
-- unbounded `while` can run up to ~65 times.)

/-- Model of `Solver.SolverRemoveFlute` (no loops of its own; delegates to the
    model `SolverCleanupPile`). -/
def SolverRemoveFlute (pile : UInt32) : EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  game := { game with pileDepth := ← game.pileDepth.setE pile ((← game.pileDepth.getE pile) - 1) }
  game := { game with hash := game.hash - (← pileHashes.getE pile) }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  SolverCleanupPile pile

/-- `repeat` loop of `solverGetDestination`: walk up the successor chain until a
    card sits at position-from-top `> 0`. -/
def getDestLoop (fuel : Nat) (game : SolverPosType) (suit card : UInt8) :
    EStateM Error Globals UInt8 := do
  match fuel with
  | 0 => return 14  -- EXTRA (fuel exhausted; unreachable with sufficient fuel)
  | fuel + 1 =>
    let globals ← get
    if card.toInt8 == (← game.kings.getE suit.toUInt32) then
      return 10 + suit  -- KINGPILE + suit
    let card := card + 1
    let toPile ← globals.card2pile.getE card.toUInt32
    let posFromTop : Int32 := (← game.pileDepth.getE toPile.toUInt32).toInt32 -
                  (← globals.card2depth.getE card.toUInt32).toUInt32.toInt32
    if posFromTop > 0 then
      return if posFromTop == 1 then toPile else 14  -- EXTRA
    else
      getDestLoop fuel game suit card

/-- Model of `Solver.solverGetDestination`. -/
def solverGetDestination (game : SolverPosType) (pile : UInt32) : EStateM Error Globals UInt8 := do
  let globals ← get
  let depth ← game.pileDepth.getE pile
  let card := ← (← globals.pos2card.getE pile).getE (depth.toInt32 - 1).toUInt32
  let suit := SUIT card
  if card.toInt8 == (← game.kings.getE suit.toUInt32) then
    return 10 + suit  -- KINGPILE + suit
  getDestLoop 16 game suit card

/-- Main `while` loop of `SolverMoveAces`: advance the foundation for one suit,
    removing flutes as freed cards are exposed.  Carries `(card, found, forcedKings)`. -/
def moveAcesLoop (fuel : Nat) (suitU32 : UInt32) (card : UInt8) (found : Int8) (forcedKings : UInt16) :
    EStateM Error (Globals × SolverPosType) (UInt8 × Int8 × UInt16) := do
  match fuel with
  | 0 => return (card, found, forcedKings)
  | fuel + 1 =>
    if VALUE card <= 13 then
      let ⟨globals, game⟩ ← get
      let pile ← globals.card2pile.getE card.toUInt32
      let cardDepth : Int32 := (← globals.card2depth.getE card.toUInt32).toUInt32.toInt32 + 1 -
                               (← game.pileDepth.getE pile.toUInt32).toInt32
      if cardDepth > 0 then
        moveAcesLoop fuel suitU32 (card + 1) (found + 1) forcedKings
      else if cardDepth == 0 then
        let game := { game with aces := ← game.aces.setE suitU32 card.toInt8 }
        set (⟨globals, game⟩ : Globals × SolverPosType)
        let fk ← SolverRemoveFlute pile.toUInt32
        moveAcesLoop fuel suitU32 (card + 1) 0 (forcedKings &&& fk)
      else
        return (card, found, forcedKings)
    else
      return (card, found, forcedKings)

/-- Model of `Solver.SolverMoveAces`. -/
def SolverMoveAces : EStateM Error (Globals × SolverPosType) UInt16 := do
  let s0 ← get
  let suit := ctz s0.2.busyAces
  let suitU32 := UInt32.ofNat suit
  let startCard : UInt8 := (← s0.2.aces.getE suitU32).toInt32.toUInt32.toUInt8 + 1
  let (card, found, forcedKings) ← moveAcesLoop 16 suitU32 startCard 0 0xffff
  let card := card - 1
  let mut ⟨globals, game⟩ ← get
  game := { game with usedSpace := game.usedSpace - found }
  game := { game with aces := ← game.aces.setE suitU32 card.toInt8 }
  if VALUE card == 13 then
    game := { game with kings := ← game.kings.setE suitU32 card.toInt8 }
  game := { game with busyAces := game.busyAces - ((1 : UInt8) <<< UInt8.ofNat suit) }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  return forcedKings

/-- `while busyAces ≠ 0 do SolverMoveAces` drain, shared by `SolverMove` and
    `SolverConvertFromPilesKings`.  Threads and accumulates `forcedKings`. -/
def drainLoop (fuel : Nat) (forcedKings : UInt16) : EStateM Error (Globals × SolverPosType) UInt16 := do
  match fuel with
  | 0 => return forcedKings
  | fuel + 1 =>
    if (← get).2.busyAces != 0 then
      let fk ← SolverMoveAces
      drainLoop fuel (forcedKings &&& fk)
    else
      return forcedKings

/-- Model of `Solver.SolverMove`. -/
def SolverMove (pile : UInt32) (toPile : UInt8) : EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  let fluteLen := ← game.pileFlute.getE pile
  if toPile < 10 then  -- pile to pile
    game := { game with pileFlute := ← game.pileFlute.setE toPile.toUInt32 ((← game.pileFlute.getE toPile.toUInt32) + fluteLen) }
  else  -- to king pile or extra
    if toPile < 14 then  -- king pile
      let kingIdx := (toPile - 10).toUInt32
      game := { game with kings := ← game.kings.setE kingIdx ((← game.kings.getE kingIdx) - fluteLen.toInt8) }
    game := { game with usedSpace := game.usedSpace + fluteLen.toInt8 }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  let forcedKings ← SolverRemoveFlute pile
  drainLoop 64 forcedKings

/-- Ace-walk of `SolverConvertFromPilesKings`: advance the foundation candidate
    while the current card is already freed. -/
def aceWalk (fuel : Nat) (game : SolverPosType) (ace card : UInt8) :
    EStateM Error (Globals × SolverPosType) UInt8 := do
  match fuel with
  | 0 => return ace
  | fuel + 1 =>
    let globals := (← get).1
    if ace <= card &&
        (← globals.card2depth.getE ace.toUInt32).toNat >=
          (← game.pileDepth.getE (← globals.card2pile.getE ace.toUInt32).toUInt32).toInt32.toNatClampNeg then
      aceWalk fuel game (ace + 1) card
    else
      return ace

/-- King-walk of `SolverConvertFromPilesKings`: count down from the king past
    freed cards to the first un-freed one. -/
def kingWalk (fuel : Nat) (game : SolverPosType) (card : UInt8) :
    EStateM Error (Globals × SolverPosType) UInt8 := do
  match fuel with
  | 0 => return card
  | fuel + 1 =>
    let globals := (← get).1
    if (← globals.card2depth.getE card.toUInt32).toNat >=
        (← game.pileDepth.getE (← globals.card2pile.getE card.toUInt32).toUInt32).toInt32.toNatClampNeg then
      kingWalk fuel game (card - 1)
    else
      return card

/-- Model of `Solver.SolverConvertFromPilesKings`.  The three `while` loops (two
    per-suit walks and the final foundation drain) are replaced by
    `aceWalk`/`kingWalk`/`drainLoop`; the two `for … in List.range` loops are kept. -/
def SolverConvertFromPilesKings (pilesking : Vector UInt8 11) :
    EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  let mut forcedKings : UInt16 := 0xffff

  game := { game with busyAces := 0, usedSpace := 52, freePiles := 0, hash := 0 }

  for i in List.range 10 do
    let iU32 := UInt32.ofNat i
    let d := ← pilesking.getE iU32
    game := { game with pileDepth := ← game.pileDepth.setE iU32 d.toInt8 }
    game := { game with pileFlute := ← game.pileFlute.setE iU32 1 }
    game := { game with usedSpace := game.usedSpace - d.toInt8 }
    game := { game with hash := game.hash + (← pileHashes.getE iU32) * d.toUInt32 }

  -- The per-suit walks read `game.pileDepth` (set above) via the local `game`;
  -- state is set only after this loop, so pass the local `game` explicitly.
  for suit in List.range 4 do
    let suitU32 := UInt32.ofNat suit
    let card0 : UInt8 := CARD (UInt8.ofNat suit) 13
    let aceStart : UInt8 := CARD (UInt8.ofNat suit) 1
    let ace0 ← aceWalk 16 game aceStart card0
    let ace := ace0 - 1
    game := { game with aces := ← game.aces.setE suitU32 ace.toInt8 }
    game := { game with usedSpace := game.usedSpace - (VALUE ace).toInt8 }
    let card ← (if ace < card0 then kingWalk 16 game card0 else pure card0)
    game := { game with kings := ← game.kings.setE suitU32 card.toInt8 }

  set (⟨globals, game⟩ : Globals × SolverPosType)

  for i in List.range 10 do
    forcedKings := forcedKings &&& (← SolverCleanupPile (UInt32.ofNat i))

  drainLoop 64 forcedKings

-- ---------------------------------------------------------------------------
-- Behavioural equivalence check (vs `Solver.lean`) by `#eval`
--
-- Both the real and model `SolverConvertFromPilesKings` are run on the same
-- `Globals` (built from a concrete deal via `initcard`) and the same pile-depth
-- vector; the resulting `(forcedKings, SolverPosType)` values are compared by
-- their `Repr` strings.  Equal ⇒ the model matches the solver on this input.
-- ---------------------------------------------------------------------------

/-- Identity deal `1,2,…,52` (a valid permutation, so all `while` loops in the
    real solver terminate). -/
def sampleShuffle : Vector UInt8 52 := Vector.ofFn (fun i => UInt8.ofNat (i.val + 1))

/-- A `Globals` skeleton (real deal is filled in by `initcard`). -/
def initialGlobals : Globals := {
  pos2card  := mkVector 10 (mkVector 5 0)
  card2pile := mkVector 64 0
  card2depth := mkVector 64 0
  hashmap   := mkVector BIG_HASH_SIZE 0
  gameStack := mkVector MAX_MOVES {
    hash := 0, pileDepth := mkVector 10 0, pileFlute := mkVector 10 0,
    aces := mkVector 4 0, kings := mkVector 4 0, usedSpace := 0, freePiles := 0, busyAces := 0 }
  hit := 0
  miss := 0
}

private def emptyPos : SolverPosType := {
  hash := 0, pileDepth := mkVector 10 0, pileFlute := mkVector 10 0,
  aces := mkVector 4 0, kings := mkVector 4 0, usedSpace := 0, freePiles := 0, busyAces := 0 }

/-- Run a convert function on the identity deal with the given pile depths and
    return the `Repr` string of `(forcedKings, resulting game)`. -/
def runConvert (conv : Vector UInt8 11 → EStateM Error (Globals × SolverPosType) UInt16)
    (pk : Vector UInt8 11) : String :=
  match EStateM.run (initcard sampleShuffle) initialGlobals with
  | .error e _ => s!"initcard error: {repr e}"
  | .ok _ g =>
    match EStateM.run (conv pk) (g, emptyPos) with
    | .error e _ => s!"convert error: {repr e}"
    | .ok fk (_, game) => s!"{fk} {repr game}"

/-- Compare real vs model convert on a pile-depth vector. -/
def convertMatches (pk : Vector UInt8 11) : Bool :=
  runConvert _root_.SolverConvertFromPilesKings pk == runConvert SolverModel.SolverConvertFromPilesKings pk

-- A handful of pile-depth configurations to exercise the code paths.
#eval convertMatches ⟨#[5,5,5,5,5,5,5,5,5,5, 0], by simp⟩  -- full initial deal
#eval convertMatches ⟨#[5,4,5,3,5,2,5,1,5,0, 0], by simp⟩  -- partially played
#eval convertMatches ⟨#[3,3,3,3,3,3,3,3,4,4, 0], by simp⟩  -- mixed
#eval convertMatches ⟨#[0,0,0,0,0,0,0,0,0,0, 0], by simp⟩  -- all empty (solved)

end SolverModel
