inductive Error
| ArrayOutOfBounds
| InvalidPointer
| Assertion
deriving Repr

def Array.getE {α m} [Monad m] [MonadExcept Error m] (a : Array α) (i : UInt32) : m α := do
  match a[i.toNat]? with
  | some v => return v
  | none   => throw Error.ArrayOutOfBounds

def Array.setE {α m} [Monad m] [MonadExcept Error m] (a : Array α) (i : UInt32) (v : α) : m (Array α) := do
  if h : i.toNat < a.size then
    return a.set i.toNat v h
  else
    throw Error.ArrayOutOfBounds

def Vector.getE {α m} [Monad m] [MonadExcept Error m]{len : Nat} (a : Vector α len) (i : UInt32) : m α := do
  match a[i.toNat]? with
  | some v => return v
  | none   => throw Error.ArrayOutOfBounds

def Vector.setE {α m} [Monad m] [MonadExcept Error m] {len : Nat} (a : Vector α len) (i : UInt32) (v : α) : m (Vector α len) := do
  if h : i.toNat < len then
    return a.set i.toNat v h
  else
    throw Error.ArrayOutOfBounds

def assert  {m} [Monad m] [MonadExcept Error m] (b : Bool) : (m Unit) := do
  if ¬ b then
    throw Error.Assertion

def mkVector {α} (n : Nat) (x : α) : Vector α n :=
  ⟨Array.mk (List.replicate n x), by simp⟩

notation a "[" i "]!" => Array.getE a i
notation a "[" i "]!←" v => Array.setE a i v
notation a "[" i "]!" => Vector.getE a i
notation a "[" i "]!←" v => Vector.setE a i v


abbrev ACE := 1
abbrev KING := 13

def CARD (s: UInt8) (v:UInt8) : UInt8 := ((s <<< 4) + v)
def VALUE (c: UInt8) : UInt8 := c &&& 0xf
def SUIT (c: UInt8) : UInt8 := c >>> 4

abbrev KINGPILE := 10
abbrev EXTRA := 14
abbrev FREESLOT := 0xff
abbrev MAX_MOVES := 50

abbrev SUCCESS := 0
abbrev ABORTED := 1
abbrev NOMOVE := 2

abbrev BIG_HASH_SIZE := (1024*1024)

abbrev CardType := UInt8



structure SolverPosType where
  hash : UInt32
  pileDepth : Vector Int8 10
  pileFlute : Vector UInt8 10
  aces : Vector Int8 4
  kings : Vector Int8 4
  usedSpace : Int8
  freePiles : Int8
  busyAces : UInt8
deriving Repr

structure Globals where
  pos2card : Vector (Vector CardType 5) 10
  card2pile : Vector UInt8 64
  card2depth : Vector UInt8 64
  hashmap : Vector UInt16 BIG_HASH_SIZE
  gameStack : Vector SolverPosType MAX_MOVES
  hit : UInt32
  miss : UInt32
deriving Repr

def pileHashes : Vector UInt32 10 := ⟨#[
  1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616, 10077696
], by simp⟩

def bits2grlex : Vector UInt8 16 := ⟨#[
  0, 1, 2, 5, 3, 6, 7, 11,
  4, 8, 9, 12, 10, 13, 14, 15
], by simp⟩

def grlex2bits : Vector UInt8 16 := ⟨#[
    0, 1, 2, 4, 8,
    3, 5, 6, 9, 10, 12,
    7, 11, 13, 14, 15
], by simp⟩

def SolverInit : EStateM Error Globals Unit := do
  modify fun globals => { globals with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) }

def ctz (x : UInt8) : Nat :=
  let rec go (n : Nat) (v : Nat) :=
    if v % 2 == 1 then n
    else if v == 0 then 8   -- convention: ctz(0) = word size
    else go (n + 1) (v / 2)
  termination_by v
  decreasing_by simp at *; omega
  go 0 x.toNat

structure ClosureInfo where
  shiftValue : UInt8
  numBits : UInt8
  offset : UInt8
deriving Repr

def closureInfos : Vector ClosureInfo 11 := ⟨ #[
    { shiftValue := 15, numBits :=  1, offset := 98 },   -- freePiles = 0
    { shiftValue := 11, numBits :=  4, offset :=  0 },   -- freePiles = 1
    { shiftValue :=  5, numBits :=  6, offset := 16 },   -- freePiles = 2
    { shiftValue :=  1, numBits :=  4, offset := 80 },   -- freePiles = 3
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 4
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 5
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 6
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 7
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 8
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 9
    { shiftValue :=  0, numBits :=  1, offset := 96 },   -- freePiles = 10
], by simp⟩

def componentTable : Vector UInt8 100 := ⟨ #[
    -- table for level 2
    0x00, 0x07, 0x19, 0x1f, 0x2a, 0x2f, 0x3b, 0x3f,
    0x34, 0x37, 0x3d, 0x3f, 0x3e, 0x3f, 0x3f, 0x3f,

    -- table for level 3; also used as dummy table
    0x0, 0x3, 0x5, 0x7, 0x6, 0x7, 0x7, 0x7,
    0x9, 0xb, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xa, 0xb, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xb, 0xb, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xc, 0xf, 0xd, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xd, 0xf, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xe, 0xf, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,

    -- table for level 4
    0x0, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
    0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,

    -- table for level 5
    0x0, 0x0,
    -- table for level 1
    0x00, 0x0f
], by simp⟩

def subsetTable : Vector UInt16 100 := ⟨ #[
    -- table for level 2
    0x0000, 0x8800, 0x9000, 0x9800, 0xa000, 0xa800, 0xb000, 0xb800,
    0xc000, 0xc800, 0xd000, 0xd800, 0xe000, 0xe800, 0xf000, 0xf800,
    -- table for level 3
    0x0000, 0x9820, 0xa840, 0xb860, 0xc880, 0xd8a0, 0xe8c0, 0xf8e0,
    0xb100, 0xb920, 0xb940, 0xb960, 0xf980, 0xf9a0, 0xf9c0, 0xf9e0,
    0xd200, 0xda20, 0xfa40, 0xfa60, 0xda80, 0xdaa0, 0xfac0, 0xfae0,
    0xf300, 0xfb20, 0xfb40, 0xfb60, 0xfb80, 0xfba0, 0xfbc0, 0xfbe0,
    0xe400, 0xfc20, 0xec40, 0xfc60, 0xec80, 0xfca0, 0xecc0, 0xfce0,
    0xf500, 0xfd20, 0xfd40, 0xfd60, 0xfd80, 0xfda0, 0xfdc0, 0xfde0,
    0xf600, 0xfe20, 0xfe40, 0xfe60, 0xfe80, 0xfea0, 0xfec0, 0xfee0,
    0xf700, 0xff20, 0xff40, 0xff60, 0xff80, 0xffa0, 0xffc0, 0xffe0,
    -- table for level 4
    0x0000, 0xb962, 0xdaa4, 0xfbe6, 0xecc8, 0xfdea, 0xfeec, 0xffee,
    0xf710, 0xff72, 0xffb4, 0xfff6, 0xffd8, 0xfffa, 0xfffc, 0xfffe,
    -- table for level 5
    0x0000, 0xffff,
    -- table for level 1
    0x0000, 0x8000
], by simp⟩

def kingOnPileMap : Vector UInt16 4 := ⟨#[
    0x469d, 0x255b, 0x1337, 0x08ef
], by simp⟩

structure KingInfo where
  possibleKings : Vector UInt16 6

def getSlot(key : UInt32) : EStateM Error Globals UInt8 := do
  let g ← get
  let high := (key / (UInt32.ofNat BIG_HASH_SIZE)) + 1
  let entry := ((high * (UInt32.ofNat 0x10001)) ^^^ key) &&& (UInt32.ofNat (BIG_HASH_SIZE - 1))
  if (((←g.hashmap[entry]!).toUInt32 ^^^ high) &&& (0x1ff)) != 0 then
    return (UInt8.ofNat FREESLOT)
  else
    return ((←g.hashmap[entry]!) >>> 9).toUInt8

def setSlot(key : UInt32) (value: UInt16) : EStateM Error Globals Unit := do
  let g ← get
  let high := (key / (UInt32.ofNat BIG_HASH_SIZE)) + 1
  let entry := ((high * (UInt32.ofNat 0x10001)) ^^^ key) &&& (UInt32.ofNat (BIG_HASH_SIZE - 1))
  set { g with hashmap := ←g.hashmap[entry]!← ((value <<< 9) ||| (high.toUInt16 &&& 0x1ff)) }

-- Returns forcedKings: bitmask of king configs forced by uncovering a lone king.
-- Precondition: game.pileDepth[pile] and game.hash already reflect the removal
-- of the old flute boundary (decremented by the caller).
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
    let mut prevCard := card - 1
    -- Merge consecutive same-suit cards below the new top into the flute.
    while depth > 1 && (← (← globals.pos2card.getE pile).getE (depth - 2).toUInt32) == card + 1 do
      depth := depth - 1
      game := { game with hash := game.hash - pilehash }
      flute := flute + 1
      card := card + 1
    -- Extend flute with predecessor cards already freed from their piles.
    while (← game.aces.getE suit.toUInt32) < prevCard.toInt8 &&
          (← globals.card2depth.getE prevCard.toUInt32).toNat >=
            (← game.pileDepth.getE (← globals.card2pile.getE prevCard.toUInt32).toUInt32).toInt32.toNatClampNeg do
      flute := flute + 1
      prevCard := prevCard - 1
      game := { game with usedSpace := game.usedSpace - 1 }
    -- If predecessor is at foundation top, mark suit for re-evaluation.
    if (← game.aces.getE suit.toUInt32) == prevCard.toInt8 then
      game := { game with busyAces := game.busyAces ||| ((1 : UInt8) <<< suit) }
    -- Lone king: vacate pile, track king sequence in usedSpace/kings.
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

def SolverRemoveFlute (pile : UInt32) : EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  game := { game with pileDepth := ← game.pileDepth.setE pile ((← game.pileDepth.getE pile) - 1) }
  game := { game with hash := game.hash - (← pileHashes.getE pile) }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  SolverCleanupPile pile

def computeKingSpaces (shiftValue : UInt8) (numBits : UInt8) (game : SolverPosType) : EStateM Error Globals KingInfo := do
  let mut kingInfo : KingInfo := { possibleKings := mkVector 6 0 }
  for i in List.range numBits.toNat do
    let mut usedSpace := game.usedSpace.toInt32
    let kingBitmap := ← grlex2bits.getE (shiftValue + UInt8.ofNat i).toUInt32
    for suit in List.range 4 do
      if kingBitmap &&& ((1 : UInt8) <<< UInt8.ofNat suit) == 0 then
        usedSpace := usedSpace - Int32.ofNat (13 - (VALUE (← game.kings.getE (UInt32.ofNat suit)).toUInt8).toNat)
    let bit : UInt8 := (1 : UInt8) <<< UInt8.ofNat i
    while usedSpace <= 4 do
      let idx := UInt32.ofNat (4 - usedSpace.toNatClampNeg)
      kingInfo := { kingInfo with possibleKings := ← kingInfo.possibleKings.setE idx ((← kingInfo.possibleKings.getE idx) ||| bit.toUInt16) }
      usedSpace := usedSpace + 1
  return kingInfo

def solverGetDestination (game : SolverPosType) (pile : UInt32) : EStateM Error Globals UInt8 := do
  let globals ← get
  let depth ← game.pileDepth.getE pile
  let mut card := ← (← globals.pos2card.getE pile).getE (depth.toInt32 - 1).toUInt32
  let suit := SUIT card
  if card.toInt8 == (← game.kings.getE suit.toUInt32) then
    return 10 + suit  -- KINGPILE + suit
  let mut toPile : UInt8 := 0
  let mut posFromTop : Int32 := 0
  repeat
    if card.toInt8 == (← game.kings.getE suit.toUInt32) then
      return 10 + suit  -- KINGPILE + suit
    card := card + 1
    toPile := ← globals.card2pile.getE card.toUInt32
    posFromTop := (← game.pileDepth.getE toPile.toUInt32).toInt32 -
                  (← globals.card2depth.getE card.toUInt32).toUInt32.toInt32
    if posFromTop > 0 then break
  return if posFromTop == 1 then toPile else 14  -- EXTRA

def SolverMoveAces : EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut forcedKings : UInt16 := 0xffff
  let mut ⟨globals, game⟩ ← get
  let suit := ctz game.busyAces
  let suitU32 := UInt32.ofNat suit
  let mut card : UInt8 := (← game.aces.getE suitU32).toInt32.toUInt32.toUInt8 + 1
  let mut found : Int8 := 0
  while VALUE card <= 13 do
    let pile := ← globals.card2pile.getE card.toUInt32
    let cardDepth : Int32 := (← globals.card2depth.getE card.toUInt32).toUInt32.toInt32 + 1 -
                             (← game.pileDepth.getE pile.toUInt32).toInt32
    if cardDepth > 0 then
      found := found + 1
      card := card + 1
    else if cardDepth == 0 then
      game := { game with aces := ← game.aces.setE suitU32 card.toInt8 }
      set (⟨globals, game⟩ : Globals × SolverPosType)
      forcedKings := forcedKings &&& (← SolverRemoveFlute pile.toUInt32)
      let s ← get; globals := s.1; game := s.2
      found := 0
      card := card + 1
    else
      break
  card := card - 1
  game := { game with usedSpace := game.usedSpace - found }
  game := { game with aces := ← game.aces.setE suitU32 card.toInt8 }
  if VALUE card == 13 then
    game := { game with kings := ← game.kings.setE suitU32 card.toInt8 }
  game := { game with busyAces := game.busyAces - ((1 : UInt8) <<< UInt8.ofNat suit) }
  set (⟨globals, game⟩ : Globals × SolverPosType)
  return forcedKings

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
  let mut forcedKings ← SolverRemoveFlute pile
  while (← get).2.busyAces != 0 do
    forcedKings := forcedKings &&& (← SolverMoveAces)
  return forcedKings

def solverGetMovable (kingInfo : KingInfo) (shiftValue : UInt8) (fluteLen : UInt8) (toPile : UInt8) :
    EStateM Error Globals UInt16 := do
  if fluteLen > 5 then
    return 0
  if toPile < 10 then  -- pile to pile
    return ← kingInfo.possibleKings.getE (fluteLen - 1).toUInt32
  else if toPile < 14 then  -- to king pile
    let kingOnPile := (← kingOnPileMap.getE (toPile - 10).toUInt32) >>> shiftValue.toUInt16
    return (← kingInfo.possibleKings.getE fluteLen.toUInt32) |||
           ((← kingInfo.possibleKings.getE (fluteLen - 1).toUInt32) &&& kingOnPile)
  else  -- to extra
    return ← kingInfo.possibleKings.getE fluteLen.toUInt32

def computeComponentKingBits (game : SolverPosType) : EStateM Error Globals UInt8 := do
  let emptyPiles := game.freePiles.toInt32
  if emptyPiles >= 1 && emptyPiles <= 3 then
    let info := ← closureInfos.getE (emptyPiles - 1).toUInt32
    let mut result : UInt16 := 0
    for i in List.range info.numBits.toNat do
      let mut usedSpace := game.usedSpace.toInt32
      let kingBitmap := ← grlex2bits.getE (info.shiftValue + UInt8.ofNat i).toUInt32
      for suit in List.range 4 do
        if kingBitmap &&& ((1 : UInt8) <<< UInt8.ofNat suit) == 0 then
          usedSpace := usedSpace - Int32.ofNat (13 - (VALUE (← game.kings.getE (UInt32.ofNat suit)).toUInt8).toNat)
      if usedSpace <= 4 then
        result := result ||| ((1 : UInt16) <<< UInt16.ofNat i)
    return (← componentTable.getE (info.offset.toUInt32 + result.toUInt32))
  else
    return 0

partial def solverRecCheckSolvable (game : SolverPosType) : EStateM Error Globals UInt16 := do
  if game.hash == 0 then return 1
  let closureInfo ← closureInfos.getE game.freePiles.toInt32.toUInt32
  let cachedValue ← getSlot game.hash
  if cachedValue != 0xff then
    return cachedValue.toUInt16
  let kingInfo ← computeKingSpaces closureInfo.shiftValue closureInfo.numBits game
  let allkings ← kingInfo.possibleKings.getE 0
  let component := (← computeComponentKingBits game).toUInt16
  let mut solvable : UInt16 := 0
  for pile in List.range 10 do
    let pileU32 := UInt32.ofNat pile
    if (← game.pileDepth.getE pileU32) == 0 then continue
    let fluteLen ← game.pileFlute.getE pileU32
    let toPile ← solverGetDestination game pileU32
    let movable ← solverGetMovable kingInfo closureInfo.shiftValue fluteLen toPile
    if movable &&& ~~~solvable != 0 then
      let globals ← get
      match EStateM.run (SolverMove pileU32 toPile) (globals, game) with
      | .ok forcedKings ⟨newGlobals, childGame⟩ =>
        set newGlobals
        let nextClosureInfo ← closureInfos.getE childGame.freePiles.toInt32.toUInt32
        let childSolvable ← solverRecCheckSolvable childGame
        let childSolvable' := childSolvable &&& (forcedKings >>> nextClosureInfo.shiftValue.toUInt16)
        let movable' := movable &&&
          ((← subsetTable.getE (nextClosureInfo.offset.toUInt32 + childSolvable'.toUInt32))
            >>> closureInfo.shiftValue.toUInt16)
        let movable'' := if movable' &&& component != 0 then movable' ||| component else movable'
        solvable := solvable ||| movable''
        if solvable == allkings then break
      | .error e _ => throw e
  setSlot game.hash solvable
  return solvable

def SolverConvertFromPilesKings (pilesking : Vector UInt8 11) :
    EStateM Error (Globals × SolverPosType) UInt16 := do
  let mut ⟨globals, game⟩ ← get
  let mut forcedKings : UInt16 := 0xffff

  game := { game with busyAces := 0, usedSpace := 52, freePiles := 0, hash := 0 }

  -- Set pile depths, pileFlute, usedSpace, hash from the input depths.
  for i in List.range 10 do
    let iU32 := UInt32.ofNat i
    let d := ← pilesking.getE iU32
    game := { game with pileDepth := ← game.pileDepth.setE iU32 d.toInt8 }
    game := { game with pileFlute := ← game.pileFlute.setE iU32 1 }
    game := { game with usedSpace := game.usedSpace - d.toInt8 }
    game := { game with hash := game.hash + (← pileHashes.getE iU32) * d.toUInt32 }

  -- Compute aces[] (highest foundation card per suit) and kings[] (first
  -- un-freed card counting down from king) for each suit.
  for suit in List.range 4 do
    let suitU32 := UInt32.ofNat suit
    let mut card : UInt8 := CARD (UInt8.ofNat suit) 13
    let mut ace  : UInt8 := CARD (UInt8.ofNat suit) 1
    while ace <= card &&
          (← globals.card2depth.getE ace.toUInt32).toNat >=
            (← game.pileDepth.getE (← globals.card2pile.getE ace.toUInt32).toUInt32).toInt32.toNatClampNeg do
      ace := ace + 1
    ace := ace - 1
    game := { game with aces := ← game.aces.setE suitU32 ace.toInt8 }
    game := { game with usedSpace := game.usedSpace - (VALUE ace).toInt8 }
    if ace < card then
      while (← globals.card2depth.getE card.toUInt32).toNat >=
              (← game.pileDepth.getE (← globals.card2pile.getE card.toUInt32).toUInt32).toInt32.toNatClampNeg do
        card := card - 1
    game := { game with kings := ← game.kings.setE suitU32 card.toInt8 }

  set (⟨globals, game⟩ : Globals × SolverPosType)

  -- Per-pile cleanup: merge flutes, absorb freed predecessors, handle lone kings.
  for i in List.range 10 do
    forcedKings := forcedKings &&& (← SolverCleanupPile (UInt32.ofNat i))

  -- Auto-advance any suits whose flute can be moved directly to foundation.
  while (← get).2.busyAces != 0 do
    forcedKings := forcedKings &&& (← SolverMoveAces)

  return forcedKings

-- A default SolverPosType used as a throwaway initial state.
-- cardshuffle[i] is a card number 1..52 (1=Ace of suit 0, 13=King of suit 0,
-- 14=Ace of suit 1, ...).  Cards are dealt column-by-column into 10 piles of 5.
-- The last two cards (i=50,51) go to extra and are not placed in pos2card.
def initcard (cardshuffle : Vector UInt8 52) : EStateM Error Globals Unit := do
  SolverInit
  for i in List.range 52 do
    let ci ← cardshuffle.getE (UInt32.ofNat i)
    let suit : UInt8 := (ci - 1) / 13
    let card : UInt8 := CARD suit (ci - 13 * suit)
    let mut g ← get
    g := { g with card2pile  := ← g.card2pile.setE  card.toUInt32 (UInt8.ofNat (i % 10)) }
    g := { g with card2depth := ← g.card2depth.setE card.toUInt32 (UInt8.ofNat (i / 10)) }
    if i < 50 then
      let innerVec ← g.pos2card.getE (UInt32.ofNat (i % 10))
      let innerVec ← innerVec.setE (UInt32.ofNat (i / 10)) card
      g := { g with pos2card := ← g.pos2card.setE (UInt32.ofNat (i % 10)) innerVec }
    set g

private def emptySolverPosType : SolverPosType := {
  hash      := 0
  pileDepth := mkVector 10 0
  pileFlute := mkVector 10 0
  aces      := mkVector 4 0
  kings     := mkVector 4 0
  usedSpace := 0
  freePiles := 0
  busyAces  := 0
}

-- stacks[0..9]: current pile depths.  stacks[10]: king bitmask (bit k SET
-- means suit k's king is still in a regular pile; XOR 0xf converts to internal
-- convention).  Returns SUCCESS (0) if solvable, NOMOVE (2) if not.
def solve (stacks : Vector UInt8 11) : EStateM Error Globals UInt8 := do
  let globals ← get
  -- Run SolverConvertFromPilesKings in the paired state monad.
  match EStateM.run (SolverConvertFromPilesKings stacks) (globals, emptySolverPosType) with
  | .error e _ => throw e
  | .ok forcedKings (globals', game) =>
    set globals'
    if game.hash == 0 then
      return 0  -- SUCCESS: game already solved
    let kingbit ← bits2grlex.getE ((← stacks.getE 10) ^^^ 0xf).toUInt32
    let ci ← closureInfos.getE game.freePiles.toInt32.toUInt32
    let solvable := (← solverRecCheckSolvable game) &&&
                    (forcedKings >>> ci.shiftValue.toUInt16)
    let tableEntry ← subsetTable.getE (ci.offset.toUInt32 + solvable.toUInt32)
    if tableEntry &&& ((1 : UInt16) <<< kingbit.toUInt16) != 0 then
      return 0  -- SUCCESS
    else
      return 2  -- NOMOVE
