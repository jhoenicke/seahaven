inductive Suit
  | clubs | diamonds | hearts | spades
  deriving DecidableEq, Repr, BEq, Hashable

inductive Rank
  | ace | two | three | four | five | six | seven
  | eight | nine | ten | jack | queen | king
  deriving DecidableEq, Repr, BEq, Hashable

def allSuits := [ Suit.clubs, Suit.diamonds, Suit.hearts, Suit.spades ]

def rankToNat (r: Rank) : Nat :=
  match r with
  | Rank.ace => 1
  | Rank.two => 2
  | Rank.three => 3
  | Rank.four => 4
  | Rank.five => 5
  | Rank.six => 6
  | Rank.seven => 7
  | Rank.eight => 8
  | Rank.nine => 9
  | Rank.ten => 10
  | Rank.jack => 11
  | Rank.queen => 12
  | Rank.king => 13

def natToRank (n : Nat) : Option Rank :=
  match n with
  | 1 => Rank.ace
  | 2 => Rank.two
  | 3 => Rank.three
  | 4 => Rank.four
  | 5 => Rank.five
  | 6 => Rank.six
  | 7 => Rank.seven
  | 8 => Rank.eight
  | 9 => Rank.nine
  | 10 => Rank.ten
  | 11 => Rank.jack
  | 12 => Rank.queen
  | 13 => Rank.king
  | _ => none

def optRankToNat (r: Option Rank) : Nat :=
  match r with
  | none => 0
  | some r' => rankToNat r'

def nextRank (r: Option Rank) : Option Rank :=
  natToRank (optRankToNat r + 1)

theorem rankToNatToRank (r: Option Rank) : natToRank (optRankToNat r) = r := by
  unfold optRankToNat
  unfold rankToNat
  unfold natToRank
  cases r with
  | none => simp
  | some r' => cases r' <;> simp

theorem natToRankToNat (n: Nat) (r : Rank) :
  natToRank n = some r -> rankToNat r = n := by
  unfold natToRank
  unfold rankToNat
  intro h
  split at h <;> simp at h <;> simp[h.symm]

theorem nextRankNat (r: Option Rank) (r' : Rank) :
  nextRank r = some r' -> rankToNat r' = optRankToNat r + 1 := by
  unfold nextRank
  intro h1
  have h2 := natToRankToNat (optRankToNat r + 1) r' h1
  exact h2

theorem rankInj (r r': Rank) (h : rankToNat r = rankToNat r') : r = r' := by
  unfold rankToNat at h
  cases r <;> cases r' <;> simp at h <;> simp

@[ext]
structure Card where
  suit : Suit
  rank : Rank
  deriving DecidableEq, Repr, BEq, Hashable

def nextCard (c : Card) : Option Card :=
  match nextRank c.rank with
  | none => none
  | some r => some { c with rank := r }

abbrev Column := List Card

structure State where
  cells       : Fin 4 → Option Card
  foundations : Suit → Option Rank     -- highest completed rank
  tableau     : Fin 10 → Column

structure StateView where
  cells : List (Option Card)
  foundations : List (Option Rank)
  tableau : List (Column)
  deriving Repr

def State.toView (s : State) : StateView :=
  { cells := [s.cells 0, s.cells 1, s.cells 2, s.cells 3]
  , foundations :=
      [ s.foundations Suit.clubs
      , s.foundations Suit.diamonds
      , s.foundations Suit.hearts
      , s.foundations Suit.spades
      ]
  , tableau :=
      [ s.tableau 0, s.tableau 1, s.tableau 2, s.tableau 3, s.tableau 4
      , s.tableau 5, s.tableau 6, s.tableau 7, s.tableau 8, s.tableau 9
      ]
  }

def updateColumn (s : State) (c : Fin 10) (col : Column) : State :=
  { s with tableau := fun i => if i = c then col else s.tableau i }
def updateCell (s : State) (c : Fin 4) (card : Option Card) : State :=
  { s with cells := fun i => if i = c then card else s.cells i }
def updateFoundation (s : State) (card : Card) : State :=
  { s with foundations := fun i => if i = card.suit then card.rank else s.foundations i }

inductive Position
  | column (col : Fin 10)
  | cell   (cel : Fin 4)
  | foundation
  deriving Repr, DecidableEq, BEq, Hashable

structure Move where
  src : Position
  dest : Position
  deriving Repr

def top? (c: Column) : Option Card :=
  match c with
  | [] => none
  | x :: _ => some x

def pop? (c : Column) : Option (Card × Column) :=
  match c with
  | [] => none
  | x :: xs => some (x, xs)

def takeFromCol (s : State) (src : Fin 10) : Option (Card × State) :=
  match s.tableau src with
  | [] => none
  | card :: restColumn => (card, updateColumn s src restColumn)

def takeFromCell (s : State) (src : Fin 4) : Option (Card × State) :=
  match s.cells src with
  | none => none
  | some card => (card, updateCell s src none)

def takeFromPosition (s : State) (pos : Position) : Option (Card × State) :=
  match pos with
  | Position.column c => takeFromCol s c
  | Position.cell c => takeFromCell s c
  | Position.foundation => none

def dropCol (s : State) (dst : Fin 10) (card : Card) : Option State :=
  let col := (s.tableau dst)
  -- kings can be dropped on empty columns, other cards only on next in suit.
  if (top? col = nextCard card) then
    updateColumn s dst (card :: col)
  else none

def dropCell (s : State) (dst : Fin 4) (card : Card) : Option State :=
  if (s.cells dst = none) then
    updateCell s dst card
  else none

def dropFoundation (s : State) (c : Card) : Option State :=
  if (some c.rank = nextRank (s.foundations c.suit)) then
    updateFoundation s c
  else none

def dropPosition (s : State) (pos : Position) (card : Card) : Option State :=
  match pos with
  | Position.column c => dropCol s c card
  | Position.cell c => dropCell s c card
  | Position.foundation => dropFoundation s card

def applyMove (s : State) (m : Move) : Option State :=
  match takeFromPosition s m.src with
    | none => none
    | some (card, s1) => dropPosition s1 m.dest card

def goal (s : State) : Prop :=
  ∀ suit : Suit, s.foundations suit = some Rank.king

def colRowToIdx (col : Fin 10) (row : Fin 5) : Fin 52 :=
  ⟨5 * col.val + row.val, by omega⟩

def cellToIdx (cell : Fin 2) : Fin 52 :=
  ⟨50 + cell.val, by omega⟩

def init (cards : Fin 52 -> Card) : State :=
  {
    cells := fun i => if h : i < 2 then some (cards (cellToIdx ⟨i, h⟩)) else none
    foundations := fun _ => none
    tableau := fun col =>
      [4,3,2,1,0].map fun row => cards (colRowToIdx col row)
  }

def applyMoveOpt (s : Option State) (m : Move) : Option State :=
  match s with
  | none => none
  | some s1 => applyMove s1 m

def isGoal (s : State) :=
  List.all [ Suit.clubs, Suit.diamonds, Suit.spades, Suit.hearts ]
    (fun suit => s.foundations suit == Rank.king)

def isSolution (s : State) (solution : List Move) : Bool :=
  match (List.foldl applyMoveOpt (some s) solution) with
  | none => false
  | some s1 => isGoal s1

def allCards (idx : Fin 52) : Card :=
  {
    rank := Option.getD (natToRank ((idx % 13) + 1)) Rank.ace,
    suit := List.get allSuits (⟨idx / 13, by omega⟩ : Fin 4)
  }

#eval (init allCards).toView
