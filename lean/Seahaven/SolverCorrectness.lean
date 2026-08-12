import Seahaven.Rules
import Seahaven.Solver

/-
  The glue between the Rules and the Solver.  The application creates a
  random card shuffle.  When querying the solvability, it sends the cardshuffle
  to the solver (initcard).  Afterwards it can query multiple positions.  A
  position is defined by its pile depths (number of cards until the first flute
  starts) and the suits of the piled kings.

  A king on a pile is marked with depth 0 (empty pile) and the corresponding
  bit for the suit set in the kingBitmap.

  solve is called with a vector of 11 elements, the first 10 being the pile
  depths and the last entry is the kingBitmap.
-/

/-- Compute the pile without the flute card (boundary card is included). -/
def removeFlute (col : Column) :=
  match col with
  | c1 :: rest => if (nextCard c1 = rest.head?) then removeFlute rest else c1 :: rest
  | [] => []

/-- The depth of a pile (without flute) -/
def pileDepth (s : State) (pile : Fin 10) : UInt8 :=
  UInt8.ofNat (List.length (removeFlute (s.tableau pile)))

/-- The kingBit for a single pile: if it is a king pile, it's the bit of the
    suit, otherwise 0. -/
def kingBit (col : Column) : UInt8 :=
  match col with
  | c1 :: _ => if (removeFlute col == []) then 1 <<< UInt8.ofNat (allSuits.idxOf c1.suit) else 0
  | [] => 0

/-- The kingBitmap of the full state. -/
def kingBitmap (s : State) : UInt8 :=
  Fin.foldl 10 (fun (bits : UInt8) pile => bits ||| kingBit (s.tableau pile)) 0

/-- Compute the depths and the kingBitmap of a state as vector. -/
def pilesKingsFromState (s : State) : (Vector UInt8 11) :=
  Vector.ofFn (fun (pile : Fin 11) =>
    if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s)

/-- The interface value of a card (1..52) used for a shuffle. -/
def cardToNat (c : Card) : Nat :=
  13 * (allSuits.idxOf c.suit) + rankToNat c.rank

/-- Compute the initcard argument for a given shuffle. -/
def Shuffle.vector (s : Shuffle) :=
  Vector.ofFn (fun i : Fin 52 => UInt8.ofNat (cardToNat (s.perm i)))

/--
The main correctness property of the Solver.

If the solver is initialized with the correct shuffle and it is given the encoding `pilesKingsFromState s`
of a state reachable from the initial state of that shuffle, then it will give always the right result:
`NOMOVE` if `s` is not solvable and `SUCCESS` if `s` is solvable.

The solver can be queried for multiple states and will always answer correctly, provided it was initialized
with the correct shuffle.

We encode two global invariants `inv0` and `inv1`.  Invariant `inv0` must always hold (and is implied by `inv1`).
The invariant `inv1` depends on the initial shuffle and states that the globals are initialized for this
shuffle and the hashmap is valid for the current shuffle.  Calling `initcard` on an arbitrary state guarantees
that `inv0 shuffle` holds.  Calling `solve` on the `pilesKingsFromState s` encoding of a reachable state `s`
will preserves `inv shuffle` and return the correct result.

We don't make any guarantees if the interface is not used correctly.  We assume that the application will
only query valid positions.
-/

def Correctness : Prop :=
  ∃ inv0 : Globals → Prop,
  ∃ inv1 : Shuffle → Globals → Prop,
  inv0 emptyGlobals
  ∧ ∀ shuffle : Shuffle, ∀ g : Globals,
    (inv1 shuffle g → inv0 g)
    ∧ (inv0 g →
       ∃ g' : Globals,
       EStateM.run (initcard shuffle.vector) g = .ok () g' ∧ inv1 shuffle g')
    ∧ (inv1 shuffle g →
       ∀ s : State, isReachable (init shuffle.perm) s →
       ∃ g' : Globals, ∃ res : UInt8,
        EStateM.run (solve (pilesKingsFromState s)) g = .ok res g' ∧ inv1 shuffle g'
        ∧ ((res = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (res = UInt8.ofNat SUCCESS ∧ isSolvable s)))
