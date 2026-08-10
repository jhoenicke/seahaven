import Seahaven.Rules
import Seahaven.Solver

def removeFlute (col : Column) :=
  match col with
  | c1 :: rest => if (nextCard c1 = rest.head?) then removeFlute rest else c1 :: rest
  | [] => []

def pileDepth (s : State) (pile : Fin 10) : UInt8 :=
  UInt8.ofNat (List.length (removeFlute (s.tableau pile)))

def kingBit (col : Column) : UInt8 :=
  match col with
  | c1 :: _ => if (removeFlute col == []) then 1 <<< UInt8.ofNat (allSuits.idxOf c1.suit) else 0
  | [] => 0

def kingBitmap (s : State) : UInt8 :=
  Fin.foldl 10 (fun (bits : UInt8) pile => bits ||| kingBit (s.tableau pile)) 0

def pilesKingsFromState (s : State) : (Vector UInt8 11) :=
  Vector.ofFn (fun (pile : Fin 11) =>
    if h : (pile : Nat) < 10 then pileDepth s ⟨pile, h⟩ else kingBitmap s)

def cardToNat (c : Card) : Nat :=
  13 * (allSuits.idxOf c.suit) + rankToNat c.rank

def Shuffle.vector (s : Shuffle) :=
  Vector.ofFn (fun i : Fin 52 => UInt8.ofNat (cardToNat (s.perm i)))

/--
The main correctness property of the Solver.

If the solver is initialized with the correct shuffle and it is given the encoding `pilesKingsFromState s`
of a state reachable from the initial state of that shuffle, then it will give always the right result:
`NOMOVE` if `s` is not solvable and `SUCCESS` if `s` is solvable.

The solver can be queried for multiple states and will always answer correctly, provided it was initialized
with the correct shuffle.

We encode a global invariant `inv` for the global variables of the solver (card2pos, hash table, etc) that
depends on the initial shuffle.  Calling `initcard` on an arbitrary state guarantees that `inv shuffle` holds.
Calling `solve` on the `pilesKingsFromState s` encoding of a reachable state `s` will preserves `inv shuffle`
and return the correct result.

Note that calling `solve` on an invalid encoding may result in undefined behavior (although it should do that
only if any pileDepth is greater than 5).

-/

def correctness :
  ∃ inv : Shuffle → Globals → Prop,
  ∀ shuffle : Shuffle,
    (∀ g : Globals, ∃ g' : Globals,
     EStateM.run (initcard shuffle.vector) g = .ok unit g' ∧ inv shuffle g')
    ∧
    (∀ g : Globals, inv shuffle g →
     ∀ s : State, isReachable (init shuffle.perm) s →
     ∃ g' : Globals, ∃ res : UInt8,
        EStateM.run (solve (pilesKingsFromState s)) g = .ok res g' ∧ inv shuffle g'
        ∧ ((res = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (res = UInt8.ofNat SUCCESS ∧ isSolvable s))) := by
  sorry
