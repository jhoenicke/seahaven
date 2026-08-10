import Seahaven.Rules
import Seahaven.Solver
import Seahaven.DealMatches

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

def correctness :
  ∃ inv : Shuffle → Globals → Prop,
  ∀ shuffle : Shuffle,
    (∀ g : Globals, ∃ g' : Globals,
     EStateM.run (initcard (Vector.ofFn (fun i : Fin 52 => UInt8.ofNat (cardToNat (shuffle.perm i))))) g = .ok unit g'
     ∧ inv shuffle g')
    ∧
    (∀ g : Globals, inv shuffle g →
     ∀ s : State, Reach (init shuffle.perm) s →
     ∃ g' : Globals, ∃ res : UInt8,
        EStateM.run (solve (pilesKingsFromState s)) g = .ok res g'
        ∧ inv shuffle g'
        ∧ ((res = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (res = UInt8.ofNat SUCCESS ∧ isSolvable s))) := by
  sorry
