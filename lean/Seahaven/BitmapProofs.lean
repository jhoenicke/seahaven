import Seahaven.Solver
import Mathlib

instance : ToString ClosureInfo := ⟨reprStr⟩

def bitsToSet (size: Nat) (bits: Nat) : (Fin size -> Bool) :=
  fun i => (bits / Nat.pow 2 i) % 2 != 0


def popcount (n: Nat) : Nat :=
  if n > 0 then (n % 2) + popcount (n / 2) else 0

def grlex (n: Nat) (m: Nat) : Bool :=
  popcount n < popcount m ∨ (popcount n = popcount m ∧ n ≤ m)

def grlexToBits : Vector Nat 16 :=
  ⟨Array.mk (List.mergeSort (List.range 16) grlex),
    by simp⟩

def reverse (g: Vector Nat 16): Except Error (Vector Nat 16) := do
  let mut arr : Vector Nat 16 := ⟨Array.mk (List.replicate 16 0), by simp⟩
  for i in [0:16] do
    let j ← g[UInt32.ofNat i]!
    arr := ← arr[UInt32.ofNat j]!← i
  return arr

def bitsToGrlex : Vector Nat 16 :=
  match reverse grlexToBits with
  | .ok x => x
  | _ => mkVector 16 0

def grlex2bits_correct (i : Fin 16) :
  grlex2bits[i]?.map (UInt8.toNat) = grlexToBits[i]? := by
  fin_cases i <;> native_decide

def bits2grlex_correct (i : Fin 16) :
  bits2grlex[i]?.map (UInt8.toNat) = bitsToGrlex[i]? := by
  fin_cases i <;> native_decide

def isSuperset {m} (a : Fin m -> Bool) (b : Fin m -> Bool) : Bool :=
  ∀ i : Fin m, a i ∨ !b i

def supersetUsingBitmap (a : Nat) (b : Nat) : Except Error Bool := do
  let ga ← bits2grlex[UInt32.ofNat ↑a]!
  let ci ← closureInfos[UInt32.ofNat (4 - popcount b)]!
  let gb ← bits2grlex[UInt32.ofNat ↑b]!
  assert (gb >= ci.shiftValue)
  let bb := gb - ci.shiftValue
  let subsetBits ← subsetTable[(ci.offset + (1 <<< bb)).toUInt32]!
  return subsetBits &&& (1 <<< ga.toUInt16) != 0

def supersetBits_correct_1 (a : Fin 16) (b : Fin 16) :
  (supersetUsingBitmap a.val b.val).toOption == ((a ||| (15 - b)) == 15) := by
  fin_cases a <;> fin_cases b <;> native_decide

def cnt2num (a : Fin 5) := [1,4,6,4,1].get a
def offsets (a : Fin 5) := closureInfos[a + 1]?.map (fun s:ClosureInfo => s.offset.toNat)

def kingBits2setOfKing (a : Fin 5) (b : Fin 64) : Except Error UInt16 := do
  let ci ← closureInfos[UInt32.ofNat a + 1]!
  return (UInt16.ofNat b  <<< ci.shiftValue.toUInt16)

def kingBits2superset (a : Fin 5) (b : Fin (Nat.pow 2 (cnt2num a))) : Except Error UInt16 := do
  let ci ← closureInfos[UInt32.ofNat a + 1]!
  return ←subsetTable[ci.offset.toUInt32 + UInt32.ofNat b]!
