
--------------------------------------------------
-- Seahaven allows to fill empty piles with kings.  This is somewhat tricky, as it can lead to cycles when solving.
-- Instead we compute all possible king moves by a precomputed bitmap.
--
-- A king configuration is a 4-bit bitmap.  The bit is 0 if the king is on an empty pile, 1 if the king is
-- on a free space.
--
--

import Std

def popcount (n: Nat) : Nat :=
  if n > 0 then (n % 2) + popcount (n / 2) else 0

def grlex (n: Nat) (m: Nat) : Bool :=
  popcount n < popcount m ∨ (popcount n = popcount m ∧ n ≤ m)

def grlexToBits : Vector Nat 16 :=
  ⟨Array.mk (List.mergeSort (List.range 16) grlex),
    by simp⟩

#eval grlexToBits

def bits2Grlex : Vector Nat 16 := Id.run do
  let g := grlexToBits
  let mut arr : Vector Nat 16 := ⟨Array.mk (List.replicate 16 0), by simp⟩
  for i in List.range 16 do
    let j := g[i]!
    arr := arr.set! j i
  return arr

#eval bits2Grlex

abbrev FSuit := Fin 4
abbrev KingState := FSuit → Bool

def update {T1 T2} [DecidableEq T1] (f: T1 → T2) (i: T1) (v: T2) : T1 → T2 :=
  fun j => if i = j then v else f j

@[simp]
theorem update_same [DecidableEq T1] (f : T1 → T2) (i : T1) (v : T2) :
  update f i v i = v := by
  simp[update]

@[simp]
theorem update_diff [DecidableEq T1] (f : T1 → T2) (i j : T1) (v : T2) (h : i ≠ j) :
  update f i v j = f j := by
  simp[update,h]

@[simp]
theorem update2 [DecidableEq T1] (f : T1 → T2) (i : T1) (v w : T2) :
  update (update f i v) i w = update f i w := by
  funext
  simp[update]
  split <;> simp

theorem updateSum {k : Nat} (f : Fin k -> Nat) (c : Fin k) (v : Nat) :
  (List.ofFn (update f c v)).sum + (f c)=
  (List.ofFn f).sum + v := by
  induction k with
  | zero => exact c.elim0
  | succ k' hk' =>
    cases hc : c.val
    case zero =>
      simp at hc
      simp [hc, List.ofFn_succ, List.sum_cons]
      have htail : (List.ofFn fun i : Fin k' =>
                     update f 0 v (Fin.succ i : Fin _)) =
                   List.ofFn (fun i => f (Fin.succ i)) := by
        congr 1
      rw [htail]
      omega
    case succ vc' => -- c = c'.succ: tail is recursively updated
      let c' : Fin k' := ⟨vc',by omega⟩
      have hc' : c = Fin.succ c' := by simp[c',←hc]
      simp [hc']
      have ih := hk' (fun i => f (Fin.succ i)) c'
      have h1 : update f c'.succ v 0 = f 0 := by
        exact update_diff f c'.succ 0 v (Fin.succ_ne_zero c')
      have h2 : (List.ofFn fun i : Fin k' =>
                   update f (Fin.succ c') v (Fin.succ i : Fin _)) =
                List.ofFn (update (fun i : Fin k' => f (Fin.succ i)) c' v) := by
        congr 1; ext i
        simp [update, Fin.succ_inj]
      rw [h1, h2]
      omega

def applyKingDrop (admissible : KingState → Bool) (start : KingState) (drop : FSuit) : Option KingState :=
  let removeDrop := update start drop false
  if start drop ∧ admissible removeDrop then
    removeDrop
  else
    none

def applyKingPick (admissible : KingState → Bool) (start : KingState) (pick : FSuit) : Option KingState :=
  let addPick := update start pick true
  if ¬ start pick ∧ admissible addPick then
    addPick
  else
    none

inductive FKingMove
| pick (s : FSuit)
| drop (s : FSuit)
  deriving DecidableEq

def applyKingMove (admissible : KingState → Bool) (start : KingState) (move : FKingMove) : Option KingState :=
  match move with
  | FKingMove.pick s => applyKingPick admissible start s
  | FKingMove.drop s => applyKingDrop admissible start s

def applyKingMoves (admissible : KingState → Bool) (start : KingState) (moves : List FKingMove) : Option KingState :=
  List.foldlM (applyKingMove admissible) start moves

def isReachableByKingMoves (admissible : KingState → Bool) (start : KingState) (dest : KingState) :=
  ∃ moves, applyKingMoves admissible start moves = some dest

def kingState_cardinality (kings : KingState) :=
  List.ofFn (fun suit : Fin 4 => (kings suit).toNat) |>.sum

theorem updateCard (kings : KingState) (suit : FSuit) (v : Bool) :
  kingState_cardinality (update kings suit v) + (kings suit).toNat =
  kingState_cardinality kings + v.toNat := by
  unfold kingState_cardinality
  have h : (fun s => (update kings suit v s).toNat) = update (fun s => (kings s).toNat) suit v.toNat := by
    funext s
    simp[update]
    split <;> simp
  rw [h]
  exact updateSum (fun s => (kings s).toNat) suit v.toNat

def admissible_upward_bounded (admissible : KingState → Bool) (max : Nat) :=
  ∀ kings, admissible kings → kingState_cardinality kings ≤ max
def admissible_upward_closed (admissible : KingState → Bool) (max : Nat) :=
  ∀ kings1 kings2, admissible kings1 → (∀ s, kings1 s → kings2 s) →
    kingState_cardinality kings2 ≤ max → admissible kings2
def admissible_wellformed (admissible : KingState → Bool) (max : Nat) :=
  admissible_upward_bounded admissible max ∧ admissible_upward_closed admissible max

def admissible_restrict_two (admissible : KingState → Bool) (max : Nat) (kings: KingState) : Bool :=
  admissible kings ∧ (kingState_cardinality kings = max - 1 ∨ kingState_cardinality kings = max)

def isDrop (move : FKingMove) :=
  match move with
  | FKingMove.pick _ => false
  | FKingMove.drop _ => true

def movePickToFront (moves : List FKingMove) (skipped : List FKingMove) : List FKingMove :=
  match moves with
  | head :: tail =>
    match head with
    | FKingMove.pick s =>  FKingMove.pick s :: skipped ++ tail
    | FKingMove.drop s => movePickToFront tail (skipped ++ [FKingMove.drop s])
  | [] => skipped

def cardinalityChangeOfMove (move : FKingMove) : Int :=
  match move with
  | FKingMove.pick _ => 1
  | FKingMove.drop _ => -1

def cardinalityChangeOfMove_correct (admissible : KingState → Bool) (start : KingState) (move : FKingMove)
  (goal : KingState)
  (h1: applyKingMove admissible start move = some goal) :
  kingState_cardinality start + cardinalityChangeOfMove move = kingState_cardinality goal := by
  cases hmove : move
  case pick suit =>
    simp[applyKingMove,applyKingPick,hmove] at h1
    have hcard := updateCard start suit true
    simp [h1] at hcard
    simp [cardinalityChangeOfMove]
    omega
  case drop suit =>
    simp[applyKingMove,applyKingDrop,hmove] at h1
    have hcard := updateCard start suit false
    simp [h1] at hcard
    simp [cardinalityChangeOfMove]
    omega

def cardinalityChangeOfMoves (moves : List FKingMove) : Int :=
  match moves with
  | [] => 0
  | move :: tail => cardinalityChangeOfMove move + cardinalityChangeOfMoves tail

def cardinalityOfGoal (admissible : KingState → Bool) (start : KingState) (moves : List FKingMove)
  (goal : KingState)
  (h0: applyKingMoves admissible start moves = some goal) :
  (kingState_cardinality start + cardinalityChangeOfMoves moves = kingState_cardinality goal) := by
  induction moves generalizing start
  case nil =>
    simp[applyKingMoves] at h0 -- start = goal
    have h : cardinalityChangeOfMoves [] = 0 := by simp[cardinalityChangeOfMoves]
    simp[h0,h]
  case cons move tail hyp =>
    simp[applyKingMoves] at h0
    cases hcase: applyKingMove admissible start move with
    | none => simp[hcase] at h0
    | some step1 =>
      simp[hcase] at h0
      have hcard: kingState_cardinality step1 + cardinalityChangeOfMoves tail = kingState_cardinality goal := hyp step1 h0
      have hcard1 := cardinalityChangeOfMove_correct admissible start move step1 hcase
      simp[cardinalityChangeOfMoves]
      omega
