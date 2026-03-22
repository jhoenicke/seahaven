import Seahaven.Rules

def rankLeq (r1: Rank) (r2 : Rank) : Bool :=
  rankToNat r1 < rankToNat r2

def countFoundation (f : Suit -> Option Rank) (c : Card) : Nat :=
  if optRankToNat (f c.suit) < rankToNat c.rank then 0 else 1

def countCard (c1 : Option Card) (c2 : Card) : Nat :=
  if c1 = some c2 then 1 else 0

def countCells (cells : Fin 4 -> Option Card) (card : Card) : Nat :=
  (List.ofFn fun i : Fin 4 => countCard (cells i) card).sum

def countColumn (xs : List Card) (card : Card) : Nat :=
  ((xs.map fun x => countCard (some x) card).sum)

def countTableau (table : Fin 10 -> List Card) (card : Card) : Nat :=
  (List.ofFn fun col : Fin 10 => countColumn (table col) card).sum

def countState (s : State) (c : Card) : Nat :=
  (countFoundation s.foundations c) + (countCells s.cells c) + (countTableau s.tableau c)

theorem countCardNone (c : Card) : countCard none c = 0 := by
  simp[countCard]

theorem countColumnPush (col : Column) (head: Card) (card: Card) :
  countColumn (head::col) card = countColumn col card + countCard head card := by
  simp[countColumn,List.map]
  omega

theorem updateSum {k : Nat} (f : Fin k -> Nat) (c : Fin k) (v : Nat) :
  (List.ofFn fun i : Fin k => if i = c then v else f i).sum + (f c)=
  (List.ofFn f).sum + v := by
  induction k with
  | zero => exact c.elim0
  | succ k' hk' =>
    refine Fin.cases ?_ ?_ c
    · -- c = 0: head changes from f 0 to v
      simp only [List.ofFn_succ, List.sum_cons, ↓reduceIte]
      have htail : (List.ofFn fun i : Fin k' =>
                     if (Fin.succ i : Fin (k'+1)) = 0 then v else f (Fin.succ i)) =
                   List.ofFn (fun i => f (Fin.succ i)) := by
        congr 1;
      rw [htail]; omega
    · -- c = c'.succ: tail is recursively updated
      intro c'
      have ih := hk' (fun i => f (Fin.succ i)) c'
      simp only [List.ofFn_succ, List.sum_cons]
      have h1 : (if (0 : Fin (k'+1)) = Fin.succ c' then v else f 0) = f 0 :=
        if_neg (Ne.symm (Fin.succ_ne_zero c'))
      have h2 : (List.ofFn fun i : Fin k' =>
                   if (Fin.succ i : Fin (k'+1)) = Fin.succ c' then v else f (Fin.succ i)) =
                List.ofFn fun i : Fin k' => if i = c' then v else f (Fin.succ i) := by
        congr 1; ext i; simp [Fin.succ_inj]
      rw [h1, h2]; omega

theorem countUpdateColumn (s : State) (c : Fin 10) (col: Column) (card: Card) :
  countState (updateColumn s c col) card + countColumn (s.tableau c) card =
    countState s card + countColumn col card := by
  simp[countState, updateColumn]
  suffices countTableau (fun i : Fin 10 => if i = c then col else s.tableau i) card + (countColumn (s.tableau c) card) =
     (countTableau s.tableau card) + (countColumn col card)
     by omega
  unfold countTableau
  have heq : ∀ i : Fin 10, countColumn (if i = c then col else s.tableau i) card =
             if i = c then countColumn col card else countColumn (s.tableau i) card := by
    intro i
    by_cases h : i = c
    · simp only [if_pos h]
    · simp only [if_neg h]
  simp only [heq]
  exact updateSum (fun i => countColumn (s.tableau i) card) c (countColumn col card)

theorem countUpdateCell (s : State) (c : Fin 4) (newCard : Option Card) (card: Card) :
  countState (updateCell s c newCard) card + countCard (s.cells c) card =
    countState s card + countCard newCard card := by
  simp[countState, updateCell]
  suffices countCells (fun i : Fin 4 => if i = c then newCard else s.cells i) card + (countCard (s.cells c) card) =
     (countCells s.cells card) + (countCard newCard card)
     by omega
  unfold countCells
  have heq : ∀ i : Fin 4, countCard (if i = c then newCard else s.cells i) card =
             if i = c then countCard newCard card else countCard (s.cells i) card := by
    intro i
    by_cases h : i = c
    · simp only [if_pos h]
    · simp only [if_neg h]
  simp only [heq]
  exact updateSum (fun i => countCard (s.cells i) card) c (countCard newCard card)

theorem countUpdateFoundation (s : State) (card : Card)
  (h : some card.rank = nextRank (s.foundations card.suit)) (c : Card) :
  countState s c + countCard card c = countState (updateFoundation s card) c := by
  simp[countState, updateFoundation]
  suffices (countFoundation s.foundations c) + (countCard card c) =
    countFoundation (fun i : Suit => if i = card.suit then card.rank else s.foundations i) c
    by omega
  unfold countFoundation
  by_cases hsuit: c.suit = card.suit
  · simp[hsuit]
    have h2 := nextRankNat (s.foundations card.suit) card.rank h.symm
    have hlt: optRankToNat (s.foundations card.suit) < rankToNat card.rank := by
      simp[h2]
    by_cases hrankEq: rankToNat c.rank = rankToNat card.rank
    · have hrank := rankInj hrankEq
      simp [hrank]
      have hsame : c = card := Card.ext hsuit hrank
      have hcc: countCard (some card) c = 1 := by
        simp[hsame,countCard]
      simp[if_pos hlt]
      simp[optRankToNat]
      exact hcc
    · have neg : ¬ card = c := by
        intro eq
        simp[eq] at hrankEq
      simp[countCard, neg]
      by_cases hranklt : rankToNat card.rank < rankToNat c.rank
      · have hranklt2 : optRankToNat (s.foundations card.suit) < rankToNat c.rank := by omega
        simp[if_pos hranklt2]
        simp[optRankToNat]
        exact hranklt
      · have hranklt2 : ¬ optRankToNat (s.foundations card.suit) < rankToNat c.rank := by omega
        simp[if_neg hranklt2]
        simp[optRankToNat]
        omega
  · have neg : ¬ card = c := by
      intro eq
      simp[eq] at hsuit
    simp[countCard, neg]
    simp[if_neg hsuit]

theorem takeColPreservesCards (s : State) (col : Fin 10)
  (card : Card) (s': State)
  (h : takeFromCol s col = some (card, s'))
  (c : Card) :
    countState s c = (countState s' c) + (countCard card c) := by
  unfold takeFromCol at h
  cases hcol: (s.tableau col) with
  | nil => simp [hcol] at h
  | cons top rest =>
    simp[hcol] at h
    simp[h.2.symm,h.1.symm]
    have h2 := countUpdateColumn s col rest c
    simp[hcol] at h2
    have h3 := countColumnPush rest top c
    omega

theorem takeCellPreservesCards (s : State) (src : Fin 4)
  (card : Card) (s': State)
  (h : takeFromCell s src = some (card, s'))
  (c : Card):
    countState s c = (countState s' c) + (countCard card c) := by
  unfold takeFromCell at h
  cases hcell: (s.cells src) with
  | none => simp[hcell] at h
  | some card0 =>
    simp[hcell] at h
    simp[h.2.symm]
    have h2 := countUpdateCell s src none c
    have h3 := countCardNone c
    simp[h.1,hcell] at h2
    omega

theorem takePreservesCards (s : State) (pos : Position)
  (card : Card) (s': State)
  (h : takeFromPosition s pos = some (card, s'))
  (c : Card):
    countState s c = (countState s' c) + (countCard card c) := by
  cases pos with
  | column src =>
    simp[takeFromPosition] at h
    exact takeColPreservesCards s src card s' h c
  | cell src =>
    simp[takeFromPosition] at h
    exact takeCellPreservesCards s src card s' h c
  | foundation =>
    simp[takeFromPosition] at h

theorem dropColPreservesCards (s : State) (col : Fin 10)
  (card : Card) (s': State)
  (h : dropCol s col card = some s')  (c : Card):
    countState s c + (countCard card c) = (countState s' c) := by
  unfold dropCol at h
  by_cases h1: top? (s.tableau col) = nextCard card
  · simp[if_pos h1] at h
    simp[h.symm]
    have h2 := countUpdateColumn s col (card :: s.tableau col) c
    have h3 := countColumnPush (s.tableau col) card c
    omega
  · simp[if_neg h1] at h

theorem dropCellPreservesCards (s : State) (dst : Fin 4)
  (card : Card) (s': State)
  (h : dropCell s dst card = some s') (c : Card) :
    countState s c + (countCard card c) = (countState s' c) := by
  unfold dropCell at h
  by_cases h1: s.cells dst = none
  · simp[if_pos h1] at h
    simp[h.symm]
    have h2 := countUpdateCell s dst card c
    simp[h1] at h2
    have h3 := countCardNone c
    omega
  · simp[if_neg h1] at h

theorem dropFoundationPreservesCards (s : State)
  (card : Card) (s': State)
  (h : dropFoundation s card = some s') (c : Card) :
    countState s c + (countCard card c) = (countState s' c) := by
  unfold dropFoundation at h
  by_cases h1: some card.rank = nextRank (s.foundations card.suit)
  · simp[if_pos h1] at h
    simp[h.symm]
    have h2 := countUpdateFoundation s card h1 c
    omega
  · simp[if_neg h1] at h

theorem dropPreservesCards (s : State) (pos : Position)
  (card : Card) (s': State)
  (h : dropPosition s pos card = some s')
  (c : Card):
    countState s c + (countCard card c) = (countState s' c) := by
  cases pos with
  | column src =>
    simp[dropPosition] at h
    exact dropColPreservesCards s src card s' h c
  | cell src =>
    simp[dropPosition] at h
    exact dropCellPreservesCards s src card s' h c
  | foundation =>
    simp[dropPosition] at h
    exact dropFoundationPreservesCards s card s' h c

theorem movePreservesCards (s : State) (m : Move) (s' : State)
  (h : applyMove s m = some s') : (countState s) = (countState s') := by
  funext c
  unfold applyMove at h
  cases h1: takeFromPosition s m.src with
  | none => simp[h1] at h
  | some pair =>
    simp[h1] at h
    have htake := takePreservesCards s m.src pair.1 pair.2 h1 c
    have hdrop := dropPreservesCards pair.2 m.dest pair.1 s' h c
    omega

def countShuffle (cards: Fin 52 -> Card)  (c : Card) :=
  (List.ofFn fun i : Fin 52 => countCard (cards i) c).sum
