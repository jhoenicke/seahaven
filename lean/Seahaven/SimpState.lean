import Seahaven.Rules

structure SimpState where
  pos2card : Fin 52 → Card
  card2pos : Card → Fin 52
  inverse (c : Card) : (pos2card (card2pos c)) = c
  depths : Fin 10 → Fin 6
  kingOnPile : Suit → Bool
  flutes : Fin 10 → Fin 14
  kingFlutes : Suit → Fin 14
  foundations : Suit → Fin 14
  space : Fin 5

inductive SimpleMove
  | FromPile (pile : Fin 10)
  | ReorgKing (drop : Suit) (pick : Suit)
  deriving DecidableEq, Repr, BEq, Hashable

inductive CardPosition
  | Inner (pile : Fin 10)
  | Bottom (pile : Fin 10) (flute: Nat)
  | King
  | Foundation
  | Extra
  deriving DecidableEq, Repr, BEq, Hashable

theorem rankOfNextCard {c: Card} {nc: Card}
  (h: nextCard c = some nc) : (nextRank c.rank = nc.rank) := by
  unfold nextCard at h
  split at h
  · contradiction
  · rename_i _ r hr
    simp only [Option.some.injEq] at h
    simp [h.symm]
    exact hr

def update [DecidableEq T1] (f: T1 → T2) (i: T1) (v: T2) : T1 → T2 :=
  fun j => if i = j then v else f j

def pileDepth2card (s: SimpState) (pile : Fin 10) (depth : Fin 5) :=
  s.pos2card ⟨depth * 10 + pile, by omega⟩

def kingPosition (s: SimpState) (suit: Suit) : CardPosition :=
  if s.kingOnPile suit then CardPosition.King else CardPosition.Extra

def findCard (s : SimpState) (c : Card) : CardPosition :=
  if s.foundations c.suit >= rankToNat c.rank then
    CardPosition.Foundation
  else
    let pos := s.card2pos c
    let pile : Fin 10 := ⟨↑pos % 10, by omega⟩
    let depth : Nat := pos
    if depth < s.depths pile then
      if depth = s.depths pile - 1 then
        CardPosition.Bottom pile (s.flutes pile - 1)
      else
        CardPosition.Inner pile
    else
      let nextCardPos := match h : nextCard c with
        | none => kingPosition s c.suit
        | some nc => findCard s nc
      match nextCardPos with
      | CardPosition.King =>
        if (s.kingFlutes c.suit).val + rankToNat c.rank > 13 then
          CardPosition.King
        else
          CardPosition.Extra
      | CardPosition.Inner _ => CardPosition.Extra
      | CardPosition.Bottom pile x =>
        if x = 0 then
          CardPosition.Extra
        else
          CardPosition.Bottom pile (x - 1)
      | _ => CardPosition.Extra
  termination_by 13 - rankToNat c.rank
  decreasing_by
    have hbound := rankBounded nc.rank
    have hr := natToRankToNat (rankToNat c.rank + 1) nc.rank (rankOfNextCard h)
    omega

inductive NormMove
  | ToFoundation (card : Card) (pos : CardPosition)
  | ToPile (card : Card) (pile : Fin 10)
  | ToKing (card : Card)

def autoKing (s : SimpState) (suit : Suit) : Option NormMove :=
  match natToRank (13 - s.kingFlutes suit) with
  | none => none
  | some rank =>
    let card := { suit := suit, rank := rank}
    match findCard s card with
    | CardPosition.Extra => NormMove.ToKing card
    | _ => none

def autoKings (s : SimpState) : Option NormMove :=
  List.findSome? (autoKing s) allSuits

def autoPile (s : SimpState) (pile : Fin 10) : Option NormMove :=
  if s.depths pile = 0 then none else
  let pilecard := pileDepth2card s pile ⟨s.depths pile - 1, by omega⟩
  match natToRank (rankToNat pilecard.rank - s.flutes pile) with
  | none => none
  | some rank =>
    let card := { suit := pilecard.suit, rank := rank}
    match findCard s card with
    | CardPosition.Extra => NormMove.ToPile card pile
    | _ => none

def autoPiles (s : SimpState) : Option NormMove :=
  List.findSome? (autoPile s) (List.finRange 10)

def autoFoundation (s : SimpState) (suit: Suit) : Option NormMove :=
  match natToRank (s.foundations suit + 1) with
  | none => none
  | some rank =>
    let card : Card := { suit := suit, rank := rank }
    let pos := findCard s card
    match pos with
    | CardPosition.Bottom _ 0 => NormMove.ToFoundation card pos
    | CardPosition.Extra => NormMove.ToFoundation card pos
    | _ => none

def autoFoundations (s : SimpState) : Option NormMove :=
  List.findSome? (autoFoundation s) allSuits

def autoMove (s : SimpState) : Option NormMove :=
  List.findSome? id [
    autoFoundations s,
    autoPiles s,
    autoKings s
  ]

def expandKings (kings: Suit -> Bool) : (Suit -> Bool) :=
  if !kings Suit.clubs then
    update kings Suit.clubs True
  else if !kings Suit.diamonds then
    update kings Suit.diamonds True
  else if !kings Suit.hearts then
    update kings Suit.hearts True
  else
    update kings Suit.spades True

def updatePile (s : SimpState) (pile : Fin 10) (d : Fin 6) (f : Fin 14) : SimpState :=
  { s with
    depths := update s.depths pile d
    flutes := update s.flutes pile f
  }

def mergeExistingFlute (s: SimpState) (pile: Fin 10) (depth: Nat) (flute : Nat)
  (h0: flute >= 1) (h1: depth + flute <= 6) : SimpState :=
  if h0: depth = 0 then
    { s with
      depths := update s.depths pile 0
      flutes := update s.flutes pile 0
      kingOnPile := expandKings s.kingOnPile
    }
  else if h1: depth = 1 then
    let card := pileDepth2card s pile ⟨depth - 1, by omega⟩
    if nextCard card = none then
      -- this is a new king pile
      {
        s with
        depths := update s.depths pile 0
        flutes := update s.flutes pile 0
        kingOnPile := if s.kingOnPile card.suit then
          expandKings s.kingOnPile
        else
          update s.kingOnPile card.suit True
      }
    else
      updatePile s pile ⟨depth, by omega⟩ ⟨flute, by omega⟩
  else
    let card := pileDepth2card s pile ⟨depth - 1, by omega⟩
    let nextInPile := pileDepth2card s pile ⟨depth - 2, by omega⟩
    if nextCard card = some nextInPile then
      mergeExistingFlute s pile (depth - 1) (flute + 1) (by omega) (by omega)
    else
      updatePile s pile ⟨depth, by omega⟩ ⟨flute, by omega⟩

def removeFlute (s: SimpState) (pile : Fin 10) : SimpState :=
  mergeExistingFlute s pile (s.depths pile - 1) 1 (by omega) (by omega)

def applyNormMove (s : SimpState) (m: NormMove) :=
  match m with
  | NormMove.ToFoundation card cardpos =>
    match cardpos with
    | CardPosition.Bottom pile 0 =>
      let flute := s.flutes pile
      let s1 := removeFlute s pile
      { s1 with
        foundations := update s.foundations card.suit (s.foundations card.suit + flute)
      }
    | CardPosition.Extra =>
      { s with
        foundations := update s.foundations card.suit (s.foundations card.suit + 1)
        space := s.space - 1
      }
    | _ => s
  | NormMove.ToPile _ pile =>
    { s with
      flutes := update s.flutes pile (s.flutes pile + 1)
      space := s.space - 1
    }
  | NormMove.ToKing card =>
    { s with
      kingFlutes := update s.kingFlutes card.suit (s.kingFlutes card.suit + 1)
      space := s.space - 1
    }

def applyAutoMovesRec (n : Nat) (s : SimpState) : SimpState :=
  match n with
  | 0 => s
  | n+1 => match autoMove s with
    | none => s
    | some m => applyAutoMovesRec n (applyNormMove s m)

def applyAutoMoves (s : SimpState) : SimpState :=
  applyAutoMovesRec 52 (s : SimpState)

def applySimpleMove (s: SimpState) (m: SimpleMove) : Option SimpState :=
  match m with
  | SimpleMove.FromPile pile =>
    if s.depths pile = 0 then none else
    let depth : Fin 5 := ⟨s.depths pile - 1, by omega⟩
    let flute := s.flutes pile
    let card := pileDepth2card s pile depth
    let dest := match nextCard card with
      | none => kingPosition s card.suit
      | some nc => findCard s nc
    match dest with
    | CardPosition.Bottom destpile 0 =>
      if ↑s.space < ↑flute - 1 then
        none
      else
        let s1 := removeFlute s pile
        some { s1 with
          flutes := update s1.flutes destpile (s1.flutes destpile + flute),
        }
    | CardPosition.King =>
      if ↑s.space < ↑flute - 1 then
        none
      else
        let s1 := removeFlute s pile
        some { s1 with
          kingFlutes := update s1.kingFlutes card.suit (s.kingFlutes card.suit + flute)
        }
    | _ =>
      if s.space.val < flute then
        none
      else
        let s1 := removeFlute s pile
        some { s with
          space := ⟨s.space.val - flute.val, by omega⟩
        }
  | SimpleMove.ReorgKing drop pick =>
    if s.space.val < s.kingFlutes drop then
      none
    else
      some { s with
        kingOnPile := update (update s.kingOnPile drop False) pick True
        space := ⟨s.space - s.kingFlutes drop, by omega⟩
      }

#eval (List.finRange 52).map allCards


def preInitState  (card2pos : Card -> Fin 52) (pos2card : Fin 52 -> Card)
  (inverse: (c : Card) -> pos2card (card2pos c) = c) : SimpState :=
  {
    card2pos := card2pos
    pos2card := pos2card
    inverse := inverse
    depths := fun _ => 5
    flutes := fun _ => 1
    kingOnPile := fun _ => False
    kingFlutes := fun _ => 0
    foundations := fun _ => 0
    space := 2
  }


def initSimpState (card2pos : Card -> Fin 52) (pos2card : Fin 52 -> Card)
  (inverse: (c : Card) -> pos2card (card2pos c) = c) : SimpState :=
  let s := preInitState card2pos pos2card inverse
  List.foldl (fun (s : SimpState) (pile : Fin 10) =>
    mergeExistingFlute s pile 5 1 (by omega) (by omega)
  ) s (List.finRange 10)
