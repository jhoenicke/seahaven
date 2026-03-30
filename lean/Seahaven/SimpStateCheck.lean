import Seahaven.SimpState

@[simp]
theorem update_same [DecidableEq T1] (f : T1 → T2) (i : T1) (v : T2) :
  update f i v i = v := by
  simp[update]

theorem update_diff [DecidableEq T1] (f : T1 → T2) (i j : T1) (v : T2) (h : i ≠ j) :
  update f i v j = f j := by
  simp[update,h]

@[simp]
theorem update2 [DecidableEq T1] (f : T1 → T2) (i : T1) (v w : T2) :
  update (update f i v) i w = update f i w := by
  funext
  simp[update]
  split <;> simp

theorem pileDepth2card_eq (s: SimpState) (s': SimpState)
  (h: s.pos2card = s'.pos2card) : pileDepth2card s = pileDepth2card s' := by
  funext _ _
  simp[pileDepth2card,h]

def allCardsList :=
  (List.finRange 52).map allCards

def countExtra (s : SimpState) :=
  List.sum (List.map (fun c => if findCard s c = CardPosition.Extra then 1 else 0)
    allCardsList)

def countFlutes (s : SimpState) : Nat :=
  (List.map s.flutes (List.finRange 10)).sum +
  (List.map s.foundations allSuits).sum +
  (List.map s.kingFlutes allSuits).sum

def prevCard (card : Card) : Option Card :=
  match natToRank (rankToNat card.rank - 1) with
  | none => none
  | some rank => some { suit := card.suit, rank := rank }

def checkInFoundation (s : SimpState) (card : Card) : Bool :=
  s.foundations card.suit >= rankToNat card.rank

def checkFreeCard (s : SimpState) (card : Card) : Bool :=
  let pos := s.card2pos card
  let pile : Fin 10 := ⟨pos % 10, by omega⟩
  let depth := pos / 10
  depth.val >= s.depths pile

def checkFluteIsFree (s : SimpState) (card : Option Card) (cnt : Nat) : Bool :=
  match cnt with
  | 0 => True
  | pcnt + 1 =>
    match card with
    | none => False
    | some card =>
      checkFreeCard s card ∧ ¬ (checkInFoundation s card) ∧ checkFluteIsFree s (prevCard card) pcnt

def checkFluteLenient (s : SimpState) (pile : Fin 10) : Bool :=
  let depth := s.depths pile
  if depth = 0 then
    s.flutes pile = 0
  else
    let card := pileDepth2card s pile ⟨depth - 1, by omega⟩
    s.flutes pile >= 1 ∧ checkFluteIsFree s (prevCard card) (s.flutes pile - 1)

def checkFluteStrict (s : SimpState) (pile : Fin 10) : Bool :=
  checkFluteLenient s pile ∧
  let depth := s.depths pile
  if (depth = 1) then
    let card := pileDepth2card s pile ⟨depth - 1, by omega⟩
    card.rank ≠ Rank.king
  else if (depth > 1) then
    let card := pileDepth2card s pile ⟨depth - 1, by omega⟩
    let topcard := pileDepth2card s pile ⟨depth - 2, by omega⟩
    nextCard card ≠ some topcard
  else
    True

def checkTableau (s : SimpState) : Bool :=
  List.finRange 10 |>.all (checkFluteStrict s)

def checkKing (s : SimpState) (suit: Suit) : Bool :=
  if s.kingOnPile suit then
    checkFluteIsFree s (some { suit := suit, rank := Rank.king }) (s.kingFlutes suit)
  else
    s.kingFlutes suit = 0

def checkFoundation (s : SimpState) (suit: Suit) : Bool :=
  List.finRange (s.foundations suit) |>.all fun r =>
    match natToRank (1 + r) with
    | none => False
    | some rank => checkFreeCard s { suit := suit, rank := rank }

def checkKingsFoundations (s : SimpState) : Bool :=
  allSuits |>.all (fun suit =>
    s.kingFlutes suit + s.foundations suit <= 13 ∧
    checkFoundation s suit ∧
    checkKing s suit
  )

def countEmptyPiles (s : SimpState) : Nat :=
  List.map (fun pile => if s.depths pile = 0 then 1 else 0) (List.finRange 10) |>.sum
def countKings (s : SimpState) : Nat :=
  List.map (fun suit => if s.kingOnPile suit then 1 else 0) allSuits |>.sum


def checkState (s : SimpState) : Bool :=
  (countExtra s) + s.space = 4 ∧
  checkTableau s ∧
  checkKingsFoundations s ∧
  countEmptyPiles s >= countKings s ∧
  (countEmptyPiles s > 4 ∨ countEmptyPiles s = countKings s)

theorem preInitStateValidFoundation (card2pos : Card → Fin 52) (pos2card : Fin 52 → Card)
  (inverse : (c : Card) → pos2card (card2pos c) = c)
  (suit : Suit):
  checkFoundation (preInitState card2pos pos2card inverse) suit := by
  simp[preInitState, checkFoundation]

theorem preInitStateValidKings (card2pos : Card → Fin 52) (pos2card : Fin 52 → Card)
  (inverse : (c : Card) → pos2card (card2pos c) = c)
  (suit : Suit) :
  checkKing (preInitState card2pos pos2card inverse) suit := by
  simp[preInitState, checkKing]

theorem preInitStateValidKingsFoundations (card2pos : Card → Fin 52) (pos2card : Fin 52 → Card)
  (inverse : (c : Card) → pos2card (card2pos c) = c) :
  checkKingsFoundations (preInitState card2pos pos2card inverse) := by
  simp[checkKingsFoundations]
  intro
  intro
  simp[preInitStateValidKings, preInitStateValidFoundation]
  simp[preInitState]

theorem preInitStateValidPileLenient (card2pos : Card → Fin 52) (pos2card : Fin 52 → Card)
  (inverse : (c : Card) → pos2card (card2pos c) = c)
  (pile : Fin 10):
  checkFluteLenient (preInitState card2pos pos2card inverse) pile := by
  simp[checkFluteLenient, preInitState, checkFluteIsFree]

theorem updatePile_depths_mono (s : SimpState) (pile : Fin 10)
    (d : Fin 6) (f : Fin 14) (h : d ≤ s.depths pile) (p : Fin 10) :
    (updatePile s pile d f).depths p ≤ s.depths p := by
  simp [updatePile, update]
  split
  · rename_i heq
    simp[←heq]
    exact h
  · omega

theorem checkFreeCard_mono (s s' : SimpState) (card : Card)
    (h_card2pos : s'.card2pos = s.card2pos)
    (h_depths : ∀ p, s'.depths p ≤ s.depths p)
    (h : checkFreeCard s card) : checkFreeCard s' card := by
  simp [checkFreeCard, h_card2pos] at h ⊢
  have hd := h_depths ⟨s.card2pos card % 10, by omega⟩
  omega

theorem checkFoundation_mono (s s' : SimpState) (card : Card)
    (h_foundations : ∀ suit, s'.foundations suit ≤ s.foundations suit)
    (h : ¬checkInFoundation s card) : ¬checkInFoundation s' card := by
  simp [checkInFoundation] at h ⊢
  have hd := h_foundations card.suit
  omega

theorem checkFluteFree_mono (s s' : SimpState) (optcard : Option Card) (count : Nat)
    (h_card2pos : s'.card2pos = s.card2pos)
    (h_depths : ∀ p, s'.depths p ≤ s.depths p)
    (h_foundations : ∀ suit, s'.foundations suit ≤ s.foundations suit)
    (h : checkFluteIsFree s optcard count) : checkFluteIsFree s' optcard count := by
  induction count generalizing optcard
  case zero => simp[checkFluteIsFree]
  case succ hyp =>
    cases optcard
    case none => simp[checkFluteIsFree] at h
    case some card =>
      simp[checkFluteIsFree] at h ⊢
      have hfreecard := checkFreeCard_mono s s' card h_card2pos h_depths
      have hfoundation := checkFoundation_mono s s' card h_foundations
      simp at hfoundation
      have hrec := hyp (prevCard card)
      exact ⟨hfreecard h.1, hfoundation h.2.1, hrec h.2.2⟩

theorem mergeExisting_card2pos (s : SimpState) (pile : Fin 10)
  (d : Nat) (f : Nat) (h0: f >= 1) (h1 : d + f ≤ 6) :
  (mergeExistingFlute s pile d f h0 h1).card2pos = s.card2pos := by
  funext
  induction d generalizing f
  case zero =>
    simp[mergeExistingFlute]
  case succ d hyp =>
    unfold mergeExistingFlute
    cases d
    case zero =>
      simp[updatePile]
      split <;> simp
    case succ d' =>
      simp
      split
      · exact hyp (f + 1) (by omega) (by omega)
      · simp[updatePile]

theorem mergeExisting_foundations (s : SimpState) (pile : Fin 10)
  (d : Nat) (f : Nat) (h0: f >= 1) (h1 : d + f ≤ 6) :
  (mergeExistingFlute s pile d f h0 h1).foundations = s.foundations := by
  funext
  induction d generalizing f
  case zero =>
    simp[mergeExistingFlute]
  case succ d hyp =>
    unfold mergeExistingFlute
    cases d
    case zero =>
      simp[updatePile]
      split <;> simp
    case succ d' =>
      simp
      split
      · exact hyp (f + 1) (by omega) (by omega)
      · simp[updatePile]

theorem mergeExistingIsMonotone (s : SimpState) (pile : Fin 10)
  (d : Nat) (f : Nat) (h0: f >= 1) (h1 : d + f ≤ 6) (h2 : d ≤ s.depths pile)
  (p : Fin 10) :
  (mergeExistingFlute s pile d f h0 h1).depths p ≤ s.depths p := by
  induction d generalizing f
  case zero =>
    unfold mergeExistingFlute
    simp[update] <;> split <;> omega
  case succ d hyp =>
    unfold mergeExistingFlute
    cases d
    case zero =>
      simp
      split
      · simp[update] <;> split <;> omega
      · exact updatePile_depths_mono _ _ _ _ (by omega) _
    case succ d' =>
      simp
      split
      · exact hyp (f + 1) (by omega) (by omega) (by omega)
      · exact updatePile_depths_mono _ _ _ _ h2 _


theorem mergeExistingKeepsFlutesValid (s : SimpState) (pile : Fin 10)
  (optcard : Option Card) (count : Nat)
  (h : checkFluteIsFree s optcard count)
  (d : Nat) (f : Nat) (h0: f >= 1) (h1 : d + f ≤ 6) (h2 : d ≤ s.depths pile) :
  checkFluteIsFree (mergeExistingFlute s pile d f h0 h1) optcard count := by
  exact checkFluteFree_mono s _ optcard count
    (mergeExisting_card2pos _ _ _ _ _ h1)
    (mergeExistingIsMonotone _ _ _ _ _ _ h2)
    (fun s => Fin.le_of_eq (congrFun (mergeExisting_foundations _ _ _ _ _ _) s))
    h

theorem nextPrevCard (c1 : Card) (c2 : Card) (h: nextCard c1 = some c2) :
  prevCard c2 = some c1 := by
  unfold nextCard at h
  split at h
  · contradiction
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    unfold prevCard
    have hrank : rankToNat r = rankToNat c1.rank + 1 := by
      have := nextRankNat (some c1.rank) r hr
      simpa [optRankToNat] using this
    have hnat : natToRank (rankToNat r - 1) = some c1.rank := by
      rw [show rankToNat r - 1 = rankToNat c1.rank by omega]
      have := rankToNatToRank (some c1.rank)
      simpa [optRankToNat] using this
    simp [hnat]

theorem mergeExistingBuildsValidFlute (s : SimpState) (pile : Fin 10)
  (optcard : Option Card) (count : Nat)
  (d : Nat) (f : Nat) (h0: f >= 1) (h1 : d + f ≤ 6) (h2 : d ≤ s.depths pile)
  (h : checkFluteLenient (updatePile s pile ⟨d, by omega⟩ ⟨f, by omega⟩) pile) :
  checkFluteStrict (mergeExistingFlute s pile d f h0 h1) pile := by
  induction d generalizing f
  case zero =>
    simp[mergeExistingFlute,checkFluteStrict,checkFluteLenient]
  case succ d hyp =>
    unfold mergeExistingFlute
    cases d
    case zero =>
      simp
      split
      · simp[checkFluteStrict,checkFluteLenient]
      · rename_i hnk
        simp[checkFluteStrict]
        exact ⟨h, (by
          simp[updatePile, pileDepth2card, nextCard, nextRank] at hnk ⊢
          intro hking
          simp[hking, rankToNat, optRankToNat, natToRank] at hnk
        )⟩
    case succ d' =>
      simp
      split
      · rename_i hnextcard
        have hprevcard := nextPrevCard _ _  hnextcard
        have pileDepth2cardEqOld := pileDepth2card_eq (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f, by omega⟩) s (by simp[updatePile])
        have pileDepth2cardEqNew := pileDepth2card_eq (updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩) s (by simp[updatePile])
        have hfluteold: checkFluteIsFree (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f, by omega⟩)
          (prevCard (pileDepth2card (updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩) pile ⟨d' + 1, by omega⟩)) (f - 1) := by
          simp[pileDepth2card] at hprevcard
          simp[checkFluteLenient, updatePile, pileDepth2card] at h
          simp[updatePile, pileDepth2card]
          exact h.2
        have hflutenew: checkFluteIsFree (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f, by omega⟩)
          (prevCard (pileDepth2card (updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩) pile ⟨d', by omega⟩)) f := by
          unfold checkFluteIsFree
          simp
          split
          · simp
          · rename_i f
            simp
            split
            · rename_i pc
              simp[pileDepth2card] at hprevcard
              simp[pileDepth2card, updatePile, hprevcard] at pc
            · rename_i cc pc
              simp[pileDepth2card] at hprevcard
              simp[pileDepth2card, updatePile, hprevcard] at pc
              simp[pc.symm]
              have cardFree : checkFreeCard (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f + 1, by omega⟩) (s.pos2card ⟨(d' + 1) * 10 + ↑pile, by omega⟩) := by
                have h1 := s.inverse (s.pos2card ⟨(d' + 1) * 10 + ↑pile, by omega⟩)
                sorry
              exact ⟨cardFree, sorry, hfluteold⟩
        have hrec : checkFluteLenient (updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩) pile := by
          have h1 := h
          simp[checkFluteLenient, updatePile] at h1 ⊢
          have hupdmono := updatePile_depths_mono (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f, by omega⟩) pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩ (by simp[updatePile])
          have hupd2 : updatePile (updatePile s pile ⟨d' + 2, by omega⟩ ⟨f, by omega⟩) pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩ =
            updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩ := by
            simp[updatePile]
          simp only[hupd2] at hupdmono
          exact ⟨Fin.mk_le_mk.mpr (by simp),
            checkFluteFree_mono
              (updatePile s pile ⟨d' + 1 + 1, by omega⟩ ⟨f, by omega⟩)
              (updatePile s pile ⟨d' + 1, by omega⟩ ⟨f + 1, by omega⟩) _ _
              (by simp[updatePile]) hupdmono (by simp[updatePile]) hflutenew⟩
        exact hyp (f + 1) (by omega) (by omega) (by omega) hrec
      · rename_i hnc
        simp[checkFluteStrict,h]
        simp[updatePile]
        split
        · rename_i hf
          exact absurd (show (⟨d' + 1 + 1, _⟩ : Fin _).val = (1 : Fin _).val from congrArg _ hf) (by simp)
        · simp[pileDepth2card] at hnc ⊢
          simp[hnc]

theorem initIsValid (card2pos : Card → Fin 52) (pos2card : Fin 52 → Card)
  (inverse : (c : Card) → pos2card (card2pos c) = c) :
  (checkState (initSimpState card2pos pos2card inverse)) = True := by
  unfold checkState
