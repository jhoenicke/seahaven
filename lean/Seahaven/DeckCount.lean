import Seahaven.CPNormal

/-!
# The deck partition

`cards_count` says every card is in the state exactly once.  Summing that over
*all fifty-two cards* turns it into a partition identity:

> `Σ_su optRank (foundations su) + #cells + Σ_i |tableau i| = 52`

This is the ingredient completeness needs and soundness did not.  Soundness only
ever needed `#outside ≤ usedSpace` (`usedSpace_ge_outside`), which is an
*injection* of the cards outside the piles into the families `usedSpace_def`
counts.  Completeness needs the converse — that `usedSpace` counts *nothing else*,
so that a state whose cells are full really does contradict the space test — and
that direction needs the whole deck accounted for.

The counting is elementary: `deckList` enumerates the deck, and summing a
`countCard`-shaped function over it picks out exactly one term.
-/

/-! ## The deck as a list -/

def allRanks : List Rank :=
  [Rank.ace, Rank.two, Rank.three, Rank.four, Rank.five, Rank.six, Rank.seven,
   Rank.eight, Rank.nine, Rank.ten, Rank.jack, Rank.queen, Rank.king]

/-- All fifty-two cards, grouped by suit. -/
def deckList : List Card :=
  allSuits.flatMap (fun su => allRanks.map (fun r => ⟨su, r⟩))

theorem deckList_length : deckList.length = 52 := by decide

theorem deckList_nodup : deckList.Nodup := by decide

theorem mem_deckList (c : Card) : c ∈ deckList := by
  refine List.mem_flatMap.2 ⟨c.suit, ?_, ?_⟩
  · cases c.suit <;> simp [allSuits]
  · exact List.mem_map.2 ⟨c.rank, by cases c.rank <;> simp [allRanks], rfl⟩

/-! ## Summing a `countCard` over the deck -/

private theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Summing "is it this card?" over a duplicate-free list containing it gives one. -/
private theorem sum_map_countCard {l : List Card} {d : Card} (hnd : l.Nodup) (hmem : d ∈ l) :
    (l.map (fun c => countCard (some d) c)).sum = 1 := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons]
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
    rcases List.mem_cons.1 hmem with rfl | hmem'
    · have hzero : (xs.map (fun c => countCard (some d) c)).sum = 0 := by
        refine List.sum_eq_zero (fun y hy => ?_)
        simp only [List.mem_map] at hy
        obtain ⟨e, hemem, rfl⟩ := hy
        have hne : ¬ (some d = some e) := by
          intro heq
          exact hx (Option.some.inj heq ▸ hemem)
        simp only [countCard]
        rw [if_neg hne]
      rw [hzero, show countCard (some d) d = 1 from by simp [countCard]]
    · have hne : ¬ (some d = some x) := by
        intro heq
        exact hx (Option.some.inj heq ▸ hmem')
      have hhead : countCard (some d) x = 0 := by
        simp only [countCard]
        rw [if_neg hne]
      rw [hhead, ih hnd' hmem']

/-- The whole deck sums a `countCard` to one. -/
theorem sum_deckList_countCard (d : Card) :
    (deckList.map (fun c => countCard (some d) c)).sum = 1 :=
  sum_map_countCard deckList_nodup (mem_deckList d)

@[simp] theorem sum_deckList_countCard_none :
    (deckList.map (fun c => countCard none c)).sum = 0 :=
  List.sum_eq_zero (fun y hy => by
    simp only [List.mem_map] at hy
    obtain ⟨e, -, rfl⟩ := hy
    simp [countCard])

/-- A column contributes its length. -/
theorem sum_deckList_countColumn (xs : List Card) :
    (deckList.map (fun c => countColumn xs c)).sum = xs.length := by
  induction xs with
  | nil => simp [countColumn]
  | cons x xs ih =>
    have hstep : ∀ c : Card,
        countColumn (x :: xs) c = countColumn xs c + countCard (some x) c :=
      fun c => countColumnPush xs x c
    simp only [hstep]
    rw [sum_map_add, ih, sum_deckList_countCard]
    simp

/-- An occupied cell contributes one, an empty cell nothing. -/
theorem sum_deckList_countCard_opt (o : Option Card) :
    (deckList.map (fun c => countCard o c)).sum = if o.isSome then 1 else 0 := by
  cases o with
  | none => simp
  | some d => simpa using sum_deckList_countCard d

/-! ## Summing over a `Fin n` family of counts -/

/-- Swapping the two sums for any family of card-counting functions. -/
theorem sum_deckList_ofFn {n : Nat} (F : Fin n → Card → Nat) (v : Fin n → Nat)
    (hF : ∀ i, (deckList.map (F i)).sum = v i) :
    (deckList.map (fun c => (List.ofFn (fun i => F i c)).sum)).sum = (List.ofFn v).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons]
    rw [sum_map_add, hF 0, ih (fun i c => F i.succ c) (fun i => v i.succ)
      (fun i => hF i.succ)]

/-! ## The three regions -/

theorem sum_deckList_countCells (cells : Fin 4 → Option Card) :
    (deckList.map (fun c => countCells cells c)).sum
      = (List.ofFn fun i : Fin 4 => if (cells i).isSome then 1 else 0).sum :=
  sum_deckList_ofFn (fun i c => countCard (cells i) c)
    (fun i => if (cells i).isSome then 1 else 0)
    (fun i => sum_deckList_countCard_opt (cells i))

theorem sum_deckList_countTableau (t : Fin 10 → Column) :
    (deckList.map (fun c => countTableau t c)).sum
      = (List.ofFn fun i : Fin 10 => (t i).length).sum :=
  sum_deckList_ofFn (fun i c => countColumn (t i) c) (fun i => (t i).length)
    (fun i => sum_deckList_countColumn (t i))

private theorem sum_flatMap {α : Type} (l : List α) (f : α → List Nat) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons,
      List.sum_cons, ih]

private theorem inner_foundation_sum (su : Suit) {n : Nat} (hn : n ≤ 13) :
    ((allRanks.map (fun r => (⟨su, r⟩ : Card))).map
      (fun c => if n < rankToNat c.rank then 0 else 1)).sum = n := by
  interval_cases n <;> simp [allRanks, rankToNat]

theorem sum_deckList_countFoundation (f : Suit → Option Rank) :
    (deckList.map (fun c => countFoundation f c)).sum
      = (allSuits.map (fun su => optRankToNat (f su))).sum := by
  rw [deckList, List.map_flatMap, sum_flatMap]
  refine congrArg List.sum (List.map_congr_left (fun su _ => ?_))
  rw [List.map_map]
  exact inner_foundation_sum su (optRankToNat_le (f su))

/-! ## The partition -/

/-- **Every card is somewhere.**  Summing `cards_count` over the deck. -/
theorem deck_partition {u : State} (hcount : ∀ c : Card, countState u c = 1) :
    (allSuits.map (fun su => optRankToNat (u.foundations su))).sum
      + (List.ofFn fun i : Fin 4 => if (u.cells i).isSome then 1 else 0).sum
      + (List.ofFn fun i : Fin 10 => (u.tableau i).length).sum = 52 := by
  have hall : (deckList.map (fun c => countState u c)).sum = 52 := by
    rw [List.map_congr_left (fun c _ => hcount c)]
    simp [deckList_length]
  rw [← sum_deckList_countFoundation, ← sum_deckList_countCells, ← sum_deckList_countTableau,
    ← sum_map_add, ← sum_map_add]
  exact hall

/-! ## In the vocabulary of `UsedSpaceBound` / `Normalize` -/

set_option linter.unnecessarySeqFocus false in
private theorem sum_map_ite_eq_countP {α : Type} (l : List α) (q : α → Bool) :
    (l.map (fun a => if q a then 1 else 0)).sum = l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : q x <;> simp [h] <;> omega

/-- The cell term of `deck_partition` is `cellList`'s length. -/
theorem occupiedCells_eq (s : State) :
    (List.ofFn fun i : Fin 4 => if (s.cells i).isSome then 1 else 0).sum
      = (cellList s).length := by
  rw [List.ofFn_eq_map, cellList, List.length_filterMap_eq_countP]
  exact sum_map_ite_eq_countP _ _

/-- **The deck partition, in the shape the space count needs**: the cells, the
columns and the foundations exhaust the deck. -/
theorem deck_partition' {u : State} (hcount : ∀ c : Card, countState u c = 1) :
    (allSuits.map (fun su => optRankToNat (u.foundations su))).sum
      + (cellList u).length + tableauCount u = 52 := by
  rw [← occupiedCells_eq]
  exact deck_partition hcount

/-! ## `usedSpace` counts exactly the cards outside the piles

`usedSpace_def` is stated with `foldl`s over the vectors' `toList`s; these are the
`Finset`-sum forms of the same three sums (`SolverInvariant` has private twins). -/

private theorem foldl_add_map {α : Type} (l : List α) (f : α → Nat) (a : Nat) :
    l.foldl (fun acc x => acc + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

private theorem foldl_add_self (l : List Nat) (a : Nat) : l.foldl (·+·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.sum_cons]; omega

private theorem vector_toList_ofFn {n : Nat} {α : Type} (v : Vector α n) :
    v.toList = List.ofFn v.get := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Vector.get]

private theorem zipWith_ofFn {n : Nat} {α β γ : Type} (f : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem <;> simp

private theorem sum_filter_map {α : Type} (l : List α) (q : α → Bool) (h : α → Nat) :
    ((l.filter q).map h).sum = (l.map (fun a => if q a then h a else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => by_cases hq : q x <;> simp [hq, ih]

/-- `aces` records the foundation heights. -/
theorem VALUE_aces_eq {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (su : Suit) :
    (VALUE (p.aces.get (finOfSuit su))).toNat = optRankToNat (u.foundations su) := by
  have hsu : suitToNat su < 4 := suitToNat_lt _
  have hf13 := optRankToNat_le (u.foundations su)
  rw [VALUE_toNat, haces su, encodeFoundation, CARD_toNat (by omega) (by omega)]
  omega

/-- **`usedSpace` is exactly what sits outside the piles, less what is parked.**
The cards in cells and on king stacks are what `usedSpace` pays for; a flute card
the position counts but that physically sits in a cell (because it was parked to
expose the boundary) is *not* paid for twice, so it appears as the negative
`parked` term. -/
theorem usedSpace_eq_outside {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    p.usedSpace.toInt
        + ∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
            ((p.pileFlute.get i).toNat : Int) + (p.pileDepth.get i).toNat - 1
              - (u.tableau i).length else 0)
      = ((cellList u).length : Int) + ((kingList u p).length : Int) := by
  -- the three sums of `usedSpace_def`, in `Finset` form
  have hused := hb.usedSpace_def
  rw [vector_foldl_add_eq_finsum p.pileDepth (fun d => d.toNat),
    vector_foldl_add_eq_finsum p.aces (fun a => (VALUE a).toNat),
    zipWith_foldl_add_eq_finsum p.pileDepth p.pileFlute
      (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)] at hused
  -- the `if` guard, as a guard on the depth's `toNat`
  have hguard : ∀ i : Fin 10,
      (if p.pileDepth.get i ≠ (0 : UInt8) then (p.pileFlute.get i).toNat - 1 else 0)
        = (if (p.pileDepth.get i).toNat ≠ 0 then (p.pileFlute.get i).toNat - 1 else 0) := by
    intro i
    by_cases hz : p.pileDepth.get i = 0
    · simp [hz]
    · rw [if_pos hz, if_pos (by
        intro h0
        exact hz (UInt8.toNat_inj.mp (by rw [h0]; rfl)))]
  rw [Finset.sum_congr rfl (fun i _ => hguard i)] at hused
  -- the deck partition
  have hdeck := deck_partition' hcount
  rw [tableauCount, List.sum_ofFn] at hdeck
  -- the foundations, both ways
  have hfnd : (∑ s : Fin 4, (VALUE (p.aces.get s)).toNat)
      = (allSuits.map (fun su => optRankToNat (u.foundations su))).sum := by
    rw [Fin.sum_univ_four]
    simp only [allSuits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [show (0 : Fin 4) = finOfSuit Suit.clubs from by decide,
      show (1 : Fin 4) = finOfSuit Suit.diamonds from by decide,
      show (2 : Fin 4) = finOfSuit Suit.hearts from by decide,
      show (3 : Fin 4) = finOfSuit Suit.spades from by decide,
      VALUE_aces_eq haces, VALUE_aces_eq haces, VALUE_aces_eq haces, VALUE_aces_eq haces]
    omega
  -- the king stacks
  have hking : (kingList u p).length
      = ∑ i : Fin 10, (if (p.pileDepth.get i).toNat = 0 then (u.tableau i).length else 0) := by
    rw [kingList_length, sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
    exact Finset.sum_congr rfl (fun i _ => by by_cases h : (p.pileDepth.get i).toNat = 0 <;>
      simp [h])
  -- one pointwise identity ties the five sums together
  have hflute_le : ∀ i : Fin 10, 1 ≤ (p.pileFlute.get i).toNat := hb.flute_pos
  have key : (∑ i : Fin 10, ((u.tableau i).length : Int))
      - (∑ i : Fin 10, ((p.pileDepth.get i).toNat : Int))
      - (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
          (((p.pileFlute.get i).toNat - 1 : Nat) : Int) else 0))
      + (∑ i : Fin 10, (if (p.pileDepth.get i).toNat ≠ 0 then
          ((p.pileFlute.get i).toNat : Int) + (p.pileDepth.get i).toNat - 1
            - (u.tableau i).length else 0))
      - (∑ i : Fin 10, (if (p.pileDepth.get i).toNat = 0 then
          ((u.tableau i).length : Int) else 0)) = 0 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : (p.pileDepth.get i).toNat = 0
    · simp [h]
    · have h1 := hflute_le i
      rw [if_pos h, if_pos h, if_neg h, Nat.cast_sub h1]
      push_cast
      ring
  push_cast at hused
  have hdeckZ : ((allSuits.map (fun su => optRankToNat (u.foundations su))).sum : Int)
      + ((cellList u).length : Int) + (∑ i : Fin 10, ((u.tableau i).length : Int)) = 52 := by
    exact_mod_cast hdeck
  have hkingZ : ((kingList u p).length : Int)
      = ∑ i : Fin 10, (if (p.pileDepth.get i).toNat = 0 then
          ((u.tableau i).length : Int) else 0) := by
    exact_mod_cast hking
  have hfndZ : (∑ s : Fin 4, ((VALUE (p.aces.get s)).toNat : Int))
      = ((allSuits.map (fun su => optRankToNat (u.foundations su))).sum : Int) := by
    exact_mod_cast hfnd
  linarith [hused, hdeckZ, key, hfndZ, hkingZ]

/-! ## The two consequences

A parked card is one the position assigns to a flute while it physically sits in a
cell; `parkedAt` is that count for one pile.  It is nonnegative exactly when the
column holds no more than its flute, which every state along the shuffle prefix
satisfies. -/

/-- How many of pile `i`'s flute cards are not physically on the column. -/
def parkedAt (u : State) (p : SolverPosType) (i : Fin 10) : Int :=
  if (p.pileDepth.get i).toNat ≠ 0 then
    ((p.pileFlute.get i).toNat : Int) + (p.pileDepth.get i).toNat - 1 - (u.tableau i).length
  else 0

theorem parkedAt_nonneg {u : State} {p : SolverPosType} {i : Fin 10}
    (h : 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat) :
    0 ≤ parkedAt u p i := by
  unfold parkedAt
  by_cases hz : (p.pileDepth.get i).toNat = 0
  · simp [hz]
  · rw [if_pos hz]
    have := h (by omega)
    have : ((u.tableau i).length : Int) + 1
        ≤ ((p.pileDepth.get i).toNat : Int) + ((p.pileFlute.get i).toNat : Int) := by
      exact_mod_cast this
    linarith

/-- **`usedSpace` is at most what is physically outside the piles** — the cards in
the cells plus the cards on king stacks.  Every other card is either resident in
its pile, part of a flute the position counts, or on a foundation. -/
theorem usedSpace_le_outside {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat) :
    p.usedSpace.toInt ≤ ((cellList u).length : Int) + ((kingList u p).length : Int) := by
  have hid := usedSpace_eq_outside hb hcount haces
  have hnn : (0 : Int) ≤ ∑ i : Fin 10, parkedAt u p i :=
    Finset.sum_nonneg (fun i _ => parkedAt_nonneg (hflute i))
  unfold parkedAt at hnn
  linarith

/-- **The affordability bound.**  Only four cells exist, so whatever `usedSpace`
does not spend on king stacks leaves room for the cards pile `a` has parked — which
is exactly the space test `solverGetMovable` reads out of `possibleKings`. -/
theorem usedSpace_add_parked_le {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (a : Fin 10) :
    p.usedSpace.toInt + parkedAt u p a ≤ 4 + ((kingList u p).length : Int) := by
  have hid := usedSpace_eq_outside hb hcount haces
  have hsingle : parkedAt u p a ≤ ∑ i : Fin 10, parkedAt u p i :=
    Finset.single_le_sum (f := fun i => parkedAt u p i)
      (fun i _ => parkedAt_nonneg (hflute i)) (Finset.mem_univ a)
  have hcells : (cellList u).length ≤ 4 := by
    have := cellList_length_add_freeCells u
    omega
  have hcellsZ : ((cellList u).length : Int) ≤ 4 := by exact_mod_cast hcells
  unfold parkedAt at hsingle ⊢
  linarith

/-- **Affordability, at the moment the boundary card is about to move.**  Pile `a`'s
column is then exactly its dealt part — the whole flute above the boundary has been
parked — so `parkedAt` is `fluteLen - 1`, and those cards occupy cells that
`usedSpace` does not pay for.  Hence `usedSpace - #kingStacks + (fluteLen - 1) ≤ 4`,
which is precisely `possibleKings[fluteLen - 1]`' space test. -/
theorem usedSpace_add_flute_le {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    p.usedSpace.toInt + ((p.pileFlute.get a).toNat : Int) - 1
      ≤ 4 + ((kingList u p).length : Int) := by
  have h := usedSpace_add_parked_le hb hcount haces hflute a
  unfold parkedAt at h
  rw [if_pos (by omega : (p.pileDepth.get a).toNat ≠ 0), hcol] at h
  linarith

/-! ## The king stacks are exactly the configuration's refund

`UsedSpaceBound` proves `kingRefund p k ≤ #kingStacks` (a *suits → columns*
injection through `RealizesKingConfig`'s assignment), which is the direction
soundness needs.  Affordability needs the converse: the refund must cover *all* the
king stacks, or the space test could be satisfied by stacks nobody paid for.  That
direction runs *columns → suits* and needs no assignment: a non-empty solver-empty
column carries one suit's complete stack (`king_pile`), distinct columns carry
distinct suits (`empty_pile_unique`), and `no_pile` forces every such suit's bit to
be clear, hence refunded. -/

theorem kingList_length_sum (s : State) (p : SolverPosType) :
    (kingList s p).length
      = ∑ i : Fin 10, (if (p.pileDepth.get i).toNat = 0 then (s.tableau i).length else 0) := by
  rw [kingList_length, sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
  exact Finset.sum_congr rfl
    (fun i _ => by by_cases h : (p.pileDepth.get i).toNat = 0 <;> simp [h])

/-- The suit whose stack a solver-empty column carries (`0` for an empty column). -/
private def kingSuitOf (s : State) (i : Fin 10) : Fin 4 :=
  match (s.tableau i).getLast? with
  | some d => finOfSuit d.suit
  | none => 0

private def kingCols (s : State) (p : SolverPosType) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => (p.pileDepth.get i).toNat = 0 ∧ s.tableau i ≠ [])

/-- The refund one piled suit earns. -/
private def refundTerm (p : SolverPosType) (su : Fin 4) : Int :=
  (13 : Int) - (VALUE (p.kings.get su)).toNat

private def clearSuits (k : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun su => ¬ CfgBitSet k (natToSuit su))

private theorem kingRefund_as_sum (p : SolverPosType) (k : Fin 16) :
    kingRefund p k = ∑ su : Fin 4,
      (if ¬ CfgBitSet k (natToSuit su) then refundTerm p su else 0) := by
  rw [kingRefund, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl (fun su _ => ?_)
  have hb : (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0 ↔ ¬ CfgBitSet k (natToSuit su) := by
    unfold CfgBitSet
    rw [suitToNat_natToSuit]
    omega
  by_cases hc : (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0
  · rw [if_pos hc, if_pos (hb.1 hc)]; rfl
  · rw [if_neg hc, if_neg (fun hn => hc (hb.2 hn))]

/-- **Every king stack is refunded**, over the three facts the count actually uses.

Stated over hypotheses rather than over `StateMatchesKingConfig` because the
completeness argument reaches it at the *middle* layer (`DepthPlusKingsCfg`),
where a king column may be shorter than its suit's stack — the rest of it parked
in cells mid-reshuffle.  A shorter column only makes the bound easier, so
`king_pile`'s equality degrades to `≤` without any change to the argument.

* `hkl` — a non-empty solver-empty column carries (at most) one suit's stack;
* `huniq` — distinct such columns carry distinct suits;
* `hnp` — every such suit has a clear configuration bit, hence is refunded. -/
theorem kingList_le_kingRefund_of {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (hkl : ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 → ∀ d ∈ (s.tableau i).getLast?,
      (s.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13)
    (huniq : ∀ (i j : Fin 10), (p.pileDepth.get i).toNat = 0 → (p.pileDepth.get j).toNat = 0 →
      ∀ {d e : Card}, (s.tableau i).getLast? = some d → (s.tableau j).getLast? = some e →
      d.suit = e.suit → i = j)
    (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile s p su) :
    ((kingList s p).length : Int) ≤ kingRefund p k := by
  -- the last card of a non-empty king column, and what it pins
  have hlast : ∀ i ∈ kingCols s p, ∃ d : Card, (s.tableau i).getLast? = some d ∧
      kingSuitOf s i = finOfSuit d.suit ∧
      (s.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13 := by
    intro i hi
    simp only [kingCols, Finset.mem_filter] at hi
    obtain ⟨-, hd0, hne⟩ := hi
    obtain ⟨d, hd⟩ : ∃ d, (s.tableau i).getLast? = some d := by
      cases hl : (s.tableau i).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
      | some d => exact ⟨d, rfl⟩
    exact ⟨d, hd, by simp only [kingSuitOf, hd], hkl i hd0 d (Option.mem_def.2 hd)⟩
  -- step 1: only the non-empty king columns contribute
  have h1 : ((kingList s p).length : Int)
      = ∑ i ∈ kingCols s p, ((s.tableau i).length : Int) := by
    rw [kingList_length_sum]
    push_cast
    rw [← Finset.sum_filter]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      simp only [kingCols, Finset.mem_filter] at hi
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi.2.1⟩
    · intro i hi hni
      simp only [Finset.mem_filter] at hi
      simp only [kingCols, Finset.mem_filter, not_and] at hni
      have : s.tableau i = [] := by
        by_contra hne
        exact hni (Finset.mem_univ _) hi.2 hne
      simp [this]
  -- step 2: each contributes at most its suit's refund
  have h2 : ∑ i ∈ kingCols s p, ((s.tableau i).length : Int)
      ≤ ∑ i ∈ kingCols s p, refundTerm p (kingSuitOf s i) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    obtain ⟨d, -, hsuit, hlen⟩ := hlast i hi
    rw [hsuit, refundTerm]
    omega
  -- step 3: distinct columns carry distinct suits
  have hinj : Set.InjOn (kingSuitOf s) ↑(kingCols s p) := by
    intro i hi' j hj' heq
    have hi := Finset.mem_coe.1 hi'
    have hj := Finset.mem_coe.1 hj'
    obtain ⟨d, hd, hsi, -⟩ := hlast i hi
    obtain ⟨e, he, hsj, -⟩ := hlast j hj
    simp only [kingCols, Finset.mem_filter] at hi hj
    refine huniq i j hi.2.1 hj.2.1 hd he ?_
    have : suitToNat d.suit = suitToNat e.suit := by
      have := hsi.symm.trans (heq.trans hsj)
      exact congrArg Fin.val this
    rw [← natToSuit_suitToNat d.suit, ← natToSuit_suitToNat e.suit]
    exact congrArg natToSuit (Fin.ext this)
  -- step 4: those suits all have a clear bit
  have hsub : (kingCols s p).image (kingSuitOf s) ⊆ clearSuits k := by
    intro su hsu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hsu
    obtain ⟨d, hd, hsi, -⟩ := hlast i hi
    simp only [kingCols, Finset.mem_filter] at hi
    simp only [clearSuits, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hbit
    rw [hsi, show natToSuit (finOfSuit d.suit) = d.suit from natToSuit_suitToNat d.suit] at hbit
    exact hnp d.suit hbit i hi.2.1 d (Option.mem_def.2 hd) rfl
  -- step 5: assemble
  have h3 : ∑ i ∈ kingCols s p, refundTerm p (kingSuitOf s i)
      = ∑ su ∈ (kingCols s p).image (kingSuitOf s), refundTerm p su :=
    (Finset.sum_image hinj).symm
  rw [h1]
  refine h2.trans ?_
  rw [h3, kingRefund_as_sum, ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun su _ _ => ?_)
  have := (hb.aces_kings_valid su).2.2.2.1
  rw [refundTerm]
  omega

/-- **Every king stack is refunded**, for a full match.  `king_pile`'s equality is
stronger than `kingList_le_kingRefund_of` needs. -/
theorem StateMatchesKingConfig.kingList_le_kingRefund {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k) :
    ((kingList s p).length : Int) ≤ kingRefund p k :=
  kingList_le_kingRefund_of hb
    (fun i hi d hd => le_of_eq (hk.toMatches.king_pile i hi d hd))
    (fun _ _ hi hj {_ _} hd he hsu => hk.toMatches.empty_pile_unique hi hj hd he hsu)
    hk.no_pile

/-! ### The sharp form: free cells are extra slack

`usedSpace_add_parked_le` throws away `#cells ≤ 4`.  Keeping the exact count instead
(`#cells + #freeCells = 4`) leaves the free cells as slack on the left, which is what
the `EXTRA` and king-pile branches of `solverGetMovable` need: they index
`possibleKings` at `fluteLen`, one higher than a column destination, and the extra
cell is exactly the one the play itself used. -/

theorem usedSpace_add_parked_add_freeCells_le {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (a : Fin 10) :
    p.usedSpace.toInt + parkedAt u p a + ((freeCells u).length : Int)
      ≤ 4 + ((kingList u p).length : Int) := by
  have hid := usedSpace_eq_outside hb hcount haces
  have hsingle : parkedAt u p a ≤ ∑ i : Fin 10, parkedAt u p i :=
    Finset.single_le_sum (f := fun i => parkedAt u p i)
      (fun i _ => parkedAt_nonneg (hflute i)) (Finset.mem_univ a)
  have hcells : (cellList u).length + (freeCells u).length = 4 :=
    cellList_length_add_freeCells u
  have hcellsZ : ((cellList u).length : Int) + ((freeCells u).length : Int) = 4 := by
    exact_mod_cast hcells
  unfold parkedAt at hsingle ⊢
  linarith

/-- The same, with pile `a`'s flute known to be parked (`hcol`). -/
theorem usedSpace_add_flute_add_freeCells_le {g : Globals} {u : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    p.usedSpace.toInt + ((p.pileFlute.get a).toNat : Int) - 1 + ((freeCells u).length : Int)
      ≤ 4 + ((kingList u p).length : Int) := by
  have h := usedSpace_add_parked_add_freeCells_le hb hcount haces hflute a
  unfold parkedAt at h
  rw [if_pos (by omega : (p.pileDepth.get a).toNat ≠ 0), hcol] at h
  linarith

/-- **The sharp affordability bound.**  Every free cell at the critical moment is one
more cell the configuration can afford — the form the `EXTRA` branch needs. -/
theorem flute_sub_one_add_freeCells_le_freeCellsOf_of {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (hkl : ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 → ∀ d ∈ (u.tableau i).getLast?,
      (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13)
    (huniq : ∀ (i j : Fin 10), (p.pileDepth.get i).toNat = 0 → (p.pileDepth.get j).toNat = 0 →
      ∀ {d e : Card}, (u.tableau i).getLast? = some d → (u.tableau j).getLast? = some e →
      d.suit = e.suit → i = j)
    (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile u p su)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    ((p.pileFlute.get a).toNat : Int) - 1 + ((freeCells u).length : Int)
      ≤ freeCellsOf p k := by
  have h1 := usedSpace_add_flute_add_freeCells_le hb hcount haces hflute a hda hcol
  have h2 := kingList_le_kingRefund_of hb hkl huniq hnp
  unfold freeCellsOf
  linarith

/-! ### Piling more suits only helps

`freeCellsOf` is monotone along `MaskSub`: a configuration that puts *more* kings on
piles earns a larger refund, hence affords at least as much.  This is what lets the
affordability of the configuration a state is *in* be transported to the block's
maximal configurations — the ones the loop's bits actually range over
(`closureInfo_block`). -/

theorem kingRefund_mono {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    {d k : Fin 16} (h : MaskSub d k) : kingRefund p k ≤ kingRefund p d := by
  unfold kingRefund
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, List.sum_ofFn, List.sum_ofFn]
  refine Finset.sum_le_sum (fun su _ => ?_)
  have hbit : ∀ c : Fin 16, ((grlex2bits.get c).toNat / 2 ^ su.val % 2 = 0)
      ↔ ¬ CfgBitSet c (natToSuit su) := by
    intro c
    unfold CfgBitSet
    rw [suitToNat_natToSuit]
    omega
  have hv := (hb.aces_kings_valid su).2.2.2.1
  by_cases hk : (grlex2bits.get k).toNat / 2 ^ su.val % 2 = 0
  · -- `k` piles this suit, so `d` does too (`MaskSub`)
    have hd : (grlex2bits.get d).toNat / 2 ^ su.val % 2 = 0 := by
      by_contra hdn
      have hdset : CfgBitSet d (natToSuit su) := by
        unfold CfgBitSet
        rw [suitToNat_natToSuit]
        omega
      exact (hbit k).1 hk ((MaskSub_iff d k).1 h (natToSuit su) hdset)
    rw [if_pos hk, if_pos hd]
  · rw [if_neg hk]
    by_cases hd : (grlex2bits.get d).toNat / 2 ^ su.val % 2 = 0
    · rw [if_pos hd]; omega
    · rw [if_neg hd]

theorem freeCellsOf_mono {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    {d k : Fin 16} (h : MaskSub d k) : freeCellsOf p k ≤ freeCellsOf p d := by
  have := kingRefund_mono hb h
  unfold freeCellsOf
  linarith

/-- **Affordability, in the form `computeKingSpaces` states it.**  `freeCellsOf p k`
is the quantity the solver compares against the flute length; at the moment pile
`a`'s boundary is about to move, the `fluteLen - 1` cards already parked in cells
are ones `usedSpace` does not pay for, so that many cells really are free at
configuration `k`.

This is the completeness counterpart of `freeCellsOf_le`: that one bounds
`freeCellsOf` *above* by the physically free cells (soundness reads a solver
decision as a physical one), this one bounds it *below* by what the play already
did (completeness reads a physical fact as a solver decision). -/
theorem flute_sub_one_le_freeCellsOf_of {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (hkl : ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 → ∀ d ∈ (u.tableau i).getLast?,
      (u.tableau i).length + (VALUE (p.kings.get (finOfSuit d.suit))).toNat ≤ 13)
    (huniq : ∀ (i j : Fin 10), (p.pileDepth.get i).toNat = 0 → (p.pileDepth.get j).toNat = 0 →
      ∀ {d e : Card}, (u.tableau i).getLast? = some d → (u.tableau j).getLast? = some e →
      d.suit = e.suit → i = j)
    (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile u p su)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    ((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p k := by
  have h1 := usedSpace_add_flute_le hb hcount haces hflute a hda hcol
  have h2 := kingList_le_kingRefund_of hb hkl huniq hnp
  unfold freeCellsOf
  linarith

/-- The same, for a full match. -/
theorem StateMatchesKingConfig.flute_sub_one_le_freeCellsOf {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g u p k)
    (hflute : ∀ i : Fin 10, 0 < (p.pileDepth.get i).toNat →
      (u.tableau i).length + 1 ≤ (p.pileDepth.get i).toNat + (p.pileFlute.get i).toNat)
    (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    ((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p k :=
  flute_sub_one_le_freeCellsOf_of hb hk.toMatches.cards_count hk.toMatches.aces_match hflute
    (fun i hi d hd => le_of_eq (hk.toMatches.king_pile i hi d hd))
    (fun _ _ hi hj {_ _} hd he hsu => hk.toMatches.empty_pile_unique hi hj hd he hsu)
    hk.no_pile a hda hcol
