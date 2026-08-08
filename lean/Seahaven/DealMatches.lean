import Seahaven.SolveSound
import Seahaven.InitCard

/-!
# The dealt state matches the solver's view of a fresh deal

`initcard sh` records the deal in `pos2card`/`card2pile`/`card2depth`, indexed by
*deal position*: position `i` goes to pile `i % 10` at depth `i / 10`.
`Rules.init` lays the same deal out as a `State`, and (since `colRowToIdx col row
= 10 * row + col`) uses the same indexing — so the two agree position by position.

This file builds the `Rules`-side deal from the shuffle and shows that the dealt
state matches the position `SolverConvertFromPilesKings` computes for the
all-fives depth vector.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## The deal, as `Rules` cards -/

/-- The card dealt at deal position `i`, as a `Rules.Card`. -/
def dealCards (sh : Vector UInt8 52) (i : Fin 52) : Card :=
  (decodeCard (dealCard sh i.val)).getD ⟨Suit.clubs, Rank.ace⟩

theorem encodeCard_dealCards {sh : Vector UInt8 52} (hdeal : IsDeal sh) (i : Fin 52) :
    encodeCard (dealCards sh i) = dealCard sh i.val := by
  obtain ⟨d, hd⟩ := exists_encodeCard (hdeal.card_real i.isLt)
  unfold dealCards
  rw [← hd, decodeCard_encodeCard]
  rfl

/-- Distinct deal positions carry distinct cards. -/
theorem dealCards_injective {sh : Vector UInt8 52} (hdeal : IsDeal sh) :
    Function.Injective (dealCards sh) := by
  intro a b hab
  have h := congrArg encodeCard hab
  rw [encodeCard_dealCards hdeal, encodeCard_dealCards hdeal] at h
  exact Fin.ext (hdeal.card_inj a.isLt b.isLt h)

/-- The state a fresh deal starts in. -/
def dealState (sh : Vector UInt8 52) : State := _root_.init (dealCards sh)

/-- The depth vector a fresh deal is passed to `solve` as: all ten piles full, and
    no suit owning a column (`stacks[10] = 0`, which `^^^ 0xf` turns into "every
    suit is in the cells' charge"). -/
def fullPk : Vector UInt8 11 := ⟨#[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0], by simp⟩

theorem fullPk_valid : ValidDepths fullPk := by
  intro i
  fin_cases i <;> decide

theorem fullPk_king : (fullPk.get ⟨10, by omega⟩).toNat < 16 := by decide

@[simp] theorem cvDepths_fullPk (i : Fin 10) : (cvDepths fullPk).get i = 5 := by
  rw [cvDepths_get]
  fin_cases i <;> decide

/-! ## The columns of the dealt state -/

theorem dealState_tableau (sh : Vector UInt8 52) (col : Fin 10) :
    (dealState sh).tableau col =
      [dealCards sh ⟨10 * 4 + col.val, by omega⟩, dealCards sh ⟨10 * 3 + col.val, by omega⟩,
       dealCards sh ⟨10 * 2 + col.val, by omega⟩, dealCards sh ⟨10 * 1 + col.val, by omega⟩,
       dealCards sh ⟨10 * 0 + col.val, by omega⟩] := by
  show ([4, 3, 2, 1, 0] : List (Fin 5)).map
    (fun row => dealCards sh (colRowToIdx col row)) = _
  simp only [List.map_cons, List.map_nil, colRowToIdx]
  rfl

theorem dealState_tableau_reverse (sh : Vector UInt8 52) (col : Fin 10) :
    ((dealState sh).tableau col).reverse =
      [dealCards sh ⟨10 * 0 + col.val, by omega⟩, dealCards sh ⟨10 * 1 + col.val, by omega⟩,
       dealCards sh ⟨10 * 2 + col.val, by omega⟩, dealCards sh ⟨10 * 3 + col.val, by omega⟩,
       dealCards sh ⟨10 * 4 + col.val, by omega⟩] := by
  rw [dealState_tableau]
  rfl

theorem dealState_tableau_length (sh : Vector UInt8 52) (col : Fin 10) :
    ((dealState sh).tableau col).length = 5 := by
  rw [dealState_tableau]; rfl

/-- **The columns are the dealt ones.**  Every pile of the fresh deal matches
    `pos2card` at full depth, with an empty flute. -/
theorem dealState_pileMatches {sh : Vector UInt8 52} (hdeal : IsDeal sh) {g : Globals}
    (hinv : InitInv sh 52 g) (col : Fin 10) :
    PileMatches g ((dealState sh).tableau col) col ⟨5, by omega⟩ := by
  have hlen : ((dealState sh).tableau col).length = 5 := dealState_tableau_length sh col
  refine ⟨by omega, ?_, ?_⟩
  · intro k
    have hk : k.val < 5 := k.isLt
    have hidx : 10 * k.val + col.val < 52 := by have := col.isLt; omega
    have hrev : ((dealState sh).tableau col).reverse[k.val]?
        = some (dealCards sh ⟨10 * k.val + col.val, hidx⟩) := by
      rw [dealState_tableau_reverse]
      interval_cases h : k.val <;> rfl
    rw [hrev, Option.map_some, encodeCard_dealCards hdeal]
    have hplaced := hinv.placed col.val k.val col.isLt hk (by omega)
    rw [show k.val * 10 + col.val = 10 * k.val + col.val from by ring] at hplaced
    exact congrArg some hplaced.symm
  · -- the flute is empty: a full column has nothing above the boundary
    have hdrop : (((dealState sh).tableau col).reverse.drop 5).map encodeCard = [] := by
      rw [dealState_tableau_reverse]; rfl
    simp only [hdrop]
    rw [dif_pos (show 0 < 5 from by omega)]
    intro i
    exact absurd i.isLt (by simp)

/-! ## Every card is dealt exactly once -/

theorem dealCards_bijective {sh : Vector UInt8 52} (hdeal : IsDeal sh) :
    Function.Bijective (dealCards sh) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨dealCards_injective hdeal, by decide⟩

theorem countCard_dealCards {sh : Vector UInt8 52} (hdeal : IsDeal sh) {c : Card} {i0 : Fin 52}
    (hi0 : dealCards sh i0 = c) (j : Fin 52) :
    countCard (some (dealCards sh j)) c = if j = i0 then 1 else 0 := by
  unfold countCard
  by_cases hj : j = i0
  · rw [if_pos hj, if_pos (by rw [hj, hi0])]
  · rw [if_neg hj, if_neg]
    intro h
    exact hj (dealCards_injective hdeal ((Option.some.inj h).trans hi0.symm))

theorem dealState_cells (sh : Vector UInt8 52) (c : Card) :
    countCells (dealState sh).cells c =
      countCard (some (dealCards sh ⟨50, by omega⟩)) c
        + countCard (some (dealCards sh ⟨51, by omega⟩)) c := by
  show (List.ofFn fun i : Fin 4 => countCard ((dealState sh).cells i) c).sum = _
  rw [show (List.ofFn fun i : Fin 4 => countCard ((dealState sh).cells i) c)
        = [countCard ((dealState sh).cells 0) c, countCard ((dealState sh).cells 1) c,
           countCard ((dealState sh).cells 2) c, countCard ((dealState sh).cells 3) c] from by
      simp [List.ofFn_succ]]
  show _ = _
  simp only [List.sum_cons, List.sum_nil]
  have h0 : (dealState sh).cells 0 = some (dealCards sh ⟨50, by omega⟩) := rfl
  have h1 : (dealState sh).cells 1 = some (dealCards sh ⟨51, by omega⟩) := rfl
  have h2 : (dealState sh).cells 2 = none := rfl
  have h3 : (dealState sh).cells 3 = none := rfl
  rw [h0, h1, h2, h3, countCardNone]
  omega

theorem dealState_countTableau (sh : Vector UInt8 52) (c : Card) :
    countTableau (dealState sh).tableau c =
      ∑ col : Fin 10, ((countCard (some (dealCards sh ⟨10 * 4 + col.val, by omega⟩)) c
        + (countCard (some (dealCards sh ⟨10 * 3 + col.val, by omega⟩)) c
        + (countCard (some (dealCards sh ⟨10 * 2 + col.val, by omega⟩)) c
        + (countCard (some (dealCards sh ⟨10 * 1 + col.val, by omega⟩)) c
        + (countCard (some (dealCards sh ⟨10 * 0 + col.val, by omega⟩)) c + 0)))))) := by
  show (List.ofFn fun col : Fin 10 => countColumn ((dealState sh).tableau col) c).sum = _
  rw [List.sum_ofFn]
  refine Finset.sum_congr rfl (fun col _ => ?_)
  rw [dealState_tableau]
  simp only [countColumn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

set_option maxHeartbeats 1000000 in
/-- **The deal is a deal**: every card occurs exactly once in the dealt state. -/
theorem dealState_cards_count {sh : Vector UInt8 52} (hdeal : IsDeal sh) (c : Card) :
    countState (dealState sh) c = 1 := by
  obtain ⟨i0, hi0⟩ := (dealCards_bijective hdeal).2 c
  have hcc := countCard_dealCards hdeal hi0
  have hfound : countFoundation (dealState sh).foundations c = 0 := by
    show (if optRankToNat ((fun _ => none) c.suit) < rankToNat c.rank then 0 else 1) = 0
    rw [if_pos]
    show 0 < rankToNat c.rank
    cases c.rank <;> decide
  rw [show countState (dealState sh) c
      = countFoundation (dealState sh).foundations c
        + countCells (dealState sh).cells c + countTableau (dealState sh).tableau c from rfl,
    hfound, dealState_cells, dealState_countTableau]
  simp only [hcc]
  by_cases hlo : i0.val < 50
  · -- the card is on a pile: pile `i0 % 10`, depth `i0 / 10`
    have h50 : (⟨50, by omega⟩ : Fin 52) ≠ i0 := fun h => by
      have h' : (50 : Nat) = i0.val := congrArg Fin.val h
      omega
    have h51 : (⟨51, by omega⟩ : Fin 52) ≠ i0 := fun h => by
      have h' : (51 : Nat) = i0.val := congrArg Fin.val h
      omega
    rw [if_neg h50, if_neg h51]
    have hq : i0.val % 10 < 10 := by omega
    rw [Finset.sum_eq_single (⟨i0.val % 10, hq⟩ : Fin 10)]
    · -- the matching column: exactly one of its five slots is the card
      have hr : i0.val / 10 < 5 := by omega
      have key : ∀ (r : Nat) (hrlt : r < 5),
          ((⟨10 * r + i0.val % 10, by omega⟩ : Fin 52) = i0) = (r = i0.val / 10) := by
        intro r hrlt
        by_cases hre : r = i0.val / 10
        · have hval : 10 * (i0.val / 10) + i0.val % 10 = i0.val := by omega
          simp only [hre]
          exact propext ⟨fun _ => trivial, fun _ => Fin.ext hval⟩
        · simp only [hre]
          refine propext ⟨fun h => absurd ?_ hre, fun h => absurd h (by simp)⟩
          have h' : 10 * r + i0.val % 10 = i0.val := congrArg Fin.val h
          omega
      have e4 := key 4 (by omega); have e3 := key 3 (by omega); have e2 := key 2 (by omega)
      have e1 := key 1 (by omega); have e0 := key 0 (by omega)
      simp only [e0, e1, e2, e3, e4]
      interval_cases hd : (i0.val / 10) <;> simp
    · -- every other column misses: the residue mod 10 is wrong
      intro col _ hne
      have hcol : col.val ≠ i0.val % 10 := fun h => hne (Fin.ext h)
      have key : ∀ (r : Nat) (hr : r < 5), (⟨10 * r + col.val, by omega⟩ : Fin 52) ≠ i0 := by
        intro r hr h
        have h' : 10 * r + col.val = i0.val := congrArg Fin.val h
        have := col.isLt
        omega
      rw [if_neg (key 4 (by omega)), if_neg (key 3 (by omega)), if_neg (key 2 (by omega)),
        if_neg (key 1 (by omega)), if_neg (key 0 (by omega))]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- the card is in one of the two cells
    have hge : 50 ≤ i0.val := by omega
    have hlt : i0.val < 52 := i0.isLt
    have hzero : ∀ col : Fin 10,
        ((if (⟨10 * 4 + col.val, by omega⟩ : Fin 52) = i0 then 1 else 0)
        + ((if (⟨10 * 3 + col.val, by omega⟩ : Fin 52) = i0 then 1 else 0)
        + ((if (⟨10 * 2 + col.val, by omega⟩ : Fin 52) = i0 then 1 else 0)
        + ((if (⟨10 * 1 + col.val, by omega⟩ : Fin 52) = i0 then 1 else 0)
        + ((if (⟨10 * 0 + col.val, by omega⟩ : Fin 52) = i0 then 1 else 0) + 0))))) = 0 := by
      intro col
      have key : ∀ (r : Nat) (hr : r < 5), (⟨10 * r + col.val, by omega⟩ : Fin 52) ≠ i0 := by
        intro r hr h
        have h' : 10 * r + col.val = i0.val := congrArg Fin.val h
        have := col.isLt
        omega
      rw [if_neg (key 4 (by omega)), if_neg (key 3 (by omega)),
        if_neg (key 2 (by omega)), if_neg (key 1 (by omega)), if_neg (key 0 (by omega))]
    rw [Finset.sum_congr rfl (fun col _ => hzero col), Finset.sum_const, smul_eq_mul, mul_zero]
    have hi50 : i0.val = 50 ∨ i0.val = 51 := by omega
    rcases hi50 with hv | hv
    · rw [if_pos (Fin.ext (show (50 : Nat) = i0.val from hv.symm)),
        if_neg (fun h => by
          have h' : (51 : Nat) = i0.val := congrArg Fin.val h
          omega)]
      rfl
    · rw [if_neg (fun h => by
          have h' : (50 : Nat) = i0.val := congrArg Fin.val h
          omega),
        if_pos (Fin.ext (show (51 : Nat) = i0.val from hv.symm))]
      rfl

/-! ## The king configuration of a fresh deal

`stacks[10] = 0` says no suit's king has left a regular pile; `^^^ 0xf` turns that
into the internal "every suit is charged to the cells", i.e. grlex index `15`. -/

theorem kingCfgOf_fullPk : (kingCfgOf fullPk fullPk_king).val = 15 := by decide

theorem cfgBitSet_fullPk (su : Suit) : CfgBitSet (kingCfgOf fullPk fullPk_king) su := by
  revert su; decide

/-! ## The dealt state matches -/

theorem convertPre_fullPk_depth (g : Globals) (i : Fin 10) :
    (convertPre g fullPk).pileDepth.get i = 5 := by
  rw [convertPre_pileDepth, cvDepths_fullPk]

set_option maxHeartbeats 1000000 in
/-- **A fresh deal, matched.**  Any state with the dealt columns still intact whose
    foundations sit exactly at the walks' values stands for the position convert's
    prologue computes from the all-fives depth vector, at the configuration
    `stacks[10] = 0` names. -/
theorem dealState_matches {sh : Vector UInt8 52} (hdeal : IsDeal sh) {g : Globals}
    (hinv : InitInv sh 52 g) (w : State)
    (htab : ∀ i : Fin 10, w.tableau i = (dealState sh).tableau i)
    (hcount : ∀ c : Card, countState w c = 1)
    (haces : ∀ su : Suit,
      cvAceVal g (cvDepths fullPk) (suitToNat su) = optRankToNat (w.foundations su)) :
    StateMatchesKingConfig g w (convertPre g fullPk) (kingCfgOf fullPk fullPk_king) := by
  have hd5 : ∀ i : Fin 10, ((convertPre g fullPk).pileDepth.get i).toNat = 5 := by
    intro i; rw [convertPre_fullPk_depth]; decide
  have hlt6 : ∀ i : Fin 10, ((convertPre g fullPk).pileDepth.get i).toNat < 6 := by
    intro i; rw [hd5]; omega
  have hmatches : StateMatchesSolverPos g w (convertPre g fullPk) := by
    refine ⟨hcount, hlt6, ?_, ?_, ?_, ?_⟩
    · intro i
      have hfin : (⟨((convertPre g fullPk).pileDepth.get i).toNat, hlt6 i⟩ : Fin 6)
          = ⟨5, by omega⟩ := Fin.ext (hd5 i)
      rw [hfin, htab i]
      exact dealState_pileMatches hdeal hinv i
    · intro i _
      rw [htab i, dealState_tableau_length, hd5 i, convertPre_pileFlute]
      rfl
    · intro i hi
      rw [hd5 i] at hi
      omega
    · intro su
      rw [convertPre_aces]
      show CARD (UInt8.ofNat (finOfSuit su).val)
        (UInt8.ofNat (cvAceVal g (cvDepths fullPk) (finOfSuit su).val)) = _
      rw [show (finOfSuit su).val = suitToNat su from rfl, haces su]
      rfl
  refine ⟨hmatches, ⟨fun _ => none, ?_, ?_, ?_⟩, ?_⟩
  · intro su i h; exact absurd h (by simp)
  · intro su su' i h; exact absurd h (by simp)
  · intro su
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_not]
    exact cfgBitSet_fullPk su
  · intro su _ i hi
    rw [hd5 i] at hi
    omega

/-! ## End to end

The one gap left is the *forced foundation plays*: the two cards dealt to the
cells (deal positions 50 and 51) are the only free cards of a fresh deal, so
`cvAceVal` is nonzero exactly for a suit whose ace — and possibly its two — is one
of them, and those must be played before the state matches.  That is what `w`,
`hreach`, `htab` and `haces` package here. -/

/-- **`solve` is sound on a fresh deal.**  `solve fullPk` answering `SUCCESS` means
    the deal really is solvable. -/
theorem solve_deal_sound {sh : Vector UInt8 52} (hdeal : IsDeal sh) {g g' : Globals}
    (hwf : WFGlobals g) (hinv : InitInv sh 52 g) (w : State)
    (hreach : Reach (dealState sh) w)
    (htab : ∀ i : Fin 10, w.tableau i = (dealState sh).tableau i)
    (haces : ∀ su : Suit,
      cvAceVal g (cvDepths fullPk) (suitToNat su) = optRankToNat (w.foundations su))
    (hrun : EStateM.run (_root_.solve fullPk) g = .ok 0 g') :
    Solvable (dealState sh) := by
  have hcount : ∀ c : Card, countState w c = 1 := by
    intro c
    rw [show countState w = countState (dealState sh) from (countState_of_reach hreach)]
    exact dealState_cards_count hdeal c
  exact solve_sound_of_reach hwf fullPk_valid fullPk_king hreach
    (dealState_matches hdeal hinv w htab hcount haces) hrun

end SolverSpec
