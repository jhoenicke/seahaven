import Seahaven.KingReshuffle
import Seahaven.UsedSpaceBound
import Seahaven.MoveSim

/-!
# The two physical king-reshuffle steps

`KingReshuffle` reduces `ComponentSound` (and `SubsetSound`'s downward closure) to
two card-level facts, and this file proves them:

* **`kingUnpileReachable`** — a suit that owns a column can have its freed king run
  moved into the cells, provided the resulting configuration still leaves the cells
  non-negative.  `parkMoves` does it one card at a time; the free cells are
  supplied by `StateMatchesKingConfig.freeCellsOf_le`, which is exactly the
  statement that `freeCellsOf` never overstates the cells actually free.

* **`kingPileReachable`** — a suit with no column of its own can have its freed run
  moved from the cells onto a spare empty column.  No cell arithmetic is needed
  (the move only frees cells), but two things must be established: that the run
  really is *in the cells*, and that a physically empty column is available.

Both directions reuse one frame lemma per direction (`frameEmptyCol` /
`frameFillCol`): the only column that changes is a solver-empty one, and matching
is insensitive to what a solver-empty column holds as long as it holds a complete
king stack — or nothing.
-/

/-! ## Bit bookkeeping -/

/-- `setCfgBit` sets exactly one bit. -/
theorem cfgBitSet_setCfgBit (k : Fin 16) (su su' : Suit) :
    CfgBitSet (setCfgBit k su) su' ↔ (su' = su ∨ CfgBitSet k su') := by
  revert k su su'; decide

/-- `clearCfgBit` clears exactly one bit. -/
theorem cfgBitSet_clearCfgBit (k : Fin 16) (su su' : Suit) :
    CfgBitSet (clearCfgBit k su) su' ↔ (su' ≠ su ∧ CfgBitSet k su') := by
  revert k su su'; decide

/-- Unpiling a suit costs its run length in cells. -/
theorem freeCellsOf_setCfgBit (p : SolverPosType) (k : Fin 16) {su : Suit}
    (hsu : ¬ CfgBitSet k su) :
    freeCellsOf p (setCfgBit k su) = freeCellsOf p k - runLen p su := by
  rw [freeCellsOf_eq, freeCellsOf_eq, piledSet_setCfgBit]
  have h := Finset.sum_erase_add (piledSet k) (runLen p) (mem_piledSet.2 hsu)
  omega

/-- Piling a suit refunds its run length. -/
theorem freeCellsOf_clearCfgBit (p : SolverPosType) (k : Fin 16) {su : Suit}
    (hsu : CfgBitSet k su) :
    freeCellsOf p (clearCfgBit k su) = freeCellsOf p k + runLen p su := by
  rw [freeCellsOf_eq, freeCellsOf_eq, piledSet_clearCfgBit,
    Finset.sum_insert (fun hc => (mem_piledSet.1 hc) hsu)]
  omega

/-! ## Framing: only one solver-empty column changes -/

/-- `PileMatches` for an empty column the solver treats as empty. -/
theorem PileMatches_nil {g : Globals} {i : Fin 10} {n : Fin 6} (hn : n.val = 0) :
    PileMatches g [] i n := by
  refine ⟨by omega, fun k => absurd k.isLt (by omega), ?_⟩
  simp only [hn, gt_iff_lt, lt_self_iff_false, dif_neg, not_false_eq_true]
  exact ⟨0, fun k => absurd k.isLt (by simp)⟩

/-- **A state whose only change is that a solver-empty column was emptied still
matches `p`.**  Nothing the position records mentions those cards: the column's
depth stays `0`, no flute is involved, and the foundations are untouched. -/
theorem StateMatchesSolverPos.frameEmptyCol {g : Globals} {s t : State} {p : SolverPosType}
    {i : Fin 10} (h : StateMatchesSolverPos g s p)
    (hd0 : (p.pileDepth.get i).toNat = 0)
    (hreach : Reach s t) (hti : t.tableau i = [])
    (htq : ∀ q, q ≠ i → t.tableau q = s.tableau q)
    (htf : t.foundations = s.foundations) :
    StateMatchesSolverPos g t p where
  cards_count c := by rw [countState_of_reach hreach]; exact h.cards_count c
  depth_lt6 := h.depth_lt6
  depth_match q := by
    by_cases hq : q = i
    · subst hq
      rw [hti]
      exact PileMatches_nil (by simpa using hd0)
    · rw [htq q hq]; exact h.depth_match q
  flute_match q hq := by
    have hqi : q ≠ i := by intro hc; rw [hc] at hq; omega
    rw [htq q hqi]; exact h.flute_match q hq
  king_pile q hq c hc := by
    by_cases hqi : q = i
    · subst hqi; rw [hti] at hc; simp at hc
    · rw [htq q hqi] at hc ⊢; exact h.king_pile q hq c hc
  aces_match su := by rw [htf]; exact h.aces_match su

/-! ## Unpiling -/

/-- The freed run of a suit that owns a column is exactly that column. -/
private theorem ownsPile_length {g : Globals} {s : State} {p : SolverPosType} {su : Suit}
    {i : Fin 10} (hm : StateMatchesSolverPos g s p) (hb : SolverInvBase g p)
    (hown : OwnsPile s p su i) : ((s.tableau i).length : Int) ≤ runLen p su := by
  obtain ⟨hd0, hphys⟩ := hown
  rcases hphys with ⟨d, hd, hdsuit, -⟩ | ⟨hnil, h13⟩
  · have hc := hm.king_pile i hd0 d (Option.mem_def.1 hd)
    rw [hdsuit] at hc
    unfold runLen
    omega
  · rw [hnil]
    simpa using runLen_nonneg hb su

/-- **The unpile step.**  Move the owning column's whole king run into the cells:
`parkMoves` realizes it, and the cells are there because `freeCellsOf` bounds the
free cells from below. -/
theorem kingUnpileReachable : KingUnpileReachable := by
  intro g p s k su hwf hm hk hsu hfeas
  obtain ⟨assign, hassOwn, hinj, hiff⟩ := hk.realizes
  obtain ⟨i, hassign⟩ := Option.isSome_iff_exists.1 ((hiff su).2 hsu)
  obtain ⟨hd0, hphys⟩ := hassOwn su i hassign
  -- enough free cells for the run
  have hLrun : ((s.tableau i).length : Int) ≤ runLen p su :=
    ownsPile_length hk.toMatches hm.toSolverInvBase ⟨hd0, hphys⟩
  have hLle : (s.tableau i).length ≤ (freeCells s).length := by
    have h1 := hk.freeCellsOf_le hwf hm.toSolverInvBase
    have h2 := freeCellsOf_setCfgBit p k hsu
    omega
  obtain ⟨cells, hnd, hlen, hfreec⟩ := exists_free_cells hLle
  obtain ⟨t, hfold, hti, htq, htf, -, -⟩ :=
    run_parkMoves (s := s) (a := i) (cells := cells) (top := s.tableau i) (rest := [])
      (by simp) hlen hnd hfreec
  have hreach : Reach s t := reach_of_foldl hfold
  have hmt : StateMatchesSolverPos g t p :=
    hk.toMatches.frameEmptyCol hd0 hreach hti htq htf
  -- no solver-empty column of `t` carries `su` any more
  have hnkp : NoKingPile t p su := by
    intro j hj d hd
    by_cases hji : j = i
    · subst hji; rw [hti] at hd; simp at hd
    rw [htq j hji] at hd
    intro hdsu
    rcases hphys with ⟨e, he, hesuit, -⟩ | ⟨hnil, h13⟩
    · exact hji (hk.toMatches.empty_pile_unique hj hd0 (Option.mem_def.1 hd)
        (Option.mem_def.1 he) (by rw [hdsu, hesuit]))
    · have hc := hk.toMatches.king_pile j hj d hd
      rw [hdsu] at hc
      have hpos : 0 < (s.tableau j).length :=
        List.length_pos_iff_ne_nil.2 (fun hnil' => by
          rw [hnil'] at hd; simp at hd)
      omega
  refine ⟨t, hreach, hmt, ⟨fun su' => if su' = su then none else assign su', ?_, ?_, ?_⟩, ?_⟩
  · -- every other suit keeps the column it owned; that column is untouched
    intro su' i' hi'
    by_cases hc : su' = su
    · simp [hc] at hi'
    simp only [hc, if_false] at hi'
    have hine : i' ≠ i := fun hcc => hc (hinj su' su i' hi' (hcc ▸ hassign))
    exact (hassOwn su' i' hi').frame rfl rfl (htq i' hine)
  · intro su' su'' i' h1 h2
    by_cases hc1 : su' = su
    · simp [hc1] at h1
    by_cases hc2 : su'' = su
    · simp [hc2] at h2
    simp only [hc1, if_false] at h1
    simp only [hc2, if_false] at h2
    exact hinj su' su'' i' h1 h2
  · intro su'
    by_cases hc : su' = su
    · subst hc
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_not, reduceIte]
      exact (cfgBitSet_setCfgBit k su' su').2 (Or.inl rfl)
    · simp only [hc, if_false, hiff su']
      constructor
      · exact fun h hb => h (((cfgBitSet_setCfgBit k su su').1 hb).resolve_left hc)
      · exact fun h hb => h ((cfgBitSet_setCfgBit k su su').2 (Or.inr hb))
  · -- and the negative clause: `su` has no column, the others still have none
    intro su' hbit
    rcases (cfgBitSet_setCfgBit k su su').1 hbit with rfl | hk'
    · exact hnkp
    · refine (hk.no_pile su' hk').frame (fun j hj => ?_)
      by_cases hji : j = i
      · subst hji
        exact Or.inr (fun d hd => by rw [hti] at hd; simp at hd)
      · exact Or.inl ⟨hj, htq j hji⟩

/-! ## The freed king run, as a list

For the pile direction the run has to be *named*: unlike unpiling, which moves
whatever the column holds, piling has to know which cards to look for in the cells
and in which order to drop them. -/

/-- The card of suit `su` with value `v` (meaningful for `1 ≤ v ≤ 13`). -/
def cardOf (su : Suit) (v : Nat) : Card := ⟨su, (natToRank v).getD Rank.ace⟩

theorem rankToNat_cardOf (su : Suit) {v : Nat} (h1 : 1 ≤ v) (h2 : v ≤ 13) :
    rankToNat (cardOf su v).rank = v := by
  interval_cases v <;> rfl

theorem cardOf_inj (su : Suit) {v w : Nat} (h1 : 1 ≤ v) (h2 : v ≤ 13) (h3 : 1 ≤ w) (h4 : w ≤ 13)
    (h : cardOf su v = cardOf su w) : v = w := by
  rw [← rankToNat_cardOf su h1 h2, ← rankToNat_cardOf su h3 h4, h]

theorem nextCard_cardOf (su : Suit) {v : Nat} (h1 : 1 ≤ v) (h2 : v ≤ 12) :
    nextCard (cardOf su v) = some (cardOf su (v + 1)) := by
  interval_cases v <;> rfl

theorem nextCard_cardOf_king (su : Suit) : nextCard (cardOf su 13) = none := rfl

/-- The freed king run of suit `su` from value `lo` up to the king, **top card
first** — the head of a `Column` is the accessible card, so values increase with
depth. -/
def kingRun (su : Suit) (lo : Nat) : List Card :=
  (List.range (14 - lo)).map (fun m => cardOf su (lo + m))

@[simp] theorem kingRun_length (su : Suit) (lo : Nat) : (kingRun su lo).length = 14 - lo := by
  simp [kingRun]

@[simp] theorem kingRun_of_14 (su : Suit) : kingRun su 14 = [] := by simp [kingRun]

theorem kingRun_cons (su : Suit) {lo : Nat} (h : lo ≤ 13) :
    kingRun su lo = cardOf su lo :: kingRun su (lo + 1) := by
  unfold kingRun
  rw [show 14 - lo = (14 - (lo + 1)) + 1 from by omega, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  refine congrArg₂ List.cons (by simp) (List.map_congr_left (fun m _ => ?_))
  simp only [Function.comp_apply]
  congr 1
  omega

theorem kingRun_head? (su : Suit) {lo : Nat} (h : lo ≤ 13) :
    (kingRun su lo).head? = some (cardOf su lo) := by
  rw [kingRun_cons su h]; rfl

theorem isRun_kingRun (su : Suit) : ∀ (n lo : Nat), 14 - lo = n → 1 ≤ lo →
    IsRun (kingRun su lo) := by
  intro n
  induction n with
  | zero =>
    intro lo hn _
    rw [show kingRun su lo = [] from by simp [kingRun, hn]]
    trivial
  | succ n ih =>
    intro lo hn hlo1
    have hlo : lo ≤ 13 := by omega
    rw [kingRun_cons su hlo]
    refine ⟨fun y hy => ?_, ih (lo + 1) (by omega) (by omega)⟩
    by_cases h : lo + 1 ≤ 13
    · rw [kingRun_head? su h, Option.mem_def, Option.some.injEq] at hy
      rw [← hy]
      exact nextCard_cardOf su (by omega) (by omega)
    · rw [show kingRun su (lo + 1) = [] from by rw [show lo + 1 = 14 from by omega]; simp] at hy
      simp at hy

/-- Reading the run from the bottom: position `m` from the bottom holds value
`13 - m`.  This is the `IsSameSuitDescending` shape `PileMatches`' king branch
asks for. -/
theorem kingRun_reverse_getElem? (su : Suit) {lo m : Nat} (hlo : lo ≤ 13) (h : m < 14 - lo) :
    (kingRun su lo).reverse[m]? = some (cardOf su (13 - m)) := by
  have hlen : (kingRun su lo).length = 14 - lo := kingRun_length su lo
  rw [List.getElem?_reverse' (j := 14 - lo - 1 - m) (by omega),
    List.getElem?_eq_getElem (by rw [hlen]; omega)]
  simp only [kingRun, List.getElem_map, List.getElem_range, Option.some.injEq]
  congr 1
  omega

/-! ## Piling: dropping the run from the cells onto a column

One move per card, highest value first: the king lands on the physically empty
column (`dropCol` accepts it, since `nextCard` of a king is `none`), and every
later card lands on its successor. -/

theorem reach_pile_run (su : Suit) (V : Nat) :
    ∀ (n : Nat) (s : State) (j : Fin 10), V + 1 + n ≤ 14 →
      s.tableau j = kingRun su (V + 1 + n) →
      (∀ m, V < m → m < V + 1 + n → ∃ c : Fin 4, s.cells c = some (cardOf su m)) →
      ∃ t : State, Reach s t ∧ t.tableau j = kingRun su (V + 1) ∧
        (∀ q, q ≠ j → t.tableau q = s.tableau q) ∧ t.foundations = s.foundations ∧
        (∀ c : Fin 4, t.cells c = s.cells c ∨ t.cells c = none) := by
  intro n
  induction n with
  | zero =>
    intro s j _ hcol _
    exact ⟨s, Relation.ReflTransGen.refl, by simpa using hcol, fun _ _ => rfl, rfl,
      fun _ => Or.inl rfl⟩
  | succ n ih =>
    intro s j hle hcol hcells
    -- the highest card still in a cell goes next
    obtain ⟨c, hc⟩ := hcells (V + 1 + n) (by omega) (by omega)
    have hhead : (s.tableau j).head? = nextCard (cardOf su (V + 1 + n)) := by
      rw [hcol]
      by_cases hk : V + 1 + n ≤ 12
      · rw [show V + 1 + (n + 1) = (V + 1 + n) + 1 from by omega,
          kingRun_head? su (by omega), nextCard_cardOf su (by omega) hk]
      · rw [show V + 1 + (n + 1) = 14 from by omega,
          show V + 1 + n = 13 from by omega, kingRun_of_14, nextCard_cardOf_king]
        rfl
    have hstep : applyMove s ⟨Position.cell c, Position.pile j⟩
        = some (updateColumn (updateCell s c none) j (cardOf su (V + 1 + n) :: s.tableau j)) := by
      rw [applyMove_eq]
      refine ⟨cardOf su (V + 1 + n), updateCell s c none, ?_, ?_⟩
      · simp only [takeFromPosition, takeFromCell_eq]
        exact ⟨hc, trivial⟩
      · simp only [dropPosition, dropCol_eq, updateCell_tableau]
        exact ⟨hhead, trivial⟩
    -- the shortened run is what the induction hypothesis wants
    set s1 := updateColumn (updateCell s c none) j (cardOf su (V + 1 + n) :: s.tableau j) with hs1
    have hcolnew : s1.tableau j = kingRun su (V + 1 + n) := by
      rw [hs1]
      simp only [updateColumn_tableau, update, hcol]
      rw [show V + 1 + (n + 1) = (V + 1 + n) + 1 from by omega, ← kingRun_cons su (by omega)]
      simp
    have hcellsnew : ∀ m, V < m → m < V + 1 + n →
        ∃ c' : Fin 4, s1.cells c' = some (cardOf su m) := by
      intro m hm1 hm2
      obtain ⟨c', hc'⟩ := hcells m hm1 (by omega)
      refine ⟨c', ?_⟩
      have hne : c ≠ c' := by
        intro hcc
        rw [hcc, hc'] at hc
        exact absurd (cardOf_inj su (by omega) (by omega) (by omega) (by omega)
          (Option.some.inj hc)) (by omega)
      rw [hs1]
      simp only [updateColumn_cells, updateCell_cells, update, if_neg hne]
      exact hc'
    obtain ⟨t, hreach, htj, htq, htf, hcellsub⟩ := ih s1 j (by omega) hcolnew hcellsnew
    refine ⟨t, Relation.ReflTransGen.head ⟨_, hstep⟩ hreach, htj, ?_, ?_, ?_⟩
    · intro q hq
      rw [htq q hq, hs1]
      simp [updateColumn, update, Ne.symm hq]
    · rw [htf, hs1]; simp
    · intro c'
      rcases hcellsub c' with h | h
      · rw [h, hs1]
        simp only [updateColumn_cells, updateCell_cells, update]
        by_cases hcc : c = c'
        · exact Or.inr (by simp [hcc])
        · exact Or.inl (by simp [hcc])
      · exact Or.inr h

/-! ## Where the freed run of an unpiled suit is

The one genuinely semantic step of the pile direction: the cards `kings[su] + 1 …
K` are all sitting in cells.  They are free (`king_frontier`), they are past the
foundation (`aces ≤ kings`), and no column can hold them — a solver-empty column
would have to be `su`'s own (`no_pile` forbids that), and on a real pile the card
would sit in the flute above a boundary card of the same suit and *higher* value,
which `king_frontier` declares free while `depth_card_not_free` declares it not. -/

/-- Every card of a solver-empty column carries the deepest card's suit. -/
private theorem empty_col_suit {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (q : Fin 10)
    (hq : (p.pileDepth.get q).toNat = 0) {d e : Card}
    (hlast : (s.tableau q).getLast? = some d) (he : e ∈ s.tableau q) : e.suit = d.suit := by
  obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.1 he
  have hlen : (s.tableau q).reverse.length = (s.tableau q).length := by simp
  have hj : (s.tableau q).length - 1 - idx < (s.tableau q).reverse.length := by omega
  have hrev : (s.tableau q).reverse[(s.tableau q).length - 1 - idx] = e := by
    have h1 := List.getElem?_reverse' (l := s.tableau q)
      (i := (s.tableau q).length - 1 - idx) (j := idx) (by omega)
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hidx, hget] at h1
    exact Option.some.inj h1
  have hcc := (h.king_pile_contents q hq hlast).2 ((s.tableau q).length - 1 - idx) hj
  rw [hrev] at hcc
  have hse : suitToNat e.suit < 4 := suitToNat_lt _
  have hsd : suitToNat d.suit < 4 := suitToNat_lt _
  have hre : rankToNat e.rank ≤ 13 := rankBounded _
  have hre1 : 1 ≤ rankToNat e.rank := rankToNat_pos _
  have heq := congrArg UInt8.toNat hcc
  rw [show encodeCard e
      = CARD (UInt8.ofNat (suitToNat e.suit)) (UInt8.ofNat (rankToNat e.rank)) from rfl,
    CARD_toNat (by omega) (by omega), CARD_toNat (by omega) (by omega)] at heq
  exact suitToNat_inj (by omega)

/-- **The freed run of an unpiled suit sits in the cells.** -/
theorem run_card_in_cell {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16} {su : Suit}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k) (hsu : CfgBitSet k su)
    {v : Nat} (hv1 : (VALUE (p.kings.get (finOfSuit su))).toNat < v) (hv2 : v ≤ 13) :
    ∃ c : Fin 4, s.cells c = some (cardOf su v) := by
  have hv0 : 1 ≤ v := by omega
  have hsuitOf : (cardOf su v).suit = su := rfl
  have hcode : SUIT (encodeCard (cardOf su v)) = (finOfSuit su).val.toUInt8 := by
    rw [encodeCard_SUIT, hsuitOf]; rfl
  have hval : (VALUE (encodeCard (cardOf su v))).toNat = v := by
    rw [encodeCard_VALUE, rankToNat_cardOf su hv0 hv2]
  have hfree : isFreeCard g p (encodeCard (cardOf su v)) :=
    (hb.king_frontier (finOfSuit su)).2 _ hcode (by rw [hval]; omega) (by rw [hval]; omega)
  -- past the foundation
  have hfound : countFoundation s.foundations (cardOf su v) = 0 := by
    have hak := hb.aces_kings_valid (finOfSuit su)
    have hsa := congrArg UInt8.toNat hak.1
    have hsk := congrArg UInt8.toNat hak.2.2.1
    have hle : (p.aces.get (finOfSuit su)).toNat ≤ (p.kings.get (finOfSuit su)).toNat := hak.2.2.2.2
    have hva := VALUE_toNat (p.aces.get (finOfSuit su))
    have hvk := VALUE_toNat (p.kings.get (finOfSuit su))
    have hsa' := SUIT_toNat (p.aces.get (finOfSuit su))
    have hsk' := SUIT_toNat (p.kings.get (finOfSuit su))
    have hfv := hk.toMatches.foundation_value su
    unfold countFoundation
    rw [if_pos ?_]
    · rw [hsuitOf, rankToNat_cardOf su hv0 hv2, ← hfv]
      omega
  -- and on no column
  have hnotcol : ∀ q : Fin 10, cardOf su v ∉ s.tableau q := by
    intro q hmem
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.1 hmem
    by_cases hq : (p.pileDepth.get q).toNat = 0
    · -- a solver-empty column holding it would be `su`'s own
      have hne : s.tableau q ≠ [] := fun hc => by rw [hc] at hmem; simp at hmem
      obtain ⟨d, hd⟩ : ∃ d, (s.tableau q).getLast? = some d := by
        cases hlast : (s.tableau q).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 hlast) hne
        | some d => exact ⟨d, rfl⟩
      have hsd := empty_col_suit hk.toMatches q hq hd hmem
      rw [hsuitOf] at hsd
      exact (hk.no_pile su hsu q hq d (Option.mem_def.2 hd)) hsd.symm
    · -- a real pile: the boundary card would be free
      have hd6 := hk.toMatches.depth_lt6 q
      have hpos : 0 < (p.pileDepth.get q).toNat := by omega
      have hidx5 : (p.pileDepth.get q).toNat - 1 < 5 := by omega
      have habove := hk.toMatches.free_above_boundary hwf hb q hidx (by rw [hget]; exact hfree)
      obtain ⟨hsuit, hvalue⟩ := flute_elem hk.toMatches q hpos
        ⟨(p.pileDepth.get q).toNat - 1, hidx5⟩ rfl idx (by omega) hidx
      rw [hget] at hsuit hvalue
      set B := (g.pos2card.get q).get ⟨(p.pileDepth.get q).toNat - 1, hidx5⟩ with hBdef
      have hreal : IsRealCard B := hwf.pos2card_real q _
      refine depth_card_not_free hwf hb q ⟨(p.pileDepth.get q).toNat - 1, hidx5⟩
        (by simp only [UInt8.toInt_toNat] at hpos ⊢; omega) ?_
      exact (hb.king_frontier (finOfSuit su)).2 B (by rw [← hsuit]; exact hcode)
        (by rw [hval] at hvalue; omega) hreal.2.2
  -- so it is in a cell
  have hcount := hk.toMatches.cards_count (cardOf su v)
  unfold countState at hcount
  have hzero : countTableau s.tableau (cardOf su v) = 0 := by
    unfold countTableau
    refine List.sum_eq_zero (fun x hx => ?_)
    obtain ⟨q, -, rfl⟩ := List.mem_ofFn.1 hx
    unfold countColumn
    refine List.sum_eq_zero (fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    unfold countCard
    rw [if_neg (fun hc => hnotcol q (by rw [Option.some.inj hc] at hz; exact hz))]
  have hcells : 1 ≤ countCells s.cells (cardOf su v) := by omega
  by_contra hcon
  push Not at hcon
  unfold countCells countCard at hcells
  simp only [hcon, if_false] at hcells
  simp at hcells

/-! ## The filled column matches

A solver-empty column carrying a complete king stack is exactly `PileMatches`'
`n = 0` branch: read from the bottom the codes are `CARD su 13, CARD su 12, …`. -/

theorem kingRun_getLast? (su : Suit) {lo : Nat} (hlo : lo ≤ 13) :
    (kingRun su lo).getLast? = some (cardOf su 13) := by
  rw [← List.head?_reverse, List.head?_eq_getElem?]
  exact kingRun_reverse_getElem? su hlo (by omega)

theorem isSameSuitDescending_kingRun (su : Suit) {lo : Nat} (hlo1 : 1 ≤ lo) (hlo : lo ≤ 14) :
    IsSameSuitDescending (UInt8.ofNat (suitToNat su)) 13
      ((kingRun su lo).reverse.map encodeCard) := by
  intro m
  have hlen : ((kingRun su lo).reverse.map encodeCard).length = 14 - lo := by simp
  have hm : m.val < 14 - lo := by rw [← hlen]; exact m.isLt
  have hget : ((kingRun su lo).reverse.map encodeCard).get m
      = encodeCard (cardOf su (13 - m.val)) := by
    have h1 : ((kingRun su lo).reverse.map encodeCard)[m.val]?
        = some (encodeCard (cardOf su (13 - m.val))) := by
      rw [List.getElem?_map, kingRun_reverse_getElem? su (by omega) hm, Option.map_some]
    rw [List.getElem?_eq_getElem m.isLt, Option.some.injEq] at h1
    rw [List.get_eq_getElem]
    exact h1
  rw [hget]
  refine ⟨encodeCard_SUIT _, ?_⟩
  rw [encodeCard_VALUE, rankToNat_cardOf su (by omega) (by omega)]

/-- `PileMatches` for a solver-empty column carrying a complete king stack. -/
theorem PileMatches_kingRun {g : Globals} {j : Fin 10} {n : Fin 6} {su : Suit} {lo : Nat}
    (hn : n.val = 0) (hlo1 : 1 ≤ lo) (hlo : lo ≤ 14) :
    PileMatches g (kingRun su lo) j n := by
  refine ⟨by omega, fun m => absurd m.isLt (by omega), ?_⟩
  simp only [hn, gt_iff_lt, lt_self_iff_false, dif_neg, not_false_eq_true, List.drop_zero]
  exact ⟨_, isSameSuitDescending_kingRun su hlo1 hlo⟩

/-- **A state whose only change is that a solver-empty column was filled with a
suit's complete freed king stack still matches `p`.** -/
theorem StateMatchesSolverPos.frameFillCol {g : Globals} {s t : State} {p : SolverPosType}
    {j : Fin 10} {su : Suit} {V : Nat} (h : StateMatchesSolverPos g s p)
    (hd0 : (p.pileDepth.get j).toNat = 0)
    (hV : (VALUE (p.kings.get (finOfSuit su))).toNat = V) (hV13 : V ≤ 13)
    (hreach : Reach s t) (htj : t.tableau j = kingRun su (V + 1))
    (htq : ∀ q, q ≠ j → t.tableau q = s.tableau q)
    (htf : t.foundations = s.foundations) :
    StateMatchesSolverPos g t p where
  cards_count c := by rw [countState_of_reach hreach]; exact h.cards_count c
  depth_lt6 := h.depth_lt6
  depth_match q := by
    by_cases hq : q = j
    · subst hq
      rw [htj]
      exact PileMatches_kingRun (su := su) (by simpa using hd0) (by omega) (by omega)
    · rw [htq q hq]; exact h.depth_match q
  flute_match q hq := by
    have hqj : q ≠ j := by intro hc; rw [hc] at hq; omega
    rw [htq q hqj]; exact h.flute_match q hq
  king_pile q hq c hc := by
    by_cases hqj : q = j
    · subst hqj
      rw [htj] at hc ⊢
      by_cases hV13' : V = 13
      · rw [show V + 1 = 14 from by omega, kingRun_of_14] at hc; simp at hc
      · rw [kingRun_getLast? su (by omega), Option.mem_def, Option.some.injEq] at hc
        rw [← hc]
        have : (cardOf su 13).suit = su := rfl
        rw [this, hV, kingRun_length]
        omega
    · rw [htq q hqj] at hc ⊢; exact h.king_pile q hq c hc
  aces_match su' := by rw [htf]; exact h.aces_match su'

/-! ## A spare column to pile onto -/

/-- **An unassigned empty column, and it is physically empty.**  Fewer suits are
piled than the position has empty columns, so the assignment misses one; and a
missed empty column carries nothing — whatever its deepest card's suit were, that
suit either owns a *different* column (`empty_pile_unique`, so this one would be
assigned after all) or owns none at all (`no_pile`). -/
private theorem exists_spare_col {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hm : SolverInvMerged g p) (hk : StateMatchesKingConfig g s p k)
    {assign : Suit → Option (Fin 10)}
    (hassOwn : ∀ su i, assign su = some i → OwnsPile s p su i)
    (hiff : ∀ su, (assign su).isSome ↔ ¬ CfgBitSet k su)
    (hcard : (piledSet k).card < p.freePiles.toNat) :
    ∃ j : Fin 10, (p.pileDepth.get j).toNat = 0 ∧ s.tableau j = [] ∧
      ∀ su' : Suit, assign su' ≠ some j := by
  have hEcard : (Finset.univ.filter (fun i : Fin 10 => p.pileDepth.get i = 0)).card
      = p.freePiles.toNat := card_empty_piles_eq_freePiles hm
  have hImgcard : ((piledSet k).image (fun su => (assign su).getD 0)).card ≤ (piledSet k).card :=
    Finset.card_image_le
  have hnsub : ¬ (Finset.univ.filter (fun i : Fin 10 => p.pileDepth.get i = 0))
      ⊆ (piledSet k).image (fun su => (assign su).getD 0) := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨j, hjE, hjImg⟩ := Finset.not_subset.1 hnsub
  have hjd : (p.pileDepth.get j).toNat = 0 := by
    rw [(Finset.mem_filter.1 hjE).2]; rfl
  have hjassign : ∀ su' : Suit, assign su' ≠ some j := by
    intro su' hc
    exact hjImg (Finset.mem_image.2
      ⟨su', mem_piledSet.2 ((hiff su').1 (by rw [hc]; rfl)), by rw [hc]; rfl⟩)
  refine ⟨j, hjd, ?_, hjassign⟩
  by_contra hne
  obtain ⟨d, hd⟩ : ∃ d, (s.tableau j).getLast? = some d := by
    cases hlast : (s.tableau j).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hlast) hne
    | some d => exact ⟨d, rfl⟩
  by_cases hbit : CfgBitSet k d.suit
  · exact (hk.no_pile d.suit hbit j hjd d (Option.mem_def.2 hd)) rfl
  · obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 ((hiff d.suit).2 hbit)
    obtain ⟨hd0', hphys'⟩ := hassOwn d.suit i' hi'
    rcases hphys' with ⟨e, he, hesuit, -⟩ | ⟨hnil', h13⟩
    · exact hjassign d.suit ((hk.toMatches.empty_pile_unique hd0' hjd
        (Option.mem_def.1 he) (Option.mem_def.2 hd) (by rw [hesuit])) ▸ hi')
    · have hc := hk.toMatches.king_pile j hjd d (Option.mem_def.2 hd)
      have hpos : 0 < (s.tableau j).length := List.length_pos_iff_ne_nil.2 hne
      omega

/-! ## Piling, assembled -/

/-- **The pile step.**  The run is in the cells (`run_card_in_cell`), a spare empty
column is available (`exists_spare_col`), and `reach_pile_run` drops the cards on
one at a time.  No cell arithmetic: piling only frees cells. -/
theorem kingPileReachable : KingPileReachable := by
  intro g p s k su hwf hm hk hsu hcard
  have hb := hm.toSolverInvBase
  obtain ⟨assign, hassOwn, hinj, hiff⟩ := hk.realizes
  obtain ⟨j, hjd, hjnil, hjassign⟩ := exists_spare_col hm hk hassOwn hiff hcard
  have hV13 : (VALUE (p.kings.get (finOfSuit su))).toNat ≤ 13 :=
    (hb.aces_kings_valid (finOfSuit su)).2.2.2.1
  set V := (VALUE (p.kings.get (finOfSuit su))).toNat with hVdef
  -- drop the run, card by card, onto the spare column
  obtain ⟨t, hreach, htj, htq, htf, -⟩ :=
    reach_pile_run su V (13 - V) s j (by omega)
      (by rw [hjnil, show V + 1 + (13 - V) = 14 from by omega, kingRun_of_14])
      (fun m hm1 hm2 => run_card_in_cell hwf hb hk hsu (by omega) (by omega))
  have hmt : StateMatchesSolverPos g t p :=
    hk.toMatches.frameFillCol hjd hVdef.symm hV13 hreach htj htq htf
  -- `su` now owns `j`; every other suit is untouched
  have hownj : OwnsPile t p su j := by
    refine ⟨hjd, ?_⟩
    by_cases hV : V = 13
    · exact Or.inr ⟨by rw [htj, show V + 1 = 14 from by omega, kingRun_of_14], by
        rw [← hVdef]; omega⟩
    · exact Or.inl ⟨cardOf su 13, by rw [htj]; exact kingRun_getLast? su (by omega), rfl, rfl⟩
  refine ⟨t, hreach, hmt, ⟨fun su' => if su' = su then some j else assign su', ?_, ?_, ?_⟩, ?_⟩
  · intro su' i' hi'
    by_cases hc : su' = su
    · subst hc
      simp only [reduceIte, Option.some.injEq] at hi'
      rw [← hi']
      exact hownj
    · simp only [hc, if_false] at hi'
      have hine : i' ≠ j := fun hcc => hjassign su' (hcc ▸ hi')
      exact (hassOwn su' i' hi').frame rfl rfl (htq i' hine)
  · intro su' su'' i' h1 h2
    by_cases hc1 : su' = su
    · by_cases hc2 : su'' = su
      · rw [hc1, hc2]
      · simp only [hc1, reduceIte, Option.some.injEq] at h1
        simp only [hc2, if_false] at h2
        exact absurd (h1 ▸ h2) (hjassign su'')
    · by_cases hc2 : su'' = su
      · simp only [hc2, reduceIte, Option.some.injEq] at h2
        simp only [hc1, if_false] at h1
        exact absurd (h2 ▸ h1) (hjassign su')
      · simp only [hc1, if_false] at h1
        simp only [hc2, if_false] at h2
        exact hinj su' su'' i' h1 h2
  · intro su'
    by_cases hc : su' = su
    · subst hc
      simp only [reduceIte, Option.isSome_some, true_iff]
      intro hcon
      exact ((cfgBitSet_clearCfgBit k su' su').1 hcon).1 rfl
    · simp only [hc, if_false, hiff su']
      constructor
      · exact fun h hb' => h ((cfgBitSet_clearCfgBit k su su').1 hb').2
      · exact fun h hb' => h ((cfgBitSet_clearCfgBit k su su').2 ⟨hc, hb'⟩)
  · intro su' hbit
    obtain ⟨hne, hbit'⟩ := (cfgBitSet_clearCfgBit k su su').1 hbit
    refine (hk.no_pile su' hbit').frame (fun i hi => ?_)
    by_cases hij : i = j
    · subst hij
      refine Or.inr (fun d hd => ?_)
      by_cases hV : V = 13
      · rw [htj, show V + 1 = 14 from by omega, kingRun_of_14] at hd
        simp at hd
      · rw [htj, kingRun_getLast? su (by omega), Option.mem_def, Option.some.injEq] at hd
        rw [← hd]
        exact fun hc => hne hc.symm
    · exact Or.inl ⟨hi, htq i hij⟩

/-! ## The obligation, discharged -/

/-- **`ComponentSound`.**  `KingReshuffle`'s reduction, fed with the two physical
steps.  This is the second of `SoundnessSkeleton`'s named obligations to be
proved (after `KingSpacesSpec`), and it is what licenses
`movable'' := movable' ||| component` in `solverRecCheckSolvable`.

`SubsetSound` — the other consumer of these two steps — needs only
`kingPileReachable`: its `subsetTable` closure moves *more* kings onto columns,
which is the direction with no cell-space side condition. -/
theorem componentSound : ComponentSound :=
  componentSound_of kingUnpileReachable kingPileReachable

/-- **`SubsetSound`.**  `KingReshuffle`'s `subsetSound_of`, fed with the piling
step alone: closing a stored set downwards under "put fewer kings on piles" means
piling the extra suits, and piling never needs a cell to spare. -/
theorem subsetSound : SubsetSound :=
  subsetSound_of kingPileReachable
