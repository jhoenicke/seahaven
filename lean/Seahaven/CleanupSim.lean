import Seahaven.MoveSim
import Seahaven.GetDestination

/-!
# Simulating `SolverCleanupPile`, phase 2 of `SolverMove`

`SolverCleanupPile` does four things to the pile it is called on; only one of them
moves a card:

1. **merge** (`while depth > 1 && pos2card[pile][depth-2] == card + 1`) — reclassify
   dealt cards below the boundary as flute cards.  `depth` drops and `pileFlute`
   grows by the same amount, so `depth + pileFlute` is unchanged and the *state does
   not change at all*: `cleanupMerge` below is an implication between two matching
   facts about the same `s`.
2. **flute extension** (`while aces[suit] < prevCard && prevCard is free`) — take
   freed predecessor cards and stack them on the pile.  These *are* card moves: each
   one is a `CPStep`, and the whole run is `run_unparkMoves`.  This is
   `cleanupExtend`.
3. **`busyAces` marking** — invisible to matching, which does not read `busyAces`.
4. **lone-king vacate** (`depth == 1 && VALUE card == 13`) — reclassify the pile as
   empty carrying a king stack.  Again no card moves: `cleanupVacate` is another
   implication about the same `s`, trading `pileDepth = 1` for `pileDepth = 0` plus
   `king_pile`.

So the concrete move list of a whole `SolverCleanupPile` call is exactly the
extension's `unparkMoves`.
-/

/-! ## Prepending a run to a matching column -/

/-- `PileMatches_append_run`, with the column's head named — the shape the extension
produces (`ds ++ e :: rest`, where `e` was the exposed card). -/
theorem PileMatches_append_head {g : Globals} {p : Fin 10} {n : Fin 6}
    {ds rest : Column} {e : Card}
    (hm : PileMatches g (e :: rest) p n) (hrun : IsRun (ds ++ [e])) :
    PileMatches g (ds ++ e :: rest) p n := by
  induction ds with
  | nil => simpa using hm
  | cons x xs ih =>
    simp only [List.cons_append] at hrun ⊢
    refine PileMatches_cons (ih hrun.tail) ?_
    obtain ⟨y, hy⟩ : ∃ y, (xs ++ [e]).head? = some y := by
      cases hl : xs ++ [e] with
      | nil => simp at hl
      | cons y ys => exact ⟨y, by simp⟩
    rw [head?_append_cons, hy]
    exact (hrun.head y (Option.mem_def.2 hy)).symm

/-! ## The flute extension: the only card moves in a cleanup -/

/-- **The freed-predecessor extension is realized by cell→pile moves.**

The cards the solver appends to the flute are the freed predecessors of the pile's
run; physically they are sitting in cells, and returning them is exactly
`unparkMoves` (each step a `CPStep`).  `depth` is untouched, so the only abstract
change matching sees is `pileFlute` growing by the number of returned cards —
which is also how much the column grows. -/
theorem StateMatchesSolverPos.cleanupExtend {g : Globals} {s : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) (a : Fin 10)
    {ds rest : Column} {e : Card} {cells : List (Fin 4)}
    (hcol : s.tableau a = e :: rest)
    (hd : 0 < (p.pileDepth.get a).toNat)
    (hnd : cells.Nodup)
    (hhold : HoldsCards s.cells cells ds)
    (hrun : IsRun (ds ++ [e]))
    -- the abstract effect: `pileFlute[a]` grows by `|ds|`, nothing else moves
    (hqd : q.pileDepth = p.pileDepth)
    (hqf : (q.pileFlute.get a).toNat = (p.pileFlute.get a).toNat + ds.length)
    (hqfne : ∀ i : Fin 10, i ≠ a → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces)
    (hqkings : q.kings = p.kings) :
    ∃ v : State, Reach s v ∧
      List.foldl applyMoveOpt (some s) (unparkMoves a cells) = some v ∧
      (∀ i : Fin 10, i ≠ a → v.tableau i = s.tableau i) ∧
      StateMatchesSolverPos g v q := by
  obtain ⟨v, hfold, hva, hvo, hvempty, hvoth, hvf⟩ :=
    run_unparkMoves (u := s) (b := a) (top := ds) (restb := rest) hnd hhold hcol hrun
  refine ⟨v, reach_of_foldl hfold, hfold, hvo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cards_count
    intro d
    rw [congrFun (countState_of_reach (reach_of_foldl hfold)) d]
    exact h.cards_count d
  · -- depth_lt6
    intro i
    rw [hqd]
    exact h.depth_lt6 i
  · -- depth_match
    intro i
    by_cases hia : i = a
    · subst hia
      rw [hva]
      have hidx : (⟨(q.pileDepth.get i).toNat, by rw [hqd]; exact h.depth_lt6 i⟩ : Fin 6)
          = ⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ := by simp only [hqd]
      rw [hidx]
      refine PileMatches_append_head ?_ hrun
      rw [← hcol]
      exact h.depth_match i
    · rw [hvo i hia]
      have hidx : (⟨(q.pileDepth.get i).toNat, by rw [hqd]; exact h.depth_lt6 i⟩ : Fin 6)
          = ⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ := by simp only [hqd]
      rw [hidx]
      exact h.depth_match i
  · -- flute_match
    intro i hdi
    rw [hqd] at hdi
    by_cases hia : i = a
    · subst hia
      have hfm := h.flute_match i hdi
      rw [hva, hqd, hqf]
      rw [hcol] at hfm
      simp only [List.length_append, List.length_cons] at hfm ⊢
      omega
    · rw [hvo i hia, hqd, hqfne i hia]
      exact h.flute_match i hdi
  · -- king_pile
    intro i hdi
    rw [hqd] at hdi
    by_cases hia : i = a
    · subst hia
      omega
    · rw [hvo i hia, hqkings]
      exact h.king_pile i hdi
  · -- aces_match
    intro su
    rw [hqaces, hvf]
    exact h.aces_match su

/-! ## The lone-king vacate: no card moves -/

private theorem isSameSuitDescending_cons {suit : UInt8} {sv : Nat} {x : UInt8} {L : List UInt8}
    (hL : IsSameSuitDescending suit (sv - 1) L) (hs : SUIT x = suit)
    (hv : (VALUE x).toNat = sv) :
    IsSameSuitDescending suit sv (x :: L) := by
  intro ⟨i, hi⟩
  cases i with
  | zero => exact ⟨by simpa using hs, by simpa using hv⟩
  | succ j =>
    have hj : j < L.length := by simpa using hi
    obtain ⟨h1, h2⟩ := hL ⟨j, hj⟩
    simp only [List.get_eq_getElem, List.getElem_cons_succ] at *
    exact ⟨h1, by omega⟩

/-- **Reclassifying a depth-1 king pile as empty.**  When the pile's single dealt
card is a king, its `PileMatches` witness drops from `1` to `0`: the whole column
becomes the king run. -/
theorem PileMatches_vacate {g : Globals} {col : Column} {a : Fin 10}
    (hm : PileMatches g col a 1)
    (hking : (VALUE ((g.pos2card.get a).get ⟨0, by omega⟩)).toNat = 13) :
    PileMatches g col a 0 := by
  obtain ⟨hlen, hbot, hflute⟩ := hm
  have hlen1 : 1 ≤ col.length := hlen
  have hrev : 0 < col.reverse.length := by simp only [List.length_reverse]; omega
  have hb0 : encodeCard (col.reverse[0]'hrev) = (g.pos2card.get a).get ⟨0, by omega⟩ := by
    have hk := hbot ⟨0, by omega⟩
    rw [List.getElem?_eq_getElem hrev, Option.map_some] at hk
    exact Option.some.inj hk
  have hfl : IsSameSuitDescending (SUIT ((g.pos2card.get a).get ⟨0, by omega⟩))
      ((VALUE ((g.pos2card.get a).get ⟨0, by omega⟩)).toNat - 1)
      ((col.reverse.drop 1).map encodeCard) := by
    simpa using hflute
  refine ⟨by omega, fun k => k.elim0, ?_⟩
  simp only [show ((0 : Fin 6)).val = 0 from rfl, gt_iff_lt, lt_self_iff_false, dif_neg,
    not_false_eq_true, List.drop_zero]
  refine ⟨SUIT ((g.pos2card.get a).get ⟨0, by omega⟩), ?_⟩
  have hsplit : col.reverse.map encodeCard
      = encodeCard (col.reverse[0]'hrev) :: ((col.reverse.drop 1).map encodeCard) := by
    conv_lhs => rw [show col.reverse = col.reverse[0]'hrev :: col.reverse.drop 1 from by
      rw [← List.drop_eq_getElem_cons hrev, List.drop_zero]]
    simp
  rw [hsplit]
  exact isSameSuitDescending_cons (by rw [hking] at hfl; exact hfl) (by rw [hb0])
    (by rw [hb0]; exact hking)

/-- **The lone-king vacate moves no card.**  It trades `pileDepth[a] = 1` for
`pileDepth[a] = 0` plus the `king_pile` bookkeeping, on the *same* state. -/
theorem StateMatchesSolverPos.cleanupVacate {g : Globals} {s : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) (a : Fin 10)
    (hd1 : (p.pileDepth.get a).toNat = 1)
    (hking : (VALUE ((g.pos2card.get a).get ⟨0, by omega⟩)).toNat = 13)
    -- the abstract vacate
    (hqd : (q.pileDepth.get a).toNat = 0)
    (hqdne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i)
    (hqfne : ∀ i : Fin 10, i ≠ a → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces)
    (hqkne : ∀ i : Fin 10, i ≠ a → (p.pileDepth.get i).toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit))
    (hqk : ∀ d ∈ (s.tableau a).getLast?,
      (s.tableau a).length + (VALUE (q.kings.get (finOfSuit d.suit))).toNat = 13) :
    StateMatchesSolverPos g s q := by
  have hlt6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6 := by
    intro i
    by_cases hia : i = a
    · subst hia; omega
    · rw [hqdne i hia]; exact h.depth_lt6 i
  refine ⟨h.cards_count, hlt6, ?_, ?_, ?_, ?_⟩
  · -- depth_match
    intro i
    by_cases hia : i = a
    · subst hia
      have hidx : (⟨(q.pileDepth.get i).toNat, hlt6 i⟩ : Fin 6) = 0 := Fin.ext (by simpa using hqd)
      rw [hidx]
      refine PileMatches_vacate ?_ hking
      have hidx1 : (⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ : Fin 6) = 1 :=
        Fin.ext (by simpa using hd1)
      rw [← hidx1]
      exact h.depth_match i
    · have hidx : (⟨(q.pileDepth.get i).toNat, hlt6 i⟩ : Fin 6)
          = ⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ := by simp only [hqdne i hia]
      rw [hidx]
      exact h.depth_match i
  · -- flute_match
    intro i hdi
    by_cases hia : i = a
    · subst hia; omega
    · rw [hqdne i hia, hqfne i hia]
      exact h.flute_match i (by rw [hqdne i hia] at hdi; exact hdi)
  · -- king_pile
    intro i hdi
    by_cases hia : i = a
    · subst hia; exact hqk
    · rw [hqdne i hia] at hdi
      intro d hd
      rw [hqkne i hia hdi d hd]
      exact h.king_pile i hdi d hd
  · -- aces_match
    intro su
    rw [hqaces]
    exact h.aces_match su

/-! ## The merge: no card moves either

The merge lowers `pileDepth` and raises `pileFlute` by the same amount, so the
column length is still `pileDepth + pileFlute - 1`; what has to be re-checked is
`depth_match`, whose `PileMatches` witness now has to treat the merged dealt cards
as flute.  That is exactly the condition the merge loop tests. -/

/-- From `x = y + 1` on real card codes: same suit, value one higher. -/
private theorem succ_code {x y : UInt8} (hy : IsRealCard y) (h : x = y + 1) :
    SUIT x = SUIT y ∧ (VALUE x).toNat = (VALUE y).toNat + 1 := by
  have hy61 : y.toNat ≤ 61 := by
    have h1 := hy.1; have h2 := hy.2.2
    have h3 := SUIT_toNat y; have h4 := VALUE_toNat y
    omega
  have hxn : x.toNat = y.toNat + 1 := by
    rw [h, UInt8.toNat_add, show ((1 : UInt8).toNat = 1) from rfl]
    omega
  have hsx := SUIT_toNat x; have hvx := VALUE_toNat x
  have hsy := SUIT_toNat y; have hvy := VALUE_toNat y
  have hv13 := hy.2.2
  refine ⟨UInt8.toNat_inj.mp (by omega), by omega⟩

/-- **The merge chain descends by one, within one suit.** -/
private theorem merge_chain {g : Globals} {a : Fin 10} {n₁ n₀ : Nat}
    (hwf : WellFormedLayout g) (h5 : n₀ ≤ 5) (h1 : 1 ≤ n₁) (hle : n₁ ≤ n₀)
    (hchain : ∀ j, n₁ ≤ j → j < n₀ → ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get a).get ⟨j - 1, hj1⟩ = (g.pos2card.get a).get ⟨j, hj⟩ + 1) :
    ∀ t, n₁ - 1 + t ≤ n₀ - 1 → ∀ (ht : n₁ - 1 + t < 5) (hb : n₁ - 1 < 5),
      SUIT ((g.pos2card.get a).get ⟨n₁ - 1 + t, ht⟩)
          = SUIT ((g.pos2card.get a).get ⟨n₁ - 1, hb⟩) ∧
        (VALUE ((g.pos2card.get a).get ⟨n₁ - 1 + t, ht⟩)).toNat + t
          = (VALUE ((g.pos2card.get a).get ⟨n₁ - 1, hb⟩)).toNat := by
  intro t
  induction t with
  | zero => intro _ ht hb; exact ⟨by congr 1, by simp⟩
  | succ t ih =>
    intro hlt ht hb
    have ht' : n₁ - 1 + t < 5 := by omega
    obtain ⟨hs, hv⟩ := ih (by omega) ht' hb
    -- one more chain step, at `j = n₁ + t`
    have hj : n₁ + t < 5 := by omega
    have hj1 : n₁ + t - 1 < 5 := by omega
    have hstep := hchain (n₁ + t) (by omega) (by omega) hj1 hj
    have hi1 : (⟨n₁ + t - 1, hj1⟩ : Fin 5) = ⟨n₁ - 1 + t, ht'⟩ :=
      Fin.ext (show n₁ + t - 1 = n₁ - 1 + t from by omega)
    have hi2 : (⟨n₁ + t, hj⟩ : Fin 5) = ⟨n₁ - 1 + (t + 1), ht⟩ :=
      Fin.ext (show n₁ + t = n₁ - 1 + (t + 1) from by omega)
    rw [hi1, hi2] at hstep
    obtain ⟨hs2, hv2⟩ := succ_code (hwf.pos2card_real a _) hstep
    exact ⟨by rw [← hs, ← hs2], by omega⟩

/-- **Lowering a `PileMatches` witness along the merge chain.** -/
theorem PileMatches_lower {g : Globals} {col : Column} {a : Fin 10} {n₀ n₁ : Fin 6}
    (hwf : WellFormedLayout g) (hm : PileMatches g col a n₀)
    (h1 : 1 ≤ n₁.val) (hle : n₁.val ≤ n₀.val)
    (hchain : ∀ j, n₁.val ≤ j → j < n₀.val → ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get a).get ⟨j - 1, hj1⟩ = (g.pos2card.get a).get ⟨j, hj⟩ + 1) :
    PileMatches g col a n₁ := by
  obtain ⟨hlen, hbot, hflute⟩ := hm
  have h5 : n₀.val ≤ 5 := by have := n₀.isLt; omega
  have hb : n₁.val - 1 < 5 := by omega
  have hb0 : n₀.val - 1 < 5 := by omega
  set B₁ := (g.pos2card.get a).get ⟨n₁.val - 1, hb⟩ with hB₁
  refine ⟨by omega, fun k => hbot ⟨k.val, by omega⟩, ?_⟩
  rw [dif_pos (show n₁.val > 0 from by omega)]
  have hchain' := merge_chain hwf h5 h1 hle hchain
  -- the old flute part, and the merged dealt cards, both descend from `B₁`
  obtain ⟨hs0, hv0⟩ := hchain' (n₀.val - n₁.val) (by omega) (by omega) hb
  rw [← hB₁] at hs0 hv0
  have hidx0 : (⟨n₁.val - 1 + (n₀.val - n₁.val), by omega⟩ : Fin 5) = ⟨n₀.val - 1, hb0⟩ :=
    Fin.ext (show n₁.val - 1 + (n₀.val - n₁.val) = n₀.val - 1 from by omega)
  rw [hidx0] at hs0 hv0
  have hfl : IsSameSuitDescending (SUIT ((g.pos2card.get a).get ⟨n₀.val - 1, hb0⟩))
      ((VALUE ((g.pos2card.get a).get ⟨n₀.val - 1, hb0⟩)).toNat - 1)
      ((col.reverse.drop n₀.val).map encodeCard) := by
    have := hflute
    rw [dif_pos (show n₀.val > 0 from by omega)] at this
    exact this
  show IsSameSuitDescending (SUIT B₁) ((VALUE B₁).toNat - 1)
    ((col.reverse.drop n₁.val).map encodeCard)
  intro i
  obtain ⟨t, htlt0⟩ := i
  have hlenlist : ((col.reverse.drop n₁.val).map encodeCard).length = col.length - n₁.val := by
    simp
  have htlt : t < col.length - n₁.val := by rw [hlenlist] at htlt0; exact htlt0
  have htcol : n₁.val + t < col.length := by omega
  have hrev : n₁.val + t < col.reverse.length := by
    simp only [List.length_reverse]; omega
  have hget : ((col.reverse.drop n₁.val).map encodeCard)[t]
      = encodeCard (col.reverse[n₁.val + t]'hrev) := by
    rw [List.getElem_map, List.getElem_drop]
  simp only [List.get_eq_getElem, hget]
  by_cases hsplit : n₁.val + t < n₀.val
  · -- still a dealt card: its code is `pos2card[a][n₁ + t]`
    have hk := hbot ⟨n₁.val + t, hsplit⟩
    rw [List.getElem?_eq_getElem hrev, Option.map_some] at hk
    have hn1t : n₁.val + t < 5 := by omega
    have hcode : encodeCard (col.reverse[n₁.val + t]'hrev)
        = (g.pos2card.get a).get ⟨n₁.val + t, hn1t⟩ := Option.some.inj hk
    obtain ⟨hs, hv⟩ := hchain' (t + 1) (by omega) (by omega) hb
    have hidx : (⟨n₁.val - 1 + (t + 1), (by omega : n₁.val - 1 + (t + 1) < 5)⟩ : Fin 5)
        = ⟨n₁.val + t, hn1t⟩ :=
      Fin.ext (show n₁.val - 1 + (t + 1) = n₁.val + t from by omega)
    rw [hidx, ← hB₁] at hs hv
    rw [hcode]
    exact ⟨hs, by omega⟩
  · -- an old flute card: shift the index into the `n₀` flute list
    have hge : n₀.val ≤ n₁.val + t := by omega
    have hidx2 : (n₁.val + t) - n₀.val < ((col.reverse.drop n₀.val).map encodeCard).length := by
      simp only [List.length_map, List.length_drop, List.length_reverse]
      omega
    obtain ⟨hs, hv⟩ := hfl ⟨(n₁.val + t) - n₀.val, hidx2⟩
    have hget2 : ((col.reverse.drop n₀.val).map encodeCard)[(n₁.val + t) - n₀.val]
        = encodeCard (col.reverse[n₁.val + t]'hrev) := by
      rw [List.getElem_map, List.getElem_drop]
      congr 2
      omega
    simp only [List.get_eq_getElem, hget2] at hs hv
    refine ⟨by rw [hs, hs0], ?_⟩
    have hV1 : 1 ≤ (VALUE (encodeCard (col.reverse[n₁.val + t]'hrev))).toNat := by
      rw [encodeCard_VALUE]; exact rankToNat_pos _
    omega

/-- **The merge moves no card.**  It lowers `pileDepth[a]` and raises `pileFlute[a]`
by the same amount, on the *same* state: the column is untouched, and the merged
dealt cards are re-read as flute cards, which `PileMatches_lower` justifies from the
very equalities the merge loop tests. -/
theorem StateMatchesSolverPos.cleanupMerge {g : Globals} {s : State} {p q : SolverPosType}
    (hwf : WellFormedLayout g) (h : StateMatchesSolverPos g s p) (a : Fin 10)
    (h1 : 1 ≤ (q.pileDepth.get a).toNat)
    (hle : (q.pileDepth.get a).toNat ≤ (p.pileDepth.get a).toNat)
    (hchain : ∀ j, (q.pileDepth.get a).toNat ≤ j →
      j < (p.pileDepth.get a).toNat → ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get a).get ⟨j - 1, hj1⟩ = (g.pos2card.get a).get ⟨j, hj⟩ + 1)
    (hsum : (q.pileDepth.get a).toNat + (q.pileFlute.get a).toNat
      = (p.pileDepth.get a).toNat + (p.pileFlute.get a).toNat)
    (hqdne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i)
    (hqfne : ∀ i : Fin 10, i ≠ a → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces) (hqkings : q.kings = p.kings) :
    StateMatchesSolverPos g s q := by
  have hp6 := h.depth_lt6 a
  have hlt6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6 := by
    intro i
    by_cases hia : i = a
    · subst hia; omega
    · rw [hqdne i hia]; exact h.depth_lt6 i
  refine ⟨h.cards_count, hlt6, ?_, ?_, ?_, ?_⟩
  · -- depth_match: the merged dealt cards become flute cards
    intro i
    by_cases hia : i = a
    · subst hia
      exact PileMatches_lower hwf (h.depth_match i) h1 hle hchain
    · have hidx : (⟨(q.pileDepth.get i).toNat, hlt6 i⟩ : Fin 6)
          = ⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ := by simp only [hqdne i hia]
      rw [hidx]
      exact h.depth_match i
  · -- flute_match: `depth + flute` is unchanged
    intro i hdi
    by_cases hia : i = a
    · subst hia
      have hfm := h.flute_match i (by omega)
      omega
    · rw [hqdne i hia, hqfne i hia]
      exact h.flute_match i (by rw [hqdne i hia] at hdi; exact hdi)
  · -- king_pile: `a` is still non-empty
    intro i hdi
    by_cases hia : i = a
    · subst hia; omega
    · rw [hqdne i hia] at hdi
      rw [hqkings]
      exact h.king_pile i hdi
  · intro su
    rw [hqaces]
    exact h.aces_match su

/-! ## Where the extension cards are

`cleanupExtend` needs the returned cards to be *in cells*.  A card is somewhere —
`cards_count = 1` — so it is on a foundation, in a cell, or in a column, and the
other two are excluded:

* not on a foundation, because the loop guard `aces[suit] < prevCard` puts it above
  the foundation top (`not_covered`);
* not in a column, because a column holds only resident dealt cards (not free), the
  flute cards above the boundary, and — on a solver-empty pile — a king run.
  `column_cases` says which of the three a card in a column is, *with its code
  identified*, so that the exclusions become arithmetic on card codes. -/

/-- A card is on a foundation, in a cell, or in some column. -/
theorem NoDupState.location {s : State} (hnd : ∀ c : Card, countState s c = 1) (d : Card) :
    countFoundation s.foundations d = 1 ∨ (∃ i : Fin 4, s.cells i = some d) ∨
      (∃ j : Fin 10, d ∈ s.tableau j) := by
  have h1 := hnd d
  unfold countState at h1
  by_cases hf : countFoundation s.foundations d = 1
  · exact Or.inl hf
  by_cases hc : countCells s.cells d = 0
  · -- it must be in the tableau
    refine Or.inr (Or.inr ?_)
    by_contra hcon
    push Not at hcon
    have hzero : countTableau s.tableau d = 0 := by
      unfold countTableau
      refine List.sum_eq_zero (fun x hx => ?_)
      simp only [List.mem_ofFn] at hx
      obtain ⟨j, rfl⟩ := hx
      unfold countColumn
      refine List.sum_eq_zero (fun y hy => ?_)
      simp only [List.mem_map] at hy
      obtain ⟨e, hemem, rfl⟩ := hy
      have hne : e ≠ d := fun heq => hcon j (heq ▸ hemem)
      simp only [countCard, Option.some.injEq]
      rw [if_neg hne]
    have hf0 : countFoundation s.foundations d = 0 := by
      unfold countFoundation at hf ⊢; split at hf <;> simp_all
    omega
  · -- it is in a cell
    refine Or.inr (Or.inl ?_)
    by_contra hcon
    push Not at hcon
    apply hc
    unfold countCells
    refine List.sum_eq_zero (fun x hx => ?_)
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    cases hci : s.cells i with
    | none => simp [countCard]
    | some e =>
      have hne : ¬ (some e = some d) := by
        intro heq
        exact hcon i (hci.trans heq)
      simp only [countCard]
      rw [if_neg hne]

/-- **A card above its suit's foundation top is not covered by the foundation.** -/
theorem StateMatchesSolverPos.not_covered {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (d : Card)
    (hs : (SUIT (encodeCard d)).toNat < 4)
    (haces : p.aces.get ⟨(SUIT (encodeCard d)).toNat, hs⟩ < encodeCard d) :
    countFoundation s.foundations d ≠ 1 := by
  have hsu : suitToNat d.suit < 4 := suitToNat_lt _
  have hsuit : (SUIT (encodeCard d)).toNat = suitToNat d.suit := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat']; omega
  have hidx : (⟨(SUIT (encodeCard d)).toNat, hs⟩ : Fin 4) = finOfSuit d.suit := Fin.ext hsuit
  rw [hidx, h.aces_match d.suit, UInt8.lt_iff_toNat_lt] at haces
  have hr13 : rankToNat d.rank ≤ 13 := rankBounded _
  have hf13 : optRankToNat (s.foundations d.suit) ≤ 13 := by
    cases hf : s.foundations d.suit with
    | none => simp [optRankToNat]
    | some r => simpa [optRankToNat] using rankBounded r
  rw [show (encodeFoundation d.suit (s.foundations d.suit))
      = CARD (UInt8.ofNat (suitToNat d.suit))
        (UInt8.ofNat (optRankToNat (s.foundations d.suit))) from rfl,
    CARD_toNat (by omega) (by omega), encodeCard,
    CARD_toNat (by omega) (by omega)] at haces
  unfold countFoundation
  rw [if_pos (by omega)]
  omega

/-- **What a card in a column is**: a resident dealt card (hence not free), or the
`m`-th flute card above the pile's boundary for some `1 ≤ m < pileFlute`, or a card
of a solver-empty pile's king run (whose length pins `kings` for that suit). -/
theorem StateMatchesSolverPos.column_cases {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (j : Fin 10) {d : Card} (hmem : d ∈ s.tableau j) :
    (¬ isFreeCard g p (encodeCard d)) ∨
      (∃ (m : Nat) (hidx : (p.pileDepth.get j).toNat - 1 < 5),
        1 ≤ m ∧ m < (p.pileFlute.get j).toNat ∧
        encodeCard d = (g.pos2card.get j).get ⟨_, hidx⟩ - UInt8.ofNat m) ∨
      ((p.pileDepth.get j).toNat = 0 ∧
        (VALUE (p.kings.get (finOfSuit d.suit))).toNat < (VALUE (encodeCard d)).toNat) := by
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hrevlt : (s.tableau j).length - 1 - idx < (s.tableau j).reverse.length := by
    simp only [List.length_reverse]; omega
  have hrev : (s.tableau j).reverse[(s.tableau j).length - 1 - idx]'hrevlt = d := by
    rw [List.getElem_reverse hrevlt, ← hidxeq]
    congr 1
    omega
  by_cases hd0 : (p.pileDepth.get j).toNat = 0
  · -- solver-empty pile: the column is one suit's king run
    refine Or.inr (Or.inr ⟨hd0, ?_⟩)
    have hne : s.tableau j ≠ [] := by
      intro hnil; rw [hnil] at hidxlt; simp at hidxlt
    obtain ⟨e, he⟩ : ∃ e, (s.tableau j).getLast? = some e := by
      cases hl : (s.tableau j).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
      | some e => exact ⟨e, rfl⟩
    obtain ⟨hlen, hcont⟩ := h.king_pile_contents j hd0 he
    have hcode := hcont ((s.tableau j).length - 1 - idx) hrevlt
    rw [hrev] at hcode
    -- `d` carries the run's suit, so `hlen` is already the claim
    have hsu : suitToNat e.suit < 4 := suitToNat_lt _
    have hsd : suitToNat d.suit < 4 := suitToNat_lt _
    have h13 : 13 - ((s.tableau j).length - 1 - idx) < 16 := by omega
    have h3 : (encodeCard d).toNat = suitToNat e.suit * 16
        + (13 - ((s.tableau j).length - 1 - idx)) := by
      rw [hcode, CARD_toNat (by omega) (by omega)]
    have h4 := SUIT_toNat (encodeCard d)
    have h5 := VALUE_toNat (encodeCard d)
    have hrb := rankBounded d.rank
    have hrp := rankToNat_pos d.rank
    have h6 : (encodeCard d).toNat = suitToNat d.suit * 16 + rankToNat d.rank := by
      rw [encodeCard, CARD_toNat (by omega) (by omega)]
    have h7 : suitToNat d.suit = suitToNat e.suit := by omega
    have hsame : d.suit = e.suit := by
      rw [← natToSuit_suitToNat d.suit, ← natToSuit_suitToNat e.suit]
      exact congrArg natToSuit (Fin.ext h7)
    rw [hsame]
    have h8 := VALUE_toNat (encodeCard d)
    omega
  · -- non-empty pile
    have hdpos : 0 < (p.pileDepth.get j).toNat := by omega
    have hidx5 : (p.pileDepth.get j).toNat - 1 < 5 := by
      have := h.depth_lt6 j; omega
    have hnL : (p.pileDepth.get j).toNat ≤ (s.tableau j).length := (h.depth_match j).1
    by_cases hres : (s.tableau j).length - (p.pileDepth.get j).toNat ≤ idx
    · -- resident dealt card: not free
      left
      obtain ⟨_, hbot, _⟩ := h.depth_match j
      have hk : (s.tableau j).length - 1 - idx < (p.pileDepth.get j).toNat := by omega
      have hkb := hbot ⟨(s.tableau j).length - 1 - idx, hk⟩
      rw [List.getElem?_eq_getElem hrevlt, Option.map_some, hrev] at hkb
      have hslot : encodeCard d = (g.pos2card.get j).get
          ⟨(s.tableau j).length - 1 - idx, by omega⟩ := Option.some.inj hkb
      rw [hslot]
      exact depth_card_not_free hwf hb j ⟨(s.tableau j).length - 1 - idx, by omega⟩
        (by simpa using hk)
    · -- flute card, `m = L - depth - idx` above the boundary
      right; left
      have hfm := h.flute_match j hdpos
      obtain ⟨hs, hv⟩ := flute_elem h j hdpos ⟨_, hidx5⟩ rfl idx (by omega) hidxlt
      rw [hidxeq] at hs hv
      refine ⟨(s.tableau j).length - (p.pileDepth.get j).toNat - idx, hidx5,
        by omega, by omega, ?_⟩
      -- same suit, value `m` lower ⇒ the code is `boundary - m`
      set B := (g.pos2card.get j).get
        (⟨(p.pileDepth.get j).toNat - 1, hidx5⟩ : Fin 5) with hBdef
      set m := (s.tableau j).length - (p.pileDepth.get j).toNat - idx with hmdef
      have hVd : 1 ≤ (VALUE (encodeCard d)).toNat := by
        rw [encodeCard_VALUE]; exact rankToNat_pos _
      have hmof : (UInt8.ofNat m).toNat = m := by
        rw [UInt8.toNat_ofNat']
        have := VALUE_toNat B
        omega
      have hle : (UInt8.ofNat m) ≤ B := by
        rw [UInt8.le_iff_toNat_le, hmof]
        have := VALUE_toNat B
        omega
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_sub_of_le _ _ hle, hmof]
      have h1 := SUIT_toNat (encodeCard d)
      have h2 := VALUE_toNat (encodeCard d)
      have h3 := SUIT_toNat B
      have h4 := VALUE_toNat B
      have h5 := congrArg UInt8.toNat hs
      omega

/-- **The freed predecessors the extension loop walks are in cells.**

`B` is the pile's boundary (not free), `B - 1 … B - f` are the free cards the loop
accepted, all above the suit's foundation top, and `hBflute1` says the pile whose
boundary is `B` has a trivial flute — which is exactly the state cleanup is called
in.  Then the card at `B - k` is in a cell: it is somewhere, it is not on a
foundation, and each of the three ways of being in a column is excluded. -/
theorem StateMatchesSolverPos.extension_in_cell {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {B : UInt8} (hBreal : IsRealCard B) (hBnotfree : ¬ isFreeCard g p B)
    (hBflute1 : ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
        ∀ hidx : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨_, hidx⟩ = B → p.pileFlute.get j = 1)
    {f : Nat} (hf : f + 1 ≤ (VALUE B).toNat)
    (hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g p (B - UInt8.ofNat l))
    (haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
      p.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l)
    {k : Nat} (hk1 : 1 ≤ k) (hkf : k ≤ f)
    {d : Card} (hd : encodeCard d = B - UInt8.ofNat k) :
    ∃ i : Fin 4, s.cells i = some d := by
  have hVB := VALUE_toNat B
  have hSB := SUIT_toNat B
  have hs4 : (SUIT B).toNat < 4 := hBreal.1
  have hkof : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
  have hkle : (UInt8.ofNat k) ≤ B := by rw [UInt8.le_iff_toNat_le, hkof]; omega
  have hdnat : (encodeCard d).toNat = B.toNat - k := by
    rw [hd, UInt8.toNat_sub_of_le _ _ hkle, hkof]
  have hdS : (SUIT (encodeCard d)).toNat = (SUIT B).toNat := by
    rw [SUIT_toNat, SUIT_toNat, hdnat]; omega
  have hdV : (VALUE (encodeCard d)).toNat = (VALUE B).toNat - k := by
    rw [VALUE_toNat, VALUE_toNat, hdnat]; omega
  rcases NoDupState.location h.cards_count d with hfound | hcell | ⟨j, hmem⟩
  · -- not on a foundation: the loop guard put it above `aces[suit]`
    refine absurd hfound (h.not_covered d (by omega) ?_)
    have hidx : (⟨(SUIT (encodeCard d)).toNat,
        (show (SUIT (encodeCard d)).toNat < 4 by omega)⟩ : Fin 4) = ⟨(SUIT B).toNat, hs4⟩ :=
      Fin.ext hdS
    rw [hidx, hd]
    exact haces k hk1 hkf hs4
  · exact hcell
  · -- not in a column
    exfalso
    rcases h.column_cases hwf hb j hmem with hnf | ⟨m, hidx, hm1, hm2, hcode⟩ | ⟨hd0, hkv⟩
    · -- resident: but the card is free
      exact hnf (hd ▸ hfree k hk1 hkf)
    · -- a flute card of pile `j`: compare `m` with `k`
      have hdj : 0 < (p.pileDepth.get j).toNat := by
        by_contra hz
        have h0 : p.pileDepth.get j = 0 := by
          apply UInt8.toNat_inj.mp
          simpa using (by omega : (p.pileDepth.get j).toNat = 0)
        rw [(hb.pileBase j).flute_empty h0,
          show ((1 : UInt8).toNat = 1) from rfl] at hm2
        omega
      have hdjn : (p.pileDepth.get j).toNat > 0 := by simpa using hdj
      have hBjreal : IsRealCard ((g.pos2card.get j).get ⟨_, hidx⟩) := hwf.pos2card_real j _
      have hBjnotfree : ¬ isFreeCard g p ((g.pos2card.get j).get ⟨_, hidx⟩) :=
        boundary_not_free hwf hb j hdjn
      have hflv : (p.pileFlute.get j).toNat
          ≤ (VALUE ((g.pos2card.get j).get ⟨_, hidx⟩)).toNat := hb.flute_le_value hwf j hdjn
      have hVBj := VALUE_toNat ((g.pos2card.get j).get ⟨_, hidx⟩)
      have hSBj := SUIT_toNat ((g.pos2card.get j).get ⟨_, hidx⟩)
      have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
      have hmle : (UInt8.ofNat m) ≤ (g.pos2card.get j).get ⟨_, hidx⟩ := by
        rw [UInt8.le_iff_toNat_le, hmof]; omega
      have hcnat : (encodeCard d).toNat
          = ((g.pos2card.get j).get ⟨_, hidx⟩).toNat - m := by
        rw [hcode, UInt8.toNat_sub_of_le _ _ hmle, hmof]
      have hkey : ((g.pos2card.get j).get ⟨_, hidx⟩).toNat + k = B.toNat + m := by omega
      rcases Nat.lt_trichotomy m k with hlt | heq | hgt
      · -- `B_j` is one of the free extension cards, but boundaries are not free
        have hof : (UInt8.ofNat (k - m)).toNat = k - m := by rw [UInt8.toNat_ofNat']; omega
        have hle2 : (UInt8.ofNat (k - m)) ≤ B := by rw [UInt8.le_iff_toNat_le, hof]; omega
        have hBjeq : (g.pos2card.get j).get ⟨_, hidx⟩ = B - UInt8.ofNat (k - m) := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hle2, hof]
          omega
        exact hBjnotfree (hBjeq ▸ hfree (k - m) (by omega) (by omega))
      · -- `B_j = B`, so pile `j` is the one being cleaned and its flute is trivial
        have hBjB : (g.pos2card.get j).get ⟨_, hidx⟩ = B := UInt8.toNat_inj.mp (by omega)
        rw [hBflute1 j hdj hidx hBjB, show ((1 : UInt8).toNat = 1) from rfl] at hm2
        omega
      · -- `B` would be one of `j`'s flute interiors, hence free
        have hof : (UInt8.ofNat (m - k)).toNat = m - k := by rw [UInt8.toNat_ofNat']; omega
        have hle2 : (UInt8.ofNat (m - k)) ≤ (g.pos2card.get j).get ⟨_, hidx⟩ := by
          rw [UInt8.le_iff_toNat_le, hof]; omega
        have hBeq : B = (g.pos2card.get j).get ⟨_, hidx⟩ - UInt8.ofNat (m - k) := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hle2, hof]
          omega
        exact hBnotfree (hBeq ▸ hb.flute_cards_free j (UInt8.ofNat (m - k)) hdjn
          (by rw [hof]; omega) (by rw [hof]; omega))
    · -- a king-run card: its value would exceed the frontier, but it is below `B`
      have hsuitd : suitToNat d.suit = (SUIT B).toNat := by
        have he := encodeCard_SUIT d
        have h1 : (SUIT (encodeCard d)).toNat = suitToNat d.suit := by
          rw [he, UInt8.toNat_ofNat']
          have := suitToNat_lt d.suit
          omega
        omega
      have hidxsu : finOfSuit d.suit = (⟨(SUIT B).toNat, hs4⟩ : Fin 4) := Fin.ext hsuitd
      rw [hidxsu] at hkv
      -- `B` is not free, so it does not exceed its suit's frontier
      have hsuitB : SUIT B = ((⟨(SUIT B).toNat, hs4⟩ : Fin 4).val).toUInt8 := by
        show SUIT B = ((SUIT B).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      have hle : (VALUE B).toNat
          ≤ (VALUE (p.kings.get ⟨(SUIT B).toNat, hs4⟩)).toNat := by
        by_contra hgt
        exact hBnotfree ((hb.king_frontier ⟨(SUIT B).toNat, hs4⟩).2 B hsuitB (by omega)
          hBreal.2.2)
      omega

/-! ## Composing a whole cleanup

`cleanupPile_nonempty_eq` gives the run's result as
`cleanupRunResult pile hpile B ph hs4 d32 m f p`, with `m` merge steps and `f` freed
predecessors.  Its matching-relevant fields are read off below, and the simulation
then composes `cleanupMerge` (no moves) with `cleanupExtend` (the `f` cell→pile
moves). -/

/-- A cell listed in a `HoldsCards` witness holds one of the listed cards. -/
private theorem holdsCards_mem {s : State} : ∀ (cells : List (Fin 4)) (ds : List Card),
    HoldsCards s.cells cells ds → ∀ i ∈ cells, ∃ e ∈ ds, s.cells i = some e
  | [], [], _, i, hi => by simp at hi
  | _ :: _, [], h, _, _ => h.elim
  | [], _ :: _, h, _, _ => h.elim
  | c :: cs, d :: ds, h, i, hi => by
    rcases List.mem_cons.1 hi with rfl | hi'
    · exact ⟨d, by simp, h.1⟩
    · obtain ⟨e, he, hce⟩ := holdsCards_mem cs ds h.2 i hi'
      exact ⟨e, by simp [he], hce⟩

/-- Cards known to be in *some* cell can be lined up with a `Nodup` cell list. -/
theorem holdsCards_of_mem_cells {s : State} :
    ∀ ds : List Card, ds.Nodup → (∀ d ∈ ds, ∃ i : Fin 4, s.cells i = some d) →
      ∃ cells : List (Fin 4), cells.Nodup ∧ HoldsCards s.cells cells ds := by
  intro ds
  induction ds with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, trivial⟩
  | cons d ds ih =>
    intro hnodup hmem
    obtain ⟨i, hi⟩ := hmem d (by simp)
    obtain ⟨cells, hcnd, hhold⟩ := ih (List.nodup_cons.1 hnodup).2
      (fun e he => hmem e (by simp [he]))
    refine ⟨i :: cells, List.nodup_cons.2 ⟨fun hmemi => ?_, hcnd⟩, hi, hhold⟩
    obtain ⟨e, he, hce⟩ := holdsCards_mem cells ds hhold i hmemi
    exact (List.nodup_cons.1 hnodup).1 ((Option.some.inj (hi.symm.trans hce)) ▸ he)

/-- **`cleanupRunResult`'s matching-relevant fields, ordinary (no lone-king)
branch.**  `hash`/`usedSpace`/`busyAces` are untouched by matching, so only these
four matter. -/
theorem cleanupRunResult_fields_ordinary (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d32 : UInt8) (m f : Nat) (p : SolverPosType)
    (hnk : ¬ ((d32 - UInt8.ofNat m == 1) && (VALUE (B + UInt8.ofNat m) == 13)) = true) :
    (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.pileDepth
        = p.pileDepth.set pile.toNat (d32 - UInt8.ofNat m) hpile ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.pileFlute
        = p.pileFlute.set pile.toNat
            (1 + UInt8.ofNat m + UInt8.ofNat f) hpile ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.aces = p.aces ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.kings = p.kings := by
  unfold cleanupRunResult
  rw [if_neg hnk]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### The extension cards as `Card`s

The solver names the returned predecessors by *code* (`B - 1 … B - f`); the moves
need them as `Card`s, in column order (`B - f` ends up on top). -/

/-- Every real code is some card's code. -/
theorem exists_encodeCard {c : UInt8} (h : IsRealCard c) : ∃ d : Card, encodeCard d = c := by
  obtain ⟨hs, hv1, hv13⟩ := h
  have hvn := VALUE_toNat c
  have hsn := SUIT_toNat c
  obtain ⟨r, hr⟩ : ∃ r : Rank, rankToNat r = (VALUE c).toNat := by
    have h1 : 1 ≤ (VALUE c).toNat := hv1
    have h2 : (VALUE c).toNat ≤ 13 := hv13
    interval_cases h : (VALUE c).toNat
    exacts [⟨Rank.ace, rfl⟩, ⟨Rank.two, rfl⟩, ⟨Rank.three, rfl⟩, ⟨Rank.four, rfl⟩,
      ⟨Rank.five, rfl⟩, ⟨Rank.six, rfl⟩, ⟨Rank.seven, rfl⟩, ⟨Rank.eight, rfl⟩,
      ⟨Rank.nine, rfl⟩, ⟨Rank.ten, rfl⟩, ⟨Rank.jack, rfl⟩, ⟨Rank.queen, rfl⟩,
      ⟨Rank.king, rfl⟩]
  refine ⟨⟨natToSuit ⟨(SUIT c).toNat, hs⟩, r⟩, ?_⟩
  have hsu : suitToNat (natToSuit ⟨(SUIT c).toNat, hs⟩) = (SUIT c).toNat :=
    suitToNat_natToSuit ⟨(SUIT c).toNat, hs⟩
  apply UInt8.toNat_inj.mp
  show (CARD (UInt8.ofNat (suitToNat (natToSuit ⟨(SUIT c).toNat, hs⟩)))
      (UInt8.ofNat (rankToNat r))).toNat = c.toNat
  rw [CARD_toNat (by rw [hsu]; omega) (by omega), hsu, hr]
  omega

/-- Stepping down inside one suit block. -/
private theorem sub_code_facts {B : UInt8} (hB : IsRealCard B) {k : Nat}
    (hk : k + 1 ≤ (VALUE B).toNat) :
    IsRealCard (B - UInt8.ofNat k) ∧ SUIT (B - UInt8.ofNat k) = SUIT B ∧
      (VALUE (B - UInt8.ofNat k)).toNat = (VALUE B).toNat - k := by
  have hvn := VALUE_toNat B
  have hsn := SUIT_toNat B
  have hs4 := hB.1
  have hv13 := hB.2.2
  have hkof : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
  have hkle : (UInt8.ofNat k) ≤ B := by rw [UInt8.le_iff_toNat_le, hkof]; omega
  have hnat : (B - UInt8.ofNat k).toNat = B.toNat - k := by
    rw [UInt8.toNat_sub_of_le _ _ hkle, hkof]
  have hs : SUIT (B - UInt8.ofNat k) = SUIT B := by
    apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hnat]
    omega
  have hv : (VALUE (B - UInt8.ofNat k)).toNat = (VALUE B).toNat - k := by
    rw [VALUE_toNat, hnat]
    omega
  exact ⟨⟨by rw [hs]; exact hs4, by omega, by omega⟩, hs, hv⟩

/-- Subtracting within the value nibble, without demanding the result be a real
card: a whole freed suit lands on the `VALUE = 0` sentinel. -/
private theorem sub_value {B : UInt8} (hB : IsRealCard B) {k : Nat}
    (hk : k ≤ (VALUE B).toNat) :
    (VALUE (B - UInt8.ofNat k)).toNat = (VALUE B).toNat - k := by
  have hvn := VALUE_toNat B
  have hsn := SUIT_toNat B
  have hs4 := hB.1
  have hv13 := hB.2.2
  have hkof : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
  have hkle : (UInt8.ofNat k) ≤ B := by rw [UInt8.le_iff_toNat_le, hkof]; omega
  rw [VALUE_toNat, UInt8.toNat_sub_of_le _ _ hkle, hkof]
  omega

/-- **The extension cards, as a list in column order.**  `ds = [B-f, …, B-1]`, a run
that continues into the card coded `B`. -/
theorem exists_extension_cards {B : UInt8} (hB : IsRealCard B) (f : Nat)
    (hf : f + 1 ≤ (VALUE B).toNat) :
    ∃ ds : List Card, ds.length = f ∧ ds.Nodup ∧
      (∀ (i : Nat) (hi : i < ds.length),
        encodeCard (ds[i]'hi) = B - UInt8.ofNat (f - i)) ∧
      (∀ e : Card, encodeCard e = B → IsRun (ds ++ [e])) := by
  have hcode : ∀ i : Fin f, ∃ d : Card, encodeCard d = B - UInt8.ofNat (f - i.val) := by
    intro i
    exact exists_encodeCard (sub_code_facts hB (by have := i.isLt; omega)).1
  choose gc hgc using hcode
  have hginj : Function.Injective gc := by
    intro i j hij
    have h1 := hgc i
    have h2 := hgc j
    rw [hij, h2] at h1
    have hfi := (sub_code_facts hB (k := f - i.val) (by have := i.isLt; omega)).2.2
    have hfj := (sub_code_facts hB (k := f - j.val) (by have := j.isLt; omega)).2.2
    rw [h1] at hfj
    have := i.isLt; have := j.isLt
    exact Fin.ext (by omega)
  refine ⟨List.ofFn gc, by simp, List.nodup_ofFn.2 hginj, ?_, ?_⟩
  · intro i hi
    simp only [List.getElem_ofFn]
    exact hgc _
  · intro e he
    refine isRun_of_getElem (fun j hj => ?_)
    simp only [List.length_append, List.length_ofFn, List.length_singleton] at hj
    have hjf : j < f := by omega
    -- the `j`-th card of the run, and its successor
    have hgetj : (List.ofFn gc ++ [e])[j] = gc ⟨j, hjf⟩ := by
      rw [List.getElem_append_left (by simp [hjf])]
      simp
    have hcj := hgc ⟨j, hjf⟩
    obtain ⟨_, hsj, hvj⟩ := sub_code_facts hB (k := f - j) (by omega)
    by_cases hlast : j + 1 = f
    · -- the successor is `e`, coded `B`
      have hget1 : (List.ofFn gc ++ [e])[j + 1] = e := by
        rw [List.getElem_append_right (by simp [hlast])]
        simp [hlast]
      rw [hgetj, hget1]
      refine nextCard_of_encode ?_ ?_
      · rw [he, hcj, hsj]
      · rw [he, hcj, hvj]
        have := hB.2.1
        omega
    · have hj1f : j + 1 < f := by omega
      have hget1 : (List.ofFn gc ++ [e])[j + 1] = gc ⟨j + 1, hj1f⟩ := by
        rw [List.getElem_append_left (by simp [hj1f])]
        simp
      have hcj1 := hgc ⟨j + 1, hj1f⟩
      obtain ⟨_, hsj1, hvj1⟩ := sub_code_facts hB (k := f - (j + 1)) (by omega)
      rw [hgetj, hget1]
      refine nextCard_of_encode ?_ ?_
      · rw [hcj, hcj1, hsj, hsj1]
      · rw [hcj, hcj1, hvj, hvj1]
        omega

/-! ## The whole cleanup, composed

`cleanupMerge` (no moves) followed by `cleanupExtend` (the `f` cell→pile moves).
The target position is given by field equations — `cleanupRunResult`'s, read off by
`cleanupRunResult_fields_ordinary`. -/

/-- **A whole non-lone-king `SolverCleanupPile` is simulated by `f` cell→pile
moves.**  `m` is the merge count and `f` the freed-predecessor count; the
hypotheses on them are what the two loop guards say. -/
theorem StateMatchesSolverPos.cleanupPileSim {g : Globals} {s : State} {p q : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {m f : Nat}
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfl1 : p.pileFlute.get ⟨pile.toNat, hpile⟩ = 1)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    -- the merge loop ran `m` times
    (hm : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hchain : ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1)
    -- the freed loop ran `f` times
    (hf : f + 1 ≤ (VALUE B).toNat)
    (hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g p (B - UInt8.ofNat l))
    (haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
      p.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l)
    (hBflute1 : ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
      ∀ hidxj : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨_, hidxj⟩ = B → p.pileFlute.get j = 1)
    -- the resulting position
    (hqd : (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m)
    (hqf : (q.pileFlute.get ⟨pile.toNat, hpile⟩).toNat = 1 + m + f)
    (hqdne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → q.pileDepth.get i = p.pileDepth.get i)
    (hqfne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces) (hqkings : q.kings = p.kings) :
    ∃ v : State, Reach s v ∧ (∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
      v.tableau i = s.tableau i) ∧ StateMatchesSolverPos g v q := by
  set a : Fin 10 := ⟨pile.toNat, hpile⟩ with hadef
  have hBreal : IsRealCard B := by rw [← hB]; exact hwf.pos2card_real a _
  -- the column is exactly the dealt cards, exposing `B`
  have hd : 0 < (p.pileDepth.get a).toNat := by omega
  obtain ⟨e, hhead, hes, hev⟩ := h.head_code a hd hidx
  rw [hB] at hes hev
  rw [hfl1, show ((1 : UInt8).toNat = 1) from rfl] at hev
  have hecode : encodeCard e = B := by
    apply UInt8.toNat_inj.mp
    have h1 := SUIT_toNat (encodeCard e)
    have h2 := VALUE_toNat (encodeCard e)
    have h3 := SUIT_toNat B
    have h4 := VALUE_toNat B
    have h5 := congrArg UInt8.toNat hes
    omega
  obtain ⟨rest, hcol⟩ : ∃ rest, s.tableau a = e :: rest := by
    cases hc : s.tableau a with
    | nil => rw [hc] at hhead; simp at hhead
    | cons x xs =>
      rw [hc] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨xs, by rw [hhead]⟩
  -- the returned predecessors, and where they are
  obtain ⟨ds, hdslen, hdsnd, hdscode, hdsrun⟩ := exists_extension_cards hBreal f hf
  have hdscell : ∀ d ∈ ds, ∃ i : Fin 4, s.cells i = some d := by
    intro d hd'
    obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hd'
    refine h.extension_in_cell hwf hb hBreal ?_ hBflute1 hf hfree haces
      (k := f - i) (by omega) (by omega) ?_
    · rw [← hB]
      exact boundary_not_free hwf hb a (by simpa using hd)
    · rw [← hieq]
      exact hdscode i hi
  obtain ⟨cells, hcnd, hhold⟩ := holdsCards_of_mem_cells ds hdsnd hdscell
  -- (1) the merge: same state, `depth ↓ m`, `flute ↑ m`
  set p₁ : SolverPosType := { p with
    pileDepth := p.pileDepth.set pile.toNat
      (UInt8.ofNat ((p.pileDepth.get a).toNat - m)) hpile,
    pileFlute := p.pileFlute.set pile.toNat (UInt8.ofNat (1 + m)) hpile } with hp₁
  have hd5 : (p.pileDepth.get a).toNat < 6 := by have := h.depth_lt6 a; simpa using this
  have hp₁d : (p₁.pileDepth.get a).toNat = (p.pileDepth.get a).toNat - m := by
    show ((p.pileDepth.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
    rw [Vector.getElem_set_self]
    simp only [UInt8.toInt_toNat, UInt8.toNat_ofNat']
    have hd5' : (p.pileDepth.get a).toNat < 6 := hd5
    omega
  have hp₁f : (p₁.pileFlute.get a).toNat = 1 + m := by
    show ((p.pileFlute.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
    rw [Vector.getElem_set_self, UInt8.toNat_ofNat']
    omega
  have hp₁dne : ∀ i : Fin 10, i ≠ a → p₁.pileDepth.get i = p.pileDepth.get i := by
    intro i hi
    show (p.pileDepth.set pile.toNat _ hpile)[i.val] = p.pileDepth[i.val]
    exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
  have hp₁fne : ∀ i : Fin 10, i ≠ a → p₁.pileFlute.get i = p.pileFlute.get i := by
    intro i hi
    show (p.pileFlute.set pile.toNat _ hpile)[i.val] = p.pileFlute[i.val]
    exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
  have hfl1n : (p.pileFlute.get a).toNat = 1 := by rw [hfl1]; rfl
  have hmatch₁ : StateMatchesSolverPos g s p₁ := by
    refine h.cleanupMerge hwf a (by omega) (by omega) ?_ (by omega) hp₁dne hp₁fne rfl rfl
    intro j hj1 hj2 hjb hjc
    exact hchain j (by omega) hj2 hjb hjc
  -- (2) the extension: `f` cell→pile moves
  have hdepthEq : q.pileDepth = p₁.pileDepth := by
    refine SolverSpec.vector_ext_get _ _ (fun i => ?_)
    by_cases hia : i = a
    · subst hia
      apply UInt8.toNat_inj.mp
      have h1 := hqd
      have h2 := hp₁d
      omega
    · rw [hqdne i hia, hp₁dne i hia]
  obtain ⟨v, hreach, _, hframe, hmatch₂⟩ := hmatch₁.cleanupExtend a hcol
    (by rw [hp₁d]; omega) hcnd hhold (hdsrun e hecode) hdepthEq
    (by rw [hp₁f, hdslen]; exact hqf)
    (fun i hi => by rw [hqfne i hi, hp₁fne i hi])
    (by rw [hqaces]) (by rw [hqkings])
  exact ⟨v, hreach, hframe, hmatch₂⟩

/-! ### The lone-king branch

When the merged boundary turns out to be a king on a depth-1 pile, cleanup vacates
the pile.  That is `cleanupPileSim` followed by `cleanupVacate` — still `f` moves in
total, since the vacate moves nothing. -/

/-- A card whose rank counts as 13 is a king. -/
theorem rank_king_of_13 {r : Rank} (h : rankToNat r = 13) : r = Rank.king := by
  cases r <;> simp_all [rankToNat]

/-- **The lone-king branch owns its suit outright.**  When cleanup's merge leaves a
single dealt card on `pile` and that card is a king (exactly the branch's own test),
that king is *physically* the deepest card of `pile`'s column — `pos2card[pile][0]` by
`merge_chain`, and `PileMatches`' bottom-`n` clause puts it at the bottom of the column.
Any *other* solver-empty pile's deepest card is its own suit's king
(`empty_pile_king`), so it cannot carry `B`'s suit: that would be one card sitting in
two columns, and every card occurs exactly once.

This is why `cleanupRunResult_sim` need not take the side condition as a hypothesis.
It would be the wrong thing to assume in general — a suit may perfectly well have its
top cards freed onto an empty column while a lower card of it is still some pile's
boundary — and it is only ever *used* in the lone-king branch, where it is free. -/
theorem StateMatchesSolverPos.noshare_of_king {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {m : Nat}
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    (hm : m + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hchain : ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1)
    (hkingval : (VALUE B).toNat + m = 13) :
    ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
      (p.pileDepth.get i).toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?, suitToNat d.suit ≠ (SUIT B).toNat := by
  set a : Fin 10 := ⟨pile.toNat, hpile⟩ with hadef
  have hd1 : 1 ≤ (p.pileDepth.get a).toNat := by omega
  have hBreal : IsRealCard B := by rw [← hB]; exact hwf.pos2card_real a _
  have hzero5 : (0 : Nat) < 5 := by omega
  have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
  -- the pile's single remaining dealt card is the suit's king (as in `cleanupPileSimKing`)
  have hkingcode : (g.pos2card.get a).get ⟨0, hzero5⟩ = B + UInt8.ofNat m := by
    have h5' : (p.pileDepth.get a).toNat ≤ 5 := by
      have := hb.pileDepth_bound a
      exact this
    obtain ⟨hcs, hcv⟩ := merge_chain (a := a) (n₀ := (p.pileDepth.get a).toNat)
      (n₁ := (p.pileDepth.get a).toNat - m) hwf h5' (by omega) (by omega)
      hchain m (by omega) (by omega) (by omega)
    have hi1 : (⟨(p.pileDepth.get a).toNat - m - 1 + m, by omega⟩ : Fin 5)
        = ⟨(p.pileDepth.get a).toNat - 1, hidx⟩ :=
      Fin.ext (show (p.pileDepth.get a).toNat - m - 1 + m
        = (p.pileDepth.get a).toNat - 1 from by omega)
    have hi2 : (⟨(p.pileDepth.get a).toNat - m - 1, by omega⟩ : Fin 5) = ⟨0, hzero5⟩ :=
      Fin.ext (show (p.pileDepth.get a).toNat - m - 1 = 0 from by omega)
    rw [hi1, hi2, hB] at hcs hcv
    apply UInt8.toNat_inj.mp
    have h1 := SUIT_toNat ((g.pos2card.get a).get ⟨0, hzero5⟩)
    have h2 := VALUE_toNat ((g.pos2card.get a).get ⟨0, hzero5⟩)
    have h3 := SUIT_toNat B
    have h4 := VALUE_toNat B
    have h5 := congrArg UInt8.toNat hcs
    have h6 : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof]
      have := hBreal.1
      omega
    omega
  -- and it is physically the deepest card of `pile`'s column
  obtain ⟨e, hemem, hesuit, herank⟩ :
      ∃ e : Card, e ∈ s.tableau a ∧ suitToNat e.suit = (SUIT B).toNat
        ∧ rankToNat e.rank = 13 := by
    obtain ⟨-, hbot, -⟩ := h.depth_match a
    have h0 : ((s.tableau a).reverse[0]?).map encodeCard
        = some ((g.pos2card.get a).get ⟨0, hzero5⟩) := hbot ⟨0, hd1⟩
    cases hr : (s.tableau a).reverse[0]? with
    | none => rw [hr] at h0; exact absurd h0 (by simp)
    | some e =>
      rw [hr] at h0
      simp only [Option.map_some] at h0
      have hecode : encodeCard e = B + UInt8.ofNat m :=
        (Option.some.inj h0).trans hkingcode
      have hcodeNat : (encodeCard e).toNat = B.toNat + m := by
        rw [hecode, UInt8.toNat_add, hmof]
        have := hBreal.1; have := SUIT_toNat B; have := VALUE_toNat B
        omega
      have hse : (SUIT (encodeCard e)).toNat = suitToNat e.suit := by
        rw [encodeCard_SUIT, UInt8.toNat_ofNat']
        have := suitToNat_lt e.suit; omega
      have hve : (VALUE (encodeCard e)).toNat = rankToNat e.rank := encodeCard_VALUE e
      have h1 := SUIT_toNat (encodeCard e); have h2 := VALUE_toNat (encodeCard e)
      have h3 := SUIT_toNat B; have h4 := VALUE_toNat B
      have h5 := hBreal.1
      exact ⟨e, List.mem_reverse.1 (List.mem_of_getElem? hr), by omega, by omega⟩
  -- a second solver-empty pile of the same suit would hold that same king
  intro i hi hdi d hd hcon
  have hdlast : (s.tableau i).getLast? = some d := hd
  have hde : d = e :=
    Card.ext (suitToNat_inj (by rw [hcon, hesuit]))
      (by rw [h.empty_pile_king i hdi hdlast, rank_king_of_13 herank])
  exact hi (h.noDup.pile_unique (hde ▸ List.mem_of_getLast? hdlast) hemem)

/-- **A whole lone-king `SolverCleanupPile` is simulated**, again by just the `f`
cell→pile moves of the extension.  `hkingval` is the branch's own test
(`VALUE (B + m) = 13`), and `hqk_self` is its `kings` write. -/
theorem StateMatchesSolverPos.cleanupPileSimKing {g : Globals} {s : State}
    {p q : SolverPosType} (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (h : StateMatchesSolverPos g s p)
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {m f : Nat}
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hfl1 : p.pileFlute.get ⟨pile.toNat, hpile⟩ = 1)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    -- the merge left exactly one dealt card, and it is a king
    (hm : m + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hchain : ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1)
    (hkingval : (VALUE B).toNat + m = 13)
    -- the freed loop ran `f` times
    (hf : f + 1 ≤ (VALUE B).toNat)
    (hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g p (B - UInt8.ofNat l))
    (haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
      p.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l)
    (hBflute1 : ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
      ∀ hidxj : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨_, hidxj⟩ = B → p.pileFlute.get j = 1)
    -- the vacated position
    (hqd : (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat = 0)
    (hqdne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → q.pileDepth.get i = p.pileDepth.get i)
    (hqfne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → q.pileFlute.get i = p.pileFlute.get i)
    (hqaces : q.aces = p.aces)
    (hqk_self : ∀ hs : (SUIT B).toNat < 4, q.kings.get ⟨(SUIT B).toNat, hs⟩
      = p.kings.get ⟨(SUIT B).toNat, hs⟩ - UInt8.ofNat (1 + m + f))
    (hqk_ne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → (p.pileDepth.get i).toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit)) :
    ∃ v : State, Reach s v ∧
      (∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → v.tableau i = s.tableau i) ∧
      StateMatchesSolverPos g v q ∧
      ∃ c ∈ (v.tableau ⟨pile.toNat, hpile⟩).getLast?,
        suitToNat c.suit = (SUIT B).toNat ∧ c.rank = Rank.king := by
  set a : Fin 10 := ⟨pile.toNat, hpile⟩ with hadef
  have hd1 : 1 ≤ (p.pileDepth.get a).toNat := by omega
  have hBreal : IsRealCard B := by rw [← hB]; exact hwf.pos2card_real a _
  have hs4 : (SUIT B).toNat < 4 := hBreal.1
  -- the pile's single remaining dealt card is the suit's king
  have hzero5 : (0 : Nat) < 5 := by omega
  have hkingcode : (g.pos2card.get a).get ⟨0, hzero5⟩ = B + UInt8.ofNat m := by
    have h5' : (p.pileDepth.get a).toNat ≤ 5 := by
      have := hb.pileDepth_bound a
      exact this
    obtain ⟨hcs, hcv⟩ := merge_chain (a := a) (n₀ := (p.pileDepth.get a).toNat)
      (n₁ := (p.pileDepth.get a).toNat - m) hwf h5' (by omega) (by omega)
      hchain m (by omega) (by omega) (by omega)
    have hi1 : (⟨(p.pileDepth.get a).toNat - m - 1 + m, by omega⟩ : Fin 5)
        = ⟨(p.pileDepth.get a).toNat - 1, hidx⟩ :=
      Fin.ext (show (p.pileDepth.get a).toNat - m - 1 + m
        = (p.pileDepth.get a).toNat - 1 from by omega)
    have hi2 : (⟨(p.pileDepth.get a).toNat - m - 1, by omega⟩ : Fin 5) = ⟨0, hzero5⟩ :=
      Fin.ext (show (p.pileDepth.get a).toNat - m - 1 = 0 from by omega)
    rw [hi1, hi2, hB] at hcs hcv
    -- same suit, value `m` higher
    apply UInt8.toNat_inj.mp
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have h1 := SUIT_toNat ((g.pos2card.get a).get ⟨0, hzero5⟩)
    have h2 := VALUE_toNat ((g.pos2card.get a).get ⟨0, hzero5⟩)
    have h3 := SUIT_toNat B
    have h4 := VALUE_toNat B
    have h5 := congrArg UInt8.toNat hcs
    have h6 : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof]
      have := hBreal.1
      omega
    omega
  have hkingv : (VALUE ((g.pos2card.get a).get ⟨0, hzero5⟩)).toNat = 13 := by
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    rw [hkingcode, VALUE_toNat, UInt8.toNat_add, hmof]
    have h4 := VALUE_toNat B
    have h3 := SUIT_toNat B
    have := hBreal.1
    omega
  -- the frontier is the king itself, since the king is still resident
  have hknotfree : ¬ isFreeCard g p ((g.pos2card.get a).get ⟨0, hzero5⟩) :=
    depth_card_not_free hwf hb a ⟨0, hzero5⟩
      (by show (0 : Nat) < (p.pileDepth.get a).toNat
          have := hd1; omega)
  have hksuit : SUIT ((g.pos2card.get a).get ⟨0, hzero5⟩) = ((SUIT B).toNat).toUInt8 := by
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    apply UInt8.toNat_inj.mp
    rw [hkingcode, SUIT_toNat, UInt8.toNat_add, hmof, UInt8.toNat_ofNat']
    have h4 := VALUE_toNat B
    have h3 := SUIT_toNat B
    have := hBreal.1
    omega
  have hkings13 : (VALUE (p.kings.get ⟨(SUIT B).toNat, hs4⟩)).toNat = 13 := by
    have hle := (hb.aces_kings_valid ⟨(SUIT B).toNat, hs4⟩).2.2.2.1
    by_contra hne
    exact hknotfree ((hb.king_frontier ⟨(SUIT B).toNat, hs4⟩).2 _ hksuit (by omega) (by omega))
  -- merge + extension, landing on the intermediate position
  set p₂ : SolverPosType := { p with
    pileDepth := p.pileDepth.set pile.toNat (UInt8.ofNat 1) hpile,
    pileFlute := p.pileFlute.set pile.toNat (UInt8.ofNat (1 + m + f)) hpile } with hp₂
  have hp₂d : (p₂.pileDepth.get a).toNat = 1 := by
    show ((p.pileDepth.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
    rw [Vector.getElem_set_self]
    simp only [UInt8.toInt_toNat, UInt8.toNat_ofNat']
  have hp₂f : (p₂.pileFlute.get a).toNat = 1 + m + f := by
    show ((p.pileFlute.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
    rw [Vector.getElem_set_self, UInt8.toNat_ofNat']
    have := hb.pileDepth_bound a
    have hfB := hBreal.2.2
    omega
  have hp₂dne : ∀ i : Fin 10, i ≠ a → p₂.pileDepth.get i = p.pileDepth.get i := by
    intro i hi
    show (p.pileDepth.set pile.toNat _ hpile)[i.val] = p.pileDepth[i.val]
    exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
  have hp₂fne : ∀ i : Fin 10, i ≠ a → p₂.pileFlute.get i = p.pileFlute.get i := by
    intro i hi
    show (p.pileFlute.set pile.toNat _ hpile)[i.val] = p.pileFlute[i.val]
    exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
  obtain ⟨v, hreach, hframe, hmatch₂⟩ := h.cleanupPileSim hwf hb hpile hidx hd1 hfl1 hB
    (by rw [← hadef]; omega) hchain hf hfree haces hBflute1 (q := p₂)
    (by rw [← hadef]; omega) hp₂f
    hp₂dne hp₂fne rfl rfl
  -- the column the vacate empties has `1 + m + f` cards, and its deepest card is
  -- the suit's king — needed both by `cleanupVacate` and by the exported fact
  have hlen : (v.tableau a).length + 1 = 1 + (1 + m + f) := by
    have := hmatch₂.flute_match a (by omega)
    rw [hp₂d, hp₂f] at this
    exact this
  have hcode : ∀ d ∈ (v.tableau a).getLast?,
      encodeCard d = (g.pos2card.get a).get ⟨0, hzero5⟩ := by
    intro d hd
    obtain ⟨_, hbotm, _⟩ := hmatch₂.depth_match a
    have hrevlt : 0 < (v.tableau a).reverse.length := by
      simp only [List.length_reverse]; omega
    have hk0 := hbotm ⟨0, by show (0 : Nat) < (p₂.pileDepth.get a).toNat; omega⟩
    rw [List.getElem?_eq_getElem hrevlt, Option.map_some] at hk0
    have hd0 : (v.tableau a).reverse[0]'hrevlt = d :=
      reverse_getElem_zero_of_getLast? (Option.mem_def.1 hd) hrevlt
    rw [hd0] at hk0
    exact Option.some.inj hk0
  have hsuitOf : ∀ d ∈ (v.tableau a).getLast?,
      finOfSuit d.suit = (⟨(SUIT B).toNat, hs4⟩ : Fin 4) := by
    intro d hd
    refine Fin.ext (show suitToNat d.suit = (SUIT B).toNat from ?_)
    have he := encodeCard_SUIT d
    have h1 : (SUIT (encodeCard d)).toNat = suitToNat d.suit := by
      rw [he, UInt8.toNat_ofNat']
      have := suitToNat_lt d.suit
      omega
    rw [hcode d hd] at h1
    have h2 := congrArg UInt8.toNat hksuit
    rw [UInt8.toNat_ofNat'] at h2
    omega
  have hexport : ∃ c ∈ (v.tableau a).getLast?,
      suitToNat c.suit = (SUIT B).toNat ∧ c.rank = Rank.king := by
    have hne : (v.tableau a) ≠ [] := by
      intro he; rw [he] at hlen; simp at hlen
    refine ⟨(v.tableau a).getLast hne, ?_, ?_, ?_⟩
    · exact Option.mem_def.2 (List.getLast?_eq_some_getLast hne)
    · exact congrArg Fin.val
        (hsuitOf _ (Option.mem_def.2 (List.getLast?_eq_some_getLast hne)))
    · refine rank_king_of_13 ?_
      rw [← encodeCard_VALUE, hcode _ (Option.mem_def.2 (List.getLast?_eq_some_getLast hne))]
      exact hkingv
  -- the vacate: no moves
  refine ⟨v, hreach, hframe, hmatch₂.cleanupVacate a hp₂d hkingv hqd ?_ ?_ (by rw [hqaces]) ?_ ?_,
    hexport⟩
  · exact fun i hi => by rw [hqdne i hi, hp₂dne i hi]
  · exact fun i hi => by rw [hqfne i hi, hp₂fne i hi]
  · -- other empty piles keep their frontier
    intro i hi hdi d hd
    rw [hp₂dne i hi] at hdi
    rw [hframe i hi] at hd
    exact hqk_ne i hi hdi d hd
  · -- the vacated pile: its column is exactly the suit's freed run
    intro d hd
    rw [hsuitOf d hd, hqk_self hs4]
    -- `kings` drops by the whole flute, whose length is the column's
    have hfB := hBreal.2.2
    have hflute13 : 1 + m + f ≤ 13 := by omega
    have hkreal : IsRealCard (p.kings.get ⟨(SUIT B).toNat, hs4⟩) := by
      refine ⟨?_, by omega, by omega⟩
      have hks := (hb.aces_kings_valid ⟨(SUIT B).toNat, hs4⟩).2.2.1
      rw [hks, UInt8.toNat_ofNat']
      omega
    have hv := sub_value hkreal (k := 1 + m + f) (by omega)
    rw [hv]
    omega

/-! ## The whole `SolverCleanupPile`, either branch

`cleanupRunResult` is what `cleanupPile_nonempty_eq` rewrites the run to, so a
simulation of it *is* a simulation of the call.  The branch test is decided here
and dispatched to `cleanupPileSim` / `cleanupPileSimKing`. -/

/-- `cleanupRunResult`'s matching-relevant fields, lone-king branch. -/
theorem cleanupRunResult_fields_king (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d32 : UInt8) (m f : Nat) (p : SolverPosType)
    (hk : ((d32 - UInt8.ofNat m == 1) && (VALUE (B + UInt8.ofNat m) == 13)) = true) :
    (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.pileDepth
        = p.pileDepth.set pile.toNat (0 : UInt8) hpile ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.pileFlute
        = p.pileFlute.set pile.toNat (1 : UInt8) hpile ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.aces = p.aces ∧
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).2.kings
        = p.kings.set (SUIT B).toUInt32.toNat
            (p.kings[(SUIT B).toUInt32.toNat]'hs4
              - (1 + UInt8.ofNat m + UInt8.ofNat f)) hs4 := by
  unfold cleanupRunResult
  rw [if_pos hk]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `Int32` addition without wraparound. -/
private theorem int32_add_toInt (a b : Int32) (h1 : -2147483648 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2147483648) : (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The depth the ordinary branch writes, as a `Nat`. -/
theorem depth1_toNat {d : UInt8} {m : Nat} (hd5 : d.toNat ≤ 5) (hm : m ≤ d.toNat) :
    ((d - UInt8.ofNat m)).toNat = d.toNat - m := by
  have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
  rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hmof]; omega), hmof]

/-- The flute the loops leave, as a `Nat`. -/
private theorem flute2_toNat {m f : Nat} (hmf : 1 + m + f ≤ 13) :
    ((1 + UInt8.ofNat m + UInt8.ofNat f)).toNat = 1 + m + f := by
  have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
  have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
  rw [UInt8.toNat_add, UInt8.toNat_add, hmof, hfof,
    show ((1 : UInt8).toNat = 1) from rfl]
  omega

/-- **A whole `SolverCleanupPile` call is simulated by the extension's `f` moves.**

The position is the solver's own `cleanupRunResult`, so composing this with
`cleanupPile_nonempty_eq` turns the monadic run into a `Reach` plus a matching fact.
`hnoshare` is the king-configuration side condition: no *other* solver-empty pile
carries `B`'s suit, so only the vacated pile's frontier moves. -/
theorem StateMatchesSolverPos.cleanupRunResult_sim {g : Globals} {s : State}
    {p : SolverPosType} (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (h : StateMatchesSolverPos g s p)
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {ph : UInt32} {m f : Nat}
    (hs4' : (SUIT B).toUInt32.toNat < 4)
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfl1 : p.pileFlute.get ⟨pile.toNat, hpile⟩ = 1)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    (hm : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hchain : ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1)
    (hf : f + 1 ≤ (VALUE B).toNat)
    (hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g p (B - UInt8.ofNat l))
    (haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
      p.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l)
    (hBflute1 : ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
      ∀ hidxj : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨_, hidxj⟩ = B → p.pileFlute.get j = 1) :
    ∃ v : State, Reach s v ∧
      (∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → v.tableau i = s.tableau i) ∧
      StateMatchesSolverPos g v
      (cleanupRunResult pile hpile B ph hs4'
        (p.pileDepth[pile.toNat]'hpile) m f p).2 ∧
      ((((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1)
          && (VALUE (B + UInt8.ofNat m) == 13)) = true →
        ∃ c ∈ (v.tableau ⟨pile.toNat, hpile⟩).getLast?,
          suitToNat c.suit = (SUIT B).toNat ∧ c.rank = Rank.king) := by
  have hs4 : (SUIT B).toNat < 4 := by rwa [UInt8.toNat_toUInt32] at hs4'
  have hBreal : IsRealCard B := by rw [← hB]; exact hwf.pos2card_real _ _
  have hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 :=
    hb.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hdd : (p.pileDepth[pile.toNat]'hpile) = p.pileDepth.get ⟨pile.toNat, hpile⟩ := rfl
  have hdn : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := rfl
  have hm' : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hm
  have hd1' : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hd1
  -- the merged boundary is a real card, which bounds the resulting flute
  have hmidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - m < 5 := by omega
  have hmerged : (VALUE B).toNat + m
      ≤ (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - m, hmidx⟩)).toNat := by
    obtain ⟨_, hcv⟩ := merge_chain (a := ⟨pile.toNat, hpile⟩)
      (n₀ := (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
      (n₁ := (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m) hwf (by omega) (by omega)
      (by omega) hchain m (by omega) (by omega) (by omega)
    have hi1 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m - 1 + m, by omega⟩
        : Fin 5) = ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx⟩ :=
      Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m - 1 + m
        = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 from by omega)
    have hi2 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m - 1, by omega⟩ : Fin 5)
        = ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - m, hmidx⟩ :=
      Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m - 1
        = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - m from by omega)
    rw [hi1, hi2, hB] at hcv
    omega
  have hmreal : IsRealCard ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - m, hmidx⟩) :=
    hwf.pos2card_real _ _
  have hmf13 : 1 + m + f ≤ 13 := by
    have := hmreal.2.2
    omega
  have hflute : ((1 + UInt8.ofNat m + UInt8.ofNat f)).toNat = 1 + m + f :=
    flute2_toNat hmf13
  by_cases hk : (((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1)
      && (VALUE (B + UInt8.ofNat m) == 13)) = true
  · -- the lone-king branch
    obtain ⟨hk1, hk2⟩ := Bool.and_eq_true .. ▸ hk
    have hdepth1 : m + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by
      have heq0 : (p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m = 1 := by
        simpa using hk1
      have heq : (p.pileDepth.get ⟨pile.toNat, hpile⟩) - UInt8.ofNat m = 1 := heq0
      have h1 := depth1_toNat (d := p.pileDepth.get ⟨pile.toNat, hpile⟩) (m := m) hd5
        (by omega)
      rw [heq] at h1
      have h2 : ((1 : UInt8)).toNat = 1 := by decide
      omega
    have hkingval : (VALUE B).toNat + m = 13 := by
      have hveq : VALUE (B + UInt8.ofNat m) = 13 := by simpa using hk2
      have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
      have h1 : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by rw [hveq]; rfl
      rw [VALUE_toNat, UInt8.toNat_add, hmof] at h1
      have h2 := VALUE_toNat B
      have h3 := SUIT_toNat B
      have h4 := hBreal.2.2
      omega
    obtain ⟨hqd, hqf, hqa, hqk⟩ := cleanupRunResult_fields_king pile hpile B ph hs4'
      (p.pileDepth[pile.toNat]'hpile) m f p hk
    have hd0 : ((cleanupRunResult pile hpile B ph hs4'
        (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get
        ⟨pile.toNat, hpile⟩).toNat = 0 := by
      rw [hqd]
      show ((p.pileDepth.set pile.toNat (0 : UInt8) hpile)[pile.toNat]'hpile).toNat = 0
      rw [Vector.getElem_set_self]
      rfl
    have hdne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get i
          = p.pileDepth.get i := by
      intro i hi
      rw [hqd]
      show (p.pileDepth.set pile.toNat _ hpile)[i.val] = p.pileDepth[i.val]
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
    have hfne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.pileFlute.get i
          = p.pileFlute.get i := by
      intro i hi
      rw [hqf]
      show (p.pileFlute.set pile.toNat _ hpile)[i.val] = p.pileFlute[i.val]
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
    have hkself : ∀ hs : (SUIT B).toNat < 4,
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.kings.get ⟨(SUIT B).toNat, hs⟩
          = p.kings.get ⟨(SUIT B).toNat, hs⟩ - UInt8.ofNat (1 + m + f) := by
      intro hs
      rw [hqk]
      show (p.kings.set (SUIT B).toUInt32.toNat _ hs4')[(SUIT B).toNat] = _
      rw [Vector.getElem_set hs4' hs, if_pos (UInt8.toNat_toUInt32 _)]
      congr 1
      apply UInt8.toNat_inj.mp
      rw [hflute, UInt8.toNat_ofNat']
      omega
    have hkne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
        (p.pileDepth.get i).toNat = 0 → ∀ d ∈ (s.tableau i).getLast?,
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.kings.get (finOfSuit d.suit)
          = p.kings.get (finOfSuit d.suit) := by
      intro i hi hdi d hd
      rw [hqk]
      show (p.kings.set (SUIT B).toUInt32.toNat _ hs4')[(finOfSuit d.suit).val] = _
      refine Vector.getElem_set_ne hs4' (finOfSuit d.suit).isLt (fun hc => ?_)
      rw [UInt8.toNat_toUInt32] at hc
      exact h.noshare_of_king hwf hb hpile hidx hB hdepth1 hchain hkingval i hi hdi d hd hc.symm
    obtain ⟨v, hreach, hframe, hmatch, hexport⟩ :=
      h.cleanupPileSimKing hwf hb hpile hidx hfl1 hB hdepth1 hchain hkingval hf hfree
        haces hBflute1 hd0 hdne hfne (by rw [hqa]) hkself hkne
    exact ⟨v, hreach, hframe, hmatch, fun _ => hexport⟩
  · -- the ordinary branch
    obtain ⟨hqd, hqf, hqa, hqk⟩ := cleanupRunResult_fields_ordinary pile hpile B ph hs4'
      (p.pileDepth[pile.toNat]'hpile) m f p hk
    have hdself : ((cleanupRunResult pile hpile B ph hs4'
        (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get
        ⟨pile.toNat, hpile⟩).toNat
        = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m := by
      rw [hqd]
      show ((p.pileDepth.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
      rw [Vector.getElem_set_self]
      exact depth1_toNat (d := p.pileDepth.get ⟨pile.toNat, hpile⟩) (m := m) hd5 (by omega)
    have hfself : ((cleanupRunResult pile hpile B ph hs4'
        (p.pileDepth[pile.toNat]'hpile) m f p).2.pileFlute.get
        ⟨pile.toNat, hpile⟩).toNat = 1 + m + f := by
      rw [hqf]
      show ((p.pileFlute.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
      rw [Vector.getElem_set_self]
      exact hflute
    have hdne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.pileDepth.get i
          = p.pileDepth.get i := by
      intro i hi
      rw [hqd]
      show (p.pileDepth.set pile.toNat _ hpile)[i.val] = p.pileDepth[i.val]
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
    have hfne : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile) m f p).2.pileFlute.get i
          = p.pileFlute.get i := by
      intro i hi
      rw [hqf]
      show (p.pileFlute.set pile.toNat _ hpile)[i.val] = p.pileFlute[i.val]
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
    obtain ⟨v, hreach, hframe, hmatch⟩ := h.cleanupPileSim hwf hb hpile hidx (by omega) hfl1 hB
      (by omega) hchain hf hfree haces hBflute1 hdself hfself hdne hfne (by rw [hqa])
      (by rw [hqk])
    exact ⟨v, hreach, hframe, hmatch, fun hc => absurd hc hk⟩

/-! ### The merge guards, without a new induction

`merge_pos_chain` (`SolverSpecCommon`) already reads each merged slot off its own
guard — via `mergeIter_eq`, so there is no induction left to do here.  All that is
needed is the `Int32` index conversion into the `Nat` form `PileMatches_lower`
consumes. -/

/-- **The merge guards give `cleanupPileSim`'s chain hypothesis.** -/
theorem chain_of_mergeGuards {g : Globals} {p : SolverPosType} {pile : UInt32}
    (hpile : pile.toNat < 10) (ph : UInt32) {B : UInt8} {m : Nat}
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hm : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    (hmg : ∀ i, i < m → mergeGuard g pile
      (mergeIter ph i ⟨B, (p.pileDepth[pile.toNat]'hpile), 1, p⟩)) :
    ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1 := by
  have hdn : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := rfl
  have hdI : ((p.pileDepth[pile.toNat]'hpile)).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := rfl
  -- every merged slot, by its own guard
  have hslot : ∀ k, k ≤ m → ∀ hk5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k < 5,
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k, hk5⟩ = B + UInt8.ofNat k := by
    intro k hk hk5
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [show (UInt8.ofNat 0 : UInt8) = 0 from rfl, UInt8.add_zero, ← hB]
      exact congrArg _ (Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - 0
        = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 from by omega))
    · obtain ⟨h5, heq⟩ := SolverSpec.merge_pos_chain g pile hpile ph B
        (p.pileDepth[pile.toNat]'hpile) m p (by rw [hdI]; omega)
        (by rw [hdI]; omega) hmg k hk1 hk
      have hconv : ((p.pileDepth[pile.toNat]'hpile)
          - UInt8.ofNat k - 1).toUInt32.toNat
          = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k := by
        rw [UInt8.toNat_toUInt32, SolverSpec.depth_sub_ofNat_sub_one_eq
          (by rw [hdI]; omega)
          (by rw [hdI]; omega), hdI]
        omega
      rw [← heq]
      show (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hk5⟩ = _
      congr 1
      exact Fin.ext hconv.symm
  -- two consecutive slots differ by one
  intro j hj1' hj2' hj1 hj
  have hk : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j ≤ m := by omega
  have hk' : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1) ≤ m := by omega
  have h1 := hslot ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) hk (by omega)
  have h2 := hslot ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)) hk' (by omega)
  have hi1 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j), by omega⟩ : Fin 5) = ⟨j, hj⟩ :=
    Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) = j from by omega)
  have hi2 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)), by omega⟩ : Fin 5)
      = ⟨j - 1, hj1⟩ :=
    Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)) = j - 1 from by omega)
  rw [hi1] at h1
  rw [hi2] at h2
  rw [h1, h2]
  -- `B + (k+1) = (B + k) + 1`
  have hstep : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)
      = ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) + 1 := by omega
  rw [hstep, UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
