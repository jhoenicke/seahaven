import Seahaven.KingConfigSim

/-!
# Simulating the `busyAces` drain (`SolverMoveAces`)

`SolverMoveAces` walks up from `aces[suit] + 1`, counting *already free* cards in
`found` without touching the state, and re-syncs the position only when it reaches a
card exposed at its pile's boundary (`cardDepth = 0`, which writes `aces` and calls
`SolverRemoveFlute`).

On the `Rules` side the plays are therefore **deferred** to those sync points: during
the counting steps the position does not change at all, so a `Simulates` carries over
verbatim, and at a sync point the whole pending run is played at once.  Two facts make
that work, and both come from the invariant rather than from the state:

* `flute_eq_of_walk` — at a sync point the pile's flute is *exactly* the walked run
  plus the boundary, so the run is the top of that one column and `playsAll_column`
  ships it off (`playSyncRun`);
* at the walk's **tail** the pending cards may be anywhere — cell or king pile — and
  `accessible_of_pending` covers both uniformly, by the counting argument alone.

The matching sides are `syncPile` and `tailPile`; the configuration side is
`StateMatchesKingConfig.framePile` from `KingConfigSim`.
-/

/-- **The next foundation card of the drain's run is accessible.**  `u` is a state
reached from `s` by playing cards off the tops of columns (and out of cells) to the
foundations — the pending run so far.  Any *free* card that is next up for its
foundation is then either in a cell or already exposed: whatever sat above it in
its column was same-suit and lower (`column_above`), hence already on that
foundation, hence — the deck being intact — no longer in the column. -/
theorem accessible_of_pending {g : Globals} {s u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (hdrop : ∀ q : Fin 10, ∃ k : Nat, u.tableau q = (s.tableau q).drop k)
    (hcount : ∀ d : Card, countState u d = 1)
    {su : Suit} {c : Card} (hnext : nextFoundationCard u su = some c)
    (hfree : isFreeCard g p (encodeCard c)) :
    Accessible u c := by
  obtain ⟨hsu, hready⟩ := nextFoundationCard_spec hnext
  have hcr : rankToNat c.rank = optRankToNat (u.foundations c.suit) + 1 :=
    nextRankNat _ _ hready.symm
  have hcf : countFoundation u.foundations c = 0 := by
    unfold countFoundation
    rw [if_pos (by omega)]
  rcases NoDupState.location hcount c with hf | ⟨i, hi⟩ | ⟨q, hq⟩
  · exact absurd hf (by omega)
  · exact Or.inl ⟨i, hi⟩
  · refine Or.inr ⟨q, ?_⟩
    obtain ⟨k, hk⟩ := hdrop q
    obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hq
    have hlenu : (u.tableau q).length = (s.tableau q).length - k := by
      rw [hk]; simp only [List.length_drop]
    have hklt : k < (s.tableau q).length := by omega
    -- `c` sits at column position `k + idx`
    have h0 : (s.tableau q)[k + idx]? = some c := by
      have h1 : (u.tableau q)[idx]? = some c := by
        rw [List.getElem?_eq_getElem hidxlt, hidxeq]
      rwa [hk, List.getElem?_drop] at h1
    -- it must be the top one
    have hidx0 : idx = 0 := by
      by_contra hne
      have hkidxlt : k + idx < (s.tableau q).length := by
        rw [List.getElem?_eq_some_iff] at h0
        exact h0.choose
      have hceq : (s.tableau q)[k + idx]'hkidxlt = c := by
        rw [List.getElem?_eq_getElem hkidxlt, Option.some.injEq] at h0
        exact h0
      obtain ⟨hxsuit, hxrank⟩ := h.column_above hwf hb q
        (a := k) (b := k + idx) (by omega) hkidxlt (by rw [hceq]; exact hfree)
      rw [hceq] at hxsuit hxrank
      -- the card above is already on `c`'s foundation
      have hxf : countFoundation u.foundations ((s.tableau q)[k]'hklt) = 1 := by
        unfold countFoundation
        rw [hxsuit, if_neg (by omega)]
      have hxmem : ((s.tableau q)[k]'hklt) ∈ u.tableau q := by
        rw [hk]
        have : ((s.tableau q).drop k)[0]? = some ((s.tableau q)[k]'hklt) := by
          rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hklt]
        exact List.mem_of_getElem? this
      have hxcol : 1 ≤ countColumn (u.tableau q) ((s.tableau q)[k]'hklt) :=
        one_le_countColumn hxmem
      have hxtab : 1 ≤ countTableau u.tableau ((s.tableau q)[k]'hklt) := by
        unfold countTableau
        rw [List.sum_ofFn]
        exact le_trans hxcol
          (Finset.single_le_sum (f := fun j : Fin 10 =>
            countColumn (u.tableau j) ((s.tableau q)[k]'hklt))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      have := hcount ((s.tableau q)[k]'hklt)
      unfold countState at this
      omega
    -- so it is the head
    subst hidx0
    rw [hk, List.head?_drop]
    simpa using h0

/-- **The drain's pending run plays.**  Given that the next `j` cards of the suit
are free in the position — exactly what `MoveAcesInv` supplies for the `found`
cards the walk has counted — they can all be played to the foundation, and the
result is again a state that differs from `s` only by cards taken off column tops.

The bound `j` is why this is a hand-rolled induction rather than an instance of
`exists_playsAll_runFrom`: that driver needs *every* subsequent card to be
accessible, whereas the drain stops after the counted ones. -/
theorem exists_playsAll_pending {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (su : Suit) :
    ∀ (j : Nat) (u : State),
      (∀ q : Fin 10, ∃ k : Nat, u.tableau q = (s.tableau q).drop k) →
      (∀ d : Card, countState u d = 1) →
      (∀ d ∈ runFrom (nextFoundationCard u su) j, isFreeCard g p (encodeCard d)) →
      ∃ w, PlaysAll u (runFrom (nextFoundationCard u su) j) w ∧
        (∀ q : Fin 10, ∃ k : Nat, w.tableau q = (s.tableau q).drop k) ∧
        (∀ d : Card, countState w d = 1) := by
  intro j
  induction j with
  | zero => intro u hdrop hcount _; exact ⟨u, PlaysAll.nil u, hdrop, hcount⟩
  | succ j ih =>
    intro u hdrop hcount hfree
    cases hnf : nextFoundationCard u su with
    | none =>
      refine ⟨u, ?_, hdrop, hcount⟩
      rw [runFrom_none]
      exact PlaysAll.nil u
    | some c =>
      have hcfree : isFreeCard g p (encodeCard c) := by
        refine hfree c ?_
        rw [hnf, runFrom_some]
        exact List.mem_cons_self
      have hacc := accessible_of_pending hwf hb h hdrop hcount hnf hcfree
      obtain ⟨hsu, hready⟩ := nextFoundationCard_spec hnf
      obtain ⟨t1, hplay⟩ := PlaysTo.of_accessible hacc hready
      -- the deck is intact after one play
      have hreach1 : Reach u t1 := (PlaysAll.cons hplay (PlaysAll.nil t1)).toReach
      have hcount1 : ∀ d : Card, countState t1 d = 1 := by
        intro d
        rw [congrFun (countState_of_reach hreach1) d]
        exact hcount d
      -- and columns have only lost another top card
      have hdrop1 : ∀ q : Fin 10, ∃ k : Nat, t1.tableau q = (s.tableau q).drop k := by
        intro q
        rcases hplay.cases with ⟨i, -, rfl⟩ | ⟨q0, rest, hcol, rfl⟩
        · simpa using hdrop q
        · obtain ⟨k, hk⟩ := hdrop q
          by_cases hq : q = q0
          · subst hq
            refine ⟨k + 1, ?_⟩
            simp only [updateFoundation_tableau, updateColumn_tableau, update_same]
            have hrest : rest = (u.tableau q).tail := by rw [hcol, List.tail_cons]
            rw [hrest, hk, List.tail_drop]
          · refine ⟨k, ?_⟩
            simp only [updateFoundation_tableau, updateColumn_tableau, update,
              if_neg (show ¬ (q0 = q) from fun hc => hq hc.symm)]
            exact hk
      -- recurse on the rest of the run
      have hnext1 : nextFoundationCard t1 su = nextCard c := nextFoundationCard_playsTo hsu hplay
      have hfree1 : ∀ d ∈ runFrom (nextFoundationCard t1 su) j, isFreeCard g p (encodeCard d) := by
        rw [hnext1]
        intro d hd
        refine hfree d ?_
        rw [hnf, runFrom_some]
        exact List.mem_cons_of_mem c hd
      obtain ⟨w, hall, hw1, hw2⟩ := ih t1 hdrop1 hcount1 hfree1
      refine ⟨w, ?_, hw1, hw2⟩
      rw [runFrom_some]
      rw [hnext1] at hall
      exact PlaysAll.cons hplay hall

/-- **At a sync point the walk has already passed the whole flute.**

When the drain reaches a card exposed at pile `j`'s boundary, that boundary `B`
sits `found + 1` above the foundation top `A`.  The pile's flute can then be no
longer than `found + 1`: its topmost card carries `B`'s suit and value
`VALUE B - (pileFlute - 1)`, so a longer flute would put a card of that suit at or
below `A` — already on the foundation, and no card is in two places.

This is what makes the sync step's `flute_match` arithmetic work out: *every*
flute interior of the pile is among the `found` cards the walk counted, so playing
the pending run plus the boundary leaves exactly `pileDepth - 1` cards in the
column — which is what the cleanup's entry position (`fluteNorm` of
`removeFlutePre`, with `pileFlute := 1`) claims. -/
theorem StateMatchesSolverPos.flute_walked {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (j : Fin 10)
    (hdj : 0 < (p.pileDepth.get j).toInt.toNat)
    (b : Fin 5) (hb : b.val = (p.pileDepth.get j).toInt.toNat - 1)
    {su : Suit} (found : Nat)
    (hsuit : SUIT ((g.pos2card.get j).get b) = UInt8.ofNat (suitToNat su))
    (hval : (VALUE ((g.pos2card.get j).get b)).toNat
      = (VALUE (p.aces.get (finOfSuit su))).toNat + found + 1) :
    (p.pileFlute.get j).toNat ≤ found + 1 := by
  by_contra hgt
  push Not at hgt
  have hLen : (s.tableau j).length + 1
      = (p.pileDepth.get j).toInt.toNat + (p.pileFlute.get j).toNat := h.flute_match j hdj
  have hnL : (p.pileDepth.get j).toInt.toNat ≤ (s.tableau j).length := (h.depth_match j).1
  have hlt : (0 : Nat) < (s.tableau j).length := by omega
  -- the topmost flute card
  obtain ⟨hs0, hv0⟩ := flute_elem h j hdj b hb 0 (by omega) hlt
  rw [encodeCard_VALUE] at hv0
  have hfv := h.foundation_value su
  -- it carries the boundary's suit
  have hxsuit : ((s.tableau j)[0]'hlt).suit = su := by
    refine suitToNat_inj ?_
    have h1 : (SUIT (encodeCard ((s.tableau j)[0]'hlt))).toNat
        = suitToNat ((s.tableau j)[0]'hlt).suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt ((s.tableau j)[0]'hlt).suit
      omega
    have h2 : (SUIT ((g.pos2card.get j).get b)).toNat = suitToNat su := by
      rw [hsuit, UInt8.toNat_ofNat']
      have := suitToNat_lt su
      omega
    rw [← h1, ← h2, hs0]
  -- and a value at or below the foundation top, so it is already played
  have hxf : countFoundation s.foundations ((s.tableau j)[0]'hlt) = 1 := by
    unfold countFoundation
    rw [hxsuit, if_neg (by omega)]
  have hxtab : 1 ≤ countTableau s.tableau ((s.tableau j)[0]'hlt) :=
    one_le_countTableau (List.getElem_mem hlt)
  have := h.cards_count ((s.tableau j)[0]'hlt)
  unfold countState at this
  omega

/-! ### The sync point's flute, from the invariant alone

At a sync point the walked run and the pile's flute coincide, and this needs no
state-side reasoning at all — the two halves are both invariant clauses:

* `PileBase.flute_not_aces` bounds the flute above: it never reaches past the
  foundation top, so `pileFlute ≤ VALUE boundary - VALUE aces[suit] = found + 1`;
* `PileMerged.flute_maximal` bounds it below: the card just under the flute is
  either the foundation top itself, or not free — and the walk has just certified
  that every card of the suit strictly between the foundation top and the boundary
  *is* free, so the second case forces it to be the foundation top.

Consequently the top `found + 1` cards of the boundary's column are exactly the
walked run plus the boundary, in ascending order from the top — so the sync step
plays them straight off that one column with `playsAll_column`, and no other pile
or cell is touched. -/

/-- **The flute at a sync point is exactly the walked run plus the boundary.** -/
theorem flute_eq_of_walk {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (i : Fin 10) (hm : PileMerged g p i (hb.pileDepth_bound i))
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hidx : (p.pileDepth.get i).toNat - 1 < 5)
    (hs4 : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat < 4)
    (hfreebelow : ∀ c : UInt8, SUIT c = SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) →
      (VALUE (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat < (VALUE c).toNat →
      (VALUE c).toNat < (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat → isFreeCard g p c) :
    (p.pileFlute.get i).toNat
      = (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (VALUE (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat := by
  have hbcs := SUIT_toNat ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)
  have hbcv := VALUE_toNat ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)
  have hAs := SUIT_toNat (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)
  have hAv := VALUE_toNat (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)
  have hbc256 : (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat < 256 := UInt8.toNat_lt _
  have hA256 : (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).toNat < 256 := UInt8.toNat_lt _
  -- `aces[s]` carries suit `s`
  have hAsuitN : (SUIT (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := by
    rw [(hb.aces_kings_valid ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).1]
    show (UInt8.ofNat (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat
    rw [UInt8.toNat_ofNat']
    omega
  -- upper bound: the flute never reaches past the foundation top
  have hle : (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).toNat + (p.pileFlute.get i).toNat
      ≤ (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := (hb.pileBase i).flute_not_aces hd hs4
  have hfl1 : 1 ≤ (p.pileFlute.get i).toNat := (hb.pileBase i).flute_pos
  -- the card just below the flute
  have hsubN : (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i).toNat = (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (p.pileFlute.get i).toNat := by
    rw [UInt8.toNat_sub]
    omega
  have hsubs : (SUIT (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i)).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := by
    rw [SUIT_toNat, hsubN]
    omega
  have hsubv : (VALUE (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i)).toNat
      = (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (p.pileFlute.get i).toNat := by
    rw [VALUE_toNat, hsubN, hbcv]
    omega
  -- lower bound: `flute_maximal`
  rcases hm.flute_maximal with hz | hmax
  · exact absurd (congrArg UInt8.toNat hz) (by
      show ¬ ((p.pileDepth.get i).toNat = (0 : UInt8).toNat)
      have : ((0 : UInt8)).toNat = 0 := by decide
      omega)
  · simp only [] at hmax
    rcases hmax with ⟨hs4', heq⟩ | hnf
    · -- the flute reaches down to the foundation top
      have := congrArg UInt8.toNat heq
      rw [hsubN] at this
      omega
    · -- otherwise the card below would be free, which the walk excludes
      by_contra hne
      refine hnf (hfreebelow _ (UInt8.toNat_inj.mp hsubs) (by rw [hsubv]; omega)
        (by rw [hsubv]; omega))

/-- **The sync step's matching side.**  Playing pile `i`'s whole flute together with
its boundary onto the foundation leaves the state matching the position with
`pileDepth[i]` decremented, `pileFlute[i] = 1`, and `aces` re-read off the new
foundations — which is exactly `fluteNorm i (removeFlutePre i …)`, the position
`SolverCleanupPile` is entered at, so `Simulates.ofCleanupRun` takes over from here.

`k` is the flute-interior count, pinned to `found` by `flute_eq_of_walk`; the column
surgery is `PileMatches_drop_flute`. -/
theorem StateMatchesSolverPos.syncPile {g : Globals} {s w : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10) {k : Nat}
    (hd : 0 < (p.pileDepth.get i).toInt.toNat)
    (hcol : w.tableau i = (s.tableau i).drop (k + 1))
    (hframe : ∀ j : Fin 10, j ≠ i → w.tableau j = s.tableau j)
    (hcount : ∀ c : Card, countState w c = 1)
    (hflen : (s.tableau i).length = (p.pileDepth.get i).toInt.toNat + k)
    (hqd : (q.pileDepth.get i).toInt.toNat = (p.pileDepth.get i).toInt.toNat - 1)
    (hqdne : ∀ j : Fin 10, j ≠ i → q.pileDepth.get j = p.pileDepth.get j)
    (hqf : (q.pileFlute.get i).toNat = 1)
    (hqfne : ∀ j : Fin 10, j ≠ i → q.pileFlute.get j = p.pileFlute.get j)
    (hqkings : q.kings = p.kings)
    (hqaces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (w.foundations su)) :
    StateMatchesSolverPos g w q := by
  have hlt6 : ∀ j : Fin 10, (q.pileDepth.get j).toInt.toNat < 6 := by
    intro j
    by_cases hj : j = i
    · subst hj; have := h.depth_lt6 j; omega
    · rw [hqdne j hj]; exact h.depth_lt6 j
  -- the new column length
  have hwlen : (w.tableau i).length = (p.pileDepth.get i).toInt.toNat - 1 := by
    rw [hcol, List.length_drop, hflen]
    omega
  refine ⟨hcount, hlt6, ?_, ?_, ?_, hqaces⟩
  · -- depth_match
    intro j
    by_cases hj : j = i
    · subst hj
      have hfin : (⟨(q.pileDepth.get j).toInt.toNat, hlt6 j⟩ : Fin 6)
          = ⟨(p.pileDepth.get j).toInt.toNat - 1, by have := h.depth_lt6 j; omega⟩ :=
        Fin.ext (show (q.pileDepth.get j).toInt.toNat = (p.pileDepth.get j).toInt.toNat - 1
          from hqd)
      rw [hfin, hcol]
      exact PileMatches_drop_flute (h.depth_match j) hd hflen (by have := h.depth_lt6 j; omega)
    · have hfin : (⟨(q.pileDepth.get j).toInt.toNat, hlt6 j⟩ : Fin 6)
          = ⟨(p.pileDepth.get j).toInt.toNat, h.depth_lt6 j⟩ := by
        refine Fin.ext (show (q.pileDepth.get j).toInt.toNat
          = (p.pileDepth.get j).toInt.toNat from ?_)
        rw [hqdne j hj]
      rw [hfin, hframe j hj]
      exact h.depth_match j
  · -- flute_match
    intro j hdj
    by_cases hj : j = i
    · subst hj
      rw [hwlen, hqf]
      omega
    · rw [hframe j hj, hqfne j hj, hqdne j hj]
      exact h.flute_match j (by rwa [hqdne j hj] at hdj)
  · -- king_pile
    intro j hdj
    by_cases hj : j = i
    · -- the column is empty, so there is nothing to check
      subst hj
      have hnil : w.tableau j = [] := by
        refine List.eq_nil_of_length_eq_zero ?_
        rw [hwlen]
        omega
      intro d hdmem
      rw [hnil] at hdmem
      simp at hdmem
    · rw [hframe j hj, hqkings]
      exact h.king_pile j (by rwa [hqdne j hj] at hdj)

/-- **`aces` after the sync step's plays.**  The solver writes `aces[su] := bc`; on
the state side `su`'s foundation now holds `bc`'s rank and no other foundation
moved, so `aces_match` transfers — this is `syncPile`'s last hypothesis. -/
theorem StateMatchesSolverPos.aces_match_play {g : Globals} {s w : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) {su : Suit} {bc : Card} (hsu : bc.suit = su)
    (hqsu : q.aces.get (finOfSuit su) = encodeCard bc)
    (hqne : ∀ su' : Suit, su' ≠ su → q.aces.get (finOfSuit su') = p.aces.get (finOfSuit su'))
    (hwfound : w.foundations = update s.foundations su bc.rank) :
    ∀ su' : Suit, q.aces.get (finOfSuit su') = encodeFoundation su' (w.foundations su') := by
  intro su'
  by_cases hs : su' = su
  · subst hs
    rw [hqsu, hwfound, update_same, encodeFoundation_some]
    obtain ⟨bs, br⟩ := bc
    simp only [] at hsu
    rw [hsu]
  · have hupd : (update s.foundations su bc.rank) su' = s.foundations su' := by
      unfold update
      rw [if_neg (fun hc => hs hc.symm)]
    rw [hqne su' hs, hwfound, hupd]
    exact h.aces_match su'

/-! ### The tail

At the walk's end the pending cards have been played from wherever they were —
cells, or, when the suit ran to completion, off its king pile.  A king pile is
always drained *completely*: its cards are free and contiguous up to the king, so
the walk cannot stop inside one.  So every column either survives untouched or is
now empty, and the position's `aces`/`kings` writes are what re-establish matching
(`busyAces` matching never reads). -/

/-- **The tail's matching side.** -/
theorem StateMatchesSolverPos.tailPile {g : Globals} {s w : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p)
    (hcount : ∀ c : Card, countState w c = 1)
    (hframe : ∀ j : Fin 10, w.tableau j = s.tableau j ∨
      (w.tableau j = [] ∧ (p.pileDepth.get j).toInt.toNat = 0))
    (hqd : q.pileDepth = p.pileDepth) (hqf : q.pileFlute = p.pileFlute)
    (hqk : ∀ j : Fin 10, (p.pileDepth.get j).toInt.toNat = 0 → w.tableau j = s.tableau j →
      ∀ d ∈ (s.tableau j).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit))
    (hqaces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (w.foundations su)) :
    StateMatchesSolverPos g w q := by
  have hdeq : ∀ j : Fin 10, q.pileDepth.get j = p.pileDepth.get j := by
    intro j; rw [hqd]
  have hfeq : ∀ j : Fin 10, q.pileFlute.get j = p.pileFlute.get j := by
    intro j; rw [hqf]
  have hlt6 : ∀ j : Fin 10, (q.pileDepth.get j).toInt.toNat < 6 := by
    intro j; rw [hdeq j]; exact h.depth_lt6 j
  refine ⟨hcount, hlt6, ?_, ?_, ?_, hqaces⟩
  · -- depth_match
    intro j
    have hfin : (⟨(q.pileDepth.get j).toInt.toNat, hlt6 j⟩ : Fin 6)
        = ⟨(p.pileDepth.get j).toInt.toNat, h.depth_lt6 j⟩ :=
      Fin.ext (show (q.pileDepth.get j).toInt.toNat = (p.pileDepth.get j).toInt.toNat from by
        rw [hdeq j])
    rw [hfin]
    rcases hframe j with hsame | ⟨hnil, hd0⟩
    · rw [hsame]; exact h.depth_match j
    · -- the emptied pile matches at depth `0`
      have hfin0 : (⟨(p.pileDepth.get j).toInt.toNat, h.depth_lt6 j⟩ : Fin 6) = ⟨0, by omega⟩ :=
        Fin.ext (show (p.pileDepth.get j).toInt.toNat = 0 from hd0)
      rw [hfin0, hnil]
      refine ⟨by simp, fun kk => kk.elim0, ?_⟩
      rw [dif_neg (by omega : ¬ (0 : Nat) > 0)]
      refine ⟨0, ?_⟩
      intro idx
      exact absurd idx.isLt (by simp)
  · -- flute_match
    intro j hdj
    rw [hdeq j] at hdj
    rcases hframe j with hsame | ⟨-, hd0⟩
    · rw [hsame, hdeq j, hfeq j]; exact h.flute_match j hdj
    · omega
  · -- king_pile
    intro j hdj
    rw [hdeq j] at hdj
    rcases hframe j with hsame | ⟨hnil, -⟩
    · intro d hd
      rw [hsame] at hd ⊢
      rw [hqk j hdj hsame d hd]
      exact h.king_pile j hdj d hd
    · intro d hd
      rw [hnil] at hd
      simp at hd

/-! ### The sync step's plays

Everything the sync step needs from the `Rules` side, in one step: the top
`found + 1` cards of the boundary's column are a run whose head is exactly the
suit's next foundation card, so `playsAll_column` ships them all off. -/

theorem natToRank_rankToNat (r : Rank) : natToRank (rankToNat r) = some r := by
  cases r <;> rfl

/-- **The sync step plays the flute and the boundary off the column.** -/
theorem StateMatchesSolverPos.playSyncRun {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10) {su : Suit} {found : Nat}
    (hd : 0 < (p.pileDepth.get i).toInt.toNat)
    (hidx : (p.pileDepth.get i).toInt.toNat - 1 < 5)
    (hbsuit : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat = suitToNat su)
    (hflute : (p.pileFlute.get i).toNat = found + 1)
    (hbval : (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat
      = optRankToNat (s.foundations su) + found + 1) :
    ∃ w : State,
      PlaysAll s ((s.tableau i).take (found + 1)) w ∧
      w.tableau i = (s.tableau i).drop (found + 1) ∧
      (∀ j : Fin 10, j ≠ i → w.tableau j = s.tableau j) ∧
      (s.tableau i).length = (p.pileDepth.get i).toInt.toNat + found := by
  -- the column's length, from `flute_match`
  have hlen : (s.tableau i).length = (p.pileDepth.get i).toInt.toNat + found := by
    have := h.flute_match i hd
    omega
  -- the segment is a run
  have hrun : IsRun ((s.tableau i).take (found + 1)) :=
    h.isRun_take i hd (found + 1) (by omega)
  -- its head is the suit's next foundation card
  have hhead : ∀ c ∈ ((s.tableau i).take (found + 1)).head?,
      some c.rank = nextRank (s.foundations c.suit) := by
    intro c hc
    have h0lt : 0 < (s.tableau i).length := by omega
    have hc0 : c = (s.tableau i)[0]'h0lt := by
      have : ((s.tableau i).take (found + 1))[0]? = some c := by
        rw [← List.head?_eq_getElem?]
        exact hc
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem h0lt,
        Option.some.injEq] at this
      exact this.symm
    obtain ⟨hs0, hv0⟩ := flute_elem h i hd ⟨_, hidx⟩ rfl 0 (by omega) h0lt
    rw [encodeCard_VALUE] at hv0
    -- suit and rank of the head
    have hcsuit : c.suit = su := by
      refine suitToNat_inj ?_
      have h1 : (SUIT (encodeCard ((s.tableau i)[0]'h0lt))).toNat
          = suitToNat ((s.tableau i)[0]'h0lt).suit := by
        rw [encodeCard_SUIT, UInt8.toNat_ofNat']
        have := suitToNat_lt ((s.tableau i)[0]'h0lt).suit
        omega
      rw [hc0, ← h1, hs0, hbsuit]
    have hcrank : rankToNat c.rank = optRankToNat (s.foundations su) + 1 := by
      rw [hc0]; omega
    rw [hcsuit, nextRank, ← hcrank, natToRank_rankToNat]
  -- play them
  obtain ⟨w, hall, hwi, hwj, -⟩ :=
    playsAll_column (q := i) (cs := (s.tableau i).take (found + 1))
      (rest := (s.tableau i).drop (found + 1)) (List.take_append_drop _ _).symm hrun hhead
  exact ⟨w, hall, hwi, hwj, hlen⟩

/-- **The foundations after the sync step's plays**: the drained suit's foundation now
holds the boundary card, and no other foundation moved.  This is `aces_match_play`'s
last hypothesis. -/
theorem StateMatchesSolverPos.syncRun_foundations {g : Globals} {s w : State}
    {p : SolverPosType} (h : StateMatchesSolverPos g s p) (i : Fin 10)
    {su : Suit} {bc : Card} {found : Nat}
    (hd : 0 < (p.pileDepth.get i).toInt.toNat)
    (hidx : (p.pileDepth.get i).toInt.toNat - 1 < 5)
    (hbsuit : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat = suitToNat su)
    (hlen : (s.tableau i).length = (p.pileDepth.get i).toInt.toNat + found)
    (hbc : encodeCard bc = (g.pos2card.get i).get ⟨_, hidx⟩)
    (hall : PlaysAll s ((s.tableau i).take (found + 1)) w) :
    w.foundations = update s.foundations su bc.rank := by
  -- every played card carries the drained suit, with the value climbing to the boundary
  have hsuits : ∀ (idx : Nat) (hidxf : idx < found + 1) (hidxlt : idx < (s.tableau i).length),
      ((s.tableau i)[idx]'hidxlt).suit = su ∧
      (VALUE (encodeCard ((s.tableau i)[idx]'hidxlt))).toNat
        + found = (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat + idx := by
    intro idx hidxf hidxlt
    obtain ⟨hs, hv⟩ := flute_elem h i hd ⟨_, hidx⟩ rfl idx (by omega) hidxlt
    refine ⟨suitToNat_inj ?_, by omega⟩
    have h1 : (SUIT (encodeCard ((s.tableau i)[idx]'hidxlt))).toNat
        = suitToNat ((s.tableau i)[idx]'hidxlt).suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt ((s.tableau i)[idx]'hidxlt).suit
      omega
    rw [← h1, hs, hbsuit]
  have hmemsuit : ∀ c ∈ (s.tableau i).take (found + 1), c.suit = su := by
    intro c hc
    obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hc
    have hcslen : ((s.tableau i).take (found + 1)).length = found + 1 := by
      simp only [List.length_take]; omega
    have hidxlt' : idx < (s.tableau i).length := by omega
    have hget : ((s.tableau i).take (found + 1))[idx]'hidxlt = (s.tableau i)[idx]'hidxlt' :=
      List.getElem_take ..
    rw [← hidxeq, hget]
    exact (hsuits idx (by omega) hidxlt').1
  -- `bc` carries the suit too, and is the last played card
  have hfl : found < (s.tableau i).length := by omega
  have hbcsu : bc.suit = su := by
    refine suitToNat_inj ?_
    have h1 : (SUIT (encodeCard bc)).toNat = suitToNat bc.suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt bc.suit
      omega
    rw [← h1, hbc, hbsuit]
  have hbceq : (s.tableau i)[found]'hfl = bc := by
    refine card_eq_of_suit_rank ((hsuits found (by omega) hfl).1.trans hbcsu.symm) ?_
    have hbcv : (VALUE (encodeCard ((s.tableau i)[found]'hfl))).toNat
        = (VALUE (encodeCard bc)).toNat := by
      rw [hbc]
      have := (hsuits found (by omega) hfl).2
      omega
    rw [encodeCard_VALUE, encodeCard_VALUE] at hbcv
    exact hbcv
  have hlast : ((s.tableau i).take (found + 1)).getLast? = some bc := by
    have hcslen : ((s.tableau i).take (found + 1)).length = found + 1 := by
      simp only [List.length_take]; omega
    rw [List.getLast?_eq_getElem?, hcslen]
    have hg : ((s.tableau i).take (found + 1))[found + 1 - 1]?
        = some ((s.tableau i)[found]'hfl) := by
      simp only [Nat.add_sub_cancel]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hfl]
    rw [hg, hbceq]
  -- assemble
  funext v
  by_cases hv : v = su
  · subst hv
    rw [update_same, ← hbcsu]
    exact hall.foundations_getLast bc hlast
  · have hupd : (update s.foundations su bc.rank) v = s.foundations v := by
      unfold update
      rw [if_neg (fun hc => hv hc.symm)]
    rw [hupd]
    exact hall.foundations_of_forall_ne v
      (fun c hc => by rw [hmemsuit c hc]; exact fun hc' => hv hc'.symm)
