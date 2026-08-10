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
        (∀ d : Card, countState w d = 1) ∧
        -- a column that changed gave up one of the run's cards
        (∀ q : Fin 10, w.tableau q = u.tableau q ∨
          ∃ d ∈ runFrom (nextFoundationCard u su) j, d ∈ u.tableau q) := by
  intro j
  induction j with
  | zero => intro u hdrop hcount _; exact ⟨u, PlaysAll.nil u, hdrop, hcount, fun _ => Or.inl rfl⟩
  | succ j ih =>
    intro u hdrop hcount hfree
    cases hnf : nextFoundationCard u su with
    | none =>
      refine ⟨u, ?_, hdrop, hcount, fun _ => Or.inl rfl⟩
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
      obtain ⟨w, hall, hw1, hw2, hw3⟩ := ih t1 hdrop1 hcount1 hfree1
      refine ⟨w, ?_, hw1, hw2, ?_⟩
      · rw [runFrom_some]
        rw [hnext1] at hall
        exact PlaysAll.cons hplay hall
      · -- either this play or a later one touched the column
        intro q
        rcases hplay.cases with ⟨i0, hcell0, ht1⟩ | ⟨q0, rest, hcol, ht1⟩
        · -- played from a cell: this step changed no column
          have hteq : t1.tableau q = u.tableau q := by rw [ht1]; simp
          rcases hw3 q with hsame | ⟨d, hdrun, hdmem⟩
          · exact Or.inl (hsame.trans hteq)
          · refine Or.inr ⟨d, ?_, hteq ▸ hdmem⟩
            rw [runFrom_some]
            rw [hnext1] at hdrun
            exact List.mem_cons_of_mem c hdrun
        · -- played off column `q0`
          by_cases hq : q = q0
          · subst hq
            refine Or.inr ⟨c, ?_, ?_⟩
            · rw [runFrom_some]; exact List.mem_cons_self
            · rw [hcol]; exact List.mem_cons_self
          · have hteq : t1.tableau q = u.tableau q := by
              rw [ht1]
              simp only [updateFoundation_tableau, updateColumn_tableau, update,
                if_neg (show ¬ (q0 = q) from fun hc => hq hc.symm)]
            rcases hw3 q with hsame | ⟨d, hdrun, hdmem⟩
            · exact Or.inl (hsame.trans hteq)
            · refine Or.inr ⟨d, ?_, hteq ▸ hdmem⟩
              rw [runFrom_some]
              rw [hnext1] at hdrun
              exact List.mem_cons_of_mem c hdrun


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
    (hdj : 0 < (p.pileDepth.get j).toNat)
    (b : Fin 5) (hb : b.val = (p.pileDepth.get j).toNat - 1)
    {su : Suit} (found : Nat)
    (hsuit : SUIT ((g.pos2card.get j).get b) = UInt8.ofNat (suitToNat su))
    (hval : (VALUE ((g.pos2card.get j).get b)).toNat
      = (VALUE (p.aces.get (finOfSuit su))).toNat + found + 1) :
    (p.pileFlute.get j).toNat ≤ found + 1 := by
  by_contra hgt
  push Not at hgt
  have hLen : (s.tableau j).length + 1
      = (p.pileDepth.get j).toNat + (p.pileFlute.get j).toNat := h.flute_match j hdj
  have hnL : (p.pileDepth.get j).toNat ≤ (s.tableau j).length := (h.depth_match j).1
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
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hcol : w.tableau i = (s.tableau i).drop (k + 1))
    (hframe : ∀ j : Fin 10, j ≠ i → w.tableau j = s.tableau j)
    (hcount : ∀ c : Card, countState w c = 1)
    (hflen : (s.tableau i).length = (p.pileDepth.get i).toNat + k)
    (hqd : (q.pileDepth.get i).toNat = (p.pileDepth.get i).toNat - 1)
    (hqdne : ∀ j : Fin 10, j ≠ i → q.pileDepth.get j = p.pileDepth.get j)
    (hqf : (q.pileFlute.get i).toNat = 1)
    (hqfne : ∀ j : Fin 10, j ≠ i → q.pileFlute.get j = p.pileFlute.get j)
    (hqkings : q.kings = p.kings)
    (hqaces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (w.foundations su)) :
    StateMatchesSolverPos g w q := by
  have hlt6 : ∀ j : Fin 10, (q.pileDepth.get j).toNat < 6 := by
    intro j
    by_cases hj : j = i
    · subst hj; have := h.depth_lt6 j; omega
    · rw [hqdne j hj]; exact h.depth_lt6 j
  -- the new column length
  have hwlen : (w.tableau i).length = (p.pileDepth.get i).toNat - 1 := by
    rw [hcol, List.length_drop, hflen]
    omega
  refine ⟨hcount, hlt6, ?_, ?_, ?_, hqaces⟩
  · -- depth_match
    intro j
    by_cases hj : j = i
    · subst hj
      have hfin : (⟨(q.pileDepth.get j).toNat, hlt6 j⟩ : Fin 6)
          = ⟨(p.pileDepth.get j).toNat - 1, by have := h.depth_lt6 j; omega⟩ :=
        Fin.ext (show (q.pileDepth.get j).toNat = (p.pileDepth.get j).toNat - 1
          from hqd)
      rw [hfin, hcol]
      exact PileMatches_drop_flute (h.depth_match j) hd hflen (by have := h.depth_lt6 j; omega)
    · have hfin : (⟨(q.pileDepth.get j).toNat, hlt6 j⟩ : Fin 6)
          = ⟨(p.pileDepth.get j).toNat, h.depth_lt6 j⟩ := by
        refine Fin.ext (show (q.pileDepth.get j).toNat
          = (p.pileDepth.get j).toNat from ?_)
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
      (w.tableau j = [] ∧ (p.pileDepth.get j).toNat = 0))
    (hqd : q.pileDepth = p.pileDepth) (hqf : q.pileFlute = p.pileFlute)
    (hqk : ∀ j : Fin 10, (p.pileDepth.get j).toNat = 0 → w.tableau j = s.tableau j →
      ∀ d ∈ (s.tableau j).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit))
    (hqaces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (w.foundations su)) :
    StateMatchesSolverPos g w q := by
  have hdeq : ∀ j : Fin 10, q.pileDepth.get j = p.pileDepth.get j := by
    intro j; rw [hqd]
  have hfeq : ∀ j : Fin 10, q.pileFlute.get j = p.pileFlute.get j := by
    intro j; rw [hqf]
  have hlt6 : ∀ j : Fin 10, (q.pileDepth.get j).toNat < 6 := by
    intro j; rw [hdeq j]; exact h.depth_lt6 j
  refine ⟨hcount, hlt6, ?_, ?_, ?_, hqaces⟩
  · -- depth_match
    intro j
    have hfin : (⟨(q.pileDepth.get j).toNat, hlt6 j⟩ : Fin 6)
        = ⟨(p.pileDepth.get j).toNat, h.depth_lt6 j⟩ :=
      Fin.ext (show (q.pileDepth.get j).toNat = (p.pileDepth.get j).toNat from by
        rw [hdeq j])
    rw [hfin]
    rcases hframe j with hsame | ⟨hnil, hd0⟩
    · rw [hsame]; exact h.depth_match j
    · -- the emptied pile matches at depth `0`
      have hfin0 : (⟨(p.pileDepth.get j).toNat, h.depth_lt6 j⟩ : Fin 6) = ⟨0, by omega⟩ :=
        Fin.ext (show (p.pileDepth.get j).toNat = 0 from hd0)
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
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hidx : (p.pileDepth.get i).toNat - 1 < 5)
    (hbsuit : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat = suitToNat su)
    (hflute : (p.pileFlute.get i).toNat = found + 1)
    (hbval : (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat
      = optRankToNat (s.foundations su) + found + 1) :
    ∃ w : State,
      PlaysAll s ((s.tableau i).take (found + 1)) w ∧
      w.tableau i = (s.tableau i).drop (found + 1) ∧
      (∀ j : Fin 10, j ≠ i → w.tableau j = s.tableau j) ∧
      (s.tableau i).length = (p.pileDepth.get i).toNat + found := by
  -- the column's length, from `flute_match`
  have hlen : (s.tableau i).length = (p.pileDepth.get i).toNat + found := by
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
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hidx : (p.pileDepth.get i).toNat - 1 < 5)
    (hbsuit : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat = suitToNat su)
    (hlen : (s.tableau i).length = (p.pileDepth.get i).toNat + found)
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

/-! ### The sync step's plays, as one `Simulates`

Gluing the pieces: `playSyncRun` ships the run off the column, `syncRun_foundations`
and `aces_match_play` handle `aces`, `syncPile` gives the matching at the cleanup's
entry position, and `framePile` carries the king configuration — unchanged, since the
only pile touched either stays non-empty or ends up with a physically empty column.
`Simulates.ofCleanupRun` then composes onto this with `Simulates.trans`. -/

/-- **The drain's foundation plays are simulated**, landing exactly at the position
`SolverCleanupPile` is entered at. -/
theorem SimulatesNorm.syncPlays {g : Globals} {s : State} {p q : SolverPosType} {k : Fin 16}
    (hk : StateMatchesKingConfig g s p k) (i : Fin 10)
    {su : Suit} {bc : Card} {found : Nat}
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hidx : (p.pileDepth.get i).toNat - 1 < 5)
    (hbsuit : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat = suitToNat su)
    (hbc : encodeCard bc = (g.pos2card.get i).get ⟨_, hidx⟩)
    (hflute : (p.pileFlute.get i).toNat = found + 1)
    (hbval : (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat
      = optRankToNat (s.foundations su) + found + 1)
    (hqd : (q.pileDepth.get i).toNat = (p.pileDepth.get i).toNat - 1)
    (hqdne : ∀ j : Fin 10, j ≠ i → q.pileDepth.get j = p.pileDepth.get j)
    (hqf : (q.pileFlute.get i).toNat = 1)
    (hqfne : ∀ j : Fin 10, j ≠ i → q.pileFlute.get j = p.pileFlute.get j)
    (hqkings : q.kings = p.kings)
    (hqasu : q.aces.get (finOfSuit su) = encodeCard bc)
    (hqane : ∀ su' : Suit, su' ≠ su → q.aces.get (finOfSuit su') = p.aces.get (finOfSuit su')) :
    ∃ v : State, SimulatesNorm g s p k v q k ∅ 0xffff := by
  -- play the run off the column
  obtain ⟨w, hall, hwi, hwj, hlen⟩ :=
    hk.toMatches.playSyncRun i hd hidx hbsuit hflute hbval
  have hreach : Reach s w := hall.toReach
  have hcount : ∀ c : Card, countState w c = 1 := by
    intro c
    rw [congrFun (countState_of_reach hreach) c]
    exact hk.toMatches.cards_count c
  -- `aces` follows the foundations
  have hfound := hk.toMatches.syncRun_foundations i hd hidx hbsuit hlen hbc hall
  have hbcsu : bc.suit = su := by
    refine suitToNat_inj ?_
    have h1 : (SUIT (encodeCard bc)).toNat = suitToNat bc.suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt bc.suit
      omega
    rw [← h1, hbc, hbsuit]
  have hqaces := hk.toMatches.aces_match_play hbcsu hqasu hqane hfound
  -- matching at the cleanup's entry position
  have hmatch := hk.toMatches.syncPile i hd hwi hwj hcount hlen hqd hqdne hqf hqfne hqkings hqaces
  -- and the king configuration is untouched
  refine ⟨w, hk.framePile hall.toNormReach hmatch hd ?_ hwj hqdne hqkings⟩
  by_cases hd1 : 0 < (p.pileDepth.get i).toNat - 1
  · exact Or.inl (by omega)
  · refine Or.inr ?_
    refine List.eq_nil_of_length_eq_zero ?_
    rw [hwi, List.length_drop, hlen]
    omega

/-! ### At the walk's end, no flute gave up a card

The tail's frame: a column that handed over one of the played cards cannot have been
a *non-empty* pile.  Such a card would be a flute interior, so that pile's boundary
carries the same suit above it; the boundary is not free, so it cannot sit inside the
walked window, and flute contiguity then puts the walk's *stopping* card inside the
same flute — where it is either the boundary itself or a flute interior, hence free.
Both contradict the exit test, which is exactly "not free and not the boundary".

Note on spelling: the boundary index is written `(p.pileDepth.get j).toNat - 1`, matching
`PileBase.flute_cards_free`, and card codes are never rewritten *inside* `isFreeCard`
(its body branches on `c.toNat < 64`, so unifying two defeq-but-different codes there
sends `whnf` into the weeds).  Equalities between codes are moved by rewriting the
subterm in a hypothesis instead. -/

/-- **No flute gives up a played card at the walk's end.** -/
theorem StateMatchesSolverPos.no_flute_at_exit {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {su : Suit} {V : Nat} {stop : UInt8} (j : Fin 10)
    (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidxj : (p.pileDepth.get j).toNat - 1 < 5)
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ V → (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat)
    (hstopsuit : (SUIT stop).toNat = suitToNat su)
    (hstopval : (VALUE stop).toNat = V + 1)
    (hstopfree : ¬ isFreeCard g p stop)
    (hstopbnd : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩ ≠ stop)
    {x : Card} (hxmem : x ∈ s.tableau j) (hxsuit : x.suit = su)
    (hxgt : (VALUE (p.aces.get (finOfSuit su))).toNat < rankToNat x.rank)
    (hxle : rankToNat x.rank ≤ V) : False := by
  have hbridge : (p.pileDepth.get j).toNat = (p.pileDepth.get j).toNat := rfl
  -- codes decompose as `16 * suit + value`
  have hdec : ∀ c : UInt8, c.toNat = 16 * (SUIT c).toNat + (VALUE c).toNat := by
    intro c
    have h1 := SUIT_toNat c
    have h2 := VALUE_toNat c
    omega
  -- `x` carries the suit and, being in the window, is free
  have hxs : (SUIT (encodeCard x)).toNat = suitToNat su := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat', hxsuit]
    have := suitToNat_lt su
    omega
  have hxv : (VALUE (encodeCard x)).toNat = rankToNat x.rank := encodeCard_VALUE x
  have hxfree : isFreeCard g p (encodeCard x) := by
    by_contra hnf
    have := hnotfree (encodeCard x) hxs hnf (by omega)
    omega
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hxmem
  have hxi : (s.tableau j)[idx]'hidxlt = x := hidxeq
  have habove := h.free_above_boundary hwf hb j hidxlt (by rw [hxi]; exact hxfree)
  have hLen : (s.tableau j).length + 1
      = (p.pileDepth.get j).toNat + (p.pileFlute.get j).toNat :=
    h.flute_match j (by omega)
  -- the boundary: same suit, value at least `x`'s
  obtain ⟨hs0, hv0⟩ := flute_elem h j (by omega)
    ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩ rfl idx (by omega) hidxlt
  rw [hxi] at hs0 hv0
  rw [encodeCard_VALUE] at hv0
  have hbs : (SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat
      = suitToNat su := by rw [← hs0]; exact hxs
  have hbnotfree :
      ¬ isFreeCard g p ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩) :=
    depth_card_not_free hwf hb j ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩
      (show (p.pileDepth.get j).toNat - 1 < (p.pileDepth.get j).toNat from by omega)
  -- it lies above the walked window
  have hbgt : V
      < (VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat := by
    by_contra hle
    push Not at hle
    have := hnotfree _ hbs hbnotfree hle
    omega
  have hfl1 : 1 ≤ (p.pileFlute.get j).toNat := (hb.pileBase j).flute_pos
  have hdecB := hdec ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)
  have hvB := VALUE_toNat ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)
  have hB256 : ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩).toNat < 256 :=
    UInt8.toNat_lt _
  -- the stop card sits in this pile's flute, at offset `m`
  rcases Nat.eq_zero_or_pos
      ((VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat - (V + 1))
    with hm0 | hm1
  · -- offset zero: the stop card *is* the boundary
    refine hstopbnd (UInt8.toNat_inj.mp ?_)
    rw [hdecB, hdec stop, hbs, hstopsuit, hstopval]
    omega
  · -- positive offset: the stop card is a flute interior, hence free
    have hmof : (UInt8.ofNat
        ((VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat
          - (V + 1))).toNat
        = (VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat
          - (V + 1) := by
      rw [UInt8.toNat_ofNat']
      omega
    have hfree := (hb.pileBase j).flute_cards_free
      (UInt8.ofNat
        ((VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat - (V + 1)))
      (by omega) (by rw [hmof]; omega) (by rw [hmof]; omega)
    -- move the code equality by rewriting the hypothesis, never inside `isFreeCard`'s goal
    have heq : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩
        - UInt8.ofNat
          ((VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat
            - (V + 1)) = stop := by
      refine UInt8.toNat_inj.mp ?_
      rw [UInt8.toNat_sub, hmof, hdec stop, hstopsuit, hstopval, hdecB, hbs]
      omega
    rw [heq] at hfree
    exact hstopfree hfree

/-- **No column at all gives up a played card at a non-completing exit.**  Extends
`no_flute_at_exit` to solver-empty piles: there `flute_empty` kills the flute-interior
case, and a king-run card would put the stop card above the suit's frontier, where
`king_frontier` makes it free.  So when the walk stops at a card that is neither free
nor a boundary, every played card came out of a *cell*. -/
theorem StateMatchesSolverPos.no_played_in_column {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {su : Suit} {V : Nat} {stop : UInt8} (j : Fin 10)
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ V → (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat)
    (hstopsuit : (SUIT stop).toNat = suitToNat su)
    (hstopval : (VALUE stop).toNat = V + 1)
    (hstopreal : (VALUE stop).toNat ≤ 13)
    (hstopfree : ¬ isFreeCard g p stop)
    (hstopbnd : ∀ hd : 0 < (p.pileDepth.get j).toNat,
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound j; omega⟩ ≠ stop)
    {x : Card} (hxmem : x ∈ s.tableau j) (hxsuit : x.suit = su)
    (hxgt : (VALUE (p.aces.get (finOfSuit su))).toNat < rankToNat x.rank)
    (hxle : rankToNat x.rank ≤ V) : False := by
  have hdb := hb.pileDepth_bound j
  have hxs : (SUIT (encodeCard x)).toNat = suitToNat su := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat', hxsuit]
    have := suitToNat_lt su
    omega
  have hxv : (VALUE (encodeCard x)).toNat = rankToNat x.rank := encodeCard_VALUE x
  have hxfree : isFreeCard g p (encodeCard x) := by
    by_contra hnf
    have := hnotfree (encodeCard x) hxs hnf (by omega)
    omega
  by_cases hdj : 0 < (p.pileDepth.get j).toNat
  · exact h.no_flute_at_exit hwf hb j hdj (by omega) hnotfree hstopsuit hstopval hstopfree
      (hstopbnd hdj) hxmem hxsuit hxgt hxle
  · -- solver-empty pile
    push Not at hdj
    have hd0 : (p.pileDepth.get j).toNat = 0 := by
      show (p.pileDepth.get j).toNat = 0
      omega
    rcases h.column_cases hwf hb j hxmem with hnf | ⟨m, -, hm1, hm2, -⟩ | ⟨-, hking⟩
    · exact hnf hxfree
    · -- an empty pile's flute is trivial
      have hfe : p.pileFlute.get j = 1 :=
        (hb.pileBase j).flute_empty (UInt8.toNat_inj.mp (show (p.pileDepth.get j).toNat
          = (0 : UInt8).toNat from by simpa using hdj))
      rw [hfe] at hm2
      simp only [show ((1 : UInt8)).toNat = 1 from rfl] at hm2
      omega
    · -- a king-run card puts the stop card above the frontier, so it is free
      refine hstopfree ?_
      have hs4 : suitToNat su < 4 := suitToNat_lt su
      have hfin : finOfSuit x.suit = (⟨suitToNat su, hs4⟩ : Fin 4) :=
        Fin.ext (show suitToNat x.suit = suitToNat su from by rw [hxsuit])
      rw [hfin] at hking
      refine (hb.king_frontier ⟨suitToNat su, hs4⟩).2 stop ?_ (by omega) (by omega)
      refine UInt8.toNat_inj.mp ?_
      rw [hstopsuit]
      show suitToNat su = ((⟨suitToNat su, hs4⟩ : Fin 4).val.toUInt8).toNat
      rw [show ((⟨suitToNat su, hs4⟩ : Fin 4).val.toUInt8).toNat
        = ((UInt8.ofNat (suitToNat su))).toNat from rfl, UInt8.toNat_ofNat']
      omega

/-! ### The suit-complete exit

When the walk runs the suit out to the king there is no stopping card to reason
about, and the two cases separate cleanly:

* a **non-empty** pile still cannot give up a played card — every card of the suit
  above the foundation top is free by then, and boundaries never are, so
  `no_flute_at_complete` needs no stop card at all;
* the suit's **king pile** is drained *completely*: all of its cards are of that suit
  and above the foundation top, hence played, and a card cannot be both on a
  foundation and in a column (`column_nil_of_all_played`). -/

/-- A column whose every card is already on a foundation is empty. -/
theorem column_nil_of_all_played {w : State} (hcount : ∀ c : Card, countState w c = 1)
    (j : Fin 10) (hall : ∀ d ∈ w.tableau j, countFoundation w.foundations d = 1) :
    w.tableau j = [] := by
  by_contra hne
  obtain ⟨d, hd⟩ : ∃ d, d ∈ w.tableau j := by
    cases hcol : w.tableau j with
    | nil => exact absurd hcol hne
    | cons y ys => exact ⟨y, List.mem_cons_self⟩
  have h1 := hall d hd
  have h2 : 1 ≤ countTableau w.tableau d := one_le_countTableau hd
  have h3 := hcount d
  unfold countState at h3
  omega

/-- **At a suit-complete exit no non-empty pile gives up a played card.**  Every card
of the suit above the foundation top is free once the walk has run to the king, and a
pile's boundary is never free — so the boundary above a played flute card cannot exist. -/
theorem StateMatchesSolverPos.no_flute_at_complete {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {su : Suit} (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ 13 → (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat)
    {x : Card} (hxmem : x ∈ s.tableau j) (hxsuit : x.suit = su)
    (hxgt : (VALUE (p.aces.get (finOfSuit su))).toNat < rankToNat x.rank) : False := by
  have hdb := hb.pileDepth_bound j
  have hbridge : (p.pileDepth.get j).toNat = (p.pileDepth.get j).toNat := rfl
  have hidxj : (p.pileDepth.get j).toNat - 1 < 5 := by omega
  have hxs : (SUIT (encodeCard x)).toNat = suitToNat su := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat', hxsuit]
    have := suitToNat_lt su
    omega
  have hxv : (VALUE (encodeCard x)).toNat = rankToNat x.rank := encodeCard_VALUE x
  have hxr13 : rankToNat x.rank ≤ 13 := rankBounded _
  have hxfree : isFreeCard g p (encodeCard x) := by
    by_contra hnf
    have := hnotfree (encodeCard x) hxs hnf (by omega)
    omega
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hxmem
  have hxi : (s.tableau j)[idx]'hidxlt = x := hidxeq
  have habove := h.free_above_boundary hwf hb j hidxlt (by rw [hxi]; exact hxfree)
  have hLen : (s.tableau j).length + 1
      = (p.pileDepth.get j).toNat + (p.pileFlute.get j).toNat :=
    h.flute_match j (by omega)
  obtain ⟨hs0, hv0⟩ := flute_elem h j (by omega)
    ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩ rfl idx (by omega) hidxlt
  rw [hxi] at hs0 hv0
  rw [encodeCard_VALUE] at hv0
  -- the boundary carries the suit, sits above `x`, and is real
  have hbs : (SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩)).toNat
      = suitToNat su := by rw [← hs0]; exact hxs
  have hbreal : IsRealCard ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩) :=
    hwf.pos2card_real j _
  have hbnotfree :
      ¬ isFreeCard g p ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩) :=
    depth_card_not_free hwf hb j ⟨(p.pileDepth.get j).toNat - 1, hidxj⟩
      (show (p.pileDepth.get j).toNat - 1 < (p.pileDepth.get j).toNat from by omega)
  have := hnotfree _ hbs hbnotfree hbreal.2.2
  omega

/-! ### The tail, assembled

At a non-completing exit no column gives up a card (`no_played_in_column`), so the
whole pending run comes out of the cells: the tableau is untouched, the position moves
only in `aces`, and both the matching (`tailPile`) and the king configuration carry
over directly. -/

/-- Every card of the walked run carries the suit and a rank inside the window. -/
theorem rank_mem_runFrom : ∀ (n : Nat) (c₀ c : Card), c ∈ runFrom (some c₀) n →
    c.suit = c₀.suit ∧ rankToNat c₀.rank ≤ rankToNat c.rank ∧
      rankToNat c.rank < rankToNat c₀.rank + n := by
  intro n
  induction n with
  | zero => intro c₀ c hc; simp at hc
  | succ n ih =>
    intro c₀ c hc
    rw [runFrom_some, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨rfl, le_refl _, by omega⟩
    · cases hnc : nextCard c₀ with
      | none => rw [hnc] at hc; simp at hc
      | some c₁ =>
        rw [hnc] at hc
        obtain ⟨hsu, hge, hlt⟩ := ih c₁ c hc
        have h1 : c₁.suit = c₀.suit := nextCard_suit hnc
        have h2 : rankToNat c₁.rank = rankToNat c₀.rank + 1 := nextCard_rank hnc
        exact ⟨hsu.trans h1, by omega, by omega⟩

/-- **At a non-completing exit the tail plays entirely out of the cells.**  Every card
of the walked run lies in the window, so `no_played_in_column` forbids it from sitting
in any column; the tableau therefore comes through untouched. -/
theorem StateMatchesSolverPos.tailPlaysCells {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {su : Suit} {found : Nat} {stop : UInt8}
    (hfree : ∀ d ∈ runFrom (nextFoundationCard s su) found, isFreeCard g p (encodeCard d))
    (hstopsuit : (SUIT stop).toNat = suitToNat su)
    (hstopval : (VALUE stop).toNat = (VALUE (p.aces.get (finOfSuit su))).toNat + found + 1)
    (hstopreal : (VALUE stop).toNat ≤ 13)
    (hstopfree : ¬ isFreeCard g p stop)
    (hstopbnd : ∀ (j : Fin 10) (hd : 0 < (p.pileDepth.get j).toNat),
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound j; omega⟩ ≠ stop)
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat + found →
      (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat) :
    ∃ v : State, PlaysAll s (runFrom (nextFoundationCard s su) found) v ∧
      (∀ j : Fin 10, v.tableau j = s.tableau j) ∧
      (∀ c : Card, countState v c = 1) := by
  obtain ⟨v, hall, -, hcount, hchanged⟩ :=
    exists_playsAll_pending hwf hb h su found s (fun q => ⟨0, by simp⟩) h.cards_count hfree
  refine ⟨v, hall, fun j => ?_, hcount⟩
  rcases hchanged j with hsame | ⟨d, hdrun, hdmem⟩
  · exact hsame
  · -- a run card in a column is impossible
    exfalso
    cases hnf : nextFoundationCard s su with
    | none => rw [hnf, runFrom_none] at hdrun; simp at hdrun
    | some c₀ =>
      rw [hnf] at hdrun
      obtain ⟨hsu0, hready0⟩ := nextFoundationCard_spec hnf
      obtain ⟨hdsuit, hdge, hdlt⟩ := rank_mem_runFrom found c₀ d hdrun
      -- the run starts one above the foundation top
      have hc0rank : rankToNat c₀.rank = optRankToNat (s.foundations su) + 1 := by
        rw [← hsu0]
        exact nextRankNat _ _ hready0.symm
      have hfv := h.foundation_value su
      exact h.no_played_in_column hwf hb j hnotfree hstopsuit hstopval hstopreal hstopfree
        (hstopbnd j) hdmem (hdsuit.trans hsu0) (by omega) (by omega)

/-- **The tail, as one `Simulates`** (non-completing exit).  The run comes out of the
cells, so the tableau is untouched: `tailPile` gets `Or.inl` at every pile and
`frameAll` carries the configuration.  The only thing the caller still owes is that the
position's `aces` really read off the new foundations — which is exactly what the
solver's `aces[su] := card - 1` write establishes. -/
theorem SimulatesNorm.tailPlays {g : Globals} {s : State} {p q : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k) {su : Suit} {found : Nat} {stop : UInt8}
    (hfree : ∀ d ∈ runFrom (nextFoundationCard s su) found, isFreeCard g p (encodeCard d))
    (hstopsuit : (SUIT stop).toNat = suitToNat su)
    (hstopval : (VALUE stop).toNat = (VALUE (p.aces.get (finOfSuit su))).toNat + found + 1)
    (hstopreal : (VALUE stop).toNat ≤ 13)
    (hstopfree : ¬ isFreeCard g p stop)
    (hstopbnd : ∀ (j : Fin 10) (hd : 0 < (p.pileDepth.get j).toNat),
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hb.pileDepth_bound j; omega⟩ ≠ stop)
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat + found →
      (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat)
    (hqd : q.pileDepth = p.pileDepth) (hqf : q.pileFlute = p.pileFlute)
    (hqkings : q.kings = p.kings) :
    ∃ v : State, PlaysAll s (runFrom (nextFoundationCard s su) found) v ∧
      ((∀ su' : Suit, q.aces.get (finOfSuit su') = encodeFoundation su' (v.foundations su')) →
        SimulatesNorm g s p k v q k ∅ 0xffff) := by
  obtain ⟨v, hall, hframe, hcount⟩ :=
    hk.toMatches.tailPlaysCells hwf hb hfree hstopsuit hstopval hstopreal hstopfree
      hstopbnd hnotfree
  refine ⟨v, hall, fun hqaces => ?_⟩
  -- the piles are untouched, so every clause of the matching transfers
  have hdeq : ∀ i : Fin 10, q.pileDepth.get i = p.pileDepth.get i := by
    intro i; rw [hqd]
  have hmatch := hk.toMatches.tailPile hcount (fun j => Or.inl (hframe j)) hqd hqf
    (fun j _ _ d _ => by rw [hqkings]) hqaces
  exact hk.frameAll hall.toNormReach hmatch hframe hdeq hqkings

/-- **The suit-complete exit's frame.**  Once the walk has run the suit out to the
king, a non-empty pile still gives up nothing (`no_flute_at_complete`), and the suit's
king pile — every card of which is now on the foundation — is emptied outright
(`column_nil_of_all_played`).  The completeness premise is left to the caller since it
speaks about the resulting state. -/
theorem StateMatchesSolverPos.tailPlaysComplete {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    {su : Suit} {found : Nat}
    (hfree : ∀ d ∈ runFrom (nextFoundationCard s su) found, isFreeCard g p (encodeCard d))
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g p c →
      (VALUE c).toNat ≤ 13 → (VALUE c).toNat ≤ (VALUE (p.aces.get (finOfSuit su))).toNat) :
    ∃ v : State, PlaysAll s (runFrom (nextFoundationCard s su) found) v ∧
      (∀ c : Card, countState v c = 1) ∧
      (optRankToNat (v.foundations su) = 13 →
        ∀ j : Fin 10, v.tableau j = s.tableau j ∨
          (v.tableau j = [] ∧ (p.pileDepth.get j).toNat = 0 ∧
            ∀ e ∈ (s.tableau j).getLast?, suitToNat e.suit = suitToNat su)) := by
  obtain ⟨v, hall, hdrop, hcount, hchanged⟩ :=
    exists_playsAll_pending hwf hb h su found s (fun q => ⟨0, by simp⟩) h.cards_count hfree
  refine ⟨v, hall, hcount, fun hdone j => ?_⟩
  rcases hchanged j with hsame | ⟨d, hdrun, hdmem⟩
  · exact Or.inl hsame
  · -- column `j` gave up a run card
    cases hnf : nextFoundationCard s su with
    | none => rw [hnf, runFrom_none] at hdrun; simp at hdrun
    | some c₀ =>
      rw [hnf] at hdrun
      obtain ⟨hsu0, hready0⟩ := nextFoundationCard_spec hnf
      obtain ⟨hdsuit, hdge, -⟩ := rank_mem_runFrom found c₀ d hdrun
      have hc0rank : rankToNat c₀.rank = optRankToNat (s.foundations su) + 1 := by
        rw [← hsu0]; exact nextRankNat _ _ hready0.symm
      have hfv := h.foundation_value su
      have hdsu : d.suit = su := hdsuit.trans hsu0
      have hdgt : (VALUE (p.aces.get (finOfSuit su))).toNat < rankToNat d.rank := by omega
      by_cases hdj : 0 < (p.pileDepth.get j).toNat
      · exact absurd (h.no_flute_at_complete hwf hb j hdj hnotfree hdmem hdsu hdgt) (fun h => h)
      · -- the suit's king pile: everything on it is now on the foundation
        push Not at hdj
        have hd0 : (p.pileDepth.get j).toNat = 0 := by
          show (p.pileDepth.get j).toNat = 0
          omega
        -- the column is one suit's run, and `d` fixes that suit
        have hne : s.tableau j ≠ [] := by
          intro hnil; rw [hnil] at hdmem; cases hdmem
        obtain ⟨e, he⟩ : ∃ e, (s.tableau j).getLast? = some e := by
          cases hl : (s.tableau j).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
          | some e => exact ⟨e, rfl⟩
        have hrun := h.empty_pile_suit j hd0 he
        -- every card of the column carries `e`'s suit
        have hcolsuit : ∀ (c : Card), c ∈ s.tableau j → suitToNat c.suit = suitToNat e.suit := by
          intro c hc
          obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hc
          have hrevlt : (s.tableau j).length - 1 - idx < (s.tableau j).reverse.length := by
            simp only [List.length_reverse]; omega
          have hjm : (s.tableau j).length - 1 - idx
              < ((s.tableau j).reverse.map encodeCard).length := by simpa using hrevlt
          obtain ⟨hs, -⟩ := hrun ⟨_, hjm⟩
          have hget : ((s.tableau j).reverse.map encodeCard).get ⟨_, hjm⟩
              = encodeCard ((s.tableau j).reverse[(s.tableau j).length - 1 - idx]'hrevlt) := by
            simp only [List.get_eq_getElem, List.getElem_map]
          rw [hget] at hs
          have hlr : (s.tableau j).reverse.length = (s.tableau j).length := by
            simp only [List.length_reverse]
          have hrev : (s.tableau j).reverse[(s.tableau j).length - 1 - idx]'hrevlt = c := by
            rw [List.getElem_reverse hrevlt, ← hidxeq]
            congr 1
            omega
          rw [hrev, encodeCard_SUIT] at hs
          have h2 := congrArg UInt8.toNat hs
          rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h2
          have := suitToNat_lt c.suit
          have := suitToNat_lt e.suit
          omega
        -- so they are all of suit `su`, hence all already played
        have hesu : suitToNat e.suit = suitToNat su := by
          rw [← hcolsuit d hdmem, hdsu]
        refine Or.inr ⟨?_, hd0, fun e' he' => ?_⟩
        · refine column_nil_of_all_played hcount j (fun c hc => ?_)
          obtain ⟨kk, hkk⟩ := hdrop j
          have hcs : c ∈ s.tableau j := by
            rw [hkk] at hc
            exact List.mem_of_mem_drop hc
          have hcsu : c.suit = su := suitToNat_inj (by rw [hcolsuit c hcs, hesu])
          unfold countFoundation
          rw [hcsu, if_neg (by
            have := rankBounded c.rank
            omega)]
        · -- the emptied column carried exactly `su`
          have hee : e' = e := Option.some.inj ((Option.mem_def.1 he').symm.trans he)
          rw [hee]; exact hesu
