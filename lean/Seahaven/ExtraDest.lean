import Seahaven.DestComplete

/-!
# `EXTRA` means the card fits nowhere

`solverGetDestination` returns `EXTRA` when its walk `B+1, B+2, …` — through cards
that are already *free* — stops at a card that is **not** a pile boundary.  This file
turns that into the physical statement completeness needs:

> if the destination is `EXTRA`, no column can accept `B`.

The argument is the one the walk itself encodes.  Suppose some column `q` accepted
`B`; then `q`'s top card is `B + 1`.  Every card physically above a column's boundary
is free (`free_above_boundary` — a non-free card sits at its own dealt slot, which is
*at or below* its own boundary), and the run above `q`'s boundary descends by one, so
the cards `B+1, …, B+n₀-1` are exactly the ones above `q`'s boundary and `B + n₀` *is*
that boundary — which is never free (`boundary_not_free`).  So the walk stops at
`n = n₀` on a boundary card, and the destination is `q`, not `EXTRA`.

The degenerate shapes close the same way: if `q` holds nothing above its boundary the
top *is* the boundary and `n = 1`; if `q` is solver-empty its whole column is a king
run, every card of it is free, and the walk would have to run past the king.
-/

/-! ## Above the boundary is free -/

/-- **A card physically above a column's boundary is free.**  If it were not, it
would sit at its own dealt slot — necessarily *at or below* its own pile's boundary —
and a card is in only one column, so the two positions would have to coincide. -/
theorem free_of_slot_above_boundary {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) {q : Fin 10} {d : Card} {r : Nat}
    (hr : (p.pileDepth.get q).toNat ≤ r) (hrl : r < (u.tableau q).reverse.length)
    (hslotq : (u.tableau q).reverse[r]'hrl = d) :
    isFreeCard g p (encodeCard d) := by
  have hnd : NoDupState u := fun c => le_of_eq (hcount c)
  by_contra hnf
  have hreal : IsRealCard (encodeCard d) := encodeCard_real d
  have hp10 : (cardPile g (encodeCard d)).toNat < 10 := hwf.pile_lt _ hreal
  set P : Fin 10 := ⟨(cardPile g (encodeCard d)).toNat, hp10⟩ with hP
  rw [isFreeCard_iff g p (encodeCard d) hp10, ← hP] at hnf
  have hlt : (cardDepth g (encodeCard d)).toNat < (p.pileDepth.get P).toNat := by omega
  have hd5 : (cardDepth g (encodeCard d)).toNat < 5 := by have := hd6 P; omega
  have hnL : (p.pileDepth.get P).toNat ≤ (u.tableau P).length := (hdm P).1
  have hrevP : (cardDepth g (encodeCard d)).toNat < (u.tableau P).reverse.length := by
    simp only [List.length_reverse]; omega
  -- a non-free card sits at its own dealt slot, at or below its own boundary
  have hslot : (u.tableau P).reverse[(cardDepth g (encodeCard d)).toNat]'hrevP = d :=
    encodeCard_inj (by
      rw [(hdm P).resident_code (by omega) hrevP]
      exact hwf.round_trip (encodeCard d) hreal hd5)
  have hmemP : d ∈ u.tableau P := by
    rw [← hslot]; exact List.mem_reverse.mp (List.getElem_mem ..)
  have hmemq : d ∈ u.tableau q := by
    rw [← hslotq]; exact List.mem_reverse.mp (List.getElem_mem ..)
  have hqP : q = P := hnd.pile_unique hmemq hmemP
  subst hqP
  have hnodup : (u.tableau P).reverse.Nodup := List.nodup_reverse.mpr (hnd.column_nodup P)
  have := hnodup.getElem_inj_iff.1 (hslot.trans hslotq.symm)
  omega

/-- The same, read off the column directly. -/
theorem free_above_boundary {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1) {q : Fin 10} {r : Nat}
    (hr : (p.pileDepth.get q).toNat ≤ r) (hrl : r < (u.tableau q).reverse.length) :
    isFreeCard g p (encodeCard ((u.tableau q).reverse[r]'hrl)) :=
  free_of_slot_above_boundary hwf hd6 hdm hcount hr hrl rfl

/-! ## The walk's stopping card, read off the column -/

/-- The code of the card at reverse index `r ≥ depth`, in `Nat` terms: the boundary's
code plus the distance down to it. -/
private theorem above_code_nat {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    {q : Fin 10} (hdpos : 0 < (p.pileDepth.get q).toNat) {r : Nat}
    (hr : (p.pileDepth.get q).toNat ≤ r) (hrl : r < (u.tableau q).reverse.length)
    (hidx : (p.pileDepth.get q).toNat - 1 < 5) :
    (encodeCard ((u.tableau q).reverse[r]'hrl)).toNat
        + (r - (p.pileDepth.get q).toNat) + 1
      = ((g.pos2card.get q).get ⟨(p.pileDepth.get q).toNat - 1, hidx⟩).toNat := by
  obtain ⟨hs0, hv0⟩ := (hdm q).above_code hdpos hr hrl
  -- restate both in this file's spelling of the boundary (`Fin` proofs are irrelevant)
  have hs : SUIT (encodeCard ((u.tableau q).reverse[r]'hrl))
      = SUIT ((g.pos2card.get q).get ⟨(p.pileDepth.get q).toNat - 1, hidx⟩) := hs0
  have hv : (VALUE (encodeCard ((u.tableau q).reverse[r]'hrl))).toNat
      = (VALUE ((g.pos2card.get q).get ⟨(p.pileDepth.get q).toNat - 1, hidx⟩)).toNat
          - 1 - (r - (p.pileDepth.get q).toNat) := hv0
  have hSs : (SUIT (encodeCard ((u.tableau q).reverse[r]'hrl))).toNat
      = (SUIT ((g.pos2card.get q).get ⟨(p.pileDepth.get q).toNat - 1, hidx⟩)).toNat := by
    rw [hs]
  have hSB := SUIT_toNat ((g.pos2card.get q).get
    (⟨(p.pileDepth.get q).toNat - 1, hidx⟩ : Fin 5))
  have hVB := VALUE_toNat ((g.pos2card.get q).get
    (⟨(p.pileDepth.get q).toNat - 1, hidx⟩ : Fin 5))
  have hSe := SUIT_toNat (encodeCard ((u.tableau q).reverse[r]'hrl))
  have hVe := VALUE_toNat (encodeCard ((u.tableau q).reverse[r]'hrl))
  have hvpos : 1 ≤ (VALUE (encodeCard ((u.tableau q).reverse[r]'hrl))).toNat := by
    rw [encodeCard_VALUE]
    exact rankToNat_pos _
  obtain ⟨-, -, hB13⟩ : IsRealCard ((g.pos2card.get q).get
      (⟨(p.pileDepth.get q).toNat - 1, hidx⟩ : Fin 5)) := hwf.pos2card_real q _
  omega

/-! ## `EXTRA` fits nowhere -/

/-- **No column accepts the boundary card when the destination is `EXTRA`.**  The
hypotheses are `DestValid`'s `EXTRA` branch verbatim: the walk `B+1 … B+n` runs
through free cards, stops at an un-free `B + n`, and `B + n` is no pile's boundary. -/
theorem no_column_accepts_of_extra {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    {c : Card} {n : Nat} (hn1 : 1 ≤ n) (hnval : (VALUE (encodeCard c)).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (encodeCard c + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (encodeCard c + UInt8.ofNat n))
    (hnoB : ∀ (j : Fin 10) (hidx : (p.pileDepth.get j).toNat - 1 < 5),
      0 < (p.pileDepth.get j).toNat →
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩
        ≠ encodeCard c + UInt8.ofNat n)
    (q : Fin 10) : (u.tableau q).head? ≠ nextCard c := by
  intro hhead
  -- name the top card and its code
  obtain ⟨e, he⟩ : ∃ e, nextCard c = some e := by
    cases hnc : nextCard c with
    | none =>
      rw [hnc] at hhead
      -- a king would need `VALUE c = 13`, contradicting `VALUE c + n ≤ 13`
      have := nextCard_none_rank hnc
      have hVc := encodeCard_VALUE c
      omega
    | some e => exact ⟨e, rfl⟩
  rw [he] at hhead
  have hcode1 : encodeCard e = encodeCard c + 1 :=
    encodeCard_succ (congrArg suitToNat (nextCard_suit he)) (nextCard_rank he)
  have hcne : u.tableau q ≠ [] := by
    intro hnil; rw [hnil] at hhead; simp at hhead
  have hL : 0 < (u.tableau q).length := List.length_pos_iff_ne_nil.2 hcne
  have hrl : (u.tableau q).length - 1 < (u.tableau q).reverse.length := by
    simp only [List.length_reverse]; omega
  have htop : (u.tableau q).reverse[(u.tableau q).length - 1]'hrl = e := by
    have := head?_reverse_last hL hrl
    rw [hhead] at this
    exact (Option.some.inj this).symm
  set D := (p.pileDepth.get q).toNat with hD
  set L := (u.tableau q).length with hLdef
  have hDL : D ≤ L := (hdm q).1
  have hC := (encodeCard c).toNat_lt_size
  have hVc := VALUE_toNat (encodeCard c)
  have hSc := SUIT_toNat (encodeCard c)
  have hSc4 : (SUIT (encodeCard c)).toNat < 4 := (encodeCard_real c).1
  have hone : ((1 : UInt8)).toNat = 1 := rfl
  have hcode1N : (encodeCard e).toNat = (encodeCard c).toNat + 1 := by
    rw [hcode1, UInt8.toNat_add, hone]
    omega
  -- the arithmetic of `B + k`, valid throughout since values stay below 14
  have hplus : ∀ k : Nat, k ≤ n → (encodeCard c + UInt8.ofNat k).toNat
      = (encodeCard c).toNat + k := by
    intro k hk
    rw [UInt8.toNat_add, UInt8.toNat_ofNat']
    omega
  by_cases hd0 : D = 0
  · -- ## a solver-empty column: the whole run is free, so the walk cannot stop
    obtain ⟨su, hrun⟩ := (hdm q).king_run (by simpa [hD] using hd0)
    -- the top card's value pins the column length
    obtain ⟨-, hvtop⟩ := hrun ((u.tableau q).length - 1) hrl
    rw [htop] at hvtop
    have hVe := encodeCard_VALUE e
    have hrevlen : (u.tableau q).reverse.length = L := by simp [hLdef]
    -- `B + n` still sits on this column, hence is free
    have hidx : L - n < (u.tableau q).reverse.length := by
      rw [hrevlen]; omega
    have hfree := free_above_boundary hwf hd6 hdm hcount (q := q) (r := L - n)
      (by omega) hidx
    obtain ⟨-, hvn⟩ := hrun (L - n) hidx
    have hVn := encodeCard_VALUE ((u.tableau q).reverse[L - n]'hidx)
    have hSn : (SUIT (encodeCard ((u.tableau q).reverse[L - n]'hidx))).toNat
        = (SUIT (encodeCard e)).toNat := by
      obtain ⟨hs1, -⟩ := hrun (L - n) hidx
      obtain ⟨hs2, -⟩ := hrun ((u.tableau q).length - 1) hrl
      rw [htop] at hs2
      rw [hs1, hs2]
    have hSe := SUIT_toNat (encodeCard e)
    have hVe' := VALUE_toNat (encodeCard e)
    have hSn' := SUIT_toNat (encodeCard ((u.tableau q).reverse[L - n]'hidx))
    have hVn' := VALUE_toNat (encodeCard ((u.tableau q).reverse[L - n]'hidx))
    have : encodeCard ((u.tableau q).reverse[L - n]'hidx) = encodeCard c + UInt8.ofNat n := by
      apply UInt8.toNat_inj.mp
      rw [hplus n le_rfl]
      omega
    exact hstop (this ▸ hfree)
  · -- ## an ordinary column
    have hdpos : 0 < D := by omega
    have hidx5 : D - 1 < 5 := by have := hb.pileDepth_bound q; omega
    set B := (g.pos2card.get q).get (⟨D - 1, hidx5⟩ : Fin 5) with hBdef
    have hbnf : ¬ isFreeCard g p B := boundary_not_free hwf hb q hdpos
    by_cases hLD : L = D
    · -- the top card *is* the boundary, so the walk stops at `n = 1`
      have hres : encodeCard e = B := by
        rw [← htop, (hdm q).resident_code (by simpa [hD] using (by omega : L - 1 < D)) hrl]
        congr 1
        exact Fin.ext (by simp; omega)
      have hn : n = 1 := by
        by_contra hne
        have h1 : (1 : Nat) < n := by omega
        have := hwalk 1 le_rfl h1
        rw [show encodeCard c + UInt8.ofNat 1 = encodeCard e from by
          rw [hcode1]; rfl] at this
        exact hbnf (hres ▸ this)
      refine hnoB q hidx5 hdpos ?_
      rw [← hBdef, ← hres, hcode1, hn]
      rfl
    · -- the run above the boundary is `B+1 … B+n₀`, and `B + n₀` is the boundary
      have hLgt : D < L := by omega
      have hrevlen : (u.tableau q).reverse.length = L := by simp [hLdef]
      set n₀ := 1 + (L - D) with hn₀
      -- the boundary's code
      have hBcode : (encodeCard e).toNat + (L - 1 - D) + 1 = B.toNat := by
        have := above_code_nat hwf hd6 hdm hdpos (r := L - 1) (by omega) hrl hidx5
        rw [htop] at this
        exact this
      have hBn : B = encodeCard c + UInt8.ofNat n₀ := by
        apply UInt8.toNat_inj.mp
        rw [hplus n₀ (by
          -- `n₀ ≤ n`: otherwise the walk stopped strictly inside the run, see below
          by_contra hlt
          have hk : 1 ≤ n ∧ n < n₀ := ⟨hn1, by omega⟩
          -- `B + n` would then sit above the boundary, hence be free
          have hidxn : L - n < (u.tableau q).reverse.length := by rw [hrevlen]; omega
          have hfree := free_above_boundary hwf hd6 hdm hcount (q := q) (r := L - n)
            (by omega) hidxn
          have hcn : (encodeCard ((u.tableau q).reverse[L - n]'hidxn)).toNat
              + ((L - n) - D) + 1 = B.toNat :=
            above_code_nat hwf hd6 hdm hdpos (r := L - n) (by omega) hidxn hidx5
          have : encodeCard ((u.tableau q).reverse[L - n]'hidxn) = encodeCard c
              + UInt8.ofNat n := by
            apply UInt8.toNat_inj.mp
            rw [hplus n le_rfl]
            omega
          exact hstop (this ▸ hfree))]
        omega
      -- so `n = n₀`, and the walk stops on `q`'s boundary
      have hn : n = n₀ := by
        by_contra hne
        have hlt : n₀ < n := by
          rcases Nat.lt_or_ge n n₀ with h | h
          · -- `n < n₀`: `B + n` is above the boundary, hence free
            exfalso
            have hidxn : L - n < (u.tableau q).reverse.length := by rw [hrevlen]; omega
            have hfree := free_above_boundary hwf hd6 hdm hcount (q := q) (r := L - n)
              (by omega) hidxn
            have hcn : (encodeCard ((u.tableau q).reverse[L - n]'hidxn)).toNat
                + ((L - n) - D) + 1 = B.toNat :=
              above_code_nat hwf hd6 hdm hdpos (r := L - n) (by omega) hidxn hidx5
            have : encodeCard ((u.tableau q).reverse[L - n]'hidxn)
                = encodeCard c + UInt8.ofNat n := by
              apply UInt8.toNat_inj.mp
              rw [hplus n le_rfl]
              omega
            exact hstop (this ▸ hfree)
          · omega
        -- `n₀ < n`: the walk claims the boundary itself is free
        exact hbnf (hBn ▸ hwalk n₀ (by omega) hlt)
      exact hnoB q hidx5 hdpos (by rw [← hBdef, hBn, hn])
