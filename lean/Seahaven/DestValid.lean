import Seahaven.GetDestination
import Seahaven.SolverSpecMove

open Solver

/-!
# From `getDestination` to `move_merged`'s preconditions

`getDest_spec` says what the destination walk returns; `move_merged` wants that
repackaged as `MoveValid`/`DestValid`.  The only non-bookkeeping step is the
`toPile = EXTRA` case: "no pile's boundary is `B + n`" follows from
`round_trip_inv` — a card sits in exactly one slot, so if it were some pile's
boundary then `pftVal` would have been `1` and the walk would have named that
pile.

Split out on its own (rather than living in `RecCheckSound`, where these were
originally proved) because `MoveSimulatedReduce`/`Phase1Sim` need `destValid_of_getDest`
too, and they sit upstream of `RecCheckSound` in the import order (`RecCheckSound`
needs `Phase1Sim`, transitively, for `MoveSimulated`).
-/

/-- A card is some pile's current boundary exactly when its `pftVal` is `1`. -/
theorem boundary_pftVal_one {g : Globals} {p : PosType} (hwf : WellFormedLayout g)
    (h : SolverInvBase g p) (c : UInt8)
    (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hb5 : (p.pileDepth.get j).toNat - 1 < 5)
    (hbnd : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩ = c) :
    pftVal g p c = 1 := by
  obtain ⟨hpj, hdj'⟩ := hwf.round_trip_inv j ⟨(p.pileDepth.get j).toNat - 1, hb5⟩
  rw [hbnd] at hpj hdj'
  -- `Fin.val` of a literal `⟨…⟩` is an `omega` atom; ascribe the reduced form
  have hdepth : (cardDepth g c).toNat = (p.pileDepth.get j).toNat - 1 := hdj'
  have hpile : (cardPile g c).toNat = j.val := hpj
  clear hdj' hpj
  have hp10 : (cardPile g c).toNat < 10 := by have := j.isLt; omega
  have hjeq : (⟨(cardPile g c).toNat, hp10⟩ : Fin 10) = j := Fin.ext hpile
  have hbound := h.pileDepth_bound j
  have hda : ((p.pileDepth.get j).toInt32).toInt = ((p.pileDepth.get j).toNat : Int) :=
    uint8_toInt32_toInt _
  have hdb : ((cardDepth g c).toUInt32.toInt32).toInt = ((cardDepth g c).toNat : Int) :=
    uint8_toInt32_toInt _
  rw [pftVal_eq g p c hp10, hjeq]
  refine Int32.toInt_inj.mp ?_
  rw [int32_toInt_sub _ _ (by rw [hda, hdb]; omega) (by rw [hda, hdb]; omega), hda, hdb,
    show ((1 : Int32)).toInt = 1 from by decide]
  omega

/-- Converse of `boundary_pftVal_one`: `pftVal = 1` puts the card at its pile's
current boundary. -/
theorem pftVal_one_depth {g : Globals} {p : PosType} (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10) (hcd : (cardDepth g c).toNat ≤ 5)
    (h1 : pftVal g p c = 1) :
    (cardDepth g c).toNat + 1 = (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat := by
  have hda : ((p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt32).toInt
      = ((p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat : Int) := uint8_toInt32_toInt _
  have hdb : ((cardDepth g c).toUInt32.toInt32).toInt = ((cardDepth g c).toNat : Int) :=
    uint8_toInt32_toInt _
  have h255 : (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat < 256 :=
    (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat_lt_size
  have := congrArg Int32.toInt (h1.symm.trans (pftVal_eq g p c hp10))
  rw [show ((1 : Int32)).toInt = 1 from by decide,
    int32_toInt_sub _ _ (by rw [hda, hdb]; omega) (by rw [hda, hdb]; omega), hda, hdb] at this
  omega

/-- `getDest_spec` restated in the `.toNat` spelling `move_merged` uses (the two are
definitionally equal, but `omega` treats `x.toNat` and `x.toNat` as unrelated
atoms — see the note in `lean-proof-gotchas`). -/
theorem getDest_spec' {g : Globals} {p : PosType} {pile : UInt32}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hp : pile.toNat < 10)
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat)
    (hb5 : (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1 < 5) :
    let B := (g.pos2card.get ⟨pile.toNat, hp⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩
    (B = (p.kings.get ⟨(SUIT B).toNat,
            (hwf.pos2card_real ⟨pile.toNat, hp⟩ ⟨_, hb5⟩).1⟩) ∧
        getDestination p pile g = .ok (10 + SUIT B) g)
    ∨ (∃ n : Nat, 1 ≤ n ∧ (VALUE B).toNat + n ≤ 13 ∧
        (∀ j, 1 ≤ j → j < n → isFreeCard g p (B + UInt8.ofNat j)) ∧
        ¬ isFreeCard g p (B + UInt8.ofNat n) ∧
        getDestination p pile g
          = .ok (if (pftVal g p (B + UInt8.ofNat n) == 1) = true
                 then cardPile g (B + UInt8.ofNat n) else 14) g) :=
  getDest_spec g p pile hwf hcan hp hd

set_option maxHeartbeats 1000000 in
/-- **`getDestination` establishes `move_merged`'s destination
preconditions.** -/
theorem destValid_of_getDest {g : Globals} {p : PosType} (hwf : WellFormedLayout g)
    (hcan : IsCanonicalPos g p) {pile : UInt32} (hp : pile.toNat < 10)
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat)
    (hb5 : (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1 < 5)
    {toPile : UInt8}
    (hrun : EStateM.run (getDestination p pile) g = .ok toPile g) :
    SolverSpec.MoveValid g p pile toPile ∧
      SolverSpec.DestValid g p ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩) toPile := by
  have hbase := hcan.toSolverInvBase
  have hreal : IsRealCard ((g.pos2card.get ⟨pile.toNat, hp⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩) := hwf.pos2card_real _ _
  have hmv10 : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hp⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hp)
  have hdmv : 0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat := by rw [hmv10]; exact hd
  rcases getDest_spec' hwf hcan hp hd hb5 with ⟨hkeq, hrun'⟩ | ⟨n, hn1, hnle, hfree, hnf, hrun'⟩
  · -- king pile
    have htp := (EStateM.Result.ok.inj (hrun.symm.trans hrun')).1
    subst htp
    have hs4 : (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat < 4 := hreal.1
    have htpn : (10 + SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat
        = 10 + (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat := by
      rw [UInt8.toNat_add, show ((10 : UInt8).toNat = 10) from rfl]
      omega
    exact ⟨⟨hp, by omega, hdmv⟩, Or.inl ⟨⟨_, hs4⟩, rfl, hkeq.symm, htpn⟩⟩
  · -- the walk
    have hs4 : (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat < 4 := hreal.1
    obtain ⟨hsn, hvn⟩ := card_walk_suit_value _ n (by omega)
    have h64 : ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n).toNat < 64 :=
      card_walk_lt64 _ hs4 n (by omega)
    have hcreal : IsRealCard ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n) :=
      ⟨by rw [hsn]; exact hs4, by omega, by omega⟩
    have hcp10 := cardPile_lt10 g hwf _ h64
    have hcd5 := hwf.depth_le _ hcreal
    have htp := (EStateM.Result.ok.inj (hrun.symm.trans hrun')).1
    by_cases hpft : (pftVal g p ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n) == 1) = true
    · -- the card is at its own pile's boundary: that pile is the destination
      rw [if_pos hpft] at htp
      subst htp
      have hdep := pftVal_one_depth _ hcp10 hcd5 (beq_iff_eq.1 hpft)
      have hdb := hbase.pileDepth_bound ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩
      refine ⟨⟨hp, by omega, hdmv⟩,
        Or.inr ⟨n, hn1, hnle, hfree, hnf, Or.inl ⟨hcp10, by omega, by omega, ?_⟩⟩⟩
      have hidx : (⟨(p.pileDepth.get ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩).toNat - 1, by omega⟩ : Fin 5)
          = ⟨(cardDepth g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, by omega⟩ := by
        refine Fin.ext ?_
        show (p.pileDepth.get ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩).toNat - 1
          = (cardDepth g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat
        omega
      rw [hidx]
      exact hwf.round_trip _ hcreal (by omega)
    · -- at no pile's boundary: the destination is EXTRA
      rw [if_neg hpft] at htp
      subst htp
      refine ⟨⟨hp, by decide, hdmv⟩, Or.inr ⟨n, hn1, hnle, hfree, hnf, Or.inr ⟨by rfl, ?_⟩⟩⟩
      intro j hidx hdj heq
      exact hpft (by
        rw [beq_iff_eq]
        exact boundary_pftVal_one hwf hbase _ j hdj hidx heq)
