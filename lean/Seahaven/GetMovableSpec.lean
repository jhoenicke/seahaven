import Seahaven.RecCheckSound

/-!
# What `solverGetMovable` returns

`solverGetMovable` (`Solver.lean:406`) answers a single question: *which king
configurations of this position can afford the move?*  A move of a `fluteLen`-card
flute needs

* `fluteLen - 1` free cells when it lands **on a column** — the bottom card of the
  flute goes onto the destination card, the other `fluteLen - 1` are parked;
* `fluteLen` free cells when it lands **in the cells** — `EXTRA`, or a king pile
  `10 + su` whose stack is itself in the cells, i.e. `CfgBitSet k su`.

So the returned mask is `possibleKings[fluteLen - 1]` for a column destination,
`possibleKings[fluteLen]` for `EXTRA`, and for a king pile the union of the two —
`possibleKings[fluteLen]` unconditionally, plus `possibleKings[fluteLen - 1]`
restricted to the configurations that really put suit `su` on a pile, which is
exactly the `kingOnPileMap[su]` row.

This file turns that into the two guarded free-cell facts phase 1 consumes
(`StateMatchesKingConfig.movePre_run`'s `hcellsCol`/`hcellsFull`), on the back of
`kingSpaces_spec` — *bit `c` of `possibleKings[x]` ⟺ configuration `c` leaves at
least `x` free cells* — which is the correctness precondition on `kingInfo`.
-/

/-! ## The `kingOnPileMap` bit, at last in `CfgBitSet` terms -/

/-- **`kingOnPileMap[su]` is the set of configurations that give suit `su` a pile.**
`kingOnPileMap_eq` says the row collects the grlex indices whose mask has bit `su`
*clear*, and a clear bit is `¬ CfgBitSet` — see the polarity note in `SolvableBits`. -/
theorem bitSet_kingOnPileMap (su : Suit) (k : Fin 16) :
    BitSet (kingOnPileMap.get (finOfSuit su)) k ↔ ¬ CfgBitSet k su := by
  revert su k
  decide

/-! ## The spec -/

set_option maxHeartbeats 1000000 in
/-- **`solverGetMovable` charges the right number of cells.**  A set bit `i` in the
returned mask certifies, for the configuration `globalCfg ci i`, exactly the
free-cell count the corresponding destination needs.

`hchar` is the precondition on `kingInfo` (`KingInfoCorrect`, what `kingSpaces_spec`
delivers from a `computeKingSpaces` run).  `h1` (`fluteLen ≥ 1`,
i.e. `flute_pos`) keeps the `fluteLen - 1` index from wrapping to `255`.

The four conclusions are, in order: the flute is short enough to be moved at all;
a column destination affords `fluteLen - 1` cells; `EXTRA` affords `fluteLen`; and a
king destination affords `fluteLen` when the suit's stack is in the cells
(`CfgBitSet`) and `fluteLen - 1` when it owns a pile. -/
theorem getMovable_cells {g : Globals} {p : SolverPosType} {ki : KingInfo}
    (hchar : KingInfoCorrect p ki)
    {fluteLen toPile : UInt8} {mv : UInt16} (h1 : 1 ≤ fluteLen.toNat)
    (hmv : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
      = .ok mv g)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hbit : BitSet mv ⟨min i 15, by omega⟩) :
    fluteLen.toNat ≤ 5
    ∧ (toPile.toNat < 10 →
        ((fluteLen.toNat - 1 : Nat) : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i))
    ∧ (¬ toPile.toNat < 14 →
        (fluteLen.toNat : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i))
    ∧ (∀ su : Suit, ¬ toPile.toNat < 10 → toPile.toNat < 14 →
        toPile.toNat - 10 = suitToNat su →
        (CfgBitSet (globalCfg (closureInfoOf p) i) su →
          (fluteLen.toNat : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i))
        ∧ (¬ CfgBitSet (globalCfg (closureInfoOf p) i) su →
          ((fluteLen.toNat - 1 : Nat) : Int)
            ≤ freeCellsOf p (globalCfg (closureInfoOf p) i))) := by
  have hshift : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits _
  have hlt16 : (closureInfoOf p).shiftValue.toNat + i < 16 := by omega
  have hbit0 : ¬ BitSet 0 (⟨min i 15, by omega⟩ : Fin 16) := by
    simp [BitSet]
  -- a flute of more than five cards is never movable: the guard returns `0`
  have hfl5 : fluteLen.toNat ≤ 5 := by
    by_contra hcon
    have hgt : ((5 : UInt8) < fluteLen) = true := by
      simpa using UInt8.lt_iff_toNat_lt.2 (show (5 : UInt8).toNat < fluteLen.toNat by
        simp only [show ((5 : UInt8).toNat = 5) from rfl]; omega)
    have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
        = .ok 0 g := by
      simp only [EStateM.run, solverGetMovable, bind, pure, EStateM.pure, hgt, reduceIte]
    rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1] at hbit
    exact hbit0 hbit
  -- the two `possibleKings` indices, and what `kingSpaces_spec` says about them
  have hi0 : fluteLen.toUInt32.toNat < 6 := by rw [UInt8.toNat_toUInt32]; omega
  have h1u : (1 : UInt8) ≤ fluteLen :=
    UInt8.le_iff_toNat_le.2 (by simp only [show ((1 : UInt8).toNat = 1) from rfl]; omega)
  have hi1v : (fluteLen - 1).toUInt32.toNat = fluteLen.toNat - 1 := by
    rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ h1u]
    simp only [show ((1 : UInt8).toNat = 1) from rfl]
  have hi1 : (fluteLen - 1).toUInt32.toNat < 6 := by rw [hi1v]; omega
  have hg1 : ((5 : UInt8) < fluteLen) = false := by
    simpa using UInt8.le_iff_toNat_le.2 (show fluteLen.toNat ≤ (5 : UInt8).toNat by
      simp only [show ((5 : UInt8).toNat = 5) from rfl]; omega)
  have hA : BitSet (ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16
        ⟨min i 15, by omega⟩ ↔ (fluteLen.toNat : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i) := by
    rw [hchar _ hi0 i hi, UInt8.toNat_toUInt32]
  have hB : BitSet (ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16
        ⟨min i 15, by omega⟩ ↔ ((fluteLen.toNat - 1 : Nat) : Int)
          ≤ freeCellsOf p (globalCfg (closureInfoOf p) i) := by
    rw [hchar _ hi1 i hi, hi1v]
  refine ⟨hfl5, ?_, ?_, ?_⟩
  · -- a column destination: `possibleKings[fluteLen - 1]`
    intro h10
    have h10b : (toPile < 10) = true := by
      simpa using UInt8.lt_iff_toNat_lt.2 (by
        simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
    have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
        = .ok (ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16 g := by
      simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
        hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi1, h10b]
      rfl
    rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1] at hbit
    exact hB.1 hbit
  · -- `EXTRA`: `possibleKings[fluteLen]`
    intro h14
    have h10b : (toPile < 10) = false := by
      simpa using UInt8.le_iff_toNat_le.2 (show (10 : UInt8).toNat ≤ toPile.toNat by
        simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
    have h14b : (toPile < 14) = false := by
      simpa using UInt8.le_iff_toNat_le.2 (show (14 : UInt8).toNat ≤ toPile.toNat by
        simp only [show ((14 : UInt8).toNat = 14) from rfl]; omega)
    have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
        = .ok (ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16 g := by
      simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
        hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0, h10b, h14b]
      rfl
    rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1] at hbit
    exact hA.1 hbit
  · -- a king pile: the union, restricted by `kingOnPileMap`
    intro su h10 h14 hsu
    have h10b : (toPile < 10) = false := by
      simpa using UInt8.le_iff_toNat_le.2 (show (10 : UInt8).toNat ≤ toPile.toNat by
        simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
    have h14b : (toPile < 14) = true := by
      simpa using UInt8.lt_iff_toNat_lt.2 (by
        simp only [show ((14 : UInt8).toNat = 14) from rfl]; omega)
    have h10le : (10 : UInt8) ≤ toPile :=
      UInt8.le_iff_toNat_le.2 (by simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
    have hk4v : (toPile - 10).toUInt32.toNat = suitToNat su := by
      rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ h10le]
      simp only [show ((10 : UInt8).toNat = 10) from rfl]
      omega
    have hk4 : (toPile - 10).toUInt32.toNat < 4 := by rw [hk4v]; exact suitToNat_lt su
    have hkeq : kingOnPileMap.get ⟨(toPile - 10).toUInt32.toNat, hk4⟩
        = kingOnPileMap.get (finOfSuit su) := congrArg kingOnPileMap.get (Fin.ext hk4v)
    have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
        = .ok ((ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16 |||
            ((ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16 &&&
              ((kingOnPileMap.get ⟨(toPile - 10).toUInt32.toNat, hk4⟩)
                >>> (closureInfoOf p).shiftValue.toUInt16))) g := by
      simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
        hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0, hi1, hk4,
        h10b, h14b]
      rfl
    rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1, BitSet_or, BitSet_and, hkeq,
      BitSet_shiftRight_globalCfg _ _ i hlt16, bitSet_kingOnPileMap] at hbit
    constructor
    · -- the stack is in the cells: the `kingOnPileMap` half is unavailable
      intro hcfg
      rcases hbit with h | ⟨-, hnop⟩
      · exact hA.1 h
      · exact absurd hcfg hnop
    · -- the suit owns a pile: either half suffices
      intro _
      rcases hbit with h | ⟨h, -⟩
      · exact le_trans (by omega) (hA.1 h)
      · exact hB.1 h

/-! ## The form phase 1 consumes

`StateMatchesKingConfig.movePre_run` asks for the affordability in *state* terms —
how many cells `s` actually has free.  `freeCellsOf_le` is the bridge: the
configuration's cell budget never exceeds the real one. -/

/-- **`solverGetMovable`'s answer, as `movePre_run`'s two hypotheses.**  Instantiate
`fluteLen := p.pileFlute[pile]` and `su := c.suit` and the two conclusions are
literally `hcellsCol` and `hcellsFull`. -/
theorem getMovable_freeCells {g : Globals} {s : State} {p : SolverPosType} {ki : KingInfo}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (hchar : KingInfoCorrect p ki)
    {fluteLen toPile : UInt8} {mv : UInt16} (h1 : 1 ≤ fluteLen.toNat)
    (hmv : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
      = .ok mv g)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hk : StateMatchesKingConfig g s p (globalCfg (closureInfoOf p) i))
    (hbit : BitSet mv ⟨min i 15, by omega⟩)
    {su : Suit} (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      toPile.toNat - 10 = suitToNat su) :
    ((toPile.toNat < 10 ∨ (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧
        ¬ CfgBitSet (globalCfg (closureInfoOf p) i) su)) →
      fluteLen.toNat - 1 ≤ (freeCells s).length)
    ∧ ((¬ toPile.toNat < 14 ∨ (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧
        CfgBitSet (globalCfg (closureInfoOf p) i) su)) →
      fluteLen.toNat ≤ (freeCells s).length) := by
  obtain ⟨-, hcol, hextra, hking⟩ := getMovable_cells hchar h1 hmv hi hbit
  have hle : freeCellsOf p (globalCfg (closureInfoOf p) i) ≤ ((freeCells s).length : Int) :=
    hk.freeCellsOf_le hwf hb
  constructor
  · rintro (h10 | ⟨h10, h14, hcfg⟩)
    · have := hcol h10; omega
    · have := (hking su h10 h14 (hsu h10 h14)).2 hcfg; omega
  · rintro (h14 | ⟨h10, h14, hcfg⟩)
    · have := hextra h14; omega
    · have := (hking su h10 h14 (hsu h10 h14)).1 hcfg; omega

/-! ## The converse: affordability puts the bit *in* the mask

`getMovable_cells` reads a set bit as a cell budget; completeness needs the other
direction — the play's own cell budget must put the bit there.  `KingInfoCorrect` is an
`↔`, so each branch is the same run equation read backwards.

The `fluteLen ≤ 5` guard needs no hypothesis: `freeCellsOf ≤ 4` always (it is
`4 - (usedSpace - kingRefund)` and `kingRefund ≤ usedSpace` on a canonical position),
so a flute of six or more is never affordable in the first place — which is exactly
why the solver may return `0` there. -/
theorem getMovable_bitSet {g : Globals} {p : SolverPosType} {ki : KingInfo}
    (hchar : KingInfoCorrect p ki)
    {fluteLen toPile : UInt8} {mv : UInt16} (h1 : 1 ≤ fluteLen.toNat) (h5 : fluteLen.toNat ≤ 5)
    (hmv : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
      = .ok mv g)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (haff : (fluteLen.toNat : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i)
      ∨ (((fluteLen.toNat - 1 : Nat) : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i)
          ∧ (toPile.toNat < 10
              ∨ (10 ≤ toPile.toNat ∧ toPile.toNat < 14 ∧ ∀ su : Suit,
                  toPile.toNat - 10 = suitToNat su →
                  ¬ CfgBitSet (globalCfg (closureInfoOf p) i) su)))) :
    BitSet mv ⟨min i 15, by omega⟩ := by
  have hshift : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits _
  have hlt16 : (closureInfoOf p).shiftValue.toNat + i < 16 := by omega
  -- the two `possibleKings` indices
  have hi0 : fluteLen.toUInt32.toNat < 6 := by rw [UInt8.toNat_toUInt32]; omega
  have h1u : (1 : UInt8) ≤ fluteLen :=
    UInt8.le_iff_toNat_le.2 (by simp only [show ((1 : UInt8).toNat = 1) from rfl]; omega)
  have hi1v : (fluteLen - 1).toUInt32.toNat = fluteLen.toNat - 1 := by
    rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ h1u]
    simp only [show ((1 : UInt8).toNat = 1) from rfl]
  have hi1 : (fluteLen - 1).toUInt32.toNat < 6 := by rw [hi1v]; omega
  have hg1 : ((5 : UInt8) < fluteLen) = false := by
    simpa using UInt8.le_iff_toNat_le.2 (show fluteLen.toNat ≤ (5 : UInt8).toNat by
      simp only [show ((5 : UInt8).toNat = 5) from rfl]; omega)
  have hA : BitSet (ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16
        ⟨min i 15, by omega⟩
      ↔ (fluteLen.toNat : Int) ≤ freeCellsOf p (globalCfg (closureInfoOf p) i) := by
    rw [hchar _ hi0 i hi, UInt8.toNat_toUInt32]
  have hB : BitSet (ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16
        ⟨min i 15, by omega⟩
      ↔ ((fluteLen.toNat - 1 : Nat) : Int)
          ≤ freeCellsOf p (globalCfg (closureInfoOf p) i) := by
    rw [hchar _ hi1 i hi, hi1v]
  by_cases h10 : toPile.toNat < 10
  · -- a column destination: `possibleKings[fluteLen - 1]`
    have h10b : (toPile < 10) = true := by
      simpa using UInt8.lt_iff_toNat_lt.2 (by
        simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
    have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
        = .ok (ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16 g := by
      simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
        hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi1, h10b]
      rfl
    rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1]
    refine hB.2 ?_
    rcases haff with h | ⟨h, -⟩
    · exact le_trans (by omega) h
    · exact h
  · by_cases h14 : toPile.toNat < 14
    · -- a king pile
      have h10b : (toPile < 10) = false := by
        simpa using UInt8.le_iff_toNat_le.2 (show (10 : UInt8).toNat ≤ toPile.toNat by
          simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
      have h14b : (toPile < 14) = true := by
        simpa using UInt8.lt_iff_toNat_lt.2 (by
          simp only [show ((14 : UInt8).toNat = 14) from rfl]; omega)
      have h10le : (10 : UInt8) ≤ toPile :=
        UInt8.le_iff_toNat_le.2 (by simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
      have hk4v : (toPile - 10).toUInt32.toNat = toPile.toNat - 10 := by
        rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ h10le]
        simp only [show ((10 : UInt8).toNat = 10) from rfl]
      have hk4 : (toPile - 10).toUInt32.toNat < 4 := by rw [hk4v]; omega
      have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
          = .ok ((ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16 |||
              ((ki.possibleKings.get ⟨(fluteLen - 1).toUInt32.toNat, hi1⟩).toUInt16 &&&
                ((kingOnPileMap.get ⟨(toPile - 10).toUInt32.toNat, hk4⟩)
                  >>> (closureInfoOf p).shiftValue.toUInt16))) g := by
        simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
          hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0, hi1, hk4,
          h10b, h14b]
        rfl
      rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1, BitSet_or]
      rcases haff with h | ⟨h, hdst⟩
      · exact Or.inl (hA.2 h)
      · refine Or.inr ?_
        rcases hdst with hc | ⟨-, -, hcfg⟩
        · omega
        · -- the suit owns a pile, so the `kingOnPileMap` half is available
          set su : Suit := natToSuit ⟨(toPile - 10).toUInt32.toNat, hk4⟩ with hsu
          have hsuv : suitToNat su = toPile.toNat - 10 := by
            rw [hsu, suitToNat_natToSuit]
            exact hk4v
          have hkeq : kingOnPileMap.get ⟨(toPile - 10).toUInt32.toNat, hk4⟩
              = kingOnPileMap.get (finOfSuit su) :=
            congrArg kingOnPileMap.get
              (Fin.ext (show (toPile - 10).toUInt32.toNat = suitToNat su by rw [hk4v, hsuv]))
          rw [BitSet_and, hkeq, BitSet_shiftRight_globalCfg _ _ i hlt16, bitSet_kingOnPileMap]
          exact ⟨hB.2 h, hcfg su hsuv.symm⟩
    · -- `EXTRA`: `possibleKings[fluteLen]`
      have h10b : (toPile < 10) = false := by
        simpa using UInt8.le_iff_toNat_le.2 (show (10 : UInt8).toNat ≤ toPile.toNat by
          simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
      have h14b : (toPile < 14) = false := by
        simpa using UInt8.le_iff_toNat_le.2 (show (14 : UInt8).toNat ≤ toPile.toNat by
          simp only [show ((14 : UInt8).toNat = 14) from rfl]; omega)
      have hz : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
          = .ok (ki.possibleKings.get ⟨fluteLen.toUInt32.toNat, hi0⟩).toUInt16 g := by
        simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
          hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0, h10b, h14b]
        rfl
      rw [(EStateM.Result.ok.inj (hmv.symm.trans hz)).1]
      refine hA.2 ?_
      rcases haff with h | ⟨-, hdst⟩
      · exact h
      · rcases hdst with hc | ⟨-, hc, -⟩ <;> omega
