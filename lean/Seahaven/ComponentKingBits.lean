import Seahaven.ComputeKingSpaces

/-!
# `computeComponentKingBits`

The function has two halves.

**The loop** is `computeKingSpaces`' loop with three differences: it enumerates the
block for `freePiles - 1` — the configurations that leave one pile completely
*unused* — it only records whether the configuration *fits at all* (`usedSpace ≤ 4`,
i.e. at least zero free cells) rather than how much room is left, and it accumulates
into a plain `UInt16` bitmask instead of a vector.  The refund fold is literally the
same, so `spaceBody`/`effSpace`/`blockSpace` are reused from `ComputeKingSpaces`.
Since nothing is written to a vector, this loop cannot throw.

**The table** turns that set of feasible one-pile-spare configurations into a set of
configurations of the *current* block: those obtained by piling one more king, so
that no pile is left unused.  `component_spec_pos` below says exactly that, decided
against the tables one index bit at a time — including the top block, where all four
kings are already piled and there is nothing more to pile, so the table is `0`.

That "one more king" is what makes the component a mutually-reachable class
(`ComponentSound`): from any such configuration the extra king can be moved back
into the cells — which is affordable, since the spare-pile configuration fits — and
then out onto the free pile again for a different suit.
-/

open Lean Lean.Order

/-! ## The loop -/

/-- Body of the per-configuration loop: set bit `i` when configuration `i` fits. -/
def compBody (info : ClosureInfo) (game : SolverPosType) :
    Nat → UInt16 → EStateM Error Globals (ForInStep UInt16) :=
  fun i result => do
    let kingBitmap ← grlex2bits.getE (info.shiftValue + UInt8.ofNat i).toUInt32
    let u ← forIn (List.range 4) game.usedSpace.toInt32 (spaceBody game kingBitmap)
    if u ≤ 4 then
      return .yield (result ||| ((1 : UInt16) <<< UInt16.ofNat i))
    else
      return .yield result

/-- Explicit-loop twin of `computeComponentKingBits`. -/
def componentExplicit (game : SolverPosType) : EStateM Error Globals UInt8 := do
  let emptyPiles := game.freePiles
  if emptyPiles ≥ 1 && emptyPiles ≤ 3 then
    let info ← closureInfos.getE (emptyPiles - 1).toUInt32
    let result ← forIn (List.range info.numBits.toNat) (0 : UInt16) (compBody info game)
    let entry ← componentTable.getE (info.offset.toUInt32 + result.toUInt32)
    return entry
  else
    return 0

theorem component_eq_explicit : computeComponentKingBits = componentExplicit := rfl

/-! ## Exact run of the loop

No vector is written, so unlike `computeKingSpaces` this loop always succeeds; the
only bound needed is that the block fits inside `grlex2bits`. -/

private theorem pure_apply {α : Type} (a : α) (t : Globals) :
    (EStateM.pure a : EStateM Error Globals α) t = .ok a t := rfl

private theorem uint16_or_testBit (r : UInt16) (i b : Nat) (hi : i < 16) (hb : b < 16) :
    (r ||| ((1 : UInt16) <<< UInt16.ofNat i)).toNat.testBit b = true
      ↔ (r.toNat.testBit b = true ∨ i = b) := by
  have hkey : ∀ i b : Fin 16,
      ((1 : UInt16) <<< UInt16.ofNat i.val).toNat.testBit b.val = decide (i.val = b.val) := by
    decide
  rw [UInt16.toNat_or, Nat.testBit_or, Bool.or_eq_true, hkey ⟨i, hi⟩ ⟨b, hb⟩]
  simp

theorem compBody_run (info : ClosureInfo) (game : SolverPosType) (s : Globals) (i : Nat)
    (r : UInt16) (hcfg : cfgIdx info.shiftValue i < 16) :
    compBody info game i r s = .ok (.yield
      (if (blockSpace info.shiftValue game i).toInt ≤ 4
        then r ||| ((1 : UInt16) <<< UInt16.ofNat i) else r)) s := by
  have hgrl : grlex2bits[cfgIdx info.shiftValue i]? = some (blockBitmap info.shiftValue i) := by
    rw [blockBitmap, dif_pos hcfg]
    exact getElem?_pos grlex2bits (cfgIdx info.shiftValue i) hcfg
  simp only [compBody, bind, EStateM.bind, pure, Vector.getE, cfgIdx] at hgrl ⊢
  by_cases hu : (blockSpace info.shiftValue game i).toInt ≤ 4
  · have hg : effSpace game (blockBitmap info.shiftValue i) ≤ (4 : Int32) := (bit_guard_iff _).2 hu
    simp only [hgrl, pure_apply, spaceLoop_run, hg, reduceIte, if_pos hu]
  · have hg : ¬ (effSpace game (blockBitmap info.shiftValue i) ≤ (4 : Int32)) :=
      fun h => hu ((bit_guard_iff _).1 h)
    simp only [hgrl, pure_apply, spaceLoop_run, hg, reduceIte, if_neg hu]

theorem compLoop_run (info : ClosureInfo) (game : SolverPosType) (s : Globals) :
    ∀ (l : List Nat) (r : UInt16),
      (∀ i ∈ l, cfgIdx info.shiftValue i < 16) → (∀ i ∈ l, i < 16) →
      ∃ res : UInt16, forIn l r (compBody info game) s = .ok res s ∧
        ∀ b : Nat, b < 16 → (res.toNat.testBit b = true ↔
          (r.toNat.testBit b = true ∨
            (b ∈ l ∧ (blockSpace info.shiftValue game b).toInt ≤ 4))) := by
  intro l
  induction l with
  | nil =>
    intro r _ _
    exact ⟨r, rfl, fun b _ => by simp⟩
  | cons i l ih =>
    intro r hcfg h16
    obtain ⟨res, hres, hchar⟩ := ih
      (if (blockSpace info.shiftValue game i).toInt ≤ 4
        then r ||| ((1 : UInt16) <<< UInt16.ofNat i) else r)
      (fun j hj => hcfg j (by simp [hj])) (fun j hj => h16 j (by simp [hj]))
    refine ⟨res, ?_, fun b hb => ?_⟩
    · rw [List.forIn_cons]
      simp only [bind, EStateM.bind, compBody_run info game s i r (hcfg i (by simp))]
      exact hres
    · rw [hchar b hb, List.mem_cons]
      by_cases hui : (blockSpace info.shiftValue game i).toInt ≤ 4
      · rw [if_pos hui, uint16_or_testBit _ _ _ (h16 i (by simp)) hb]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl h.symm, by rw [← h]; exact hui⟩
          · exact Or.inr ⟨Or.inr h.1, h.2⟩
        · rintro (h | ⟨hb', hc'⟩)
          · exact Or.inl (Or.inl h)
          · rcases hb' with rfl | hb'
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨hb', hc'⟩
      · rw [if_neg hui]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h.1, h.2⟩
        · rintro (h | ⟨hb', hc'⟩)
          · exact Or.inl h
          · rcases hb' with rfl | hb'
            · exact absurd hc' hui
            · exact Or.inr ⟨hb', hc'⟩

/-! ## What the table computes

`componentTable[offset(f-1) + T]` is the set of configurations of block `f` obtained
from some configuration in `T` by piling **one more** king.  Note the strictness: the
piled sets must actually differ, which is what makes the top block (all four kings
already piled, nothing left to pile) come out `0`.

The table is decided **one index bit at a time**, exactly as `subsetTable` is
(`subsetAt_or_consistent_block`): "some configuration of `T`" is a disjunction over
the set bits of `T`, so the entry for `T` is the `|||` of the entries for its single
bits (`componentAt_or_consistent_block`, one pass over the 82 entries).  The
specification proper then only has to look at the single-bit entries —
`numBits(f-1) × numBits(f)` cases per block, 52 in total, instead of the
`2 ^ numBits(f-1) × numBits(f)` an exhaustive `decide` would enumerate. -/

/-- `componentTable` lookup, clamped. -/
def componentAt (idx : Nat) : UInt8 := componentTable.get ⟨min idx 99, by omega⟩

/-- **The table is `|||`-decomposable**, per block: an entry is the `|||` of the
entries of the single bits of its index.

Only the blocks the guard `1 ≤ freePiles ≤ 3` can select are claimed — the higher
blocks are `|||`-decomposable too (they are all-zero or all-one), but checking them
doubles the cost of this `decide` for nothing. -/
theorem componentAt_or_consistent_block :
    ∀ f : Fin 11, f.val ≤ 2 → or_consistent (closureInfos.get f).numBits.toNat
      (fun a => (componentAt ((closureInfos.get f).offset.toNat + a)).toNat) := by
  unfold or_consistent
  decide

/-! ### The single-bit entries, per block

Read at one index bit `i`, the entry is the set of block-`f` configurations that
pile one more king than block-`(f-1)`'s configuration `i`.  Three blocks, because
that is what the guard `1 ≤ freePiles ≤ 3` can select.

Both facts the callers need are decided here, at one bit: *which* configurations the
entry holds, and that it holds no others (`componentTable_localBound` — the width
bound, which the specification cannot give since it only speaks about in-block
bits). -/

/-- The single-bit entries fit the *next* block's width. -/
private theorem compBound_bit : ∀ f : Fin 11, f.val ≤ 2 →
    ∀ i : Fin (closureInfos.get f).numBits.toNat,
      (componentAt ((closureInfos.get f).offset.toNat + 2 ^ i.val)).toNat
        < 2 ^ (closureInfos.get ⟨min (f.val + 1) 10, by omega⟩).numBits.toNat := by decide

/-- **The component contribution is in-block.**  Note the off-by-one:
`computeComponentKingBits` indexes `componentTable` through
`closureInfos[emptyPiles - 1]` — the loop enumerates the block one *below* the
position's — but the returned value is a local mask of the position's own block.  So
block `f`'s component entries are bounded by block `f + 1`'s width; instantiate at
`f := freePiles - 1` to get `LocalMask` for the `component` contribution
(`KingReshuffle.localMask_component`).

Decided one bit at a time: an entry is the `|||` of its single-bit entries, and `|||`
stays inside a bit range (`or_consistent_lt_two_pow`). -/
theorem componentTable_localBound (f : Fin 11) (hf : f.val ≤ 2) (j : Nat)
    (hj : j < 2 ^ (closureInfos.get f).numBits.toNat) :
    (componentAt ((closureInfos.get f).offset.toNat + j)).toNat
      < 2 ^ (closureInfos.get ⟨f.val + 1, by omega⟩).numBits.toNat := by
  -- `Fin.val ⟨_, _⟩` is an `omega` atom, so state the index equation before omega sees it
  have hidx : (⟨min (f.val + 1) 10, by omega⟩ : Fin 11) = ⟨f.val + 1, by omega⟩ :=
    Fin.ext (show min (f.val + 1) 10 = f.val + 1 from by omega)
  refine or_consistent_lt_two_pow (componentAt_or_consistent_block f hf) (fun i => ?_) ⟨j, hj⟩
  rw [← hidx]
  exact compBound_bit f hf i

/-- `freePiles = 1`: block `0` (all four kings in the cells) → block `1`. -/
private theorem component_bit_98 : ∀ (il : Fin 1) (jl : Fin 4),
    ((componentAt (98 + 2 ^ il.val)).toNat.testBit jl.val = true) ↔
      (MaskSub ⟨11 + jl.val, by omega⟩ ⟨15 + il.val, by omega⟩ ∧
        grlex2bits.get (⟨11 + jl.val, by omega⟩ : Fin 16)
          ≠ grlex2bits.get (⟨15 + il.val, by omega⟩ : Fin 16)) := by decide

/-- `freePiles = 2`: block `1` → block `2`. -/
private theorem component_bit_0 : ∀ (il : Fin 4) (jl : Fin 6),
    ((componentAt (0 + 2 ^ il.val)).toNat.testBit jl.val = true) ↔
      (MaskSub ⟨5 + jl.val, by omega⟩ ⟨11 + il.val, by omega⟩ ∧
        grlex2bits.get (⟨5 + jl.val, by omega⟩ : Fin 16)
          ≠ grlex2bits.get (⟨11 + il.val, by omega⟩ : Fin 16)) := by decide

/-- `freePiles = 3`: block `2` → block `3`. -/
private theorem component_bit_16 : ∀ (il : Fin 6) (jl : Fin 4),
    ((componentAt (16 + 2 ^ il.val)).toNat.testBit jl.val = true) ↔
      (MaskSub ⟨1 + jl.val, by omega⟩ ⟨5 + il.val, by omega⟩ ∧
        grlex2bits.get (⟨1 + jl.val, by omega⟩ : Fin 16)
          ≠ grlex2bits.get (⟨5 + il.val, by omega⟩ : Fin 16)) := by decide

/-! ## The run, reduced to a table lookup -/

/-- The block for one fewer free pile — the configurations the loop enumerates,
each leaving one pile completely unused. -/
def prevInfo (p : SolverPosType) : ClosureInfo :=
  closureInfos.get ⟨min (p.freePiles.toNat - 1) 10, by omega⟩

/-! ### The specification, in the `prevInfo` spelling

`component_run_eq` below reads the table at `prevInfo p`'s block, so the
specification is needed in that spelling — `prevInfo p` for the configurations the
loop enumerates, `closureInfoOf p` for the ones the entry describes.  The three
concrete blocks are mapped onto it **once**, here, and both directions come out of
it: soundness reads a set bit (`KingReshuffle.inComponent_of_component_bit`),
completeness sets one (`ComponentComplete.component_bit_of_inComponent`). -/

private theorem globalCfg_mk (ci : ClosureInfo) (sh : Nat) (hsh : ci.shiftValue.toNat = sh)
    (i : Nat) (h : sh + i < 16) : globalCfg ci i = (⟨sh + i, h⟩ : Fin 16) :=
  Fin.ext (by rw [globalCfg_val ci i (by omega), hsh])

/-- The single-bit entries of the three blocks, uniformly. -/
private theorem component_bit_pos (p : SolverPosType) (hfp1 : 1 ≤ p.freePiles.toNat)
    (hfp3 : p.freePiles.toNat ≤ 3) (il : Nat) (hil : il < (prevInfo p).numBits.toNat)
    (j : Nat) (hj : j < (closureInfoOf p).numBits.toNat) :
    ((componentAt ((prevInfo p).offset.toNat + 2 ^ il)).toNat.testBit j = true) ↔
      (MaskSub (globalCfg (closureInfoOf p) j) (globalCfg (prevInfo p) il) ∧
        grlex2bits.get (globalCfg (closureInfoOf p) j)
          ≠ grlex2bits.get (globalCfg (prevInfo p) il)) := by
  have hcases : p.freePiles.toNat = 1 ∨ p.freePiles.toNat = 2 ∨ p.freePiles.toNat = 3 := by omega
  rcases hcases with h | h | h
  · have hc : closureInfoOf p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 1 from by omega))
    have hp : prevInfo p = closureInfos.get (0 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 0 from by omega))
    rw [hc, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (0 : Fin 11)).numBits.toNat = 1 from by decide] at hil
    rw [hp, hc, show (closureInfos.get (0 : Fin 11)).offset.toNat = 98 from by decide,
      globalCfg_mk _ 11 (by decide) j (by omega), globalCfg_mk _ 15 (by decide) il (by omega)]
    exact component_bit_98 ⟨il, hil⟩ ⟨j, hj⟩
  · have hc : closureInfoOf p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 2 from by omega))
    have hp : prevInfo p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 1 from by omega))
    rw [hc, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hj
    rw [hp, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hil
    rw [hp, hc, show (closureInfos.get (1 : Fin 11)).offset.toNat = 0 from by decide,
      globalCfg_mk _ 5 (by decide) j (by omega), globalCfg_mk _ 11 (by decide) il (by omega)]
    exact component_bit_0 ⟨il, hil⟩ ⟨j, hj⟩
  · have hc : closureInfoOf p = closureInfos.get (3 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 3 from by omega))
    have hp : prevInfo p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 2 from by omega))
    rw [hc, show (closureInfos.get (3 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hil
    rw [hp, hc, show (closureInfos.get (2 : Fin 11)).offset.toNat = 16 from by decide,
      globalCfg_mk _ 1 (by decide) j (by omega), globalCfg_mk _ 5 (by decide) il (by omega)]
    exact component_bit_16 ⟨il, hil⟩ ⟨j, hj⟩

/-- **What the table entry at the loop's mask says.**  Bit `j` is set exactly when
some configuration `il` of the mask `T` piles strictly fewer kings than block
configuration `j` — the `or_consistent` decomposition of the entry, with the
single-bit entries read off the tables. -/
theorem component_spec_pos (p : SolverPosType) (hfp1 : 1 ≤ p.freePiles.toNat)
    (hfp3 : p.freePiles.toNat ≤ 3) (T : Nat) (hT : T < 2 ^ (prevInfo p).numBits.toNat)
    (j : Nat) (hj : j < (closureInfoOf p).numBits.toNat) :
    ((componentAt ((prevInfo p).offset.toNat + T)).toNat.testBit j = true) ↔
      ∃ il : Nat, il < (prevInfo p).numBits.toNat ∧ T.testBit il = true ∧
        MaskSub (globalCfg (closureInfoOf p) j) (globalCfg (prevInfo p) il) ∧
        grlex2bits.get (globalCfg (closureInfoOf p) j)
          ≠ grlex2bits.get (globalCfg (prevInfo p) il) := by
  have hor := componentAt_or_consistent_block ⟨min (p.freePiles.toNat - 1) 10, by omega⟩
    (show min (p.freePiles.toNat - 1) 10 ≤ 2 from by omega)
  refine Iff.trans (or_consistent_testBit hor ⟨T, hT⟩ j) ?_
  constructor
  · rintro ⟨il, hTbit, hbit⟩
    exact ⟨il.val, il.isLt, hTbit, (component_bit_pos p hfp1 hfp3 il.val il.isLt j hj).1 hbit⟩
  · rintro ⟨il, hil, hTbit, hspec⟩
    exact ⟨⟨il, hil⟩, hTbit, (component_bit_pos p hfp1 hfp3 il hil j hj).2 hspec⟩

private theorem freePiles_int32 (p : SolverPosType) :
    (p.freePiles.toInt32).toInt = (p.freePiles.toNat : Int) := uint8_toInt32_toInt _

/-- **`computeComponentKingBits` is the table lookup at the loop's mask**, and that
mask has bit `i` set exactly for the feasible one-pile-spare configurations. -/
theorem component_run_eq (g : Globals) (p : SolverPosType) (comp : UInt8)
    (hfp1 : 1 ≤ p.freePiles.toNat) (hfp3 : p.freePiles.toNat ≤ 3)
    (hrun : EStateM.run (computeComponentKingBits p) g = .ok comp g) :
    ∃ result : UInt16,
      (∀ b : Nat, b < 16 → (result.toNat.testBit b = true ↔
        (b < (prevInfo p).numBits.toNat ∧
          (blockSpace (prevInfo p).shiftValue p b).toInt ≤ 4))) ∧
      result.toNat < 2 ^ (prevInfo p).numBits.toNat ∧
      comp = componentAt ((prevInfo p).offset.toNat + result.toNat) := by
  -- block data, transported to the `prevInfo p` spelling
  have hfits : (prevInfo p).shiftValue.toNat + (prevInfo p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits _
  have hnb : (prevInfo p).numBits.toNat ≤ 6 := by
    have h : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
    exact h _
  have hoffb : (prevInfo p).offset.toNat + 2 ^ (prevInfo p).numBits.toNat ≤ 100 := by
    have h : ∀ f : Fin 11,
        (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
      decide
    exact h _
  -- the guard holds
  have hg1 : ((1 : UInt8) ≤ p.freePiles) := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
  have hg3 : (p.freePiles ≤ (3 : UInt8)) := by
    rw [UInt8.le_iff_toNat_le, show ((3 : UInt8).toNat = 3) from rfl]; omega
  -- the closure-info index
  have hidx : (p.freePiles - 1).toUInt32.toNat = p.freePiles.toNat - 1 := by
    rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _
      (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]
    rfl
  have hidx11 : (p.freePiles - 1).toUInt32.toNat < 11 := by rw [hidx]; omega
  have hinfo : closureInfos[(p.freePiles - 1).toUInt32.toNat]? = some (prevInfo p) := by
    rw [getElem?_pos closureInfos ((p.freePiles - 1).toUInt32.toNat) hidx11]
    exact congrArg some (congrArg closureInfos.get
      (Fin.ext (show (p.freePiles - 1).toUInt32.toNat = min (p.freePiles.toNat - 1) 10 from
        by rw [hidx]; omega)))
  -- the loop
  obtain ⟨result, hres, hchar⟩ := compLoop_run (prevInfo p) p g
    (List.range (prevInfo p).numBits.toNat) 0
    (fun i hi => by
      rw [List.mem_range] at hi
      rw [cfgIdx_eq _ _ (by omega)]
      omega)
    (fun i hi => by rw [List.mem_range] at hi; omega)
  have hcharsimp : ∀ b : Nat, b < 16 → (result.toNat.testBit b = true ↔
      (b < (prevInfo p).numBits.toNat ∧
        (blockSpace (prevInfo p).shiftValue p b).toInt ≤ 4)) := by
    intro b hb
    rw [hchar b hb]
    simp only [show ((0 : UInt16).toNat = 0) from rfl, Nat.zero_testBit, Bool.false_eq_true,
      false_or, List.mem_range]
  have hbound : result.toNat < 2 ^ (prevInfo p).numBits.toNat := by
    refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
    by_cases h16 : i < 16
    · by_contra hcon
      rw [Bool.not_eq_false] at hcon
      exact absurd ((hcharsimp i h16).1 hcon).1 (by omega)
    · have h65536 : result.toNat < 65536 := result.toNat_lt_size
      exact Nat.testBit_lt_two_pow (by
        calc result.toNat < 65536 := h65536
          _ = 2 ^ 16 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨result, hcharsimp, hbound, ?_⟩
  -- the table lookup
  have hidxsum : ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat
      = (prevInfo p).offset.toNat + result.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
    have h2 : (2 : Nat) ^ (prevInfo p).numBits.toNat ≤ 64 := by
      have : (prevInfo p).numBits.toNat ≤ 6 := hnb
      calc (2 : Nat) ^ (prevInfo p).numBits.toNat ≤ 2 ^ 6 :=
            Nat.pow_le_pow_right (by omega) this
        _ = 64 := by norm_num
    omega
  have hlt100 : ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat < 100 := by
    rw [hidxsum]; omega
  have hct : componentTable[((prevInfo p).offset.toUInt32 + result.toUInt32).toNat]?
      = some (componentAt ((prevInfo p).offset.toNat + result.toNat)) := by
    rw [getElem?_pos componentTable _ hlt100]
    exact congrArg some (congrArg componentTable.get
      (Fin.ext (show ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat
        = min ((prevInfo p).offset.toNat + result.toNat) 99 from by rw [hidxsum]; omega)))
  rw [component_eq_explicit] at hrun
  simp only [componentExplicit, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    Vector.getE, hg1, hg3, decide_true, Bool.and_self, reduceIte, hinfo, hres, hct] at hrun
  exact (EStateM.Result.ok.inj hrun.symm).1

/-! ## The free-cell reading of the loop's test -/

/-- The loop's `usedSpace ≤ 4` test is "this configuration leaves at least zero
free cells" — the `freeCellsOf` form `computeKingSpaces`' spec is stated in. -/
theorem freeCellsOf_nonneg_iff {g : Globals} (p : SolverPosType) (hb : SolverInvBase g p)
    (ci : ClosureInfo) (i : Nat) (h : ci.shiftValue.toNat + i ≤ 15) :
    (0 ≤ freeCellsOf p (globalCfg ci i)) ↔ (blockSpace ci.shiftValue p i).toInt ≤ 4 := by
  rw [freeCellsOf, globalCfg, ← blockSpace_toInt_eq p hb ci.shiftValue i h]
  constructor <;> intro <;> omega
