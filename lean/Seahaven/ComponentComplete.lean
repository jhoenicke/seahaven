import Seahaven.EmptyPileCfg
import Seahaven.MaximalCfg

/-!
# `componentTable`, read backwards

`KingReshuffle.inComponent_of_component_bit` reads a set component bit as
"this configuration can give a column back" (`InComponent`) — the direction
soundness needs.  Completeness needs the converse: a configuration that *can*
give a column back has its bit set, because that is how the loop
`movable'' := movable' ||| component` gets to add the caller's configuration
next to the one the play realized.

Two steps:

* `exists_localIdx` — a configuration whose piled set has the right size *is* one
  of its block's, so it has a local index.  Pure `closureInfo_block` arithmetic.
* `component_bit_of_inComponent` — that, plus the `←` half of
  `KingReshuffle.component_bit_iff` and `freeCellsOf_nonneg_iff` for the loop's
  `usedSpace ≤ 4` test.

`EmptyPileCfg` then supplies the semantic input: an empty-column state along the
winning play's prefix shows that both the caller's and the play's configuration
have a feasible subset with a column to spare (`HasSpareSubset`), which is
exactly `InComponent` for their block configurations.
-/

/-! ## Every configuration of the right size is in the block -/

/-- **A configuration with `min f 4` suits piled is one of block `f`'s.**  The
converse reading of `closureInfo_block`: the block *is* the set of grlex indices
of that popcount, so such a configuration has a local index. -/
theorem exists_localIdx (f : Fin 11) (c : Fin 16) (hcard : (piledSet c).card = min f.val 4) :
    ∃ il : Nat, il < (closureInfos.get f).numBits.toNat ∧
      globalCfg (closureInfos.get f) il = c := by
  have hpc : popCount4 (grlex2bits.get c).toNat = 4 - min f.val 4 := by
    have h := card_piledSet_add_popCount c
    have h4 : min f.val 4 ≤ 4 := by omega
    omega
  have hrange := (closureInfo_block f c).2 hpc
  have hc16 := c.isLt
  refine ⟨c.val - (closureInfos.get f).shiftValue.toNat, by omega, Fin.ext ?_⟩
  rw [globalCfg_val _ _ (by omega)]
  omega

/-! ## `InComponent` sets the bit -/

/-- The number of suits a block configuration piles, with the guard in force. -/
private theorem card_piledSet_block {p : SolverPosType} (hfp3 : p.freePiles.toNat ≤ 3)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat) :
    (piledSet (globalCfg (closureInfoOf p) i)).card = p.freePiles.toNat := by
  rw [card_piledSet_globalCfg p i hi]
  unfold numPiledKings
  omega

/-- **The converse of `inComponent_of_component_bit`.**  A configuration that can
give a column back has its component bit set: the configuration one suit smaller
is feasible, hence enumerated by the loop, and `componentTable` sends it back up
to every block configuration above it. -/
theorem component_bit_of_inComponent {g : Globals} {p : SolverPosType} {comp : UInt8}
    (hb : SolverInvBase g p) (hfp1 : 1 ≤ p.freePiles.toNat) (hfp3 : p.freePiles.toNat ≤ 3)
    (hrun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hic : InComponent p (globalCfg (closureInfoOf p) i)) :
    BitSet comp.toUInt16 ⟨min i 15, by omega⟩ := by
  obtain ⟨result, hchar, hbound, hcomp⟩ := component_run_eq g p comp hfp1 hfp3 hrun
  obtain ⟨su, hsu, hfeas⟩ := hic
  have hcb : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p.freePiles.toNat 10, by omega⟩
  have hpb : (prevInfo p).shiftValue.toNat + (prevInfo p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min (p.freePiles.toNat - 1) 10, by omega⟩
  -- the one-suit-smaller configuration lives in the previous block
  have hcd : (piledSet (globalCfg (closureInfoOf p) i)).card = p.freePiles.toNat :=
    card_piledSet_block hfp3 hi
  have hcc : (piledSet (setCfgBit (globalCfg (closureInfoOf p) i) su)).card
      = p.freePiles.toNat - 1 := by
    rw [piledSet_setCfgBit, Finset.card_erase_of_mem (mem_piledSet.2 hsu), hcd]
  have hprev : closureInfos.get (⟨p.freePiles.toNat - 1, by omega⟩ : Fin 11) = prevInfo p :=
    congrArg closureInfos.get (Fin.ext (show p.freePiles.toNat - 1
      = min (p.freePiles.toNat - 1) 10 by omega))
  obtain ⟨il, hil, heq⟩ := exists_localIdx ⟨p.freePiles.toNat - 1, by omega⟩
    (setCfgBit (globalCfg (closureInfoOf p) i) su) (by rw [hcc]; simp only []; omega)
  rw [hprev] at hil heq
  -- it is feasible, so the loop enumerated it
  have hfeas' : 0 ≤ freeCellsOf p (globalCfg (prevInfo p) il) := by rw [heq]; exact hfeas
  have hbit : result.toNat.testBit il = true :=
    (hchar il (by omega)).2 ⟨hil, (freeCellsOf_nonneg_iff p hb (prevInfo p) il (by omega)).1 hfeas'⟩
  -- and it sits one suit below the queried configuration, which is what sets the bit
  rw [BitSet_toNat, show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega),
    UInt8.toNat_toUInt16, hcomp]
  exact (component_bit_iff p hfp1 hfp3 result.toNat hbound i hi).2
    ⟨il, hil, hbit, su, hsu, heq.symm⟩

/-! ## From a feasible spare subset to `InComponent` -/

/-- **A configuration with a column to spare puts every block configuration above
it in the component.**  Any suit the block configuration piles and the spare
subset does not is one that can be moved back into the cells: what is left still
covers the spare subset, which fits. -/
theorem inComponent_of_hasSpareSubset {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (hfp3 : p.freePiles.toNat ≤ 3) {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    {k : Fin 16} (hks : MaskSub (globalCfg (closureInfoOf p) i) k) (hsp : HasSpareSubset p k) :
    InComponent p (globalCfg (closureInfoOf p) i) := by
  obtain ⟨c, hsub, hlt, hfeas⟩ := hsp
  have hcd : (piledSet (globalCfg (closureInfoOf p) i)).card = p.freePiles.toNat :=
    card_piledSet_block hfp3 hi
  have hcsub : piledSet c ⊆ piledSet (globalCfg (closureInfoOf p) i) :=
    hsub.trans ((maskSub_iff_piledSet_subset _ _).1 hks)
  -- a suit the block configuration piles and `c` does not
  obtain ⟨su, hsud, hsuc⟩ := Finset.not_subset.1
    (fun hcon : piledSet (globalCfg (closureInfoOf p) i) ⊆ piledSet c =>
      absurd (Finset.card_le_card hcon) (by omega))
  refine ⟨su, mem_piledSet.1 hsud, ?_⟩
  refine le_trans hfeas (freeCellsOf_mono hb ((maskSub_iff_piledSet_subset _ _).2 ?_))
  rw [piledSet_setCfgBit]
  exact Finset.subset_erase.2 ⟨hcsub, hsuc⟩

/-! ## The gap, closed

The two halves meet here.  Note what the statement does *not* need: no
`WellFormedLayout`, no solvability, no knowledge of which move is critical — the
whole content is that a king configuration cannot change while every solver-empty
column is occupied. -/

/-- **The missing step of the recursive completeness proof.**  If the winning
play's prefix carries `s` to `t`, and `s` stands for `k` while `t` stands for
`k_t`, then either the two configurations are equal — and the bit established at
`k_t` *is* the bit asked about — or both are in the component, and the loop's
`movable' ||| component` widening carries the bit from one to the other. -/
theorem cfg_eq_or_component_bits {g : Globals} {p : SolverPosType} {comp : UInt8}
    {s t : State} {k kt : Fin 16} (hm : SolverInvMerged g p)
    (hfp1 : 1 ≤ p.freePiles.toNat) (hfp3 : p.freePiles.toNat ≤ 3)
    (hrun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hs : DepthPlusKingsCfg g s p k) (ht : DepthPlusKingsCfg g t p kt)
    (hr : PrefixReach g p s t)
    {i j : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hj : j < (closureInfoOf p).numBits.toNat)
    (hik : MaskSub (globalCfg (closureInfoOf p) i) k)
    (hjk : MaskSub (globalCfg (closureInfoOf p) j) kt) :
    k = kt ∨ (BitSet comp.toUInt16 ⟨min i 15, by omega⟩ ∧
      BitSet comp.toUInt16 ⟨min j 15, by omega⟩) := by
  rcases cfg_eq_or_spareSubset hm hs ht hr with heq | ⟨hspk, hspkt⟩
  · exact Or.inl heq
  · have hb := hm.toSolverInvBase
    exact Or.inr
      ⟨component_bit_of_inComponent hb hfp1 hfp3 hrun hi
        (inComponent_of_hasSpareSubset hb hfp3 hi hik hspk),
       component_bit_of_inComponent hb hfp1 hfp3 hrun hj
        (inComponent_of_hasSpareSubset hb hfp3 hj hjk hspkt)⟩

/-! ## Outside the guard

`computeComponentKingBits` answers `0` unless `1 ≤ freePiles ≤ 3`, so there the
component widening does nothing — and it does not have to: with no free pile no
king can move at all, and with four the block holds a single configuration. -/

/-- At four or more free piles every suit can have a column of its own, so the
block holds a single configuration: whatever `k` and `k_t` are, they are covered
by the *same* bit and nothing has to be transported. -/
theorem block_index_eq_of_freePiles_four {p : SolverPosType} (hfp : 4 ≤ p.freePiles.toNat)
    {i j : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hj : j < (closureInfoOf p).numBits.toNat) : i = j := by
  have h : (closureInfoOf p).numBits.toNat = 1 := by
    rw [closureInfoOf_numBits]
    unfold numPiledKings
    rw [show min p.freePiles.toNat 4 = 4 from by omega]
    rfl
  omega

/-- With every solver-empty column occupied there is nothing to reshuffle, so at
`freePiles = 0` the two configurations always agree. -/
theorem cfg_eq_of_freePiles_zero {g : Globals} {p : SolverPosType} {s t : State} {k kt : Fin 16}
    (hm : SolverInvMerged g p) (hfp : p.freePiles.toNat = 0)
    (hs : DepthPlusKingsCfg g s p k) (ht : DepthPlusKingsCfg g t p kt)
    (hr : PrefixReach g p s t) : k = kt := by
  rcases cfg_eq_or_spareSubset hm hs ht hr with heq | ⟨⟨c, -, hlt, -⟩, -⟩
  · exact heq
  · omega
