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

Three steps:

* `exists_localIdx` — a configuration whose piled set has the right size *is* one
  of its block's, so it has a local index.  Pure `closureInfo_block` arithmetic.
* `comp_bit_of_maskSub` — the `←` half of `component_spec_*`, uniformly over the
  three blocks the guard `1 ≤ freePiles ≤ 3` admits.
* `component_bit_of_inComponent` — the two combined, plus `freeCellsOf_nonneg_iff`
  for the loop's `usedSpace ≤ 4` test.

`EmptyPileCfg` then supplies the semantic input: an empty-column state along the
winning play's prefix shows that both the caller's and the play's configuration
have a feasible subset with a column to spare (`HasSpareSubset`), which is
exactly `InComponent` for their block configurations.
-/

/-! ## `MaskSub`, as an inclusion of piled sets -/

theorem maskSub_iff_piledSet_subset (d c : Fin 16) :
    MaskSub d c ↔ piledSet c ⊆ piledSet d := by
  rw [MaskSub_iff]
  constructor
  · intro h su hsu
    rw [mem_piledSet] at hsu ⊢
    exact fun hc => hsu (h su hc)
  · intro h su hd
    by_contra hc
    exact (mem_piledSet.1 (h (mem_piledSet.2 hc))) hd

/-! ## Every configuration of the right size is in the block -/

theorem card_piledSet_add_popCount' (k : Fin 16) :
    (piledSet k).card + popCount4 (grlex2bits.get k).toNat = 4 :=
  card_piled_add_popCount k

/-- **A configuration with `min f 4` suits piled is one of block `f`'s.**  The
converse reading of `closureInfo_block`: the block *is* the set of grlex indices
of that popcount, so such a configuration has a local index. -/
theorem exists_localIdx (f : Fin 11) (c : Fin 16) (hcard : (piledSet c).card = min f.val 4) :
    ∃ il : Nat, il < (closureInfos.get f).numBits.toNat ∧
      globalCfg (closureInfos.get f) il = c := by
  have hpc : popCount4 (grlex2bits.get c).toNat = 4 - min f.val 4 := by
    have h := card_piledSet_add_popCount' c
    have h4 : min f.val 4 ≤ 4 := by omega
    omega
  have hrange := (closureInfo_block f c).2 hpc
  have hc16 := c.isLt
  refine ⟨c.val - (closureInfos.get f).shiftValue.toNat, by omega, Fin.ext ?_⟩
  rw [globalCfg_val _ _ (by omega)]
  omega

/-! ## The table lookup, backwards

`component_spec_*` are already `↔`s, so the `←` half is only a matter of putting
the three blocks in the uniform `globalCfg` phrasing — the same bookkeeping
`comp_bit_semantics` does for the `→` half. -/

private theorem globalCfg_mk (ci : ClosureInfo) (sh : Nat) (hsh : ci.shiftValue.toNat = sh)
    (i : Nat) (h : sh + i < 16) : globalCfg ci i = (⟨sh + i, h⟩ : Fin 16) :=
  Fin.ext (by rw [globalCfg_val ci i (by omega), hsh])

/-- **A block-`f-1` configuration strictly below a block-`f` one sets its bit.**
The `←` half of `component_spec_*`. -/
private theorem comp_bit_of_maskSub (p : SolverPosType) (hfp1 : 1 ≤ p.freePiles.toNat)
    (hfp3 : p.freePiles.toNat ≤ 3) (T : Nat) (hT : T < 2 ^ (prevInfo p).numBits.toNat)
    (j : Nat) (hj : j < (closureInfoOf p).numBits.toNat)
    (il : Nat) (hil : il < (prevInfo p).numBits.toNat) (hTbit : T.testBit il = true)
    (hms : MaskSub (globalCfg (closureInfoOf p) j) (globalCfg (prevInfo p) il))
    (hne : grlex2bits.get (globalCfg (closureInfoOf p) j)
      ≠ grlex2bits.get (globalCfg (prevInfo p) il)) :
    (componentAt ((prevInfo p).offset.toNat + T)).toNat.testBit j = true := by
  have hbr : p.freePiles.toNat = p.freePiles.toNat := rfl
  have hcases : p.freePiles.toNat = 1 ∨ p.freePiles.toNat = 2 ∨ p.freePiles.toNat = 3 := by omega
  rcases hcases with h | h | h
  · have hc : closureInfoOf p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 1 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (0 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 0 by rw [h]; decide))
    rw [hc, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (0 : Fin 11)).numBits.toNat = 1 from by decide] at hil hT
    rw [hp, show (closureInfos.get (0 : Fin 11)).offset.toNat = 98 from by decide]
    rw [hc, globalCfg_mk _ 11 (by decide) j (by omega)] at hms hne
    rw [hp, globalCfg_mk _ 15 (by decide) il (by omega)] at hms hne
    exact (component_spec_98 ⟨T, by simpa using hT⟩ ⟨j, hj⟩).2 ⟨⟨il, hil⟩, hTbit, hms, hne⟩
  · have hc : closureInfoOf p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 2 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (1 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 1 by rw [h]; decide))
    rw [hc, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hj
    rw [hp, show (closureInfos.get (1 : Fin 11)).numBits.toNat = 4 from by decide] at hil hT
    rw [hp, show (closureInfos.get (1 : Fin 11)).offset.toNat = 0 from by decide]
    rw [hc, globalCfg_mk _ 5 (by decide) j (by omega)] at hms hne
    rw [hp, globalCfg_mk _ 11 (by decide) il (by omega)] at hms hne
    exact (component_spec_0 ⟨T, by simpa using hT⟩ ⟨j, hj⟩).2 ⟨⟨il, hil⟩, hTbit, hms, hne⟩
  · have hc : closureInfoOf p = closureInfos.get (3 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min p.freePiles.toNat 10 = 3 by rw [hbr, h]; decide))
    have hp : prevInfo p = closureInfos.get (2 : Fin 11) :=
      congrArg closureInfos.get (Fin.ext (show min (p.freePiles.toNat - 1) 10 = 2 by rw [h]; decide))
    rw [hc, show (closureInfos.get (3 : Fin 11)).numBits.toNat = 4 from by decide] at hj
    rw [hp, show (closureInfos.get (2 : Fin 11)).numBits.toNat = 6 from by decide] at hil hT
    rw [hp, show (closureInfos.get (2 : Fin 11)).offset.toNat = 16 from by decide]
    rw [hc, globalCfg_mk _ 1 (by decide) j (by omega)] at hms hne
    rw [hp, globalCfg_mk _ 5 (by decide) il (by omega)] at hms hne
    exact (component_spec_16 ⟨T, by simpa using hT⟩ ⟨j, hj⟩).2 ⟨⟨il, hil⟩, hTbit, hms, hne⟩

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
  -- and it sits strictly below the queried configuration
  have hsub : piledSet (globalCfg (prevInfo p) il)
      ⊆ piledSet (globalCfg (closureInfoOf p) i) := by
    rw [heq, piledSet_setCfgBit]
    exact Finset.erase_subset _ _
  have hms : MaskSub (globalCfg (closureInfoOf p) i) (globalCfg (prevInfo p) il) :=
    (maskSub_iff_piledSet_subset _ _).2 hsub
  have hcardne : (piledSet (globalCfg (prevInfo p) il)).card
      ≠ (piledSet (globalCfg (closureInfoOf p) i)).card := by
    rw [heq, hcc, hcd]; omega
  have hne : grlex2bits.get (globalCfg (closureInfoOf p) i)
      ≠ grlex2bits.get (globalCfg (prevInfo p) il) := by
    intro hc
    refine hcardne (congrArg Finset.card (Finset.ext (fun x => ?_)))
    simp only [mem_piledSet, CfgBitSet, hc]
  -- read the table
  have htb := comp_bit_of_maskSub p hfp1 hfp3 result.toNat hbound i hi il hil hbit hms hne
  rw [BitSet_toNat, show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega),
    UInt8.toNat_toUInt16, hcomp]
  exact htb

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
