import Seahaven.DestAfford

/-!
# Every configuration is covered by one of its block's stored ones

`closureInfo_block` says block `f` holds exactly the grlex indices whose mask has
popcount `4 - min f 4` — i.e. exactly the **maximal** king assignments, with
`min(freePiles,4)` suits piled.  A state's own configuration (`cfgOf`, or `cfgOfPlus`)
usually piles *fewer* suits, so it has no bit in the loop at all; it enters only
through the `subsetTable` expansion, which closes the stored configurations downwards.

Completeness therefore needs the covering statement: for every configuration `k` the
position can be in, the block contains a `d` with `MaskSub d k` — `d` piles at least
what `k` piles.  That is pure counting: `k` piles at most `min(freePiles,4)` suits
(`card_clear_le_freePiles`), and a block configuration piles exactly that many, so some
superset of `k`'s piled set is stored.

Affordability comes along for free: `freeCellsOf_mono` says piling more only increases
the cell budget, so `d` affords whatever `k` afforded.

This is the arithmetic half of `SubsetComplete`.  The other half — that the *state*
can actually be brought into configuration `d`, by moving king runs from the cells onto
empty columns — is the physical direction, and is not needed for the counting here.
-/

/-! ## Piled suits versus mask popcount -/

/-- The piled suits and the mask's set bits partition the four suits. -/
theorem card_piled_add_popCount (k : Fin 16) :
    (Finset.univ.filter (fun su : Suit => ¬ CfgBitSet k su)).card
      + popCount4 (grlex2bits.get k).toNat = 4 := by
  revert k; decide

/-- A configuration piles at most four suits. -/
theorem card_piled_le_four (k : Fin 16) :
    (Finset.univ.filter (fun su : Suit => ¬ CfgBitSet k su)).card ≤ 4 := by
  have := card_piled_add_popCount k
  omega

/-! ## The covering configuration -/

/-- **The block covers every configuration it could be asked about.**  Decided against
the tables: with at most `min f 4` suits piled, some stored (maximal) configuration of
block `f` piles a superset. -/
theorem exists_globalCfg_maskSub (f : Fin 11) (k : Fin 16)
    (hcard : (Finset.univ.filter (fun su : Suit => ¬ CfgBitSet k su)).card ≤ min f.val 4) :
    ∃ j : Fin 6, j.val < (closureInfos.get f).numBits.toNat ∧
      MaskSub (globalCfg (closureInfos.get f) j.val) k := by
  revert f k; decide

/-- **The covering configuration, for a configuration the position really realizes.**
The card bound is `RealizesKingConfig.card_clear_le_freePiles`. -/
theorem exists_block_cfg_maskSub {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hm : SolverInvMerged g p) (hr : RealizesKingConfig s p k) :
    ∃ j : Nat, j < (closureInfoOf p).numBits.toNat ∧
      MaskSub (globalCfg (closureInfoOf p) j) k := by
  have hfp := hr.card_clear_le_freePiles hm
  have h4 := card_piled_le_four k
  obtain ⟨j, hj, hsub⟩ := exists_globalCfg_maskSub ⟨min p.freePiles.toNat 10, by omega⟩ k
    (by simp only []; omega)
  exact ⟨j.val, hj, hsub⟩

/-- **And it affords whatever the realized configuration afforded.**  `freeCellsOf` is
monotone along `MaskSub`, so the space bound the play established at `k` transports to
the block configuration the loop actually indexes. -/
theorem exists_block_cfg_afford {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hb : SolverInvBase g p) (hm : SolverInvMerged g p) (hr : RealizesKingConfig s p k)
    (c : Int) (hc : c ≤ freeCellsOf p k) :
    ∃ j : Nat, j < (closureInfoOf p).numBits.toNat ∧
      MaskSub (globalCfg (closureInfoOf p) j) k ∧
      c ≤ freeCellsOf p (globalCfg (closureInfoOf p) j) := by
  obtain ⟨j, hj, hsub⟩ := exists_block_cfg_maskSub hm hr
  exact ⟨j, hj, hsub, le_trans hc (freeCellsOf_mono hb hsub)⟩

/-- A suit piled by the realized configuration is piled by the covering one — which is
what the king-pile branch of `solverGetMovable` needs (`kingOnPile`). -/
theorem maskSub_piled {d k : Fin 16} (h : MaskSub d k) {su : Suit}
    (hk : ¬ CfgBitSet k su) : ¬ CfgBitSet d su :=
  fun hd => hk ((MaskSub_iff d k).1 h su hd)
