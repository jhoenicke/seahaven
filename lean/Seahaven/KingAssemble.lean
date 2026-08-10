import Seahaven.KingMoveSim
import Seahaven.MaximalCfg

/-!
# Completing a configuration, reversibly

The completeness step queries the child at a **block** configuration — one king
per free pile — while the state the play produced stands only for the sparser
configuration it happens to be in.  Closing that gap means physically piling the
missing kings, and the point of this file is that doing so costs nothing:

> the moves are cell → pile drops, and every one of them undoes itself
> (`applyMove_cell_pile_inv`), so the two states are **equi-solvable**.

That is the difference from `KingConfigReachable`, which records only `Reach s t`
and therefore carries solvability the wrong way (`Solvable t → Solvable s`).
`KingConfigEquiv` records the round trip.

Two cases hide inside one lemma, and neither needs an argument here:

* the suit's freed run is in the cells — `kingPileEquiv` walks it onto a spare
  column card by card;
* nothing of the suit is freed yet (`VALUE kings[su] = 13`) — the run is empty, no
  card moves, and the spare column is claimed through `OwnsPile`'s reservation
  branch.

The one real side condition is the column budget: a configuration may not claim
more piles than the position has empty columns.  Cell space is *not* a condition —
piling only frees cells.
-/

/-- `s` can be reshuffled into a state standing for `k` **and back again**, so the
two are equi-solvable.  The reversible strengthening of `KingConfigReachable`. -/
def KingConfigEquiv (g : Globals) (p : SolverPosType) (s : State) (k : Fin 16) : Prop :=
  ∃ t : State, Reach s t ∧ Reach t s ∧ StateMatchesKingConfig g t p k

theorem KingConfigEquiv.toReachable {g : Globals} {p : SolverPosType} {s : State} {k : Fin 16}
    (h : KingConfigEquiv g p s k) : KingConfigReachable g p s k := by
  obtain ⟨t, hf, -, ht⟩ := h
  exact ⟨t, hf, ht⟩

theorem KingConfigEquiv.refl {g : Globals} {p : SolverPosType} {s : State} {k : Fin 16}
    (h : StateMatchesKingConfig g s p k) : KingConfigEquiv g p s k :=
  ⟨s, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, h⟩

/-! ## One pile step -/

/-- Piling one more suit, with the round trip composed on. -/
theorem pile_kingConfigEquiv {g : Globals} {p : SolverPosType} {s : State} {k : Fin 16}
    {su : Suit} (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (h : KingConfigEquiv g p s k) (hsu : CfgBitSet k su)
    (hcard : (piledSet k).card < p.freePiles.toNat) :
    KingConfigEquiv g p s (clearCfgBit k su) := by
  obtain ⟨s1, hf1, hb1, hs1⟩ := h
  obtain ⟨s2, hf2, hb2, hs2⟩ := kingPileEquiv g p s1 k su hwf hm hs1 hsu hcard
  exact ⟨s2, hf1.trans hf2, hb2.trans hb1, hs2⟩

/-! ## Up to any configuration that piles more

The induction of `maskSub_kingConfigReachable`, with the round trip carried along:
one suit per round, and `d`'s own pile count bounds the columns in use throughout. -/

theorem maskSub_kingConfigEquiv {g : Globals} {p : SolverPosType} {s : State} {d : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hd : (piledSet d).card ≤ p.freePiles.toNat) :
    ∀ (m : Nat) (c : Fin 16), (piledSet d \ piledSet c).card ≤ m →
      piledSet c ⊆ piledSet d → KingConfigEquiv g p s c → KingConfigEquiv g p s d := by
  intro m
  induction m with
  | zero =>
    intro c hle hsub h
    have hdc : piledSet d ⊆ piledSet c :=
      Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 (by omega))
    exact piledSet_inj (Finset.Subset.antisymm hsub hdc) ▸ h
  | succ m ih =>
    intro c hle hsub h
    by_cases hdc : piledSet d ⊆ piledSet c
    · exact piledSet_inj (Finset.Subset.antisymm hsub hdc) ▸ h
    obtain ⟨su, hsu⟩ := Finset.sdiff_nonempty.2 hdc
    obtain ⟨hsud, hsuc⟩ := Finset.mem_sdiff.1 hsu
    have hbit : CfgBitSet c su := by
      by_contra hc
      exact hsuc (mem_piledSet.2 hc)
    have hlt : (piledSet c).card < (piledSet d).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨su, hsud, hsuc⟩)
    refine ih (clearCfgBit c su) ?_ ?_
      (pile_kingConfigEquiv hwf hm h hbit (by omega))
    · rw [piledSet_clearCfgBit, Finset.sdiff_insert, Finset.card_erase_of_mem hsu]
      omega
    · rw [piledSet_clearCfgBit]
      exact Finset.insert_subset hsud hsub

/-! ## The interface: a state standing for a block configuration

`MaskSub d k` is exactly `piledSet k ⊆ piledSet d`, and a block configuration piles
`numPiledKings p ≤ freePiles` suits — the column budget, for free. -/

/-- **Reshuffling up to a configuration that piles more, reversibly.** -/
theorem kingConfigEquiv_of_maskSub {g : Globals} {p : SolverPosType} {s : State} {k d : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hk : StateMatchesKingConfig g s p k) (hsub : MaskSub d k)
    (hd : (piledSet d).card ≤ p.freePiles.toNat) : KingConfigEquiv g p s d :=
  maskSub_kingConfigEquiv hwf hm hd _ k le_rfl
    (fun su hsu => by
      rw [mem_piledSet] at hsu ⊢
      exact fun hc => hsu ((MaskSub_iff d k).1 hsub su hc))
    (KingConfigEquiv.refl hk)

/-- **The form the completeness step uses.**  From a state standing for `k`, reach a
state standing for the block configuration `i` that covers `k` — solvable exactly
when the original was.

`i` is the bit the loop's `movable` mask and the `subsetTable` transport are both
indexed by, so this is what lets the child's answer be read at a configuration
piling everything the parent's block configuration piles. -/
theorem exists_block_match {g : Globals} {p : SolverPosType} {s : State} {k : Fin 16}
    (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hk : StateMatchesKingConfig g s p k) {i : Nat}
    (hi : i < (closureInfoOf p).numBits.toNat)
    (hsub : MaskSub (globalCfg (closureInfoOf p) i) k) :
    ∃ t : State, StateMatchesKingConfig g t p (globalCfg (closureInfoOf p) i) ∧
      (Solvable s ↔ Solvable t) := by
  have hd : (piledSet (globalCfg (closureInfoOf p) i)).card ≤ p.freePiles.toNat := by
    rw [card_piledSet_globalCfg p i hi]
    unfold numPiledKings
    omega
  obtain ⟨t, hf, hb, ht⟩ := kingConfigEquiv_of_maskSub hwf hm hk hsub hd
  exact ⟨t, ht, ⟨fun hs => Solvable.of_reach hb hs, fun hs => Solvable.of_reach hf hs⟩⟩

/-- **And a block configuration always exists.**  Every configuration a position can
realize is covered by one of its block's (`MaximalCfg`), so the completion is never
blocked. -/
theorem exists_block_match_of_realizes {g : Globals} {p : SolverPosType} {s : State}
    {k : Fin 16} (hwf : WellFormedLayout g) (hm : SolverInvMerged g p)
    (hk : StateMatchesKingConfig g s p k) :
    ∃ (i : Nat) (t : State), i < (closureInfoOf p).numBits.toNat ∧
      MaskSub (globalCfg (closureInfoOf p) i) k ∧
      StateMatchesKingConfig g t p (globalCfg (closureInfoOf p) i) ∧ (Solvable s ↔ Solvable t) := by
  obtain ⟨i, hi, hsub⟩ := exists_block_cfg_maskSub hm hk.realizes
  obtain ⟨t, ht, hsolv⟩ := exists_block_match hwf hm hk hi hsub
  exact ⟨i, t, hi, hsub, ht, hsolv⟩
