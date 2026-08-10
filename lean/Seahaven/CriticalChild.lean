import Seahaven.MovePreMatch
import Seahaven.CleanupDepth
import Seahaven.CPNormCfg
import Seahaven.SolverMoveSim
import Seahaven.RecCheckSound

/-!
# The critical move, simulated forward

Route B's payload for one iteration of `solverRecCheckSolvable`'s pile loop: from the
critical state `t₀` and the move the play makes out of it, the solver's own
`SolverMove` reaches a canonical child that a **solvable** state matches.

Nothing here is constructed — the play supplies the post-move state, and the whole job
is to show it matches, then to normalize.  The chain is

1. `critical_depthMatchesV_movePre` — `t₁` matches `movePre`'s depth vector (the source
   pile's boundary card left; every other column only received one);
2. `depthMatchesV_removeFlute` — hence the post-cleanup position's, the merge and the
   lone-king vacate both being re-readings of the same column;
3. `DepthPlusKings.of_depthMatch` + `toCfg` + `exists_cpNormal_match` — exhausting the
   cell→pile drops turns the depth match into a full `StateMatchesKingConfig`, at the
   configuration the state *is* in, with solvability unchanged in both directions;
4. `SimulatesNorm.drainFrom` — the `busyAces` drain, all foundation plays and cell→pile
   drops, so again equi-solvable.

The `forcedKings` side condition of step 4 is discharged by `kingVacates_removeFlute`:
the cleanup's vacated king is physically on the freed column, so the configuration piles
it whether anyone chose that reading or not.

`IsCanonicalPos` and the measure come from the position-level `move_merged`, which is
polarity-neutral and was proved for soundness.
-/

open Lean Lean.Order

/-! ## Depths only fall -/

theorem movePre_depth_le {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat) (i : Fin 10) :
    ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat
      ≤ (p.pileDepth.get i).toNat := by
  by_cases hi : i.val = pile.toNat
  · have hfin : i = ⟨pile.toNat, hpile⟩ := Fin.ext hi
    subst hfin
    rw [movePre_depth_sub hb pile toPile hpile hda]
    omega
  · rw [SolverSpec.movePre_depth_ne pile toPile hpile p i hi]

/-! ## Piled suits survive the critical move

The move takes from a pile of positive depth, so it never touches a solver-empty
column's *deepest* card: the take is elsewhere, and a drop only pushes a card on top of
a column that already had one. -/

theorem piledSuit_of_move {t₀ t₁ : State} {mv : Move} (hap : applyMove t₀ mv = some t₁)
    {a : Fin 10} (hsrc : mv.src = Position.pile a) {p q : SolverPosType}
    (hda : 0 < (p.pileDepth.get a).toNat)
    (hdq : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat)
    {su : Suit} (hp : PiledSuit t₀ p su) : PiledSuit t₁ q su := by
  obtain ⟨i, hd0, d, hd, hsuit⟩ := hp
  have hia : i ≠ a := by intro h; rw [h] at hd0; omega
  refine ⟨i, by have := hdq i; omega, d, ?_, hsuit⟩
  rw [applyMove_eq, hsrc] at hap
  obtain ⟨c, s0, htake, hdrop⟩ := hap
  rw [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest, hcol, rfl⟩ := htake
  have hs0 : (updateColumn t₀ a rest).tableau i = t₀.tableau i := by
    simp [update, Ne.symm hia]
  cases hdst : mv.dest with
  | foundation =>
    rw [hdst, dropPosition, dropFoundation_eq] at hdrop
    obtain ⟨-, rfl⟩ := hdrop
    rw [updateFoundation_tableau, hs0]
    exact hd
  | cell j =>
    rw [hdst, dropPosition, dropCell_eq] at hdrop
    obtain ⟨-, rfl⟩ := hdrop
    rw [updateCell_tableau, hs0]
    exact hd
  | pile r =>
    rw [hdst, dropPosition, dropCol_eq] at hdrop
    obtain ⟨-, rfl⟩ := hdrop
    rw [updateColumn_tableau]
    by_cases hir : r = i
    · subst hir
      rw [update_same, hs0]
      have hne : t₀.tableau r ≠ [] := by
        intro hc
        rw [Option.mem_def, hc] at hd
        simp at hd
      rw [getLast?_cons_of_ne_nil hne]
      exact hd
    · rw [update_diff _ _ _ _ hir, hs0]
      exact hd

/-! ## The assembly -/

set_option maxHeartbeats 1000000 in
/-- **The critical move, simulated forward.**  See the module docstring for the chain.

The last conjunct is what carries the configuration back to the parent: `k'` piles
everything the critical state physically piled, so `MaskSub` composes from the child's
`subsetTable` witness through `k'` to the parent's block configuration. -/
theorem exists_child_of_critical
    {g : Globals} {t₀ t₁ : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hdpk : DepthPlusKings g t₀ p)
    {pile : UInt32} (hpile : pile.toNat < 10)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hcol : (t₀.tableau ⟨pile.toNat, hpile⟩).length
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    {mv : Move} (hsrc : mv.src = Position.pile ⟨pile.toNat, hpile⟩)
    (hap : applyMove t₀ mv = some t₁) (hsolv : Solvable t₁)
    {toPile : UInt8}
    (hdest : EStateM.run (solverGetDestination p pile) g = .ok toPile g) :
    ∃ (fk : UInt16) (p' : SolverPosType) (s' : State) (k' : Fin 16),
      EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ SolverSpec.DepthSum p' < SolverSpec.DepthSum p ∧
      StateMatchesKingConfig g s' p' k' ∧ Solvable s' ∧ BitSet fk k' ∧
      (∀ su : Suit, PiledSuit t₀ p su → ¬ CfgBitSet k' su) := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hmerged : SolverInvMerged g p := hcan.toSolverInvMerged
  have hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by
    have := hb.pileDepth_bound ⟨pile.toNat, hpile⟩
    omega
  obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hpile hda hidx5 hdest
  -- the position-level facts: the run, canonicity, and the measure
  obtain ⟨fkM, pM, hrunM, hcanM, hmeas⟩ :=
    SolverSpec.move_merged g p pile toPile hwf hcan hvalid hpile hidx5 _ rfl hdv
  -- phase 2's entry point and result
  have hready := SolverSpec.moveDest_cleanupReady g p pile toPile hpile hwf hmerged hda _
    hidx5 rfl hdv
  have hbM := hready.1
  obtain ⟨fk1, p1, hrun1, hmerged1, haces1, -⟩ :=
    SolverSpec.removeFlute_merged pile g (SolverSpec.moveDestPre pile toPile hpile p) hpile
      hwf hready
  have hrun1' : _root_.SolverRemoveFlute pile (g, SolverSpec.moveDestPre pile toPile hpile p)
      = .ok fk1 (g, p1) := hrun1
  -- step 1: the depth vector of `movePre`
  have hd6M : ∀ i : Fin 10,
      ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat < 6 :=
    movePre_depth_lt6 hb pile toPile hpile hda
  have hdmM : DepthMatchesV g t₁
      (depthVec (SolverSpec.movePre pile toPile hpile p) hd6M) :=
    critical_depthMatchesV_movePre hb hdpk hpile toPile hcol hda hsrc hap
  -- step 2: the depth vector of the post-cleanup position
  have hd61 : ∀ i : Fin 10, (p1.pileDepth.get i).toNat < 6 := fun i => by
    have := hmerged1.toSolverInvBase.pileDepth_bound i
    omega
  have hdm1 : DepthMatchesV g t₁ (depthVec p1 hd61) :=
    depthMatchesV_removeFlute hwf hpile toPile hbM hd6M hdmM hrun1' hd61
  -- the card count and the foundations travel with the move
  have hcount1 : ∀ c : Card, countState t₁ c = 1 := fun c => by
    rw [← congrFun (movePreservesCards t₀ mv t₁ hap) c]
    exact hdpk.cards_count c
  have hdestne : mv.dest ≠ Position.foundation := by
    intro hfd
    exact no_fmStep_of_depthMatch hwf hcan hdpk.depth_lt6 hdpk.depth_match hdpk.cards_count
      hdpk.aces_match t₁ ⟨mv.src, by rw [Move.foundation_eta hfd]; exact hap⟩
  have haces1' : ∀ su : Suit,
      p1.aces.get (finOfSuit su) = encodeFoundation su (t₁.foundations su) := by
    intro su
    rw [foundations_of_nonFoundation_move hap hdestne, haces1,
      (SolverSpec.moveDestPre_depth_aces pile toPile hpile p).2]
    exact hdpk.aces_match su
  -- step 3: the middle layer at `p1`, then its CP-normal form
  have hdpk1 : DepthPlusKings g t₁ p1 :=
    DepthPlusKings.of_depthMatch hwf hmerged1.toSolverInvBase hmerged1.pileMerged hd61 hdm1
      hcount1 haces1'
  obtain ⟨u, hcp, hmatch1, hsolviff⟩ :=
    hdpk1.toCfg.exists_cpNormal_match hwf hmerged1.toSolverInvBase hmerged1.pileMerged
  -- the cleanup's `forcedKings` is met by the state
  obtain ⟨FK0, hvac0, hFK0⟩ :=
    kingVacates_removeFlute hwf hpile hbM (fun i h => hdmM i) hrun1'
  have hFK : ∀ su ∈ FK0, ¬ CfgBitSet (cfgOf t₁ p1) su := fun su hsu =>
    cfgBitSet_clear_of_piled hmatch1 ((hcp.piledSuit_iff p1 su).2 (hFK0 su hsu))
  -- step 4: the drain
  obtain ⟨fk2, p2, s2, k2, FK2, hrun2, hcan2, hsim2⟩ :=
    SimulatesNorm.drainFrom hwf hmerged1 hmatch1 hvac0 hFK
  -- the two phases are the whole call
  have hrun : EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk2 (g, p2) := by
    obtain ⟨-, htoPile14, -⟩ := hvalid
    rw [SolverSpec.moveDest_run_eq pile toPile g p hpile htoPile14]
    show (_root_.SolverRemoveFlute pile >>= fun fk =>
        Loop.forIn Loop.mk fk drainBody >>= fun r => pure r)
      (g, SolverSpec.moveDestPre pile toPile hpile p) = .ok fk2 (g, p2)
    simp only [bind, EStateM.bind, hrun1', pure, EStateM.pure]
    rw [hrun2]
  -- transport the measure through the run
  have hpMeq : pM = p2 := by
    have h := hrunM.symm.trans hrun
    simp only [EStateM.Result.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2
  rw [hpMeq] at hcanM hmeas
  refine ⟨fk2, p2, s2, k2, hrun, hcanM, hmeas, hsim2.cfg, ?_, ?_, ?_⟩
  · exact hsim2.solvable_iff.1 (hsolviff.1 (hsolv))
  · exact hsim2.toSimulates.bitSet_fk
  · intro su hp
    refine (hsim2.bound su).2 (Or.inl (cfgBitSet_clear_of_piled hmatch1 ?_))
    refine (hcp.piledSuit_iff p1 su).2 (piledSuit_of_move hap hsrc hda (fun i => ?_) hp)
    exact le_trans (removeFlute_depth_le hwf hpile hbM (fun j h => hdmM j) hrun1' i)
      (movePre_depth_le hb pile toPile hpile hda i)
