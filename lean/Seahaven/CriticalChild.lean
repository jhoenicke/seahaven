import Seahaven.MovePreMatch
import Seahaven.CPNormExcept
import Seahaven.KingAssemble
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
is to show it matches, then to hand over.  The chain is

1. `critical_depthMatchesV_movePre` — `t₁` matches `movePre`'s depth vector (the source
   pile's boundary card left; every other column only received one);
2. `exists_cpNormalForm_except` — unpark every pile *but the source*, which turns the
   depth match into a full `StateMatchesSolverPos g v (movePre …)`:
   `flute_match`/`king_pile` come from `flute_match_of_depth`/`king_pile_of_depth` at the
   other nine piles, which are `PileMerged` there (`CleanupReady`), and from exactness at
   the source, whose column the run leaves untouched (`CPReachExcept.tableau_eq`);
3. `SimulatesNorm.moveTail` — the cleanup and the `busyAces` drain, **unmodified**.

The source pile must be skipped in step 2: a cp drop onto it is precisely the cleanup's
freed-predecessor extension, which belongs to `SolverCleanupPile` rather than to
`movePre`.  Note also that `movePre` is *not* merged at the source, which is why the
match is built clause by clause here instead of through `matches_of_depth_match`.

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

/-- **`movePre` has at least as many empty columns as its `freePiles` claims.**
`CleanupReady` counts the depth-zero piles *excluding* the one being cleaned, so the
field can undercount by one — which is the safe direction for the pigeonhole that finds
a spare column (`exists_spare_col`).  This is what lets the king re-assembly run at
`movePre`, which is *not* `SolverInvMerged`. -/
theorem freePiles_le_card_of_cleanupReady {g : Globals} {q : SolverPosType} {pile : UInt32}
    (h : SolverSpec.CleanupReady g q pile) :
    q.freePiles.toNat ≤ (Finset.univ.filter (fun i : Fin 10 => q.pileDepth.get i = 0)).card := by
  obtain ⟨-, -, hfp⟩ := h
  have hcard : (Finset.univ.filter (fun i : Fin 10 => q.pileDepth.get i = 0)).card
      = (List.finRange 10).countP (fun i => q.pileDepth.get i == 0) := by
    simp only [List.countP_eq_length_filter, Finset.filter, Finset.univ, Fintype.elems,
      Finset.card, Multiset.filter, Multiset.card]
    rfl
  have hmono : (List.finRange 10).countP
        (fun j => j.val != pile.toNat && (q.pileDepth.get j == 0))
      ≤ (List.finRange 10).countP (fun i => q.pileDepth.get i == 0) :=
    List.countP_mono_left (fun j _ hj => by
      simp only [Bool.and_eq_true] at hj
      exact hj.2)
  have hcast : q.freePiles.toInt = (q.freePiles.toNat : Int) := rfl
  omega

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
/-- **The critical move, simulated forward.**

The play supplies the post-move state `t₁`; unparking every pile *but the source*
turns it into a state matching `SolverSpec.movePre` outright, and from there the
existing `SimulatesNorm.moveTail` runs the cleanup and the drain unmodified.

Why the source pile is skipped: a cp drop onto it is the cleanup's freed-predecessor
extension, which belongs to `SolverCleanupPile`, not to `movePre`.  Every *other* pile
is `PileMerged` at `movePre` (`CleanupReady`), so its flute is maximal there and the
restricted normal form pins `flute_match` exactly; the source pile is exact by
construction (`|column| = pileDepth`, `pileFlute = 1`), its column being literally
untouched by the run (`CPReachExcept.tableau_eq`). -/
theorem exists_child_of_critical
    {g : Globals} {t₀ t₁ : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    {kCrit : Fin 16} (hkc : DepthPlusKingsCfg g t₀ p kCrit)
    {pile : UInt32} (hpile : pile.toNat < 10)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hcol : (t₀.tableau ⟨pile.toNat, hpile⟩).length
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    {mv : Move} (hsrc : mv.src = Position.pile ⟨pile.toNat, hpile⟩)
    (hdst : mv.dest ≠ Position.pile ⟨pile.toNat, hpile⟩)
    (hap : applyMove t₀ mv = some t₁) (hsolv : Solvable t₁)
    {toPile : UInt8}
    (hdest : EStateM.run (solverGetDestination p pile) g = .ok toPile g)
    (hpres : ∀ su : Suit, PiledSuit t₁ p su → ¬ CfgBitSet kCrit su)
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hms : MaskSub (globalCfg (closureInfoOf p) i) kCrit) :
    ∃ (fk : UInt16) (p' : SolverPosType) (s' : State) (k' : Fin 16) (FK : Finset Suit),
      EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ SolverSpec.DepthSum p' < SolverSpec.DepthSum p ∧
      StateMatchesKingConfig g s' p' k' ∧ Solvable s' ∧
      KingVacates FK fk ∧ BitSet fk k' ∧
      MaskSub k' (globalCfg (closureInfoOf p) i) := by
  have hdpk : DepthPlusKings g t₀ p := hkc.toDepthPlusKings
  set a : Fin 10 := ⟨pile.toNat, hpile⟩ with hadef
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hmerged : SolverInvMerged g p := hcan.toSolverInvMerged
  have hidx5 : (p.pileDepth.get a).toNat - 1 < 5 := by
    have := hb.pileDepth_bound a
    omega
  obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hpile hda hidx5 hdest
  obtain ⟨fkM, pM, hrunM, hcanM, hmeas⟩ :=
    SolverSpec.move_merged g p pile toPile hwf hcan hvalid hpile hidx5 _ rfl hdv
  -- `movePre`'s invariants: merged at every pile but the source
  have hready :=
    SolverSpec.moveDest_cleanupReady g p pile toPile hpile hwf hmerged hda _ hidx5 rfl hdv
  have hfpM := freePiles_le_card_of_cleanupReady hready
  obtain ⟨hbM, hpmM, -⟩ := hready
  have hd6M : ∀ i : Fin 10,
      ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat < 6 :=
    movePre_depth_lt6 hb pile toPile hpile hda
  -- the play's state matches `movePre`'s depths …
  have hdmM : DepthMatchesV g t₁
      (depthVec (SolverSpec.movePre pile toPile hpile p) hd6M) :=
    critical_depthMatchesV_movePre hb hdpk hpile toPile hcol hda hsrc hap
  have hcount₁ : ∀ c : Card, countState t₁ c = 1 := fun c => by
    rw [← congrFun (movePreservesCards t₀ mv t₁ hap) c]
    exact hdpk.cards_count c
  have hdestne : mv.dest ≠ Position.foundation := by
    intro hfd
    exact no_fmStep_of_depthMatch hwf hcan hdpk.depth_lt6 hdpk.depth_match hdpk.cards_count
      hdpk.aces_match t₁ ⟨mv.src, by rw [Move.foundation_eta hfd]; exact hap⟩
  -- the source pile's column, after the move
  have hlenA : (t₁.tableau a).length = (p.pileDepth.get a).toNat - 1 := by
    have hap' := hap
    rw [applyMove_eq, hsrc] at hap'
    obtain ⟨c, s0, htake, hdrop⟩ := hap'
    rw [takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest, hcolA, rfl⟩ := htake
    have hrest : rest.length = (p.pileDepth.get a).toNat - 1 := by
      rw [hcolA] at hcol
      simp only [List.length_cons] at hcol
      omega
    cases hd : mv.dest with
    | foundation =>
      rw [hd, dropPosition, dropFoundation_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      simpa [update] using hrest
    | cell j =>
      rw [hd, dropPosition, dropCell_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      simpa [update] using hrest
    | pile q =>
      have hqa : q ≠ a := fun h => hdst (by rw [hd, h])
      rw [hd, dropPosition, dropCol_eq] at hdrop
      obtain ⟨-, rfl⟩ := hdrop
      simpa [update, if_neg hqa] using hrest
  -- … and unparking every other pile makes the match exact
  obtain ⟨v, hcpr, hnorm⟩ := exists_cpNormalForm_except a t₁
  have hdmV : DepthMatchesV g v (depthVec (SolverSpec.movePre pile toPile hpile p) hd6M) :=
    CPReach.depthMatchesV hcpr.toCPReach hdmM
  have hcountV : ∀ c : Card, countState v c = 1 :=
    CPReach.cards_count hcpr.toCPReach hcount₁
  have hacesV : ∀ su : Suit, (SolverSpec.movePre pile toPile hpile p).aces.get (finOfSuit su)
      = encodeFoundation su (v.foundations su) := by
    intro su
    rw [CPReach.foundations hcpr.toCPReach, foundations_of_nonFoundation_move hap hdestne,
      SolverSpec.movePre_aces]
    exact hdpk.aces_match su
  have hcpi : ∀ (i : Fin 10), i ≠ a → ∀ t, ¬ CPStepOn i v t := by
    intro i hia t ht
    obtain ⟨j, hne, hap'⟩ := ht
    exact hnorm t ⟨j, i, hia, hne, hap'⟩
  have hcolV : (v.tableau a).length = (p.pileDepth.get a).toNat - 1 := by
    rw [hcpr.tableau_eq]; exact hlenA
  have hdepA : ((SolverSpec.movePre pile toPile hpile p).pileDepth.get a).toNat
      = (p.pileDepth.get a).toNat - 1 := movePre_depth_sub hb pile toPile hpile hda
  -- the full match at `movePre`
  have hmV : StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
    refine
      { cards_count := hcountV
        depth_lt6 := hd6M
        depth_match := hdmV
        aces_match := hacesV
        flute_match := ?_
        king_pile := ?_ }
    · -- `flute_match`: exact at the source, `flute_maximal` elsewhere
      intro i hi
      by_cases hia : i = a
      · subst hia
        have h1 : ((1 : UInt8)).toNat = 1 := rfl
        rw [hcolV, SolverSpec.movePre_flute_self, hdepA, h1]
      · exact flute_match_of_depth hwf hbM hd6M hdmV hcountV hacesV i
          (hpmM i (fun hc => hia (Fin.ext hc))) (hcpi i hia) hi
    · -- `king_pile`: vacuous at the source, since its column is then empty
      intro i hi
      by_cases hia : i = a
      · subst hia
        have hnil : v.tableau a = [] := by
          refine List.eq_nil_of_length_eq_zero ?_
          rw [hcolV]
          have := hdepA
          omega
        intro d hd
        rw [hnil] at hd
        simp at hd
      · exact king_pile_of_depth hwf hbM hd6M hdmV hcountV hacesV i (hcpi i hia) hi
  have hkV : StateMatchesKingConfig g v (SolverSpec.movePre pile toPile hpile p)
      (cfgOf v (SolverSpec.movePre pile toPile hpile p)) :=
    { toMatches := hmV
      realizes := hmV.toDepthPlusKings.toCfg.realizes
      no_pile := hmV.toDepthPlusKings.toCfg.no_pile }
  -- the block configuration covers `v`'s physical piles …
  have hfpEq : (SolverSpec.movePre pile toPile hpile p).freePiles = p.freePiles := by
    unfold SolverSpec.movePre SolverSpec.fluteNorm removeFlutePre SolverSpec.moveDestPre
    split_ifs <;> rfl
  have hciEq : closureInfoOf (SolverSpec.movePre pile toPile hpile p) = closureInfoOf p := by
    unfold closureInfoOf
    refine congrArg closureInfos.get (Fin.ext ?_)
    show min (SolverSpec.movePre pile toPile hpile p).freePiles.toNat 10
      = min p.freePiles.toNat 10
    rw [hfpEq]
  have hsubV : MaskSub (globalCfg (closureInfoOf p) i)
      (cfgOf v (SolverSpec.movePre pile toPile hpile p)) := by
    rw [MaskSub_iff]
    intro su hbit
    rw [cfgBitSet_cfgOf]
    intro hp
    obtain ⟨i₁, hd0, d, hd, hsu⟩ :=
      (hcpr.toCPReach.piledSuit_iff (SolverSpec.movePre pile toPile hpile p) su).1 hp
    have hia : i₁ ≠ a := by
      intro hc
      have hd0' : ((SolverSpec.movePre pile toPile hpile p).pileDepth.get a).toNat = 0 := by
        rw [← hc]; exact hd0
      have hz : (t₁.tableau a).length = 0 := by
        rw [hlenA]
        rw [hdepA] at hd0'
        omega
      rw [hc, List.eq_nil_of_length_eq_zero hz] at hd
      simp at hd
    refine hpres su ⟨i₁, ?_, d, hd, hsu⟩ ((MaskSub_iff _ kCrit).1 hms su hbit)
    rw [← SolverSpec.movePre_depth_ne pile toPile hpile p i₁ (fun hc => hia (Fin.ext hc))]
    exact hd0
  -- … so the state can be reshuffled to stand for it, equi-solvably
  obtain ⟨v', hkV', hsolvV⟩ :=
    exists_block_match (p := SolverSpec.movePre pile toPile hpile p) hwf hbM hfpM hkV
      (i := i) (by rw [hciEq]; exact hi) (by rw [hciEq]; exact hsubV)
  rw [hciEq] at hkV'
  -- the cleanup and the drain, unmodified
  obtain ⟨fk, p', s', k', FK, hrun, hcan', hsim⟩ :=
    SimulatesNorm.moveTail pile toPile hwf hcan hvalid hpile hidx5 _ rfl hdv hkV'
  have hpMeq : pM = p' := by
    have h := hrunM.symm.trans hrun
    simp only [EStateM.Result.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2
  rw [hpMeq] at hcanM hmeas
  refine ⟨fk, p', s', k', FK, hrun, hcanM, hmeas, hsim.cfg, ?_, hsim.vacates,
    hsim.toSimulates.bitSet_fk, ?_⟩
  · exact hsim.solvable_iff.1 (hsolvV.1 (hcpr.solvable_iff.1 hsolv))
  · rw [MaskSub_iff]
    intro su hbit
    by_contra hc
    exact ((hsim.bound su).2 (Or.inl hc)) hbit
