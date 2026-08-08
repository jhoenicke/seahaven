import Seahaven.GetMovableSpec
import Seahaven.SolverMoveSim

/-!
# `MoveSimulated`, reduced to phase 1

`Simulates.move` already discharges phases 2 and 3 of a `SolverMove` call; what it
takes on trust is `hphase1`, the flute move itself.  This file shows that
`MoveSimulated`'s hypotheses supply everything *else* that `Simulates.move` wants,
so the whole obligation collapses to one statement about phase 1:

> `Phase1Simulated → MoveSimulated`.

The two hypotheses `MoveSimulated` gained for this — `KingInfoCorrect` and the
`solverGetDestination` run — are exactly what was missing:

* `destValid_of_getDest` turns the destination run into the `MoveValid`/`DestValid`
  pair `Simulates.move` consumes.  Without it the obligation is *false*, not merely
  unproved: `SolverMove` validates nothing, so its run alone admits a successor `p'`
  that no state matches while the conclusion demands `StateMatchesKingConfig … p' …`.
* `KingInfoCorrect` is what makes the returned `movable` mask mean anything; it is
  what `getMovable_freeCells` reads to produce phase 1's free-cell side conditions.
-/

/-- **Phase 1 of a `SolverMove`, simulated.**  Everything `Simulates.move` cannot
prove on its own, stated at exactly the hypotheses `MoveSimulated` has.

The configuration is unchanged (`k` on both sides) and the mask is neutral: no
phase-1 move vacates a king — vacates happen inside `SolverCleanupPile`, which
`Simulates.ofRemoveFlute` already covers. -/
def Phase1Simulated : Prop :=
  ∀ (g : Globals) (s : State) (p : SolverPosType) (ki : KingInfo) (pile : UInt32)
    (toPile : UInt8) (mv : UInt16) (i : Nat),
    i < (closureInfoOf p).numBits.toNat →
    WellFormedLayout g → IsCanonicalPos g p →
    StateMatchesKingConfig g s p (globalCfg (closureInfoOf p) i) →
    KingInfoCorrect p ki →
    ∀ hpile : pile.toNat < 10,
    0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat →
    EStateM.run (solverGetDestination p pile) g = .ok toPile g →
    EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g →
    BitSet mv ⟨min i 15, by omega⟩ →
    ∃ v : State, Simulates g s p (globalCfg (closureInfoOf p) i) v
      (SolverSpec.movePre pile toPile hpile p) (globalCfg (closureInfoOf p) i) ∅ 0xffff

/-- **The statement fix is exactly what was needed.**  With the king-space and
destination guarantees in hand, `MoveSimulated` is `Simulates.move` plus phase 1
and nothing else. -/
theorem moveSimulated_of_phase1 (h1 : Phase1Simulated) : MoveSimulated := by
  intro g s p p' pile toPile fk mv ki i hi hwf hcan hs hkic hpile hdepth hdest hmv hbit hrun
  -- the depth, in the spelling `move_merged` and `getDest_spec` use
  have hfin : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hpile)
  have hd : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by rw [← hfin]; exact hdepth
  have hb5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by
    have := hcan.toSolverInvBase.pileDepth_bound ⟨pile.toNat, hpile⟩
    omega
  -- what the destination walk guarantees
  obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hpile hd hb5 hdest
  -- phase 1, and the whole call
  obtain ⟨fk', p'', s', k', FK, hrun', hcan'', hsim⟩ :=
    Simulates.move pile toPile hwf hcan hvalid hpile hb5 _ rfl hdv
      (h1 g s p ki pile toPile mv i hi hwf hcan hs hkic hpile hdepth hdest hmv hbit)
  -- the solver's own run pins the mask and the successor position
  injection hrun'.symm.trans hrun with h1e h2e
  injection h2e with _hg hp2
  subst h1e
  subst hp2
  exact ⟨s', k', FK, hsim⟩
