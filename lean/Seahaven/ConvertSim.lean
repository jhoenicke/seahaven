import Seahaven.ConvertSound
import Seahaven.SolverMoveSim

/-!
# `SolverConvertFromPilesKings` is simulated by legal `Rules` moves

`ConvertSound` shows the call produces a canonical position.  This file adds the
`Rules`-side half: if a concrete state `s` stands for the prologue's position
`convertPre g pk` at king configuration `k`, then the rest of the call — the
per-pile cleanup loop and the `busyAces` drain — is realized by a sequence of
legal moves, and the resulting canonical position is matched by the state they
reach.

The two ingredients are already available:

* `SimulatesNorm.ofCleanupPile` — one `SolverCleanupPile` call, simulated;
* `SimulatesNorm.drain` — the whole `busyAces` drain, simulated.

`MoveAcesSim g s P k fk q` (`∃ w k' FK, Simulates g s P k w q k' FK fk`) is the
carrier: it is exactly what `SimulatesNorm.drain` already threads, and
`Simulates.trans` is what each cleanup iteration does to it.
-/

namespace SolverSpec

open Lean Lean.Order

/-- A position whose pile `pile` already carries the default flute is its own
    flute normalization — so the cleanup's precondition can be read off
    `MergedUpTo`'s suffix clause directly. -/
theorem fluteNorm_self (pile : UInt32) (hpile : pile.toNat < 10) (q : SolverPosType)
    (h : q.pileFlute.get ⟨pile.toNat, hpile⟩ = 1) : fluteNorm pile hpile q = q := by
  have hsf : q.pileFlute.set pile.toNat 1 hpile = q.pileFlute := by
    conv_lhs => rw [← h]
    exact Vector.set_getElem_self hpile
  show { q with pileFlute := q.pileFlute.set pile.toNat 1 hpile } = q
  rw [hsf]

/-- **The cleanup loop is simulated**, one `SimulatesNorm.ofCleanupPile` per pile,
    accumulated by `Simulates.trans` exactly as the loop accumulates
    `forcedKings := forcedKings &&& …`. -/
theorem cvCleanupLoop_sim (g : Globals) (hwf : WellFormedLayout g)
    (s : State) (P : SolverPosType) (k : Fin 16) :
    ∀ (n j : Nat), j + n = 10 → ∀ (fk : UInt16) (q : SolverPosType),
      MergedUpTo g q j → MoveAcesSim g s P k fk q →
      ∃ (fk' : UInt16) (q' : SolverPosType),
        forIn (List.range' j n) fk cvCleanupBody (g, q) = .ok fk' (g, q') ∧
        MergedUpTo g q' 10 ∧ MoveAcesSim g s P k fk' q' := by
  intro n
  induction n with
  | zero =>
    intro j hj fk q hq hP
    obtain rfl : j = 10 := by omega
    exact ⟨fk, q, rfl, hq, hP⟩
  | succ n ih =>
    intro j hj fk q hq hP
    have hjlt : j < 10 := by omega
    have hpile : (UInt32.ofNat j).toNat < 10 := by
      rw [UInt32.toNat_ofNat']; omega
    -- the solver's own step
    obtain ⟨fk0, q1, hrun1, hq1, -⟩ := solverCleanupPile_step g q j hjlt hwf hq
    -- pile `j` has not been touched yet, so `fluteNorm` is a no-op there
    obtain ⟨hnf, -, -, hfluteRest⟩ := hq
    have hfn : fluteNorm (UInt32.ofNat j) hpile q = q :=
      fluteNorm_self _ hpile q (hfluteRest ⟨(UInt32.ofNat j).toNat, hpile⟩
        (show j ≤ (UInt32.ofNat j).toNat from by rw [UInt32.toNat_ofNat']; omega))
    -- the simulation of that step, chained onto what we already have
    obtain ⟨w, kk, FK, hsim⟩ := hP
    have hb : SolverInvBase g (fluteNorm (UInt32.ofNat j) hpile q) := by rw [hfn]; exact hnf
    have hkcfg : StateMatchesKingConfig g w (fluteNorm (UInt32.ofNat j) hpile q) kk := by
      rw [hfn]; exact hsim.cfg
    obtain ⟨w', kk', FK', hsim'⟩ :=
      SimulatesNorm.ofCleanupPile hwf hpile hb hkcfg hrun1
    rw [hfn] at hsim'
    have hP1 : MoveAcesSim g s P k (fk &&& fk0) q1 := ⟨w', kk', FK ∪ FK', hsim.trans hsim'⟩
    obtain ⟨fk', q', hrun', hq', hP'⟩ := ih (j + 1) (by omega) (fk &&& fk0) q1 hq1 hP1
    refine ⟨fk', q', ?_, hq', hP'⟩
    rw [List.range'_succ, List.forIn_cons]
    show (cvCleanupBody j fk >>= _) (g, q) = _
    simp only [bind, EStateM.bind, cvCleanupBody_run j fk fk0 g q q1 hrun1]
    exact hrun'

/-- **A whole `SolverConvertFromPilesKings` call is simulated.**  From a state
    standing for the prologue's position, the cleanup loop and the foundation
    drain are realized by legal moves; the position they end at is canonical and
    is matched by the state they reach, at a configuration bounded by the vacated
    suits (which is what the returned `forcedKings` mask records). -/
theorem convert_simulates (g : Globals) (hwf : WellFormedLayout g) (pk : Vector UInt8 11)
    (hpk : ValidDepths pk) (p0 : SolverPosType) (s : State) (k : Fin 16)
    (hk : StateMatchesKingConfig g s (convertPre g pk) k) :
    ∃ (fk : UInt16) (p' : SolverPosType) (s' : State) (k' : Fin 16) (FK : Finset Suit),
      EStateM.run (_root_.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧
      SimulatesNorm g s (convertPre g pk) k s' p' k' FK fk := by
  have hcount : CvCountBound g pk := cvCountBound g hwf pk hpk
  -- loop 3, with the simulation riding along
  obtain ⟨fk1, q1, hrun1, hq1, hP1⟩ :=
    cvCleanupLoop_sim g hwf s (convertPre g pk) k 10 0 rfl 0xffff (convertPre g pk)
      (convertPre_mergedUpTo_zero g pk hwf hpk)
      ⟨s, k, ∅, SimulatesNorm.refl hk⟩
  have hmerged : SolverInvMerged g q1 := mergedUpTo_ten_iff.mp hq1
  -- loop 4
  obtain ⟨fk2, q2, hrun2, hcan, hP2⟩ := SimulatesNorm.drain hwf hmerged hP1
  obtain ⟨s', k', FK, hsim⟩ := hP2
  refine ⟨fk2, q2, s', k', FK, ?_, hcan, hsim⟩
  show _root_.SolverConvertFromPilesKings pk (g, p0) = _
  rw [convert_run_eq g hwf pk p0 hpk hcount]
  show (forIn (List.range 10) (0xffff : UInt16) cvCleanupBody >>= fun fk =>
      Loop.forIn Loop.mk fk drainBody >>= fun r => pure r) (g, convertPre g pk) = _
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    show List.range 10 = List.range' 0 10 from by rw [List.range_eq_range'], hrun1, hrun2]

end SolverSpec
