import Seahaven.SolveSound
import Seahaven.RecCheckComplete

/-!
# `solve` is correct

The two-sided version of `SolveSound`: `solve pk10` returns `SUCCESS` on the
positions it stands for that are solvable, and `NOMOVE` on the ones that are not —
never anything else.

Everything is already in place; this file only joins it up.

* `recCheckSolvableSpec` (`RecCheckComplete`) replaces `recCheckSolvableSound`: the
  recursion's answer is an `↔` (`SolvableBits`) rather than a one-way implication.
* `kingStep_transport_complete` (`SubsetTransport`) replaces `Simulates.transport`:
  the same `&&& forcedKings` step, read *up* instead of down.
* `SimulatesNorm.solvable_iff` (`SimulatesNorm`) is what makes the convert call
  itself two-sided — its moves (cleanup's freed-predecessor drops and the
  `SolverMoveAces` drain) are all *normalizing*, hence solvability-preserving in
  both directions.  Soundness needed only that they are legal.

The one hypothesis that changes shape is the memo invariant: the recursion carries
`HashmapCorrect` (a two-sided memo table) where soundness carried `HashmapSound`,
so `WFGlobals` is unbundled into `WellFormedLayout` + `HashmapCorrect`.

The postcondition is stated as the two-way case split `correctness`
(`SolverCorrectness`) asks for rather than as `r = SUCCESS ↔ Solvable s`: the two
are equivalent only because the tail returns nothing but those two codes, and
saying so is part of the claim.  `solveTail_spec_bits` therefore also reports
`r = SUCCESS ∨ r = NOMOVE`, and `answer_of_iff` is the repackaging.
-/

/-! ## The exit configuration piles at least the entry one

The completeness reading of `Simulates.bound`'s `←` half, in the `MaskSub` spelling
`kingStep_transport_complete` wants. -/

theorem Simulates.maskSub {g : Globals} {s s' : State} {p p' : SolverPosType}
    {k k' : Fin 16} {FK : Finset Suit} {fk : UInt16}
    (h : Simulates g s p k s' p' k' FK fk) : MaskSub k' k := by
  rw [MaskSub_iff]
  intro su hsu
  by_contra hk
  exact h.piled_of_piled hk hsu

namespace SolverSpec

open Lean Lean.Order

/-! ## The two-sided memo invariant implies the one-sided one

Needed to reach `recCheckSolvableSound`, whose conclusion carries the *frame* — that
the call touched nothing but the memo table — which `RecCheckSolvableSpec` does not
export. -/

theorem HashmapCorrect.toHashmapSound {g : Globals} (h : HashmapCorrect g) : HashmapSound g :=
  fun p hcan v hv => (h p hcan v hv).imp id (fun hs => ⟨fun s k hk hbit => (hs.1 s k hk).2 hbit,
    hs.2⟩)

theorem wfGlobals_of_correct {g : Globals} (hwf : WellFormedLayout g)
    (h : HashmapCorrect g) : WFGlobals g := ⟨hwf, HashmapCorrect.toHashmapSound h⟩

/-! ## The tail, two-sided -/

set_option maxHeartbeats 1000000 in
/-- **What `solve`'s tail computes.**  The `↔`-flavoured `solveTail_bits`: either
    the position is already solved (`hash = 0`, and the answer is `SUCCESS`), or the
    recursive check returned a mask that decides solvability exactly, and the answer
    is `SUCCESS` precisely when its `forcedKings`-filtered `subsetTable` expansion
    contains the configuration `pk10[10]` names. -/
theorem solveTail_spec_bits {g g' : Globals} {pk10 : Vector UInt8 11}
    {p : SolverPosType} {fk : UInt16} {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hrun : solveTail pk10 fk p g = .ok r g') :
    (r = UInt8.ofNat SUCCESS ∨ r = UInt8.ofNat NOMOVE) ∧
    (HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
    ((p.hash = 0 ∧ r = 0) ∨ ∃ cs : UInt16, LocalMask p cs ∧ SolvableBits g p cs ∧
      (r = 0 ↔ BitSet (subsetAt ((closureInfoOf p).offset.toNat
        + (cs &&& (fk >>> (closureInfoOf p).shiftValue.toUInt16)).toNat))
        (kingCfgOf pk10 hs10))) := by
  rw [solveTail] at hrun
  by_cases hz : (p.hash == 0) = true
  · rw [if_pos hz] at hrun
    replace hrun : (EStateM.Result.ok 0 g : EStateM.Result Error Globals UInt8) = .ok r g' := hrun
    have hr : r = 0 := (EStateM.Result.ok.inj hrun).1.symm
    have hg : g' = g := (EStateM.Result.ok.inj hrun).2.symm
    exact ⟨Or.inl hr, ⟨hg ▸ hcor, g.hashmap, by rw [hg]⟩, Or.inl ⟨by simpa using hz, hr⟩⟩
  · rw [if_neg hz, bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g
      = .ok PUnit.unit g from rfl)] at hrun
    dsimp only at hrun
    -- the `pk10[10]` read
    have h10 : (10 : UInt32).toNat < 11 := by decide
    have h10' : pk10.get ⟨(10 : UInt32).toNat, h10⟩ = pk10.get ⟨10, by omega⟩ := rfl
    rw [bind_ok (vector_getE_apply pk10 10 g h10), h10'] at hrun
    -- the `bits2grlex` read
    have hkb : ((pk10.get ⟨10, by omega⟩ ^^^ 0xf).toUInt32).toNat < 16 := by
      rw [UInt8.toNat_toUInt32]; exact cv_xor_lt16 hs10
    have hkbEq : bits2grlex.get ⟨((pk10.get ⟨10, by omega⟩ ^^^ 0xf).toUInt32).toNat, hkb⟩
        = bits2grlex.get ⟨(pk10.get ⟨10, by omega⟩ ^^^ 0xf).toNat, cv_xor_lt16 hs10⟩ :=
      congrArg bits2grlex.get (Fin.ext (UInt8.toNat_toUInt32 _))
    rw [bind_ok (vector_getE_apply bits2grlex _ g hkb), hkbEq] at hrun
    -- the `closureInfos` read
    have hfple : p.freePiles.toNat ≤ 10 := freePiles_toNat_le hcan.toSolverInvMerged
    have hfp : (p.freePiles.toUInt32).toNat < 11 := by rw [UInt8.toNat_toUInt32]; omega
    have hvaleq : (p.freePiles.toUInt32).toNat = min p.freePiles.toNat 10 := by
      rw [UInt8.toNat_toUInt32]; omega
    have hciEq : closureInfos.get ⟨(p.freePiles.toUInt32).toNat, hfp⟩ = closureInfoOf p := by
      unfold closureInfoOf
      exact congrArg closureInfos.get (Fin.ext hvaleq)
    rw [bind_ok (vector_getE_apply closureInfos _ g hfp), hciEq] at hrun
    -- the recursive check
    cases hrc : solverRecCheckSolvable p g with
    | error e g2 =>
      rw [bind_error hrc] at hrun
      simp at hrun
    | ok cs g2 =>
      obtain ⟨⟨hcsspec, hcsloc⟩, hcor2, -⟩ :=
        RecCheckSolvableSpec.apply recCheckSolvableSpec hwf hcan hcor hrc
      -- the frame: `solverRecCheckSolvable` writes nothing but the memo table
      obtain ⟨-, -, hframe⟩ :=
        recCheckSolvableSound g g2 p cs (wfGlobals_of_correct hwf hcor) hcan hrc
      rw [bind_ok hrc] at hrun
      -- the `subsetTable` read: the answer stays inside its block, and blocks fit below 100
      have hsolvloc : (cs &&& (fk >>> (closureInfoOf p).shiftValue.toUInt16)).toNat
          < 2 ^ (closureInfoOf p).numBits.toNat := LocalMask.and_left _ hcsloc
      have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
        exact hh _
      have hoff : (closureInfoOf p).offset.toNat + 2 ^ (closureInfoOf p).numBits.toNat ≤ 100 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11,
            (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
          decide
        exact hh _
      have hsum : ((closureInfoOf p).offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat
          = (closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
        omega
      have h100 : ((closureInfoOf p).offset.toUInt32
          + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat < 100 := by
        rw [hsum]
        omega
      have hidxeq : ((closureInfoOf p).offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat
          = min ((closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat) 99 := by
        rw [hsum]; omega
      rw [bind_ok (vector_getE_apply subsetTable _ g2 h100),
        show subsetTable.get ⟨((closureInfoOf p).offset.toUInt32
              + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat, h100⟩
            = subsetAt ((closureInfoOf p).offset.toNat
              + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat) from
          congrArg subsetTable.get (Fin.ext hidxeq)] at hrun
      -- the final bit test decides the answer
      by_cases htest : (subsetAt ((closureInfoOf p).offset.toNat
          + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat)
          &&& ((1 : UInt16) <<< (bits2grlex.get
            ⟨(pk10.get ⟨10, by omega⟩ ^^^ 0xf).toNat, cv_xor_lt16 hs10⟩).toUInt16) != 0) = true
      · have hbit : BitSet (subsetAt ((closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat))
            (kingCfgOf pk10 hs10) := by
          unfold BitSet kingCfgOf
          rw [← uint8_toUInt16_eq]
          exact bne_iff_ne.mp htest
        rw [if_pos htest] at hrun
        replace hrun : (EStateM.Result.ok 0 g2 : EStateM.Result Error Globals UInt8)
            = .ok r g' := hrun
        have hr : r = 0 := (EStateM.Result.ok.inj hrun).1.symm
        have hg : g' = g2 := (EStateM.Result.ok.inj hrun).2.symm
        exact ⟨Or.inl hr, ⟨hg ▸ hcor2, hg ▸ hframe⟩,
          Or.inr ⟨cs, hcsloc, hcsspec, fun _ => hbit, fun _ => hr⟩⟩
      · rw [if_neg htest] at hrun
        replace hrun : (EStateM.Result.ok 2 g2 : EStateM.Result Error Globals UInt8)
            = .ok r g' := hrun
        obtain ⟨h2r, -⟩ := EStateM.Result.ok.inj hrun
        have hr : r = 2 := h2r.symm
        have hg : g' = g2 := (EStateM.Result.ok.inj hrun).2.symm
        refine ⟨Or.inr hr, ⟨hg ▸ hcor2, hg ▸ hframe⟩,
          Or.inr ⟨cs, hcsloc, hcsspec, ?_, fun hbit => ?_⟩⟩
        · intro h0
          exact absurd (hr.symm.trans h0) (by decide)
        · refine absurd ?_ htest
          unfold BitSet kingCfgOf at hbit
          rw [← uint8_toUInt16_eq] at hbit
          exact bne_iff_ne.mpr hbit

/-! ## `solve` runs

`recCheckSolvableSpec` now carries totality, so the whole call does: the convert
prologue runs (`convert_canonical`), and the tail's four table reads are all in range —
`pk10[10]` because the vector has eleven entries, `bits2grlex` because `pk10[10] < 16`,
`closureInfos` because `freePiles ≤ 10`, and `subsetTable` because the recursion's
answer is a `LocalMask` and every block ends below `100`. -/

theorem solveTail_runs {g : Globals} {pk10 : Vector UInt8 11} {p : SolverPosType}
    {fk : UInt16}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16) :
    ∃ (r : UInt8) (g' : Globals), solveTail pk10 fk p g = .ok r g' := by
  rw [solveTail]
  by_cases hz : (p.hash == 0) = true
  · rw [if_pos hz]; exact ⟨_, _, rfl⟩
  · rw [if_neg hz, bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g
      = .ok PUnit.unit g from rfl)]
    dsimp only
    -- the `pk10[10]` read
    have h10 : (10 : UInt32).toNat < 11 := by decide
    have h10' : pk10.get ⟨(10 : UInt32).toNat, h10⟩ = pk10.get ⟨10, by omega⟩ := rfl
    rw [bind_ok (vector_getE_apply pk10 10 g h10), h10']
    -- the `bits2grlex` read
    have hkb : ((pk10.get ⟨10, by omega⟩ ^^^ 0xf).toUInt32).toNat < 16 := by
      rw [UInt8.toNat_toUInt32]; exact cv_xor_lt16 hs10
    rw [bind_ok (vector_getE_apply bits2grlex _ g hkb)]
    -- the `closureInfos` read
    have hfple : p.freePiles.toNat ≤ 10 := freePiles_toNat_le hcan.toSolverInvMerged
    have hfp : (p.freePiles.toUInt32).toNat < 11 := by rw [UInt8.toNat_toUInt32]; omega
    have hvaleq : (p.freePiles.toUInt32).toNat = min p.freePiles.toNat 10 := by
      rw [UInt8.toNat_toUInt32]; omega
    have hciEq : closureInfos.get ⟨(p.freePiles.toUInt32).toNat, hfp⟩ = closureInfoOf p := by
      unfold closureInfoOf
      exact congrArg closureInfos.get (Fin.ext hvaleq)
    rw [bind_ok (vector_getE_apply closureInfos _ g hfp), hciEq]
    -- the recursive check: it returns, and its answer fits the block
    obtain ⟨cs, g2, hrc, ⟨-, hcsloc⟩, -⟩ := recCheckSolvableSpec g p hwf hcan hcor
    have hrc' : solverRecCheckSolvable p g = .ok cs g2 := hrc
    rw [bind_ok hrc']
    -- the `subsetTable` read
    have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
      unfold closureInfoOf
      have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
      exact hh _
    have hoff : (closureInfoOf p).offset.toNat + 2 ^ (closureInfoOf p).numBits.toNat ≤ 100 := by
      unfold closureInfoOf
      have hh : ∀ f : Fin 11,
          (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
        decide
      exact hh _
    have hsolvloc : (cs &&& (fk >>> (closureInfoOf p).shiftValue.toUInt16)).toNat
        < 2 ^ (closureInfoOf p).numBits.toNat := LocalMask.and_left _ hcsloc
    have h64 : (2 : Nat) ^ (closureInfoOf p).numBits.toNat ≤ 64 :=
      calc (2 : Nat) ^ (closureInfoOf p).numBits.toNat ≤ 2 ^ 6 :=
            Nat.pow_le_pow_right (by omega) hnb
        _ = 64 := by norm_num
    have h100 : ((closureInfoOf p).offset.toUInt32
        + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat < 100 := by
      rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
      omega
    rw [bind_ok (vector_getE_apply subsetTable _ g2 h100)]
    split <;> exact ⟨_, _, rfl⟩

/-- **`solve` runs.**  The other half of what `Correctness` asks for: not only is the
    answer right, there *is* an answer. -/
theorem solve_runs {g : Globals} {pk10 : Vector UInt8 11}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16) :
    ∃ (r : UInt8) (g' : Globals), EStateM.run (_root_.solve pk10) g = .ok r g' := by
  obtain ⟨fk, p, hrunC, hcan⟩ := convert_canonical g emptySolverPosType pk10 hwf hpk
  obtain ⟨r, g', htail⟩ := solveTail_runs (fk := fk) hwf hcor hcan hs10
  refine ⟨r, g', ?_⟩
  show _root_.solve pk10 g = .ok r g'
  rw [solve_eq_explicit pk10]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hrunC,
    set, EStateM.set]
  exact htail

/-! ## From the decision to the answer

`solve` returns exactly one of two codes, so "answers `SUCCESS` iff solvable" and
"answers `SUCCESS` on solvable positions and `NOMOVE` on unsolvable ones" say the
same thing — but only the second says out loud that the unsolvable answer is
`NOMOVE` rather than `ABORTED` or a stray value.  `answer_of_iff` is the repackaging,
and `Solvable_iff_isSolvable` moves it to `Rules`' `∃`-spelling of solvability. -/

theorem Solvable_iff_isSolvable (s : State) : Solvable s ↔ isSolvable s :=
  ⟨exists_solution_of_solvable, fun ⟨_, h⟩ => solvable_of_isSolution h⟩

theorem answer_of_iff {r : UInt8} {s : State}
    (hr : r = UInt8.ofNat SUCCESS ∨ r = UInt8.ofNat NOMOVE) (hiff : r = 0 ↔ Solvable s) :
    (r = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (r = UInt8.ofNat SUCCESS ∧ isSolvable s) := by
  rw [← Solvable_iff_isSolvable]
  rcases hr with h | h
  · exact Or.inr ⟨h, hiff.1 h⟩
  · refine Or.inl ⟨h, fun hsol => ?_⟩
    exact absurd (h.symm.trans (hiff.2 hsol)) (by decide)

/-! ## The tail is correct -/

/-- **Reading the bit through a simulation, both ways.**  `s` stands for the
    prologue's position; the *normalizing* moves the cleanup and the drain perform
    take it to a state standing for `p`, and those moves preserve solvability in
    both directions (`SimulatesNorm.solvable_iff`).  So the bit the solver tests at
    the parent's configuration decides `Solvable s` outright. -/
theorem solveTail_correct {g g' : Globals} {pk10 : Vector UInt8 11} {s v : State}
    {P p : SolverPosType} {k' : Fin 16} {FK : Finset Suit} {fk : UInt16} {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hsim : SimulatesNorm g s P (kingCfgOf pk10 hs10) v p k' FK fk)
    (hrun : solveTail pk10 fk p g = .ok r g') :
    (HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
    ((r = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (r = UInt8.ofNat SUCCESS ∧ isSolvable s)) := by
  obtain ⟨hcode, hfr, hbits⟩ := solveTail_spec_bits hwf hcor hcan hs10 hrun
  refine ⟨hfr, answer_of_iff hcode ?_⟩
  rcases hbits with ⟨hz, hr0⟩ | ⟨cs, hcsloc, hcsspec, hiff⟩
  · exact ⟨fun _ => Solvable.of_reach hsim.reach.toReach
      (solvable_of_hash_zero hcan hsim.cfg.toMatches hz), fun _ => hr0⟩
  · rw [hiff]
    constructor
    · intro hbit
      exact Solvable.of_reach hsim.reach.toReach
        ((hcsspec v k' hsim.cfg).2 (hsim.toSimulates.transport hcsloc hbit))
    · intro hsol
      exact kingStep_transport_complete p hcsloc hsim.vacates hsim.toSimulates.bitSet_fk
        hsim.toSimulates.maskSub ((hcsspec v k' hsim.cfg).1 (hsim.solvable_iff.1 hsol))

/-- **What a `solve` call does to the globals, and which codes it can return** —
    independently of any state it might be about.  This is what carries a global
    invariant across a query. -/
theorem solve_frame {g g' : Globals} {pk10 : Vector UInt8 11} {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hrun : EStateM.run (_root_.solve pk10) g = .ok r g') :
    (r = UInt8.ofNat SUCCESS ∨ r = UInt8.ofNat NOMOVE) ∧
    HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } := by
  obtain ⟨fk, p, hrunC, hcan⟩ := convert_canonical g emptySolverPosType pk10 hwf hpk
  have hrun' : _root_.solve pk10 g = .ok r g' := hrun
  rw [solve_eq_explicit pk10] at hrun'
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hrunC,
    set, EStateM.set] at hrun'
  obtain ⟨hcode, hfr, -⟩ := solveTail_spec_bits hwf hcor hcan hs10 hrun'
  exact ⟨hcode, hfr⟩

/-! ## `solve` is correct -/

/-- **`solve` is correct.**  If the concrete state `s` is one of the states the
    prologue's position stands for, at the king configuration `pk10[10]` names, then
    `solve pk10` answers `SUCCESS` if `s` is solvable and `NOMOVE` if it is not.

    This is `solve_sound` with the implication turned into an equivalence; the extra
    ingredients are the two-sided recursion (`recCheckSolvableSpec`) and the fact
    that convert's own moves are normalizing (`SimulatesNorm`). -/
theorem solve_correct {g g' : Globals} {pk10 : Vector UInt8 11} {s : State} {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hmatch : StateMatchesKingConfig g s (convertPre g pk10) (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok r g') :
    (HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
    ((r = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (r = UInt8.ofNat SUCCESS ∧ isSolvable s)) := by
  obtain ⟨fk, p, v, k', FK, hrunC, hcan, hsim⟩ :=
    convert_simulates g hwf pk10 hpk emptySolverPosType s (kingCfgOf pk10 hs10) hmatch
  have hrun' : _root_.solve pk10 g = .ok r g' := hrun
  rw [solve_eq_explicit pk10] at hrun'
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hrunC,
    set, EStateM.set] at hrun'
  exact solveTail_correct hwf hcor hcan hs10 hsim hrun'

/-- **Normalizing before asking.**  Unlike the soundness reading, an arbitrary
    `Reach` is *not* enough here — a general legal play can destroy solvability.  A
    `NormReach` cannot (`normReach_solvable_iff`), so a caller may still play cards
    to the foundations and drop freed cards back onto the piles before matching. -/
theorem solve_correct_of_normReach {g g' : Globals} {pk10 : Vector UInt8 11} {s w : State}
    {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hreach : NormReach s w)
    (hmatch : StateMatchesKingConfig g w (convertPre g pk10) (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok r g') :
    (HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
    ((r = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (r = UInt8.ofNat SUCCESS ∧ isSolvable s)) := by
  rw [← Solvable_iff_isSolvable, normReach_solvable_iff (fun c =>
    (hreach.toReach.countState_eq c).trans (hmatch.toMatches.cards_count c)) hreach,
    Solvable_iff_isSolvable]
  exact solve_correct hwf hcor hpk hs10 hmatch hrun

end SolverSpec
