import Seahaven.RecCheckSpec
import Seahaven.ComponentComplete
import Seahaven.Phase1Sim

/-!
# The pile loop misses no solvable configuration

`RecLoopComplete` discharged, and with it `RecCheckSolvableSpec` modulo the two semantic
hypotheses the soundness development already discharges.

Every ingredient is proved elsewhere; what happens here is the plumbing between them,
and it is worth naming the three configurations involved, since the whole argument is
about telling them apart:

* `k` — the configuration the **caller's** state `s` is in.  This is what the goal asks
  about, and the loop never sees it.
* `k_t` — the configuration of the **critical** state `t₀`, the state the winning play
  reaches just before the depth vector breaks.  This is the one the loop's iteration
  actually establishes a bit for.
* the **block** configurations `globalCfg ci n`, the only ones a bit can name at all.
  A block stores the *maximal* assignments (every free column carrying a king), so
  neither `k` nor `k_t` is generally one of them; both enter through `MaskSub`, and
  `subsetAt` closes the stored set downwards.

The proof is one `intro s k` — the critical pile depends on `s`, so the loop lemma has
to be applied under that binder — and then:

1. `exists_critical_state` turns "`s` is solvable and some pile is non-empty" into `t₀`,
   the critical move, and `PrefixReach g p s t₀`;
2. `critical_loop_bitSet` gives a block index `i_l` above `k_t` whose bit is in `v`,
   together with `CompAllOrNothing v comp`;
3. `exists_block_cfg_maskSub` gives a block index `j_c` above `k`;
4. `cfg_eq_or_component_bits` says either `k = k_t`, and then `i_l` covers `k` outright,
   or both indices are component bits and `CompAllOrNothing.transfer` moves the bit from
   `i_l` to `j_c`.  Outside the component's guard the two extreme cases replace it:
   `cfg_eq_of_freePiles_zero` (nothing can be reshuffled) and
   `block_index_eq_of_freePiles_four` (the block holds one configuration, so
   `j_c = i_l`);
5. `subsetAt_spec_pos` turns the surviving index into the bit the goal asks for.

`hash ≠ 0` is a real hypothesis, not bookkeeping: with every pile empty the loop skips
all ten iterations and returns `0`, whose expansion is empty — while the position, being
solved, *is* solvable.  That case is the caller's `hash = 0` leaf, which answers `1`.
-/

/-- A non-empty pile, from a non-zero hash.  (The converse of
`pileDepth_eq_zero_of_hash_zero`, which is all the leaf needed.) -/
theorem exists_pos_pileDepth_of_hash_ne_zero {g : Globals} {p : SolverPosType}
    (hb : SolverInvBase g p) (hz : p.hash ≠ 0) : ∃ i : Fin 10, 0 < (p.pileDepth.get i).toNat := by
  by_contra hcon
  push Not at hcon
  refine hz ?_
  have hall : ∀ i : Fin 10, (p.pileDepth.get i).toNat.toUInt32 = 0 := by
    intro i
    rw [Nat.le_zero.1 (hcon i)]
    rfl
  rw [hb.hash_def]
  simp [hall]

/-- **The pile loop is complete.**  See the module docstring for the shape. -/
theorem recLoopComplete : RecLoopComplete := by
  intro H g gl p ki comp v hz hlocv hwf hcan hH hkiloc hkic hcsp hcomprun hloop s k hk hsol
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hm : SolverInvMerged g p := hcan.toSolverInvMerged
  -- the block is at most six bits wide, so `min n 15` is `n` for every index in it
  have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
    unfold closureInfoOf
    have h : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
    exact h _
  -- step 5, factored out: a block index above `k` whose bit is in `v` closes the goal
  have key : ∀ n : Nat, n < (closureInfoOf p).numBits.toNat →
      BitSet v ⟨min n 15, by omega⟩ → MaskSub (globalCfg (closureInfoOf p) n) k →
      BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) k := by
    intro n hn hbit hsub
    refine (subsetAt_spec_pos p hlocv k).2 ⟨n, hn, ?_, hsub⟩
    have hb' := (BitSet_toNat v ⟨min n 15, by omega⟩).1 hbit
    rwa [show ((⟨min n 15, by omega⟩ : Fin 16) : Nat) = n from by simp; omega] at hb'
  -- step 1: the critical state and its move
  obtain ⟨i₀, hi₀⟩ := exists_pos_pileDepth_of_hash_ne_zero hb hz
  obtain ⟨t₀, t₁, mv, a, cc, rest, hpre, hdpk0, -, hap, hsolv1, -, hlen, hda, hsrc, hbk⟩ :=
    exists_critical_state hwf hcan hk.toMatches hsol hi₀
  have hdst : mv.dest ≠ Position.pile a :=
    dest_ne_source hk.toMatches.depth_lt6 hdpk0.depth_match hbk hsrc hap
  -- step 2: the loop sets a bit for a block configuration above the critical one
  obtain ⟨⟨il, kt, hil, hktcfg, hsubl, hbitl⟩, hallon, -, -⟩ :=
    critical_loop_bitSet hwf hcan hkiloc hkic hH hcsp rfl a.isLt hdpk0 hlen hda hsrc hdst hap
      hsolv1 hloop
  -- step 3: a block configuration above the caller's own
  obtain ⟨jc, hjc, hsubc⟩ := exists_block_cfg_maskSub hm hk.realizes
  -- step 4: which of the two indices carries the bit
  rcases Nat.lt_or_ge p.freePiles.toNat 4 with hfp4 | hfp4
  · rcases Nat.eq_zero_or_pos p.freePiles.toNat with hfp0 | hfp1
    · -- no free column: nothing can be reshuffled, so the configurations agree
      have heq : k = kt := cfg_eq_of_freePiles_zero hm hfp0 hk.toDepthPlusKingsCfg hktcfg hpre
      exact key il hil hbitl (by rw [heq]; exact hsubl)
    · -- the component's guard: equal configurations, or a component transfer
      rcases cfg_eq_or_component_bits hm hfp1 (by omega) hcomprun hk.toDepthPlusKingsCfg hktcfg
          hpre hjc hil hsubc hsubl with heq | ⟨hcjc, hcil⟩
      · exact key il hil hbitl (by rw [heq]; exact hsubl)
      · exact key jc hjc (hallon.transfer hbitl hcil hcjc) hsubc
  · -- four free columns or more: the block holds a single configuration
    have hij : jc = il := block_index_eq_of_freePiles_four hfp4 hjc hil
    exact key jc hjc (by rw [hij]; exact hbitl) hsubc

/-- **`solverRecCheckSolvable` meets its specification**, on the same two semantic
hypotheses the soundness half runs on. -/
theorem recCheck_spec_of_loops (hSS : SubsetSound) (hMS : MoveSimulated) :
    RecCheckSolvableSpec :=
  recCheck_spec hSS hMS recLoopComplete

/-- **`solverRecCheckSolvable` meets its specification, unconditionally.**  Both
semantic hypotheses are theorems (`KingMoveSim.subsetSound`, `Phase1Sim.moveSimulated`),
the same two that make `Phase1Sim.recCheckSolvableSound` hypothesis-free — so the
recursion is now closed in *both* directions, and what stands between this and
end-to-end correctness is the `solve` wrapper. -/
theorem recCheckSolvableSpec : RecCheckSolvableSpec :=
  recCheck_spec_of_loops subsetSound moveSimulated
