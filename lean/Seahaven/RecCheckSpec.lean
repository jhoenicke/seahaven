import Seahaven.CriticalIteration
import Seahaven.RecCheckRuns
import Seahaven.ComponentComplete

open Rules
open Solver

/-!
# `recCheckSolvable` meets its two-sided specification

`RecCheckSound` proves the soundness half by an induction over `DepthSum`, and a
completeness half proved the same way would repeat that induction verbatim.  This
file does it **once**, at the two-sided memo invariant `HashmapCorrect`, and calls
the two loop developments — one per direction — inside the single induction.

## Why one induction suffices

The recursion's plumbing never inspects a memo slot: the loop body hands the memo
invariant to the recursive call and hands back whatever the call returns.  So both
loop developments are parameterized over the invariant they carry
(`RecCheckSound.ChildSpec`/`RecBodyStep`/`recLoop_all`,
`CompletenessSkeleton.ChildSpecComplete`, `CriticalIteration.critical_loop_bitSet`),
and instantiating both at `H := HashmapCorrect` lets a *single* `ChildSpec` — the
induction hypothesis of this file — feed both.  Instantiated instead at
`HashmapSound` / `HashmapComplete` the very same lemmas give the two standalone
recursions, so nothing is lost by proving the two-sided one here.

Only the *bit* content is direction-specific, and only in two of the three branches:

* **the `hash = 0` leaf** — `soundBits_of_hash_zero` (the position is already solved)
  and `completeBits_one_of_freePiles_ten` (with every pile empty the block has one
  configuration and the answer `1` covers it);
* **the memo hit** — one read, and this is where merging pays: `HashmapCorrect`
  hands over `SolvableBits` outright, where the split development reads the slot
  twice;
* **the pile loop** — `recLoop_all` for `SoundBits`, `RecLoopComplete` for
  `CompleteBits`, both applied to the same run, then `recCheck_spec_of`.

## `RecLoopComplete`

Discharged below, as `recLoopComplete`.  It is the completeness counterpart of
`recLoop_all` and stands to `critical_loop_bitSet` as a conclusion stands to its main
ingredient: that theorem delivers the bit of the configuration the *critical* state is
in — together with `CompAllOrNothing`, now threaded through the loop — and the
remaining step is the transfer from that configuration to the one the caller asked
about: `subsetAt_spec_pos` within the block (the `MaskSub` witness comes with
`CriticalBit`, so this half is arithmetic), and
`ComponentComplete.cfg_eq_or_component_bits` plus `CompAllOrNothing.transfer` across
the component. `recCheckSolvableSpec` at the end of this file uses it directly rather
than taking it as a hypothesis, since this is its only proof.
-/

/-! ## The memo write preserves the two-sided memo invariant

Verbatim `hashmapSound_slotWrite` with `SolvableBits` in place of `SoundBits`: the
`slotRead_write` trichotomy is about slots, not about what the bits mean. -/

/-- **`setSlot` preserves `HashmapCorrect`.**  The written key's own slot now holds
the correct mask; every other key either sees an untouched slot or has been evicted
and reads `FREESLOT`. -/
theorem hashmapCorrect_slotWrite {g : Globals} {p : PosType} {v : UInt16}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hmc : HashmapCorrect g)
    (hspec : SolvableBits g p v) (hloc : LocalMask p v) :
    HashmapCorrect (slotWrite g p.hash v) := by
  have hv : v.toNat < 128 := localMask_lt_128 hloc
  intro q hqcan' w hw
  have hqcan : IsCanonicalPos g q := hqcan'.of_set_hashmap
  rw [getSlot_run] at hw
  have hwval : w = slotRead (slotWrite g p.hash v) q.hash := (EStateM.Result.ok.inj hw).1.symm
  rcases slotRead_write g p.hash q.hash v (hash_lt hcan.toSolverInvBase)
      (hash_lt hqcan.toSolverInvBase) hv with hkeep | ⟨hkey, hval⟩ | hfree
  · -- untouched slot: the old memo invariant answers
    rcases hmc q hqcan w (by rw [getSlot_run, hwval, hkeep]) with hfs | ⟨hs, hl⟩
    · exact Or.inl hfs
    · exact Or.inr ⟨hs.set_hashmap _, hl⟩
  · -- the written key: `q` is `p`, and the payload came back intact
    have hpq : q = p := IsCanonicalPos_of_hash_eq g q p hwf hqcan hcan hkey
    subst hpq
    rw [hwval, hval, toUInt8_toUInt16 (by omega)]
    exact Or.inr ⟨hspec.set_hashmap _, hloc⟩
  · exact Or.inl (hwval.trans hfree)

/-! ## `hash = 0` forces ten free piles

The leaf's completeness reads the answer `1` as the maximal configuration of the
`freePiles = 10` block (`completeBits_one_of_freePiles_ten`), so it needs the free-pile
count, where soundness needed the depths themselves. -/

theorem freePiles_eq_ten_of_hash_zero {g : Globals} {p : PosType}
    (hcan : IsCanonicalPos g p) (hz : p.hash = 0) : p.freePiles.toNat = 10 := by
  have hd : ∀ i : Fin 10, p.pileDepth.get i = 0 :=
    pileDepth_eq_zero_of_hash_zero hcan.toSolverInvBase hz
  have hcard := card_empty_piles_eq_freePiles hcan.toSolverInvMerged
  rw [Finset.filter_true_of_mem (fun i _ => hd i)] at hcard
  simpa using hcard.symm

/-! ## The one open obligation

Stated as a named `Prop`, the way the soundness development stated `SubsetSound` and
`MoveSimulated` before discharging them, so that nothing here is `sorry`d.

It is `critical_loop_bitSet` plus the configuration transfer.  Note it is
parameterized over the memo invariant `H` exactly as its ingredient is — the transfer
argument is about bits and states, so it does not care which invariant the loop
carries. -/

/-- **The pile loop misses no solvable configuration.**  If the loop returns `v`, then
every state the position stands for that really is solvable has its configuration's
bit set in `v`'s expansion.

To be proved from `critical_loop_bitSet` — which supplies the bit for the
*critical* state's configuration, after `exists_critical_state` produces that state
from the caller's own, and the `CompAllOrNothing` invariant alongside it — followed by
the transfer to the caller's configuration (`exists_block_cfg_maskSub` and
`subsetAt_spec_pos` for the block, `cfg_eq_or_component_bits` with
`CompAllOrNothing.transfer` for the component). -/
def RecLoopComplete : Prop :=
  ∀ (H : Globals → Prop) (g gl : Globals) (p : PosType) (ki : KingInfo) (comp : UInt8)
    (v : UInt16),
    p.hash ≠ 0 → LocalMask p v →
    WellFormedLayout g → IsCanonicalPos g p → H g →
    PossibleKingsLocal p ki → KingInfoCorrect p ki → ChildSpecComplete H p →
    EStateM.run (computeComponentKingBits p) g = .ok comp g →
    forIn (List.range 10) (0 : UInt16)
      (recBody recCheckSolvable p (closureInfoOf p) ki comp.toUInt16
        (ki.possibleKings.get 0).toUInt16) g = .ok v gl →
    CompleteBits g p v

/-! ## `RecLoopComplete`, discharged

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
solved, *is* solvable.  That case is the caller's `hash = 0` leaf, which answers `1`. -/

/-- A non-empty pile, from a non-zero hash.  (The converse of
`pileDepth_eq_zero_of_hash_zero`, which is all the leaf needed.) -/
theorem exists_pos_pileDepth_of_hash_ne_zero {g : Globals} {p : PosType}
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

/-- **The pile loop is complete.**  See the module docstring for the shape.  Discharges
`RecLoopComplete`; used directly by `recCheckSolvableSpec` below rather than taken as a
hypothesis, since this is its only proof. -/
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

/-! ## The recursion, both directions at once -/

/-- **`recCheckSolvable` meets its specification, unconditionally.**  All three semantic
obligations — `SubsetSound`, `MoveSimulated` (already theorems by the time this runs:
`KingMoveSim.subsetSound`, `Phase1Sim.moveSimulated`) and `RecLoopComplete` (proved just
above as `recLoopComplete`) — are theorems, so nothing is assumed about any of them: the
recursion is closed in *both* directions, the same two semantic obligations that make
`RecCheckSound.recCheckSolvableSound` hypothesis-free, and what stands between this and
end-to-end correctness is the `solve` wrapper.

The induction is the one `recCheck_sound` runs, at `HashmapCorrect`: a `Nat` bounding
`DepthSum p` in the *theorem*, `induction` on it, `recCheck_eq` unfolding one level
per step.  The single induction hypothesis serves both directions — projected to
`ChildSpec` for `recLoop_all` and to `ChildSpecComplete` for `RecLoopComplete`. -/
theorem recCheckSolvableSpec :
    RecCheckSolvableSpec := by
  suffices Hind : ∀ n : Nat, ∀ (g : Globals) (p : PosType),
      SolverSpec.DepthSum p < n → WellFormedLayout g → IsCanonicalPos g p → HashmapCorrect g →
      ∃ (v : UInt16) (g' : Globals),
        EStateM.run (recCheckSolvable p) g = .ok v g' ∧
        (SolvableBits g p v ∧ LocalMask p v) ∧ HashmapCorrect g' ∧
          ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } by
    intro g p hwf hcan hcor
    obtain ⟨v, g', hrun, hv, hcor', hm, rfl⟩ :=
      Hind (SolverSpec.DepthSum p + 1) g p (by omega) hwf hcan hcor
    exact ⟨v, _, hrun, hv, hcor', rfl⟩
  intro n
  induction n with
  | zero => intro g p hmeas; omega
  | succ n ih =>
    intro g p hmeas hwf hcan hcor
    have hfp : p.freePiles.toNat ≤ 10 := by
      have h := freePiles_bound hcan.toSolverInvMerged
      have : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
      omega
    by_cases hz : p.hash = 0
    · -- the leaf: already solved, and the block has one configuration
      exact ⟨1, g, recCheck_run_hash_zero g p hz,
        ⟨recCheck_spec_of (soundBits_of_hash_zero hcan hz 1)
          (completeBits_one_of_freePiles_ten (freePiles_eq_ten_of_hash_zero hcan hz)),
          localMask_one p⟩, hcor, g.hashmap, rfl⟩
    · by_cases hfree : slotRead g p.hash = UInt8.ofNat FREESLOT
      · -- the pile loop, then the memo write
        obtain ⟨⟨ki, hki, hkiloc, hkic⟩, ⟨comp, hcomp⟩⟩ := prologueRuns g p hwf hcan
        -- the induction hypothesis, once, projected to the three readings
        have hchild : ChildSpec HashmapCorrect p := by
          intro child g₁ g₂ w hlt hwf₁ hcan₁ hcor₁ hrun₁
          obtain ⟨w', g₃, hrun', ⟨hsb, hlm⟩, hrest⟩ := ih g₁ child (by omega) hwf₁ hcan₁ hcor₁
          obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (hrun'.symm.trans hrun₁)
          exact ⟨⟨fun s k hk hbit => (hsb s k hk).2 hbit, hlm⟩, hrest⟩
        have hchildc : ChildSpecComplete HashmapCorrect p := by
          intro child g₁ g₂ w hlt hwf₁ hcan₁ hcor₁ hrun₁
          obtain ⟨w', g₃, hrun', ⟨hsb, hlm⟩, hrest⟩ := ih g₁ child (by omega) hwf₁ hcan₁ hcor₁
          obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (hrun'.symm.trans hrun₁)
          exact ⟨⟨fun s k hk hsol => (hsb s k hk).1 hsol, hlm⟩, hrest⟩
        have hchildr : ChildRuns HashmapCorrect p := by
          intro child g₁ hlt hwf₁ hcan₁ hcor₁
          obtain ⟨w, g₂, hrun₁, ⟨-, hlm⟩, -⟩ := ih g₁ child (by omega) hwf₁ hcan₁ hcor₁
          exact ⟨w, g₂, hrun₁, hlm⟩
        -- **the loop runs**: every iteration runs (`recBodyRuns`) and re-establishes the
        -- entry conditions of the next (`recBodyStep`'s frame)
        obtain ⟨v, gl, hloop, -⟩ := forIn_exists
          (fun (_ : UInt16) (g₁ : Globals) => WellFormedLayout g₁ ∧ IsCanonicalPos g₁ p ∧
            HashmapCorrect g₁ ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g₁ = { g with hashmap := hm })
          (recBody recCheckSolvable p (closureInfoOf p) ki comp.toUInt16
            (ki.possibleKings.get 0).toUInt16) (List.range 10)
          (fun a ha b g₁ hP => by
            obtain ⟨hwf₁, hcan₁, hcor₁, hm₁, rfl⟩ := hP
            obtain ⟨r, g₂, hb⟩ := recBodyRuns HashmapCorrect p ki comp _ _ a b
              (by simpa using ha) hwf₁ hcan₁ hcor₁ hkiloc hchildr
            obtain ⟨-, hcor₂, hm₂, rfl⟩ := recBodyStep HashmapCorrect p ki comp _ _ g₂ a b r
              (by simpa using ha) hwf₁ hcan₁ hcor₁ hkiloc hchild hb
            exact ⟨r, _, hb, hwf₁.set_hashmap hm₂, hcan₁.set_hashmap hm₂, hcor₂, hm₂, rfl⟩)
          0 g ⟨hwf, hcan, hcor, g.hashmap, rfl⟩
        refine ⟨v, _, recCheck_run_loop g gl p ki comp v hfp hz hfree hki hcomp hloop, ?_⟩
        -- the same loop run, read in both directions
        obtain ⟨hsound, hlocal, hcor', hm, rfl⟩ :=
          recLoop_all (recBodyStep HashmapCorrect) hwf hcan hcor hkiloc hkic hchild
            hcomp hloop
        have hcomplete : CompleteBits g p v :=
          recLoopComplete HashmapCorrect g _ p ki comp v hz hlocal hwf hcan hcor hkiloc hkic hchildc hcomp
            hloop
        have hspec : SolvableBits g p v := recCheck_spec_of hsound.of_set_hashmap hcomplete
        refine ⟨⟨hspec, hlocal⟩, ?_, ?_⟩
        · exact hashmapCorrect_slotWrite (hwf.set_hashmap hm) (hcan.set_hashmap hm) hcor'
            (hspec.set_hashmap hm) hlocal
        · exact ⟨_, rfl⟩
      · -- a memo hit: the two-sided invariant answers in one read
        refine ⟨(slotRead g p.hash).toUInt16, g, recCheck_run_cached g p hfp hz hfree, ?_⟩
        rcases hcor p hcan (slotRead g p.hash) (getSlot_run g p.hash) with hfs | ⟨hs, hl⟩
        · exact absurd hfs hfree
        · exact ⟨⟨hs, hl⟩, hcor, g.hashmap, rfl⟩
