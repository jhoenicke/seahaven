import Seahaven.CriticalIteration

/-!
# `solverRecCheckSolvable` meets its two-sided specification

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

## What is still open

`RecLoopComplete` below, and nothing else.  It is the completeness counterpart of
`recLoop_all` and stands to `critical_loop_bitSet` as a conclusion stands to its main
ingredient: that theorem delivers the bit of the configuration the *critical* state is
in — together with `CompAllOrNothing`, now threaded through the loop — and the
remaining step is the transfer from that configuration to the one the caller asked
about: `subsetAt_spec_pos` within the block (the `MaskSub` witness comes with
`CriticalBit`, so this half is arithmetic), and
`ComponentComplete.cfg_eq_or_component_bits` plus `CompAllOrNothing.transfer` across
the component.  The full assembly is sketched at the end of `CompletenessSkeleton`.
-/

/-! ## The memo write preserves the two-sided memo invariant

Verbatim `hashmapSound_slotWrite` with `SolvableBits` in place of `SoundBits`: the
`slotRead_write` trichotomy is about slots, not about what the bits mean. -/

/-- **`setSlot` preserves `HashmapCorrect`.**  The written key's own slot now holds
the correct mask; every other key either sees an untouched slot or has been evicted
and reads `FREESLOT`. -/
theorem hashmapCorrect_slotWrite {g : Globals} {p : SolverPosType} {v : UInt16}
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

theorem freePiles_eq_ten_of_hash_zero {g : Globals} {p : SolverPosType}
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
  ∀ (H : Globals → Prop) (g gl : Globals) (p : SolverPosType) (ki : KingInfo) (comp : UInt8)
    (v : UInt16),
    p.hash ≠ 0 → LocalMask p v →
    WellFormedLayout g → IsCanonicalPos g p → H g →
    PossibleKingsLocal p ki → KingInfoCorrect p ki → ChildSpecComplete H p →
    EStateM.run (computeComponentKingBits p) g = .ok comp g →
    forIn (List.range 10) (0 : UInt16)
      (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16
        (ki.possibleKings.get 0).toUInt16) g = .ok v gl →
    CompleteBits g p v

/-! ## The recursion, both directions at once -/

/-- **`solverRecCheckSolvable` meets `RecCheckSolvableSpec`**, modulo the three
semantic obligations: `SubsetSound` and `MoveSimulated` (both discharged elsewhere —
`KingMoveSim.subsetSound`, `Phase1Sim.moveSimulated`) and `RecLoopComplete`.

The induction is the one `recCheck_sound` runs, at `HashmapCorrect`: a `Nat` bounding
`DepthSum p` in the *theorem*, `induction` on it, `recCheck_eq` unfolding one level
per step.  The single induction hypothesis serves both directions — projected to
`ChildSpec` for `recLoop_all` and to `ChildSpecComplete` for `RecLoopComplete`. -/
theorem recCheck_spec (hSS : SubsetSound) (hMS : MoveSimulated) (hRLC : RecLoopComplete) :
    RecCheckSolvableSpec := by
  suffices Hind : ∀ n : Nat, ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
      SolverSpec.DepthSum p < n → WellFormedLayout g → IsCanonicalPos g p → HashmapCorrect g →
      EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
      (SolvableBits g p v ∧ LocalMask p v) ∧ HashmapCorrect g' ∧
        ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } by
    intro g g' p v hwf hcan hcor hrun
    obtain ⟨hv, hcor', hm, rfl⟩ :=
      Hind (SolverSpec.DepthSum p + 1) g g' p v (by omega) hwf hcan hcor hrun
    exact ⟨hv, hcor', rfl⟩
  intro n
  induction n with
  | zero => intro g g' p v hmeas; omega
  | succ n ih =>
    intro g g' p v hmeas hwf hcan hcor hrun
    have hfp : p.freePiles.toNat ≤ 10 := by
      have h := freePiles_bound hcan.toSolverInvMerged
      have : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
      omega
    by_cases hz : p.hash = 0
    · -- the leaf: already solved, and the block has one configuration
      rw [recCheck_run_hash_zero g p hz] at hrun
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
      exact ⟨⟨recCheck_spec_of (soundBits_of_hash_zero hcan hz 1)
        (completeBits_one_of_freePiles_ten (freePiles_eq_ten_of_hash_zero hcan hz)),
        localMask_one p⟩, hcor, g.hashmap, rfl⟩
    · by_cases hfree : slotRead g p.hash = UInt8.ofNat FREESLOT
      · -- the pile loop, then the memo write
        obtain ⟨⟨ki, hki, hkiloc, hkic⟩, ⟨comp, hcomp⟩⟩ := prologueRuns g p hwf hcan
        obtain ⟨gl, hloop, rfl⟩ :=
          recCheck_run_loop_inv g g' p ki comp v hfp hz hfree hki hcomp hrun
        -- the induction hypothesis, once, projected to the two directions
        have hchild : ChildSpec HashmapCorrect p := by
          intro child g₁ g₂ w hlt hwf₁ hcan₁ hcor₁ hrun₁
          obtain ⟨⟨hsb, hlm⟩, hrest⟩ := ih g₁ g₂ child w (by omega) hwf₁ hcan₁ hcor₁ hrun₁
          exact ⟨⟨fun s k hk hbit => (hsb s k hk).2 hbit, hlm⟩, hrest⟩
        have hchildc : ChildSpecComplete HashmapCorrect p := by
          intro child g₁ g₂ w hlt hwf₁ hcan₁ hcor₁ hrun₁
          obtain ⟨⟨hsb, hlm⟩, hrest⟩ := ih g₁ g₂ child w (by omega) hwf₁ hcan₁ hcor₁ hrun₁
          exact ⟨⟨fun s k hk hsol => (hsb s k hk).1 hsol, hlm⟩, hrest⟩
        -- the same loop run, read in both directions
        obtain ⟨hsound, hlocal, hcor', hm, rfl⟩ :=
          recLoop_all hSS hMS (recBodyStep HashmapCorrect) hwf hcan hcor hkiloc hkic hchild
            hcomp hloop
        have hcomplete : CompleteBits g p v :=
          hRLC HashmapCorrect g _ p ki comp v hz hlocal hwf hcan hcor hkiloc hkic hchildc hcomp
            hloop
        have hspec : SolvableBits g p v := recCheck_spec_of hsound.of_set_hashmap hcomplete
        refine ⟨⟨hspec, hlocal⟩, ?_, ?_⟩
        · exact hashmapCorrect_slotWrite (hwf.set_hashmap hm) (hcan.set_hashmap hm) hcor'
            (hspec.set_hashmap hm) hlocal
        · exact ⟨_, rfl⟩
      · -- a memo hit: the two-sided invariant answers in one read
        rw [recCheck_run_cached g p hfp hz hfree] at hrun
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
        rcases hcor p hcan (slotRead g p.hash) (getSlot_run g p.hash) with hfs | ⟨hs, hl⟩
        · exact absurd hfs hfree
        · exact ⟨⟨hs, hl⟩, hcor, g.hashmap, rfl⟩
