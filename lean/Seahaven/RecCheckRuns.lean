import Seahaven.RecCheckSound

/-!
# `solverRecCheckSolvable` runs

`solverRecCheckSolvable` is defined by `partial_fixpoint`, so *every* statement about
it so far has been conditional on a successful run — `recCheck_run_loop_inv`,
`recLoop_all`, `recBodyStep` all take `… = .ok v g'` as a hypothesis.  For the
end-to-end statement that is not enough: `Correctness` asserts that the call
*returns*, so termination and the absence of `ArrayOutOfBounds` have to be proved.

The measure is the same one soundness uses (`DepthSum`, which `move_merged` drops at
every child), so the shape is the same induction — run in the *constructing*
direction.  What this file adds is the two pieces that direction needs and the
inverting direction does not:

* `forIn_exists` — the existence twin of `forIn_inv`: if every iteration runs and
  preserves an invariant, the loop runs;
* `recBodyRuns` — one iteration of the pile loop runs.  This is `recBodyStep`'s proof
  with the inversion deleted: the same run lemmas in the same order, but building the
  run rather than taking it apart.  The recursive call is the only step that can fail,
  and it is supplied by `ChildRuns` (the induction hypothesis).

`LocalMask` has to ride along in `ChildRuns` because the iteration reads
`subsetTable` at `childCI.offset + childSolvable'`, and that index is only in range
because the child's answer fits its block.
-/

open Lean Lean.Order

/-! ## The loop runs if its body does -/

/-- **The existence twin of `forIn_inv`.**  Note the invariant is still needed: the
body only runs at states the previous iterations can actually produce. -/
theorem forIn_exists {β : Type} (P : β → Globals → Prop)
    (body : Nat → β → EStateM Error Globals (ForInStep β)) :
    ∀ (l : List Nat),
      (∀ a ∈ l, ∀ (b : β) (g : Globals), P b g →
        ∃ (r : ForInStep β) (g' : Globals), body a b g = .ok r g' ∧ P r.value g') →
      ∀ (b : β) (g : Globals), P b g →
        ∃ (b' : β) (g' : Globals), forIn l b body g = .ok b' g' ∧ P b' g' := by
  intro l
  induction l with
  | nil =>
    intro _ b g hP
    exact ⟨b, g, rfl, hP⟩
  | cons a l ih =>
    intro hstep b g hP
    obtain ⟨r, g'', hba, hPr⟩ := hstep a (by simp) b g hP
    rw [List.forIn_cons]
    simp only [bind, EStateM.bind, hba]
    cases r with
    | done c => exact ⟨c, g'', rfl, hPr⟩
    | yield c => exact ih (fun x hx => hstep x (by simp [hx])) c g'' hPr

/-! ## One iteration runs -/

/-- The induction hypothesis, existence half: the recursive call on a smaller child
returns, and its answer fits the child's block (which is what puts the `subsetTable`
index the caller then reads in range). -/
def ChildRuns (H : Globals → Prop) (p : SolverPosType) : Prop :=
  ∀ (child : SolverPosType) (g₁ : Globals),
    SolverSpec.DepthSum child < SolverSpec.DepthSum p → WellFormedLayout g₁ →
    IsCanonicalPos g₁ child → H g₁ →
    ∃ (w : UInt16) (g₂ : Globals),
      EStateM.run (solverRecCheckSolvable child) g₁ = .ok w g₂ ∧ LocalMask child w

/-- **One iteration of the pile loop runs.** -/
def RecBodyRuns (H : Globals → Prop) : Prop :=
  ∀ (p : SolverPosType) (ki : KingInfo) (comp : UInt8) (allkings : UInt16)
    (g₁ : Globals) (pile : Nat) (w : UInt16),
    pile < 10 → WellFormedLayout g₁ → IsCanonicalPos g₁ p → H g₁ →
    PossibleKingsLocal p ki → ChildRuns H p →
    ∃ (r : ForInStep UInt16) (g₂ : Globals),
      recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16 allkings pile w g₁
        = .ok r g₂

set_option maxHeartbeats 1000000 in
theorem recBodyRuns (H : Globals → Prop) : RecBodyRuns H := by
  intro p ki comp allkings g₁ pile w hpile hwf hcan hms hkiloc hchild
  have hidx : (UInt32.ofNat pile).toNat < 10 := by
    rw [ofNat_pile_toNat hpile]; exact hpile
  rw [recBody]
  rw [bind_ok (vector_getE_apply p.pileDepth (UInt32.ofNat pile) g₁ hidx)]
  by_cases hdz : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩ == 0) = true
  · -- the pile is empty: nothing happens
    rw [if_pos hdz]
    exact ⟨_, _, rfl⟩
  · rw [if_neg hdz,
      bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g₁ = .ok PUnit.unit g₁ from rfl)]
    dsimp only
    rw [bind_ok (vector_getE_apply p.pileFlute (UInt32.ofNat pile) g₁ hidx)]
    -- the pile is non-empty, so the destination walk and the move both make sense
    have hd : 0 < (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat := by
      rcases Nat.eq_zero_or_pos (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat with h | h
      · exact absurd (by simpa using UInt8.toNat_inj.1 (h.trans rfl.symm)) hdz
      · exact h
    have hb5 : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat - 1 < 5 := by
      have := hcan.toSolverInvBase.pileDepth_bound ⟨(UInt32.ofNat pile).toNat, hidx⟩
      omega
    obtain ⟨toPile, hgd⟩ : ∃ tp : UInt8,
        solverGetDestination p (UInt32.ofNat pile) g₁ = .ok tp g₁ := by
      rcases getDest_spec' hwf hcan hidx hd hb5 with ⟨-, h⟩ | ⟨n, -, -, -, -, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [bind_ok hgd]
    obtain ⟨mv, hmvrun, hmvloc⟩ := getMovable_run (g := g₁) ki
      (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile
      (hcan.toSolverInvBase.flute_pos ⟨(UInt32.ofNat pile).toNat, hidx⟩) hkiloc
    have hmvapp : solverGetMovable ki (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile g₁ = .ok mv g₁ := hmvrun
    rw [bind_ok hmvapp]
    by_cases hnew : (mv &&& ~~~w != 0) = true
    · rw [if_pos hnew, bind_ok (show (get : EStateM Error Globals Globals) g₁ = .ok g₁ g₁ from rfl)]
      obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hidx hd hb5 hgd
      obtain ⟨fk, p', hmove, hcan', hmeas⟩ :=
        SolverSpec.move_merged g₁ p (UInt32.ofNat pile) toPile hwf hcan hvalid hidx hb5 _ rfl hdv
      rw [hmove]
      dsimp only
      rw [bind_ok (show (set g₁ : EStateM Error Globals PUnit) g₁ = .ok PUnit.unit g₁ from rfl)]
      have hfp' : p'.freePiles.toNat ≤ 10 := by
        have h := freePiles_bound hcan'.toSolverInvMerged
        have : p'.freePiles.toInt = (p'.freePiles.toNat : Int) := rfl
        omega
      rw [bind_ok (closureInfos_getE_apply g₁ p' hfp')]
      -- the recursive call: the only step that can fail, supplied by the IH
      obtain ⟨cs, g₃, hcs, hcsloc⟩ := hchild p' g₁ hmeas hwf hcan' hms
      have hcs' : solverRecCheckSolvable p' g₁ = .ok cs g₃ := hcs
      rw [bind_ok hcs']
      -- the `subsetTable` lookup: the child's answer stays inside the child's block,
      -- and every block fits below `100`
      have hcsm : (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat
          < 2 ^ (closureInfoOf p').numBits.toNat := LocalMask.and_left _ hcsloc
      have hnb' : (closureInfoOf p').numBits.toNat ≤ 6 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
        exact hh _
      have hoff' : (closureInfoOf p').offset.toNat + 2 ^ (closureInfoOf p').numBits.toNat ≤ 100 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11,
            (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
          decide
        exact hh _
      have h64 : (2 : Nat) ^ (closureInfoOf p').numBits.toNat ≤ 64 :=
        calc (2 : Nat) ^ (closureInfoOf p').numBits.toNat ≤ 2 ^ 6 :=
              Nat.pow_le_pow_right (by omega) hnb'
          _ = 64 := by norm_num
      have hsum : ((closureInfoOf p').offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat
          = (closureInfoOf p').offset.toNat
            + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
        omega
      have h100 : ((closureInfoOf p').offset.toUInt32
          + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat < 100 := by
        rw [hsum]; omega
      rw [bind_ok (vector_getE_apply subsetTable _ g₃ h100)]
      -- the tail: whichever way the `break` test goes, it returns
      split <;> split <;> exact ⟨_, _, rfl⟩
    · rw [if_neg hnew]
      exact ⟨_, _, rfl⟩
