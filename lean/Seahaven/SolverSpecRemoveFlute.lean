import Seahaven.SolverSpecCleanupPile

/-!
# Spec for `removeFlute`

`removeFlute` is `cleanupPile`'s composed-flute-removal counterpart; this file
reduces its `PileBase`/`PileMerged` preservation facts to the `cleanupPile`
ones via the exact reduction `removeFlute_eq` (from `SolverRealSpec`).
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-! ## The progress measure: depths only ever go down

The solver's move set is designed so that every move makes progress, and the measure is
the total pile depth: a move takes the *whole* flute off its source pile, so
`removeFlutePre` decrements that pile, and **no phase ever increases any pile's depth**.
Carrying that pointwise (`DepthLe`) rather than as a sum is what makes it composable —
each phase touches one pile — and it is the same monotonicity `isFreeCard_mono` already
consumes.  The single strict decrement is assembled at the top, in `move_merged`. -/

/-- Every pile's depth in `q` is at most its depth in `p`. -/
def DepthLe (p q : SolverPosType) : Prop :=
  ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat

theorem DepthLe.rfl' (p : SolverPosType) : DepthLe p p := fun _ => Nat.le_refl _

theorem DepthLe.trans' {p q r : SolverPosType} (h : DepthLe p q) (h' : DepthLe q r) :
    DepthLe p r := fun i => le_trans (h' i) (h i)

/-- The progress measure itself: the total number of cards still on the tableau, in the
same `List.foldl` spelling `usedSpace_def` and `destFrame_depth_sum` already use. -/
def DepthSum (p : SolverPosType) : Nat :=
  p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0

/-- Pointwise `≤` on a length-matched pair of lists lifts to the running `foldl` sum.
    Stated with both accumulators free so the induction goes through. -/
private theorem foldl_toNat_mono : ∀ (L1 L2 : List UInt8), L1.length = L2.length →
    (∀ i (h1 : i < L1.length) (h2 : i < L2.length), (L2[i]).toNat ≤ (L1[i]).toNat) →
    ∀ a b : Nat, b ≤ a →
      L2.foldl (fun acc d => acc + d.toNat) b ≤ L1.foldl (fun acc d => acc + d.toNat) a := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 hlen _ a b hab
    match L2, hlen with
    | [], _ => exact hab
  | cons x xs ih =>
    intro L2 hlen h a b hab
    match L2, hlen with
    | y :: ys, hlen =>
      have hhead : y.toNat ≤ x.toNat := by
        have := h 0 (by simp) (by simp)
        simpa using this
      exact ih ys (by simpa using hlen)
        (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2)) _ _
        (by show b + y.toNat ≤ a + x.toNat; omega)

/-- **Pointwise to sum.**  The composable form is `DepthLe`; the measure the induction
    actually decreases is `DepthSum`. -/
theorem DepthLe.sum_le {p q : SolverPosType} (h : DepthLe p q) : DepthSum q ≤ DepthSum p := by
  refine foldl_toNat_mono p.pileDepth.toList q.pileDepth.toList (by simp) ?_ 0 0 (Nat.le_refl _)
  intro i h1 _h2
  have hi : i < 10 := by simpa using h1
  simpa [Vector.get, Vector.getElem_toList] using h ⟨i, hi⟩

/-- **Pointwise `≤` plus one strict index gives a strict drop in the sum.**  This is the
    shape every phase hands up: nothing grows, and the source pile lost its flute. -/
theorem DepthLe.sum_lt {p q : SolverPosType} (h : DepthLe p q) (i : Fin 10)
    (hi : (q.pileDepth.get i).toNat < (p.pileDepth.get i).toNat) : DepthSum q < DepthSum p := by
  -- Route both sums through the position that agrees with `p` off `i` and with `q` at `i`:
  -- `depth_sum_foldl_set` isolates exactly that one term.
  set r : SolverPosType :=
    { p with pileDepth := p.pileDepth.set i.val (q.pileDepth.get i) i.isLt } with hrdef
  have hrle : DepthLe p r := by
    intro j
    by_cases hj : j.val = i.val
    · have hji : j = i := Fin.ext hj
      subst hji
      show ((p.pileDepth.set j.val (q.pileDepth.get j) j.isLt)[j.val]'j.isLt).toNat ≤ _
      rw [Vector.getElem_set_self]
      omega
    · show ((p.pileDepth.set i.val (q.pileDepth.get i) i.isLt)[j.val]'j.isLt).toNat ≤ _
      rw [Vector.getElem_set_ne i.isLt j.isLt (fun hc => hj hc.symm)]
      exact Nat.le_refl _
  have hqr : DepthLe r q := by
    intro j
    by_cases hj : j.val = i.val
    · have hji : j = i := Fin.ext hj
      subst hji
      show _ ≤ ((p.pileDepth.set j.val (q.pileDepth.get j) j.isLt)[j.val]'j.isLt).toNat
      rw [Vector.getElem_set_self]
    · show _ ≤ ((p.pileDepth.set i.val (q.pileDepth.get i) i.isLt)[j.val]'j.isLt).toNat
      rw [Vector.getElem_set_ne i.isLt j.isLt (fun hc => hj hc.symm)]
      exact h j
  have hstrict : DepthSum r < DepthSum p := by
    -- ascribe the `.toNat` spelling (`depth_sum_foldl_set` says `.toInt.toNat`, defeq but
    -- a different atom to `omega`)
    have hkey : (p.pileDepth.set i.val (q.pileDepth.get i) i.isLt).toList.foldl
          (fun acc x => acc + x.toNat) 0 + (p.pileDepth.get i).toNat =
        p.pileDepth.toList.foldl (fun acc x => acc + x.toNat) 0 + (q.pileDepth.get i).toNat :=
      depth_sum_foldl_set p.pileDepth i.val i.isLt (q.pileDepth.get i)
    show (p.pileDepth.set i.val (q.pileDepth.get i) i.isLt).toList.foldl
      (fun acc d => acc + d.toNat) 0 < _
    show _ < p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0
    omega
  exact lt_of_le_of_lt (hqr.sum_le) hstrict

/-- **`SolverCleanupPile` never deepens a pile.**  The empty branch rewrites the depth it
sets back to itself (`hsd`); the loop-bearing branches are `preCleanupPile_pileDepth_le`
and, in the lone-king case, `kingMove_pileDepth_le` on top of it. -/
theorem cleanupPile_depth_le (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p)) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok fk (g, p') ∧
      DepthLe p p' := by
  rcases cleanupPile_eq pile g p hpile hwf hnf with
    ⟨_hd0, hsd, hrun⟩ | ⟨B, hs4, _hd, _hd1, hd5, _hidx, _hBdef, _hBr, _hnfp, m, f, hm_le,
      _hmc, _hms, _hfl, _hflt, _hff, _hfs, _hak, hbranch⟩
  · refine ⟨0xffff, _, hrun, fun i => ?_⟩
    show ((p.pileDepth.set pile.toNat 0 hpile).get i).toNat ≤ (p.pileDepth.get i).toNat
    rw [hsd]
  · have hpre : ∀ i : Fin 10, ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i).toNat
        ≤ (p.pileDepth.get i).toNat := fun i =>
      preCleanupPile_pileDepth_le pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f hd5
        (by omega) i
    rcases hbranch with ⟨_a, _b, _c, _d, _e, _f2, hrun⟩ |
      ⟨_a, _b, _c, _d, _e, _f2, _g2, _h2, _i2, _j2, _k2, hrun⟩
    · exact ⟨0xffff, _, hrun, hpre⟩
    · exact ⟨_, _, hrun, fun i => le_trans
        (kingMove_pileDepth_le pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile) _ i)
        (hpre i)⟩

/-- **`SolverRemoveFlute` never deepens a pile** — and strictly decrements the pile it is
called on, which is where the whole progress argument comes from. -/
theorem removeFlute_depth_le (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hnf : SolverInvBase g (fluteNorm pile hpile (removeFlutePre pile hpile p))) :
    ∃ fk p', EStateM.run (_root_.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      DepthLe p p' ∧
      (p'.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by
  rw [removeFlute_eq pile g p hpile]
  obtain ⟨fk, p', hrun, hle⟩ :=
    cleanupPile_depth_le pile g (removeFlutePre pile hpile p) hpile hwf hnf
  -- the pre-step is where the one card actually comes off
  have hpre_pile : ((removeFlutePre pile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
    simp only [removeFlutePre]
    show ((p.pileDepth.set pile.toNat _ hpile)[pile.toNat]'hpile).toNat = _
    rw [Vector.getElem_set_self]
    show ((p.pileDepth[pile.toNat]'hpile) - 1).toNat = _
    rw [UInt8.toNat_sub_of_le _ _ (by
      rw [UInt8.le_iff_toNat_le]
      show (1 : UInt8).toNat ≤ (p.pileDepth[pile.toNat]'hpile).toNat
      simp only [show (1 : UInt8).toNat = 1 from rfl]
      exact hd1)]
    rfl
  have hpre : DepthLe p (removeFlutePre pile hpile p) := by
    intro i
    by_cases hi : i.val = pile.toNat
    · have hii : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hi
      subst hii
      omega
    · show ((p.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt).toNat ≤ _
      rw [Vector.getElem_set_ne hpile i.isLt (fun hc => hi hc.symm)]
      exact Nat.le_refl _
  refine ⟨fk, p', hrun, DepthLe.trans' hpre hle, ?_⟩
  have := hle ⟨pile.toNat, hpile⟩
  omega

/-- **`SolverRemoveFlute` preserves the base layer.**  Direct corollary of
    `cleanupPile_baseNF` via the exact reduction `removeFlute_eq`: the
    precondition is stated at the composed point — depth and hash already
    decremented (`removeFlutePre`), stale flute normalized (`fluteNorm`).  At
    exactly this state the `usedSpace` ledger balances and the caller-side
    anomalies vanish (a destination flute extended by `SolverMove` is valid once
    the source depth is decremented; an `aces` advanced by `SolverMoveAces` no
    longer conflicts with the normalized flute). -/
theorem removeFlute_base (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile (removeFlutePre pile hpile p))) :
    ∃ fk p', EStateM.run (_root_.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      SolverInvBase g p' := by
  rw [removeFlute_eq pile g p hpile]
  exact cleanupPile_base pile g (removeFlutePre pile hpile p) hpile hwf hnf

/-- **`SolverRemoveFlute` re-establishes the Merged layer** from the midpoint
    predicate at the composed point (see `removeFlute_baseNF` for why the
    composed state is the right place). -/
theorem removeFlute_merged (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hready : CleanupReady g (fluteNorm pile hpile (removeFlutePre pile hpile p)) pile) :
    ∃ fk p', EStateM.run (_root_.SolverRemoveFlute pile) (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' ∧ p'.aces = p.aces ∧
      (∀ mask : UInt8, p.busyAces &&& mask ≠ 0 → p'.busyAces &&& mask ≠ 0) := by
  rw [removeFlute_eq pile g p hpile]
  obtain ⟨fk, p', hrun, hinv', haces, hbusyMono⟩ :=
    cleanupPile_merged pile g (removeFlutePre pile hpile p) hpile hwf hready
  have hbusyEq : (removeFlutePre pile hpile p).busyAces = p.busyAces := by
    simp only [removeFlutePre]
  refine ⟨fk, p', hrun, hinv', haces, fun mask hmask => hbusyMono mask ?_⟩
  rwa [hbusyEq]

end SolverSpec
