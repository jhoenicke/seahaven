import Seahaven.MaximalCfg

/-!
# The depth is a function of the column

`merge_complete` says a merged position's `pileDepth` cannot be pushed one lower: the
dealt card just below the boundary does *not* continue the boundary's run.  Read
through `PileMatches`, that says `pileDepth i` is the **least** depth the physical
column matches — and therefore, for merged positions, the depth vector is determined
by the state.

This is what makes step 4 of the completeness argument depth arithmetic.  After the
critical move the play reaches some state; whichever canonical position that state
matches, its depths are *forced*, so it is the position the solver's `SolverMove` +
`SolverCleanupPile` computed (`IsCanonicalPos_unique`).  No reasoning about the merge
loop's history is needed.

The mechanism is `PileMatches.succ_below`: at or above the boundary the column
descends by exactly one card code per position.  If the column also matched a
*smaller* depth `n`, that descent would extend down to the pair
`pos2card[i][m-2], pos2card[i][m-1]`, making them consecutive — exactly what
`merge_complete` forbids.

**The `d ≤ 1` corner.**  `merge_complete` is vacuous at depth `≤ 1`, so the argument
does not separate depth `1` from depth `0`: a column whose single dealt card is a king,
with its run above it, matches both.  The solver never produces such a position — the
cleanup's lone-king branch vacates that pile to depth `0` — but that fact is not
recorded in `PileMerged`, so it is carried here as an explicit hypothesis
(`NoLoneKing`) rather than assumed.
-/

/-! ## The merge-stop condition, as a standalone predicate -/

/-- `merge_complete`, at an arbitrary depth value: the dealt card below the boundary
does not continue the boundary's run (vacuous at depth `≤ 1`). -/
def MergeStop (g : Globals) (i : Fin 10) (d : Nat) (hd : d ≤ 5) : Prop :=
  d ≤ 1 ∨ (g.pos2card.get i).get ⟨d - 2, by omega⟩
            ≠ (g.pos2card.get i).get ⟨d - 1, by omega⟩ + 1

theorem PileMerged.mergeStop {g : Globals} {p : SolverPosType} {i : Fin 10}
    {hd : (p.pileDepth.get i).toNat ≤ 5} (h : PileMerged g p i hd) :
    MergeStop g i (p.pileDepth.get i).toNat hd := by
  rcases h.merge_complete with hle | hne
  · exact Or.inl (by
      have : (p.pileDepth.get i).toNat ≤ (1 : UInt8).toNat := UInt8.le_iff_toNat_le.1 hle
      simpa using this)
  · exact Or.inr hne

/-! ## The merged depth is the least matching one -/

/-- **A merged depth cannot be beaten.**  If the column also matches `n`, the run the
`n`-match asserts reaches down to the two dealt cards straddling `m`'s boundary and
makes them consecutive — exactly what `merge_complete` forbids. -/
theorem le_of_pileMatches_of_mergeCond {g : Globals} {col : Column} {i : Fin 10} {n m : Fin 6}
    (hwf : WellFormedLayout g) (hn : PileMatches g col i n) (hm : PileMatches g col i m)
    (hm2 : 2 ≤ m.val)
    (hne : (g.pos2card.get i).get ⟨m.val - 2, by have := m.isLt; omega⟩
        ≠ (g.pos2card.get i).get ⟨m.val - 1, by have := m.isLt; omega⟩ + 1) :
    m.val ≤ n.val := by
  by_contra hlt
  refine hne ?_
  have hmlen : m.val ≤ col.length := hm.1
  have hrevlen : col.reverse.length = col.length := by simp
  have hr1 : m.val - 1 < col.reverse.length := by rw [hrevlen]; omega
  have hr2 : m.val - 1 - 1 < col.reverse.length := by rw [hrevlen]; omega
  -- one step of the `n`-match's descent, straddling `m`'s boundary
  have hstep : encodeCard (col.reverse[m.val - 1 - 1]'hr2)
      = encodeCard (col.reverse[m.val - 1]'hr1) + 1 :=
    hn.succ_below hwf (by omega) (by omega) hr1 hr2
  -- and both cards are the dealt ones the `m`-match names
  have hres1 : encodeCard (col.reverse[m.val - 1]'hr1)
      = (g.pos2card.get i).get ⟨m.val - 1, by have := m.isLt; omega⟩ :=
    hm.resident_code (by omega) hr1
  have hres2 : encodeCard (col.reverse[m.val - 1 - 1]'hr2)
      = (g.pos2card.get i).get ⟨m.val - 1 - 1, by have := m.isLt; omega⟩ :=
    hm.resident_code (by omega) hr2
  rw [hres1, hres2] at hstep
  have hidx : (⟨m.val - 1 - 1, by have := m.isLt; omega⟩ : Fin 5)
      = ⟨m.val - 2, by have := m.isLt; omega⟩ :=
    Fin.ext (show m.val - 1 - 1 = m.val - 2 by omega)
  rw [hidx] at hstep
  exact hstep

/-- The `depth ≤ 1` corner, isolated: at depth `1` the single dealt card is not a king.
(Cleanup's lone-king branch vacates such a pile to depth `0`, so the solver never emits
one; this states the fact without relying on that development.) -/
def NoLoneKing (g : Globals) (p : SolverPosType) : Prop :=
  ∀ i : Fin 10, (p.pileDepth.get i).toNat = 1 →
    (VALUE ((g.pos2card.get i).get ⟨0, by omega⟩)).toNat ≠ 13

/-- **The merged depth is the least matching depth**, with the lone-king corner
excluded. -/
theorem le_of_pileMatches_of_mergeStop {g : Globals} {col : Column} {i : Fin 10} {n m : Fin 6}
    (hwf : WellFormedLayout g) (hn : PileMatches g col i n) (hm : PileMatches g col i m)
    (hstop : MergeStop g i m.val (by have := m.isLt; omega))
    (hlone : m.val = 1 → (VALUE ((g.pos2card.get i).get ⟨0, by omega⟩)).toNat ≠ 13) :
    m.val ≤ n.val := by
  by_cases hm2 : 2 ≤ m.val
  · rcases hstop with h | h
    · omega
    · exact le_of_pileMatches_of_mergeCond hwf hn hm hm2 h
  · -- `m ≤ 1`; only `m = 1, n = 0` is not immediate, and there the bottom card is a king
    by_contra hlt
    have hm1 : m.val = 1 := by omega
    have hn0 : n.val = 0 := by omega
    have hmlen : m.val ≤ col.length := hm.1
    have hrevlen : col.reverse.length = col.length := by simp
    have hr0 : 0 < col.reverse.length := by rw [hrevlen]; omega
    obtain ⟨su, hrun⟩ := hn.king_run hn0
    obtain ⟨-, hv⟩ := hrun 0 hr0
    have hres : encodeCard (col.reverse[0]'hr0)
        = (g.pos2card.get i).get ⟨0, by have := m.isLt; omega⟩ :=
      hm.resident_code (by omega) hr0
    refine hlone hm1 ?_
    rw [← hres]
    omega

/-- **Two merged depths for the same column agree.** -/
theorem pileMatches_depth_unique {g : Globals} {col : Column} {i : Fin 10} {n m : Fin 6}
    (hwf : WellFormedLayout g) (hn : PileMatches g col i n) (hm : PileMatches g col i m)
    (hsn : MergeStop g i n.val (by have := n.isLt; omega))
    (hsm : MergeStop g i m.val (by have := m.isLt; omega))
    (hln : n.val = 1 → (VALUE ((g.pos2card.get i).get ⟨0, by omega⟩)).toNat ≠ 13)
    (hlm : m.val = 1 → (VALUE ((g.pos2card.get i).get ⟨0, by omega⟩)).toNat ≠ 13) : n = m :=
  Fin.ext (Nat.le_antisymm (le_of_pileMatches_of_mergeStop hwf hm hn hsn hln)
    (le_of_pileMatches_of_mergeStop hwf hn hm hsm hlm))

/-! ## Consequently the depth vector — and the whole position — is determined -/

/-- **The depth vector is determined by the state.**  Both positions are merged, so
each pile's depth is the least one its column matches. -/
theorem pileDepth_eq_of_matches {g : Globals} {s : State} {p q : SolverPosType}
    (hwf : WellFormedLayout g)
    (hbp : SolverInvBase g p) (hbq : SolverInvBase g q)
    (hpm : ∀ i : Fin 10, PileMerged g p i (hbp.pileDepth_bound i))
    (hqm : ∀ i : Fin 10, PileMerged g q i (hbq.pileDepth_bound i))
    (hmp : StateMatchesSolverPos g s p) (hmq : StateMatchesSolverPos g s q)
    (hlp : NoLoneKing g p) (hlq : NoLoneKing g q) :
    p.pileDepth = q.pileDepth := by
  have hcomp : ∀ i : Fin 10, (p.pileDepth.get i).toNat = (q.pileDepth.get i).toNat := by
    intro i
    have h1 : (p.pileDepth.get i).toNat ≤ (q.pileDepth.get i).toNat :=
      le_of_pileMatches_of_mergeStop hwf (hmq.depth_match i) (hmp.depth_match i)
        (hpm i).mergeStop (fun h => hlp i h)
    have h2 : (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat :=
      le_of_pileMatches_of_mergeStop hwf (hmp.depth_match i) (hmq.depth_match i)
        (hqm i).mergeStop (fun h => hlq i h)
    omega
  ext i hi
  exact congrArg UInt8.toNat (by
    exact UInt8.toNat_inj.mp (hcomp ⟨i, hi⟩)) ▸ rfl

/-- **A state determines the canonical position it matches.**  With the depths pinned,
`IsCanonicalPos_unique` finishes: everything else a canonical position records is a
function of the depth vector.  This is what makes step 4 of the completeness argument
pure depth arithmetic — whatever canonical position the post-move state matches *is*
the one the solver computed. -/
theorem canonical_eq_of_matches {g : Globals} {s : State} {p q : SolverPosType}
    (hwf : WellFormedLayout g) (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (hmp : StateMatchesSolverPos g s p) (hmq : StateMatchesSolverPos g s q)
    (hlp : NoLoneKing g p) (hlq : NoLoneKing g q) : p = q :=
  IsCanonicalPos_unique g p q hwf hp hq
    (pileDepth_eq_of_matches hwf hp.toSolverInvBase hq.toSolverInvBase hp.pileMerged hq.pileMerged
      hmp hmq hlp hlq)
