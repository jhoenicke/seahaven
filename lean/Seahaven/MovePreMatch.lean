import Seahaven.CriticalMove
import Seahaven.CleanupSim

/-!
# The critical move lands on `movePre`'s depth vector

Route B's phase-1 state side.  The play makes the critical move out of the state
`t₀` — pile `a`'s boundary card `c`, with `a`'s flute already parked in cells, so
`|t₀.tableau a| = pileDepth a` — and the solver's own bookkeeping for that move is
`SolverSpec.movePre pile toPile hpile p`, whose depth vector is `p`'s with pile `a`
decremented (`movePre_depth_self`/`movePre_depth_ne`).

Those two agree, and the proof is short because the depth vector is all that has to
match here:

* at pile `a` the boundary card leaves, so the column is exactly the dealt cards
  *below* the boundary and nothing sits above them — `PileMatches_pop_boundary`;
* every other pile only ever receives a card, and `DepthMatchesV.drop` already knows
  drops never break a depth match.

The flute lengths deliberately play no part: `t₀`'s flute is parked in cells and
`movePre` counts it on the destination, so the two disagree about `pileFlute` until
the cell cards are dropped back — which is `CPNormCfg`'s business, not this file's.

What this does *not* yet do is descend to the merged position the cleanup computes:
`movePre` is not `PileMerged` at `a` (the merge is exactly what `SolverRemoveFlute`
still has to run), so `matches_of_depth_match` does not apply here.  Lowering the
depth along the merge chain is `PileMatches_lower` (`CleanupSim`), and feeding it the
chain the run establishes is the next step.
-/

/-! ## Removing the boundary card -/

/-- **Taking a fully exposed boundary card lowers the depth by one.**  The column
was exactly its dealt part, so what is left is the dealt part one shorter, with
nothing above it — the flute clause is vacuous on the empty tail. -/
theorem PileMatches_pop_boundary {g : Globals} {col : Column} {a : Fin 10} {n n' : Fin 6}
    {c : Card} {rest : Column} (h : PileMatches g col a n) (hcol : col = c :: rest)
    (hlen : col.length = n.val) (hn' : n'.val + 1 = n.val) :
    PileMatches g rest a n' := by
  obtain ⟨hle, hres, -⟩ := h
  subst hcol
  simp only [List.length_cons] at hlen
  have hrestlen : rest.length = n'.val := by omega
  refine ⟨by omega, ?_, ?_⟩
  · -- the bottom cards are the same ones
    intro k
    have hk : k.val < n.val := by have := k.isLt; omega
    have hkr : k.val < rest.reverse.length := by simpa using (by omega : k.val < rest.length)
    have h1 := hres ⟨k.val, hk⟩
    rw [List.reverse_cons, List.getElem?_append_left hkr] at h1
    exact h1
  · -- nothing is left above the new boundary
    have hdrop : rest.reverse.drop n'.val = [] := by
      refine List.drop_eq_nil_of_le ?_
      simpa using le_of_eq hrestlen
    simp only [hdrop, List.map_nil]
    by_cases hn0 : n'.val > 0
    · rw [dif_pos hn0]
      intro i
      exact absurd i.isLt (by simp)
    · rw [dif_neg hn0]
      exact ⟨0, fun i => absurd i.isLt (by simp)⟩

/-! ## The depth vector of `movePre` -/

/-- `movePre`'s depths are `p`'s with the source decremented, so they still fit in
`Fin 6`. -/
theorem movePre_depth_sub {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat) :
    ((SolverSpec.movePre pile toPile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩).toNat
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
  rw [SolverSpec.movePre_depth_self]
  have h := depth1_toNat (d := p.pileDepth.get ⟨pile.toNat, hpile⟩) (m := 1)
    (hb.pileDepth_bound ⟨pile.toNat, hpile⟩) (by omega)
  rwa [show (UInt8.ofNat 1) = (1 : UInt8) from rfl] at h

theorem movePre_depth_lt6 {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat) (i : Fin 10) :
    ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat < 6 := by
  by_cases hi : i.val = pile.toNat
  · have hfin : i = ⟨pile.toNat, hpile⟩ := Fin.ext hi
    subst hfin
    rw [movePre_depth_sub hb pile toPile hpile hda]
    have := hb.pileDepth_bound ⟨pile.toNat, hpile⟩
    omega
  · rw [SolverSpec.movePre_depth_ne pile toPile hpile p i hi]
    have := hb.pileDepth_bound i
    omega

/-- **The critical move's target matches `movePre`'s depth vector.**  Nothing about
flutes or king stacks is claimed — only the depths, which is exactly what
`PileMatches_lower` and `matches_of_depth_match` consume downstream. -/
theorem critical_depthMatchesV_movePre {g : Globals} {t₀ t₁ : State} {p : SolverPosType}
    (hb : SolverInvBase g p) (h : DepthPlusKings g t₀ p)
    {pile : UInt32} (hpile : pile.toNat < 10) (toPile : UInt8)
    (hlen : (t₀.tableau ⟨pile.toNat, hpile⟩).length
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    {m : Move} (hsrc : m.src = Position.pile ⟨pile.toNat, hpile⟩)
    (hap : applyMove t₀ m = some t₁) :
    DepthMatchesV g t₁ (depthVec (SolverSpec.movePre pile toPile hpile p)
      (movePre_depth_lt6 hb pile toPile hpile hda)) := by
  set a : Fin 10 := ⟨pile.toNat, hpile⟩ with hadef
  have hd5 := hb.pileDepth_bound a
  -- the new depth at the source, as a `Nat`
  have hdnew : ((SolverSpec.movePre pile toPile hpile p).pileDepth.get a).toNat
      = (p.pileDepth.get a).toNat - 1 := movePre_depth_sub hb pile toPile hpile hda
  -- take the boundary card off
  rw [applyMove_eq, hsrc] at hap
  obtain ⟨c', s0, htake, hdrop⟩ := hap
  rw [takeFromPosition, takeFromCol_eq] at htake
  obtain ⟨rest', hcol', rfl⟩ := htake
  -- the depth vector matches after the take …
  have hs0 : DepthMatchesV g (updateColumn t₀ a rest')
      (depthVec (SolverSpec.movePre pile toPile hpile p)
        (movePre_depth_lt6 hb pile toPile hpile hda)) := by
    intro i
    by_cases hia : i = a
    · subst hia
      simp only [updateColumn_tableau, update_same]
      refine PileMatches_pop_boundary (h.depth_match a) hcol' hlen ?_
      show ((SolverSpec.movePre pile toPile hpile p).pileDepth.get a).toNat + 1
        = (p.pileDepth.get a).toNat
      rw [hdnew]
      omega
    · have hidx : (depthVec (SolverSpec.movePre pile toPile hpile p)
          (movePre_depth_lt6 hb pile toPile hpile hda) i)
          = ⟨(p.pileDepth.get i).toNat, h.depth_lt6 i⟩ := by
        refine Fin.ext ?_
        show ((SolverSpec.movePre pile toPile hpile p).pileDepth.get i).toNat
          = (p.pileDepth.get i).toNat
        rw [SolverSpec.movePre_depth_ne pile toPile hpile p i
          (fun hc => hia (Fin.ext hc))]
      simpa [update, Ne.symm hia, hidx] using h.depth_match i
  -- … and drops never break it
  exact DepthMatchesV.drop hs0 hdrop
