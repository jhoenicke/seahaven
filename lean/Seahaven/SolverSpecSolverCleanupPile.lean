import Seahaven.SolverSpecKingMove
import Seahaven.SolverSpecPreCleanupPile
import Seahaven.SolverSpecCleanupPile

/-!
# Spec for `SolverCleanupPile` (the monadic per-pile cleanup step)

`solverCleanupPile_step` connects one step of the real `SolverCleanupPile`
monadic loop to the pure `cleanupPile`/`kingMove`/`preCleanupPile` model,
carrying the `MergedUpTo` invariant across it.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **`SolverCleanupPile` — one step of the convert cleanup loop.**  Given the
    loop invariant `MergedUpTo g p k` (base holds everywhere; piles below `k`
    already merged; pile `k` still raw), cleaning pile `k` succeeds, leaves
    `globals` and the other piles' depths untouched, and re-establishes the
    invariant with one more pile merged.

    Stated against the **real** `_root_.SolverCleanupPile` (its `while` loops are no
    longer opaque on Lean 4.31 — see `Seahaven.EStateMTail`); the `SolverModel` fuel
    twin is no longer needed.

    The loop invariant `MergedUpTo` has been refined so this is now true: its
    free-piles clause is the *prefix-relative* `freePilesUpTo … k` (the cleanup loop
    counts only already-processed piles), coinciding with the global `freePiles_def`
    at `k = 10`.

    **TODO (statement gap):** as stated this is *unprovable* — the `usedSpace_def`
    clause of `SolverInvBase` is only true of pile `k`'s *flute-normalized*
    position (the freed loop re-frees the old flute interiors; a stale
    `pileFlute[k]` would double-count them in the formula).  Restate `MergedUpTo`'s
    base clause about `{ p with pileFlute[k] := 1 }`, following
    `cleanupPile_baseNF`'s precondition convention.  (The lone-king `kings` update
    is no longer an obstacle: `aces_kings_valid` allows the value-0 sentinel.)

    Proof status: the **base case** (pile `k` already empty — no loops run) is proved
    below; the **loop-bearing case** (`pileDepth[k] > 0`) is `sorry` — its exact run
    is now available as `cleanupPile_nonempty_eq` (see `cleanupPile_baseNF` for the
    clause-discharge plan). -/
theorem solverCleanupPile_step (g : Globals) (p : SolverPosType) (k : Nat) (hk : k < 10)
    (hwf : WellFormedLayout g) (hpre : MergedUpTo g p k) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile (UInt32.ofNat k)) (g, p) = .ok fk (g, p') ∧
      MergedUpTo g p' (k + 1) ∧
      (∀ j : Fin 10, j.val ≠ k → p'.pileDepth.get j = p.pileDepth.get j) := by
  obtain ⟨hnf, hfp, hpm, hfluteRest⟩ := hpre
  have hp16 : p.busyAces < 16 := hnf.busyAces_lt16
  have hpkn : (UInt32.ofNat k).toNat = k :=
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hk (by decide))
  by_cases hdk : p.pileDepth.get ⟨k, hk⟩ = 0
  · -- BASE CASE: pile `k` is already empty; neither `while` loop runs.
    have hd : p.pileDepth[(UInt32.ofNat k).toNat]'(by rw [hpkn]; exact hk) = 0 := by
      simp only [hpkn]; exact hdk
    -- exact resulting state (from `SolverRealSpec.cleanupPile_empty_eq`)
    have hrun := cleanupPile_empty_eq (UInt32.ofNat k) g p (by rw [hpkn]; exact hk) hd
    have h1 : (UInt32.ofNat k).toNat < 10 := by rw [hpkn]; exact hk
    -- The two writes are to already-canonical values, so they are no-ops.
    have hsd : p.pileDepth.set (UInt32.ofNat k).toNat 0 h1 = p.pileDepth := by
      conv_lhs => rw [← hd]
      exact Vector.set_getElem_self h1
    have hfe : p.pileFlute[(UInt32.ofNat k).toNat]'h1 = 1 :=
      hnf.flute_empty ⟨(UInt32.ofNat k).toNat, h1⟩ hd
    have hsf : p.pileFlute.set (UInt32.ofNat k).toNat 1 h1 = p.pileFlute := by
      conv_lhs => rw [← hfe]
      exact Vector.set_getElem_self h1
    refine ⟨0xffff, _, hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- (1) SolverInvBase — the base layer ignores `freePiles`, and the depth/flute
      -- writes are no-ops, so it transfers verbatim from `p`.
      simp only [hsd, hsf]; exact nf_setFreePiles hnf _
    · -- (2) prefix free-piles count: bumped by one, matching the new empty pile `k`.
      have hlen : k < p.pileDepth.toList.length := by rw [Vector.length_toList]; omega
      have hlk : p.pileDepth.toList[k]'hlen = 0 := by rw [Vector.getElem_toList]; exact hdk
      have hb : freePilesUpTo p k ≤ 9 := by
        unfold freePilesUpTo
        exact le_trans List.countP_le_length (by rw [List.length_take]; omega)
      have hstep : freePilesUpTo p (k + 1) = freePilesUpTo p k + 1 := by
        rw [freePilesUpTo, freePilesUpTo, List.take_add_one, List.countP_append, List.getElem?_eq_getElem hlen]
        simp [Option.toList, hlk]
      have hle : p.freePiles.toInt ≤ 9 := by rw [hfp]; exact_mod_cast hb
      have hge : 0 ≤ p.freePiles.toInt := by rw [hfp]; exact Int.natCast_nonneg _
      have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
        rw [UInt8.toInt_add, UInt8.toInt_one]
        omega
      simp only [hsd, hsf]
      show (p.freePiles + 1).toInt = (freePilesUpTo p (k + 1) : Nat)
      rw [hstep, hadd, hfp]; push_cast; ring
    · -- (3) PileMerged for the first `k+1` piles.
      simp only [hsd, hsf]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
      · exact pm_setFreePiles (hpm i hik) _   -- piles `< k`: already merged
      · -- pile `k` is empty ⇒ trivially merged
        obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
        refine pm_setFreePiles ?_ _
        exact ⟨Or.inl (by rw [hdk]; decide),
          Or.inl hdk, by intro h; rw [hdk] at h; exact absurd h (by decide)⟩
    · -- (4) piles `≥ k+1` still carry the default `pileFlute = 1` — untouched,
      -- so this is just `hfluteRest` restricted to a weaker bound.
      simp only [hsf]
      intro i hi
      exact hfluteRest i (by omega)
    · -- frame: other piles' depths untouched (set only at index k)
      intro j hj
      exact Vector.getElem_set_ne (show (UInt32.ofNat k).toNat < 10 by rw [hpkn]; exact hk)
        j.isLt (by rw [hpkn]; omega)
  · -- LOOP-BEARING CASE: pileDepth[k] > 0 — merge/freed while loops run.
    --
    -- Bridge the `MergedUpTo` witnesses (`hnf`/`hpm`/`hfluteRest`) to
    -- `cleanupPile_eq`'s `fluteNorm`'d precondition, reuse its non-king/king
    -- bundle for the shared `SolverInvBase` reconstruction (exactly as
    -- `cleanupPile_base` does), then add the caller-specific pieces that
    -- don't fold into `cleanupPile_eq`: the `i < k` vs `i = k` case split for
    -- `MergedUpTo`'s prefix `PileMerged` clause (via
    -- `preCleanupPile_pileMerged_ne`/`kingMove_pileMerged_ne`), the
    -- `freePilesUpTo` bookkeeping (`hfreePilesStep0`/`hfreePilesStep1`), and
    -- the `pileFlute = 1` suffix clause.
    have hk_ : (UInt32.ofNat k).toNat < 10 := by rw [hpkn]; exact hk
    -- Bridge the outer `¬(pileDepth[k] = 0)` (stated via `.get ⟨k,hk⟩`) to the
    -- `[]`-indexed form `cleanupPile_eq`'s body expects.
    have hfinEq : (⟨(UInt32.ofNat k).toNat, hk_⟩ : Fin 10) = (⟨k, hk⟩ : Fin 10) := Fin.ext hpkn
    -- Pile `k` hasn't been reached by the loop yet, so `hfluteRest` says its
    -- flute is already the default `1`, making `fluteNorm` a no-op here — this
    -- is exactly what bridges `MergedUpTo`'s raw base layer to
    -- `cleanupPile_eq`'s `fluteNorm`'d precondition.
    have hfe : p.pileFlute[(UInt32.ofNat k).toNat]'hk_ = 1 :=
      hfluteRest ⟨(UInt32.ofNat k).toNat, hk_⟩ (le_of_eq hpkn.symm)
    have hsf : p.pileFlute.set (UInt32.ofNat k).toNat 1 hk_ = p.pileFlute := by
      conv_lhs => rw [← hfe]
      exact Vector.set_getElem_self hk_
    have hfluteNormEq : fluteNorm (UInt32.ofNat k) hk_ p = p := by
      show { p with pileFlute := p.pileFlute.set (UInt32.ofNat k).toNat 1 hk_ } = p
      rw [hsf]
    have hnf_ : SolverInvBase g (fluteNorm (UInt32.ofNat k) hk_ p) := by
      rw [hfluteNormEq]; exact hnf
    -- Shared prefix-count bookkeeping (mirrors the base case's `hb`/`hle`/`hge`
    -- block), reused by both branches' free-piles obligation below.
    have hb9 : freePilesUpTo p k ≤ 9 := by
      unfold freePilesUpTo
      exact le_trans List.countP_le_length (by rw [List.length_take]; omega)
    have hle9 : p.freePiles.toInt ≤ 9 := by rw [hfp]; exact_mod_cast hb9
    have hge0 : 0 ≤ p.freePiles.toInt := by rw [hfp]; exact Int.natCast_nonneg _
    -- Generic step lemmas relating `freePilesUpTo _ (k+1)` to `freePilesUpTo p k`
    -- for any position `q` agreeing with `p` outside index `k` (the frame
    -- condition each branch proves anyway), according to whether `q`'s own
    -- pile `k` is empty or not.
    have hfreePilesStep0 : ∀ (q : SolverPosType),
        (∀ j : Fin 10, j.val ≠ k → q.pileDepth.get j = p.pileDepth.get j) →
        q.pileDepth.get (⟨k, hk⟩ : Fin 10) ≠ 0 →
        freePilesUpTo q (k + 1) = freePilesUpTo p k := by
      intro q hframe hne
      have hne' : q.pileDepth[k]'hk ≠ 0 := hne
      have hlenq : k < q.pileDepth.toList.length := by rw [Vector.length_toList]; exact hk
      have htake : q.pileDepth.toList.take k = p.pileDepth.toList.take k := by
        apply List.ext_getElem
        · simp [Vector.length_toList]
        · intro n h1 h2
          have hnk : n < k := by
            have h1' := h1
            rw [List.length_take, Vector.length_toList] at h1'
            omega
          have hn10 : n < 10 := by omega
          have hnk' : n ≠ k := by omega
          rw [List.getElem_take, List.getElem_take, Vector.getElem_toList, Vector.getElem_toList]
          exact hframe ⟨n, hn10⟩ hnk'
      unfold freePilesUpTo
      rw [List.take_succ_eq_append_getElem hlenq, List.countP_append, htake, List.countP_singleton, Vector.getElem_toList]
      rw [show (q.pileDepth[k]'hk == (0 : UInt8)) = false from beq_eq_false_iff_ne.mpr hne']
      simp
    have hfreePilesStep1 : ∀ (q : SolverPosType),
        (∀ j : Fin 10, j.val ≠ k → q.pileDepth.get j = p.pileDepth.get j) →
        q.pileDepth.get (⟨k, hk⟩ : Fin 10) = 0 →
        freePilesUpTo q (k + 1) = freePilesUpTo p k + 1 := by
      intro q hframe heq
      have heq' : q.pileDepth[k]'hk = 0 := heq
      have hlenq : k < q.pileDepth.toList.length := by rw [Vector.length_toList]; exact hk
      have htake : q.pileDepth.toList.take k = p.pileDepth.toList.take k := by
        apply List.ext_getElem
        · simp [Vector.length_toList]
        · intro n h1 h2
          have hnk : n < k := by
            have h1' := h1
            rw [List.length_take, Vector.length_toList] at h1'
            omega
          have hn10 : n < 10 := by omega
          have hnk' : n ≠ k := by omega
          rw [List.getElem_take, List.getElem_take, Vector.getElem_toList, Vector.getElem_toList]
          exact hframe ⟨n, hn10⟩ hnk'
      unfold freePilesUpTo
      rw [List.take_succ_eq_append_getElem hlenq, List.countP_append, htake, List.countP_singleton, Vector.getElem_toList]
      rw [show (q.pileDepth[k]'hk == (0 : UInt8)) = true from by rw [beq_iff_eq]; exact heq']
      simp
    rcases cleanupPile_eq (UInt32.ofNat k) g p hk_ hwf hnf_ with
      ⟨hd0, hsd0, hrun0⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
        hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
    · -- Impossible: we're in the `¬hdk` (nonempty) case, but `cleanupPile_eq`
      -- took the empty branch.
      exact absurd (hfinEq ▸ hd0) hdk
    · rcases hbranch with
        ⟨-, hframe, hpc, hsuit, hhash, hused, hrun⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
      · -- NON-KING sub-branch.
        have hframeNK : ∀ j : Fin 10, j.val ≠ k →
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p).pileDepth.get j =
            p.pileDepth.get j :=
          fun j hj => hframe j (by rw [hpkn]; exact hj)
        refine ⟨0xffff, preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
            (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p, hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ⟨fun i => ?_, hsuit, hhash, hused,
            preCleanupPile_busyAces_lt16 (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p hp16⟩
          by_cases hij : i.val = (UInt32.ofNat k).toNat
          · have hii : i = ⟨(UInt32.ofNat k).toNat, hk_⟩ := Fin.ext hij
            subst hii
            exact hpc.toPileBase
          · exact preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 (by omega) i hij (hnfp i hij)
        · -- (2) prefix free-piles count: `preCleanupPile` never touches
          -- `freePiles`, and pile `k` stays occupied (`m ≤ depth−1`), so the
          -- prefix count over the first `k+1` piles is unchanged.
          have hpfEq2 : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p).freePiles = p.freePiles := by
            simp only [preCleanupPile]
          have hpdEqNK : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ =
              ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_) - UInt8.ofNat m) := by
            simp only [preCleanupPile]
            rw [Vector.getElem_set_self]
          have hpdNeNK : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p).pileDepth.get
                (⟨k, hk⟩ : Fin 10) ≠ 0 := by
            rw [← hfinEq]
            show (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ ≠ 0
            rw [hpdEqNK]
            intro heq
            have h' := congrArg UInt8.toNat heq
            rw [depth_sub_ofNat_eq hd5 (by omega),
              show ((0 : UInt8).toNat = 0) from rfl] at h'
            omega
          have hstepEq := hfreePilesStep0 _ hframeNK hpdNeNK
          rw [hpfEq2, hstepEq]
          exact hfp
        · -- (3) `PileMerged` for the first `k+1` piles: piles `< k` transfer
          -- from `hpm` via `preCleanupPile_pileMerged_ne`; pile `k` itself is
          -- freshly `PileClean` (hence `PileMerged`) via `hpc`.
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
          · exact preCleanupPile_pileMerged_ne (UInt32.ofNat k) g hk_ hwf B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 hm_le hmcards hak i
              (by rw [hpkn]; omega) (hnf.pileBase i) (hpm i hik)
          · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
            rw [← hfinEq]
            exact hpc.toPileMerged
        · -- (4) piles `≥ k+1` still carry the default `pileFlute = 1` — untouched
          -- by `preCleanupPile` (which only writes `pileFlute[k]`).
          intro i hi
          rw [preCleanupPile_pileFlute_eq_of_ne (UInt32.ofNat k) hk_ B
            (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f i (by rw [hpkn]; omega)]
          exact hfluteRest i (by omega)
        · -- frame: other piles' depths untouched.
          exact hframeNK
      · -- KING sub-branch.
        have hframeK : ∀ j : Fin 10, j.val ≠ k →
            (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)).pileDepth.get j =
            p.pileDepth.get j :=
          fun j hj => hframe j (by rw [hpkn]; exact hj)
        refine ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
          kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p), hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ⟨fun i => ?_, hsuit, hhash, hused, ?_⟩
          swap
          · rw [kingMove_busyAces_eq]
            exact preCleanupPile_busyAces_lt16 (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p hp16
          by_cases hij : i.val = (UInt32.ofNat k).toNat
          · have hii : i = ⟨(UInt32.ofNat k).toNat, hk_⟩ := Fin.ext hij
            subst hii
            exact hpc.toPileBase
          · exact kingMove_pileBase_ne (UInt32.ofNat k) g hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p) i hij
              (preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B
                (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 (by omega) i hij (hnfp i hij))
        · -- (2) prefix free-piles count: `kingMove` empties pile `k` and bumps
          -- `freePiles` by one — mirrors the base case's `hadd`/`hle`/`hge` block.
          have hkmfp : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)).freePiles = p.freePiles + 1 := by
            simp only [kingMove, preCleanupPile]
          have hkd0 : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)).pileDepth.get
                (⟨k, hk⟩ : Fin 10) = 0 := by
            rw [← hfinEq]
            exact kingMove_pileDepth_self (UInt32.ofNat k) hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)
          have haddFP : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
            rw [UInt8.toInt_add, UInt8.toInt_one]
            omega
          have hstepEq := hfreePilesStep1 _ hframeK hkd0
          show (p.freePiles + 1).toInt = (freePilesUpTo (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4
            (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)) (k + 1) : Nat)
          rw [hstepEq, haddFP, hfp]
          push_cast
          ring
        · -- (3) `PileMerged` for the first `k+1` piles: piles `< k` transfer
          -- from `hpm` through `preCleanupPile_pileMerged_ne` then
          -- `kingMove_pileMerged_ne`; pile `k` itself is freshly `PileClean`
          -- (hence `PileMerged`) via `hpc`.
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
          · have hijk : i.val ≠ (UInt32.ofNat k).toNat := by rw [hpkn]; omega
            exact kingMove_pileMerged_ne (UInt32.ofNat k) g hk_ hwf (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p)
              hd1' K hKdef hVK13 hak i hijk
              (preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B
                (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 (by omega) i hijk
                (hnfp i hijk))
              (preCleanupPile_pileMerged_ne (UInt32.ofNat k) g hk_ hwf B
                (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 hm_le hmcards hak i hijk
                (hnf.pileBase i) (hpm i hik))
          · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
            rw [← hfinEq]
            exact hpc.toPileMerged
        · -- (4) piles `≥ k+1` still carry the default `pileFlute = 1` — untouched
          -- by `preCleanupPile`/`kingMove` (which only ever write `pileFlute[k]`).
          intro i hi
          have hine : i.val ≠ (UInt32.ofNat k).toNat := by rw [hpkn]; omega
          rw [kingMove_pileFlute_eq_of_ne (UInt32.ofNat k) hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_) m f p) i hine,
            preCleanupPile_pileFlute_eq_of_ne (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f i hine]
          exact hfluteRest i (by omega)
        · -- frame: other piles' depths untouched.
          exact hframeK

end SolverSpec
