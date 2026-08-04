import Seahaven.SolverInvariant
import Seahaven.SolverModel
import Seahaven.SolverRealSpec

/-!
# Specs: the model canonicalization functions establish the invariant tower

Each theorem says: run the corresponding `SolverModel` function on a state
satisfying a precondition, and it succeeds (`.ok`, no `Error` thrown), leaving
`globals` unchanged and producing a `SolverPosType` satisfying the postcondition.

All proofs are `sorry` at this stage — they are Stage 2+ work (unfold the fuel
recursion, do induction, discharge the arithmetic).  The value here is the
*shape*: exactly which layer of the tower each function establishes.

Several preconditions (`CleanupPre`, `MoveValid`) are still approximate and
flagged `TODO refine` — the exact conditions will be pinned down against the
recursion during the proofs (as anticipated in `VerificationPlan.md`).

This file (`SolverSpec.lean`'s former preamble) collects the auxiliary
preconditions/definitions and helper lemmas shared across the per-function
spec files below (`SolverSpecKingMove`, `SolverSpecPreCleanupPile`,
`SolverSpecCleanupPile`, `SolverSpecRemoveFlute`, `SolverSpecSolverCleanupPile`,
`SolverSpecMoveAces`, `SolverSpecMove`, `SolverSpecDrain`,
`SolverSpecSolverConvert`, `SolverSpecFreedBoundary`).
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

-- ---------------------------------------------------------------------------
-- Auxiliary preconditions (approximate; refined during the proofs)
-- ---------------------------------------------------------------------------

/-- All ten pile depths in the input vector are `≤ 5` (a legal deal). -/
def ValidDepths (pk : Vector UInt8 11) : Prop :=
  ∀ i : Fin 10, (pk.get ⟨i.val, by omega⟩).toNat ≤ 5

/-- **TODO refine.** Validity precondition for `SolverMove pile toPile`: the pile
    is non-empty, the destination is a legal target, and the move the solver is
    about to make is one it actually considers (flute length fits, etc.).  The
    exact conditions (mirroring `solverGetMovable`) will be pinned down during the
    soundness proof. -/
def MoveValid (_g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8) : Prop :=
  pile.toNat < 10 ∧ toPile.toNat ≤ 14 ∧ (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat > 0

-- ---------------------------------------------------------------------------
-- Specs
-- ---------------------------------------------------------------------------

/-- `PileBase` reused verbatim across a state differing only in fields it
    doesn't mention: `PileBase g p i` and `PileBase g p' i` aren't themselves
    defeq just because `p`/`p'` agree on the fields that matter (the whole
    record is an opaque argument to the `PileBase` type former), but each
    individual field PROPOSITION unfolds transparently through `p`'s
    projections, so reconstructing field-by-field works. -/
private theorem pileBase_setFreePiles {g : Globals} {p : SolverPosType} {i : Fin 10}
    (h : PileBase g p i) (x : UInt8) : PileBase g { p with freePiles := x } i :=
  ⟨h.pileDepth_bound, h.pileDepth_nonneg, h.flute_pos, h.flute_empty,
   h.flute_cards_free, h.flute_not_aces⟩

private theorem pileBase_setBusyAces {g : Globals} {p : SolverPosType} {i : Fin 10}
    (h : PileBase g p i) (y : UInt8) : PileBase g { p with busyAces := p.busyAces ||| y } i :=
  ⟨h.pileDepth_bound, h.pileDepth_nonneg, h.flute_pos, h.flute_empty,
   h.flute_cards_free, h.flute_not_aces⟩

/-- The base layer ignores `freePiles`, so it transfers across a `freePiles` write. -/
theorem nf_setFreePiles {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (x : UInt8) : SolverInvBase g { p with freePiles := x } :=
  ⟨fun i => pileBase_setFreePiles (h.pileBase i) x,
   fun s => ⟨h.aces_kings_valid s, h.foundation_cards_free s, h.foundation_maximal_weak s, h.king_frontier s⟩,
   h.hash_def, h.usedSpace_def, h.busyAces_lt16⟩

/-- Setting more bits in a bitmask can't clear an already-set bit. -/
theorem uint8_and_ne_zero_of_or_left {a b c : UInt8} (h : a &&& c ≠ 0) :
    (a ||| b) &&& c ≠ 0 := by
  intro heq
  apply h
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have h1 := congrArg (fun x : UInt8 => x.toBitVec.getLsbD i) heq
  simp [UInt8.toBitVec_and, UInt8.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or] at h1
  simp [UInt8.toBitVec_and, BitVec.getLsbD_and]
  tauto

/-- OR-ing in a bit makes it survive the AND check, regardless of what was
    already set. -/
theorem uint8_and_ne_zero_of_or_right {a b c : UInt8} (h : b &&& c ≠ 0) :
    (a ||| b) &&& c ≠ 0 := by
  rw [UInt8.or_comm]
  exact uint8_and_ne_zero_of_or_left h

/-- A single shifted bit, ANDed with itself, is nonzero (as long as the shift
    doesn't push it out of the byte). -/
theorem uint8_shift_self_ne_zero (x : UInt8) (hx : x.toNat < 4) :
    ((1 : UInt8) <<< x) &&& ((1 : UInt8) <<< x) ≠ 0 := by
  have hxe : x = UInt8.ofNat x.toNat := by simp
  rw [hxe]
  set b := x.toNat with hb
  clear_value b
  interval_cases b <;> decide

/-- `a ||| b < 16` whenever both operands are, since OR-ing two 4-bit values
    (`< 2^4`) stays `< 2^4` (`Nat.or_lt_two_pow`). -/
theorem uint8_or_lt16_of_lt16 {a b : UInt8} (ha : a < 16) (hb : b < 16) :
    a ||| b < 16 := by
  have h16 : (16 : UInt8).toNat = 16 := by decide
  have ha' : a.toNat < 16 := by rwa [UInt8.lt_iff_toNat_lt, h16] at ha
  have hb' : b.toNat < 16 := by rwa [UInt8.lt_iff_toNat_lt, h16] at hb
  rw [UInt8.lt_iff_toNat_lt, h16, UInt8.toNat_or]
  exact Nat.or_lt_two_pow (n := 4) ha' hb'

/-- The base layer ignores `busyAces`, so it transfers across a `busyAces` write —
    **as long as the write only ADDS bits** (`p.busyAces ||| y`, never clears one):
    `king_frontier`'s busyAces-pending disjunct is monotone in the bitmask, so an
    already-set bit stays set. (This collapses the `busyAces` branch of
    `cleanupRunResult`, whose only busyAces write is exactly this OR-in shape.)
    Needs `y < 16` too (`busyAces_lt16` transfer): every real caller ORs in
    `1 <<< SUIT B` for a real card `B`, so `y < 16` always holds there. -/
theorem nf_setBusyAces {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (y : UInt8) (hy : y < 16) :
    SolverInvBase g { p with busyAces := p.busyAces ||| y } :=
  ⟨fun i => pileBase_setBusyAces (h.pileBase i) y,
   fun s => ⟨h.aces_kings_valid s,
             h.foundation_cards_free s,
             (h.foundation_maximal_weak s).imp id (fun hb => hb.imp id uint8_and_ne_zero_of_or_left),
             ⟨(h.king_frontier s).1.imp (fun hc => ⟨hc.1, hc.2.imp id uint8_and_ne_zero_of_or_left⟩) id,
              (h.king_frontier s).2⟩⟩,
   h.hash_def, h.usedSpace_def, uint8_or_lt16_of_lt16 h.busyAces_lt16 hy⟩

/-- `PileMerged` ignores `freePiles`, so it transfers across a `freePiles` write. -/
theorem pm_setFreePiles {g : Globals} {p : SolverPosType} {i : Fin 10}
    {bound : (p.pileDepth.get i).toNat ≤ 5}
    (h : PileMerged g p i bound) (x : UInt8) :
    PileMerged g { p with freePiles := x } i bound :=
  ⟨h.merge_complete, h.flute_maximal, h.busyAces_complete⟩

/-- Freeness is monotone under pointwise pile-depth decrease: `SolverCleanupPile`
    only ever lowers depths, so no card loses its freeness. -/
theorem isFreeCard_mono {g : Globals} {p p' : SolverPosType} {c : UInt8}
    (hdepth : ∀ i : Fin 10, (p'.pileDepth.get i).toNat ≤
      (p.pileDepth.get i).toNat)
    (h : isFreeCard g p c) : isFreeCard g p' c := by
  unfold isFreeCard at h ⊢
  simp only [] at h ⊢
  by_cases h10 : (if h64 : c.toNat < 64 then g.card2pile.get ⟨c.toNat, h64⟩ else 0).toNat < 10
  · rw [dif_pos h10] at h ⊢
    exact le_trans (hdepth ⟨_, h10⟩) h
  · rw [dif_neg h10] at h ⊢
    exact h

/-- The flute normalization of the pile about to be cleaned: `pileFlute[pile] := 1`.
    Callers of `SolverCleanupPile`/`SolverRemoveFlute` leave a stale
    `pileFlute[pile]` behind (the function never reads it and overwrites it at
    the end); their preconditions are stated about this normalized position. -/
def fluteNorm (pile : UInt32) (hpile : pile.toNat < 10) (p : SolverPosType) : SolverPosType :=
  { p with pileFlute := p.pileFlute.set pile.toNat 1 hpile }

/-- **Midpoint predicate for `SolverCleanupPile`/`SolverRemoveFlute` (Merged
    layer).**  All invariants hold except: `freePiles` does not yet count `pile`
    (whose depth may just have reached 0), and the `PileMerged` clauses
    (`merge_complete`/`flute_maximal`/`busyAces_complete`) are missing for `pile`
    itself — cleanup re-establishes them and increments `freePiles` when it
    empties the pile. -/
def CleanupReady (g : Globals) (p : SolverPosType) (pile : UInt32) : Prop :=
  ∃ hnf : SolverInvBase g p,
  (∀ j : Fin 10, j.val ≠ pile.toNat → PileMerged g p j (hnf.pileDepth_bound j)) ∧
  p.freePiles.toInt = ((List.finRange 10).countP
    (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) : Nat)

/-- `a - (b + c) = a - b - c` for `UInt32` (core has no `sub_sub`). -/
theorem uint32_sub_add (a b c : UInt32) : a - (b + c) = a - b - c := by
  simp only [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.add_assoc]

/-- Updating one pile's depth changes the hash dot-product by exactly that
    pile's coefficient times the depth change (additive form, so no wraparound
    conditions are needed). -/
theorem hash_foldl_set (v : Vector UInt8 10) (k : Nat) (hk : k < 10) (x : UInt8) :
    ((List.finRange 10).foldl
      (fun acc i => acc + pileHashes.get i * ((v.set k x hk).get i).toInt.toNat.toUInt32) 0)
      + (pileHashes[k]'hk) * ((v[k]'hk).toInt.toNat.toUInt32) =
    ((List.finRange 10).foldl
      (fun acc i => acc + pileHashes.get i * (v.get i).toInt.toNat.toUInt32) 0)
      + (pileHashes[k]'hk) * (x.toInt.toNat.toUInt32) := by
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    pileHashes, Vector.get, Vector.getElem_toArray, Fin.isValue, Fin.val_cast, Fin.val_zero,
    Fin.val_succ, Nat.reduceAdd, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, Vector.getElem_set]
  interval_cases k <;>
    simp only [reduceIte, Nat.reduceEqDiff, UInt32.zero_add] <;>
    ac_rfl

/-- `(L.set n a).sum + L[n] = L.sum + a`: the additive "isolate one term" fact
    for `List Nat`, used to relate `usedSpace_def`'s three sums before/after a
    single-index `Vector.set`. -/
private theorem list_sum_set_eq (L : List Nat) (n : Nat) (hn : n < L.length) (a : Nat) :
    (L.set n a).sum + L[n] = L.sum + a := by
  have h1 := List.sum_set L n a
  rw [if_pos hn] at h1
  have h2 : L.sum = (L.take n).sum + L[n] + (L.drop (n + 1)).sum := by
    conv_lhs => rw [← List.take_append_drop n L]
    rw [List.sum_append, List.drop_eq_getElem_cons hn, List.sum_cons]
    omega
  omega

/-- `List.zipWith` commutes with simultaneously `.set`-ing the same index in
    both input lists. -/
private theorem zipWith_set_eq {α β γ : Type} (L1 : List α) (L2 : List β) (g : α → β → γ)
    (k : Nat) (a : α) (b : β) (hlen : L1.length = L2.length) :
    List.zipWith g (L1.set k a) (L2.set k b) = (List.zipWith g L1 L2).set k (g a b) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    by_cases hik : i = k
    · subst hik; simp
    · simp [List.getElem_set_ne (Ne.symm hik)]

/-- Updating one pile's depth changes `usedSpace_def`'s `ΣDepth` sum by exactly
    that pile's `toNatClampNeg` change (additive form). -/
theorem depth_sum_foldl_set (d : Vector UInt8 10) (k : Nat) (hk : k < 10) (xd : UInt8) :
    (d.set k xd hk).toList.foldl (fun acc x => acc + x.toInt.toNat) 0 + (d[k]'hk).toInt.toNat =
    d.toList.foldl (fun acc x => acc + x.toInt.toNat) 0 + xd.toInt.toNat := by
  rw [show (d.set k xd hk).toList.foldl (fun acc x => acc + x.toInt.toNat) 0
        = ((d.set k xd hk).toList.map (fun x => x.toInt.toNat)).foldl (·+·) 0 from
      (List.foldl_map ..).symm, show d.toList.foldl (fun acc x => acc + x.toInt.toNat) 0
        = (d.toList.map (fun x => x.toInt.toNat)).foldl (·+·) 0 from (List.foldl_map ..).symm, Vector.toList_set, List.map_set, ← List.sum_eq_foldl_nat, ← List.sum_eq_foldl_nat]
  have hk' : k < (d.toList.map (fun x => x.toInt.toNat)).length := by
    rw [List.length_map, Vector.length_toList]; omega
  have h := list_sum_set_eq (d.toList.map (fun x => x.toInt.toNat)) k hk' xd.toInt.toNat
  rw [List.getElem_map, Vector.getElem_toList] at h
  exact h

/-- Updating one pile's depth AND flute simultaneously changes `usedSpace_def`'s
    `ΣFluteTerm` sum by exactly that pile's term change (additive form). -/
theorem usedSpace_term_foldl_set (d : Vector UInt8 10) (fl : Vector UInt8 10)
    (k : Nat) (hk : k < 10) (xd : UInt8) (xf : UInt8) :
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        (d.set k xd hk).toList (fl.set k xf hk).toList).foldl (·+·) 0
      + (if (d[k]'hk) ≠ (0 : UInt8) then (fl[k]'hk).toNat - 1 else 0) =
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        d.toList fl.toList).foldl (·+·) 0
      + (if xd ≠ (0 : UInt8) then xf.toNat - 1 else 0) := by
  rw [Vector.toList_set, Vector.toList_set]
  have hlen : d.toList.length = fl.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]
  rw [zipWith_set_eq d.toList fl.toList _ k xd xf hlen, ← List.sum_eq_foldl_nat, ← List.sum_eq_foldl_nat]
  have hk' : k < (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
      d.toList fl.toList).length := by
    rw [List.length_zipWith, Vector.length_toList, Vector.length_toList]; omega
  have h := list_sum_set_eq
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0) d.toList fl.toList)
    k hk' (if xd ≠ (0 : UInt8) then xf.toNat - 1 else 0)
  rw [List.getElem_zipWith] at h
  rw [Vector.getElem_toList, Vector.getElem_toList] at h
  exact h

/-- Updating one entry of `aces` changes `usedSpace_def`'s `ΣAces` sum by
    exactly that entry's `VALUE`-of-`toUInt8` change (additive form) — the
    `aces`-analogue of `depth_sum_foldl_set`, needed when the foundation walk
    (`SolverMoveAces`, `cardDepth == 0` case) writes a new value into
    `aces[suit]`. -/
theorem aces_sum_foldl_set (v : Vector UInt8 4) (k : Nat) (hk : k < 4) (x : UInt8) :
    (v.set k x hk).toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 +
        (VALUE (v[k]'hk)).toNat =
      v.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 +
        (VALUE x).toNat := by
  rw [show (v.set k x hk).toList.foldl (fun acc a => acc + (VALUE a).toNat) 0
        = ((v.set k x hk).toList.map (fun a => (VALUE a).toNat)).foldl (·+·) 0 from
      (List.foldl_map ..).symm, show v.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0
        = (v.toList.map (fun a => (VALUE a).toNat)).foldl (·+·) 0 from (List.foldl_map ..).symm, Vector.toList_set, List.map_set, ← List.sum_eq_foldl_nat, ← List.sum_eq_foldl_nat]
  have hk' : k < (v.toList.map (fun a => (VALUE a).toNat)).length := by
    rw [List.length_map, Vector.length_toList]; omega
  have h := list_sum_set_eq (v.toList.map (fun a => (VALUE a).toNat)) k hk'
    (VALUE x).toNat
  rw [List.getElem_map, Vector.getElem_toList] at h
  exact h

/-- `Vector.ext` restated with `Fin`-indexed `.get` (matching the shape of the
    field-access facts established throughout this file), avoiding the
    raw-index/proof-irrelevance friction of the primed `[i]'hi` form. -/
theorem vector_ext_get {α : Type} {n : Nat} (v w : Vector α n)
    (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

/-- Index bound for the merge guard's internal `pos2card` read (`depth − 2`),
    reusable at every step of the merge-realness chain below. -/
private theorem merge_step_idx_bound {x : Int32} (hgt : 1 < x) (hle : x.toInt ≤ 5) :
    (x - 2).toUInt32.toNat < 5 ∧ (x - 2).toInt = x.toInt - 2 := by
  have hgt' : (1 : Int) < x.toInt := by
    rw [Int32.lt_iff_toInt_lt, Int32.toInt_one] at hgt; exact hgt
  have h2le : (2 : Int32) ≤ x := by
    rw [Int32.le_iff_toInt_le, show ((2 : Int32).toInt = 2) from by decide]; omega
  have hsub2 : (x - 2).toInt = x.toInt - 2 := by
    rw [Int32.toInt_sub_of_le _ _ (by decide) h2le, show ((2 : Int32).toInt = 2) from by decide]
  have hnn : (0 : Int32) ≤ x - 2 := by
    rw [Int32.le_iff_toInt_le, hsub2, show ((0 : Int32).toInt = 0) from by decide]; omega
  refine ⟨?_, hsub2⟩
  rw [Int32.toNat_toUInt32_of_le hnn]
  show (x - 2).toInt.toNat < 5
  omega

/-- `(d0 - ofNat i).toInt = d0.toInt - i` for `i` within `d0`'s range, wrap-free. -/
theorem depth_sub_ofNat_eq {d0 : Int32} {i : Nat}
    (hd0 : d0.toInt ≤ 5) (hi : (i : Int) ≤ d0.toInt) :
    (d0 - Int32.ofNat i).toInt = d0.toInt - i := by
  have hiofI : (Int32.ofNat i).toInt = (i : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [Int32.toInt_sub_of_le _ _
    (by rw [Int32.le_iff_toInt_le, hiofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
    (by rw [Int32.le_iff_toInt_le, hiofI]; omega), hiofI]

/-- `(d0 - ofNat i - 1).toInt = d0.toInt - i - 1`, wrap-free (one more subtraction
    layered onto `depth_sub_ofNat_eq`, reused for "the slot vacated by merge step
    `i`" index computations). -/
theorem depth_sub_ofNat_sub_one_eq {d0 : Int32} {i : Nat}
    (hd0 : d0.toInt ≤ 5) (hi : (i : Int) + 1 ≤ d0.toInt) :
    (d0 - Int32.ofNat i - 1).toInt = d0.toInt - i - 1 := by
  have h1 : (d0 - Int32.ofNat i).toInt = d0.toInt - i := depth_sub_ofNat_eq hd0 (by omega)
  rw [Int32.toInt_sub_of_le _ _ (by decide)
    (by rw [Int32.le_iff_toInt_le, h1, show ((1 : Int32).toInt = 1) from by decide]; omega),
    show ((1 : Int32).toInt = 1) from by decide, h1]

/-- `(d0 - ofNat i - 2).toInt = d0.toInt - i - 2`, wrap-free (the "two below the
    boundary" counterpart of `depth_sub_ofNat_sub_one_eq`, needed for
    `merge_complete`'s own index). -/
theorem depth_sub_ofNat_sub_two_eq {d0 : Int32} {i : Nat}
    (hd0 : d0.toInt ≤ 5) (hi : (i : Int) + 2 ≤ d0.toInt) :
    (d0 - Int32.ofNat i - 2).toInt = d0.toInt - i - 2 := by
  have h1 : (d0 - Int32.ofNat i).toInt = d0.toInt - i := depth_sub_ofNat_eq hd0 (by omega)
  rw [Int32.toInt_sub_of_le _ _ (by decide)
    (by rw [Int32.le_iff_toInt_le, h1, show ((2 : Int32).toInt = 2) from by decide]; omega),
    show ((2 : Int32).toInt = 2) from by decide, h1]

/-- `(n - 1).toUInt32 = (n : UInt32) - 1` for a small nonzero `n` — the
    `UInt32.ofNat` analogue of ordinary `Nat` decrement, needed to match
    `hash_foldl_set`'s `UInt32`-cast replacement term against the pile-depth
    decrement's own `Nat.sub`. -/
private theorem uint32_ofNat_sub_one {n : Nat} (hn : 1 ≤ n) (hlt : n < 2 ^ 32) :
    (n - 1 : Nat).toUInt32 = n.toUInt32 - 1 := by
  have h4 : n.toUInt32.toNat = n := by rw [UInt32.toNat_ofNat']; omega
  have h1 : (n - 1 : Nat).toUInt32.toNat = n - 1 := by
    rw [UInt32.toNat_ofNat']; omega
  have h3 : (1 : UInt32).toNat = 1 := by decide
  have h2 : (n.toUInt32 - 1).toNat = n.toUInt32.toNat - (1 : UInt32).toNat := by
    apply UInt32.toNat_sub_of_le
    rw [UInt32.le_iff_toNat_le, h3, h4]; omega
  apply UInt32.toNat_inj.mp
  rw [h1, h2, h3, h4]

/-- `x.toInt = x.toNat` for a `UInt8` `x` known to stay under `128`
    (so the signed cast doesn't wrap negative).  Reused everywhere a UInt8
    card value needs to be compared as a plain integer (`haces_lt_B`-style
    arguments) — `Int.bmod_eq_of_le`'s "no wraparound" range is `[0, 128)`. -/
theorem uint8_toInt8_toInt_of_lt128 {x : UInt8} (hx : x.toNat < 128) :
    x.toInt = (x.toNat : Int) := rfl

/-- `x.toInt = x.toNat` for a nonnegative `UInt8` `x`: the unsigned
    reinterpretation just reads off the (already-nonnegative) value.  Paired
    with `uint8_toInt8_toInt_of_lt128` to compare an `UInt8` field (e.g.
    `aces`/`kings`) against a plain `UInt8` card byte via `UInt8.lt_iff_toInt_lt`/
    `UInt8.le_iff_toInt_le`. -/
theorem int8_toInt_eq_toUInt8_toNat_of_nonneg {x : UInt8} (hx : (0 : UInt8) ≤ x) :
    x.toInt = (x.toNat : Int) := rfl

/-- **Split a flute-interior offset `j` (`0 < j.toNat < 1+m+f`) into either a
    merge-absorbed card (`j.toNat ≤ m`, giving `B+m-j = B+k` for some `k < m`)
    or a freed-predecessor card (`j.toNat > m`, giving `B+m-j = B-l` for some
    `1 ≤ l ≤ f`).**  Shared by `flute_cards_free`/`flute_not_aces` (own-pile
    case): both need exactly this case split before invoking their respective
    per-card fact (`hfree_interior`/`hfree_freed`, or `haces_lt_Bk`/`hffree`). -/
theorem flute_offset_split (B : UInt8) (m f : Nat) (hBrange : B.toNat ≤ 61)
    (hm4 : m ≤ 4) (hf_le : f ≤ B.toNat - 1) (j : UInt8) (hj0 : 0 < j.toNat)
    (hjmf : j.toNat < 1 + m + f) :
    (∃ k, k < m ∧ B + UInt8.ofNat m - j = B + UInt8.ofNat k) ∨
    (∃ l, 1 ≤ l ∧ l ≤ f ∧ B + UInt8.ofNat m - j = B - UInt8.ofNat l) := by
  have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
  have hlt : B.toNat + m < 256 := by omega
  have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
    rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt]
  have hjB : j ≤ B + UInt8.ofNat m := by
    rw [UInt8.le_iff_toNat_le, hBmB]; omega
  by_cases hjle : j.toNat ≤ m
  · left
    refine ⟨m - j.toNat, by omega, ?_⟩
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hjB]
    have hkB : (UInt8.ofNat (m - j.toNat)).toNat = m - j.toNat := by
      rw [UInt8.toNat_ofNat']; omega
    have hltk : B.toNat + (m - j.toNat) < 256 := by omega
    have hBkB : (B + UInt8.ofNat (m - j.toNat)).toNat = B.toNat + (m - j.toNat) := by
      rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hltk]
    rw [hBmB, hBkB]
    omega
  · right
    refine ⟨j.toNat - m, by omega, by omega, ?_⟩
    apply UInt8.toNat_inj.mp
    have hlB : (UInt8.ofNat (j.toNat - m)).toNat = j.toNat - m := by
      rw [UInt8.toNat_ofNat']; omega
    have hlB' : UInt8.ofNat (j.toNat - m) ≤ B := by
      rw [UInt8.le_iff_toNat_le, hlB]; omega
    rw [UInt8.toNat_sub_of_le _ _ hjB, UInt8.toNat_sub_of_le _ _ hlB', hBmB, hlB]
    omega

/-- **Merge-realness chain.**  Under `m` merge-loop guard-satisfying steps from
    a real boundary card `B`, every intermediate top card `B + j` (`j ≤ m`) is
    real, with `VALUE(B+j) = VALUE(B) + j`.  Each guard step's equality
    `pos2card[pile][…] = card_j + 1` transports `WellFormedLayout.pos2card_real`
    onto `card_j + 1 = B + (j+1)`; `SUIT_succ`/`VALUE_succ` (licensed by the
    freshly-established `VALUE < 15`) carries the arithmetic relation forward. -/
theorem merge_real_chain (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g) (ph : UInt32) (B : UInt8) (d0 : Int32) (m : Nat)
    (p0 : SolverPosType) (hreal : IsRealCard B) (hd0 : d0.toInt ≤ 5)
    (hmlt : (m : Int) < d0.toInt)
    (hmg : ∀ i, i < m → mergeGuard g pile (mergeIter ph i ⟨B, d0, (1 : Int32), p0⟩)) :
    ∀ j, j ≤ m → IsRealCard (B + UInt8.ofNat j) ∧
      (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
    exact ⟨hreal, by omega⟩
  | succ j ih =>
    intro hjm
    obtain ⟨hrealj, hvalj⟩ := ih (by omega)
    obtain ⟨hgt, heq⟩ := hmg j (by omega)
    simp only [mergeIter_eq] at hgt heq
    have hdjle : (d0 - Int32.ofNat j).toInt = d0.toInt - j :=
      depth_sub_ofNat_eq hd0 (by omega)
    obtain ⟨h5, _⟩ := merge_step_idx_bound hgt (by omega)
    have heqB := heq hpile h5
    have hstep : B + UInt8.ofNat j + 1 = B + UInt8.ofNat (j + 1) := by
      rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
    rw [hstep] at heqB
    have hrealj1 : IsRealCard (B + UInt8.ofNat (j + 1)) := heqB ▸ hwf.pos2card_real _ _
    refine ⟨hrealj1, ?_⟩
    have hv15 : (VALUE (B + UInt8.ofNat j)).toNat < 15 := by
      have := hrealj.2.2; omega
    rw [← hstep, VALUE_succ _ hv15, hvalj]
    omega

/-- **Merge-realness chain, semantic form.**  Same conclusion as
    `merge_real_chain`, but from the *positions* directly (`hmcards`, as
    supplied by `preCleanupPile_pileBase_self`'s simplified interface) instead
    of unfolding raw `mergeGuard`s: since `hmcards` already hands us `B + k`'s
    *own* slot for every `k ≤ m` (not just incrementally via a loop
    invariant), realness at each step is immediate from `hwf.pos2card_real`,
    and the induction only has to carry the `VALUE` arithmetic forward. -/
theorem merge_real_chain' (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g) (B : UInt8) (d0 : Int32) (m : Nat)
    (hreal : IsRealCard B)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : (d0 - Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[(d0 - Int32.ofNat k - 1).toUInt32.toNat]'h5 =
        B + UInt8.ofNat k) :
    ∀ j, j ≤ m → IsRealCard (B + UInt8.ofNat j) ∧
      (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
    exact ⟨hreal, by omega⟩
  | succ j ih =>
    intro hjm
    obtain ⟨hrealj, hvalj⟩ := ih (by omega)
    obtain ⟨hidxj1, heqj1⟩ := hmcards (j + 1) hjm
    have hrealj1 : IsRealCard (B + UInt8.ofNat (j + 1)) := heqj1 ▸ hwf.pos2card_real _ _
    refine ⟨hrealj1, ?_⟩
    have hv15 : (VALUE (B + UInt8.ofNat j)).toNat < 15 := by
      have := hrealj.2.2; omega
    have hstep : B + UInt8.ofNat j + 1 = B + UInt8.ofNat (j + 1) := by
      rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
    rw [← hstep, VALUE_succ _ hv15, hvalj]
    omega

/-- **Merge-position chain.**  Under `m` merge-loop guard-satisfying steps from
    depth `d0`, for every `1 ≤ j ≤ m` the pile's slot at index `d0 - j - 1`
    (the slot vacated by the `j`-th merge step, now the flute interior) holds
    exactly `B + j`.  This is the guard's own equality at step `j - 1`,
    reindexed from "card produced at step `j-1`" to "card `B + j`". -/
theorem merge_pos_chain (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
    (ph : UInt32) (B : UInt8) (d0 : Int32) (m : Nat) (p0 : SolverPosType)
    (hd0 : d0.toInt ≤ 5) (hmlt : (m : Int) < d0.toInt)
    (hmg : ∀ i, i < m → mergeGuard g pile (mergeIter ph i ⟨B, d0, (1 : Int32), p0⟩)) :
    ∀ j, 1 ≤ j → j ≤ m → ∃ hidx : (d0 - Int32.ofNat j - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[(d0 - Int32.ofNat j - 1).toUInt32.toNat]'hidx
        = B + UInt8.ofNat j := by
  intro j hj1 hjm
  set i := j - 1 with hidef
  have hij : j = i + 1 := by omega
  have him : i < m := by omega
  obtain ⟨hgt, heq⟩ := hmg i him
  simp only [mergeIter_eq] at hgt heq
  have hdile : (d0 - Int32.ofNat i).toInt = d0.toInt - i := depth_sub_ofNat_eq hd0 (by omega)
  obtain ⟨h5, _⟩ := merge_step_idx_bound hgt (by omega)
  have heqB := heq hpile h5
  have hstep : B + UInt8.ofNat i + 1 = B + UInt8.ofNat (i + 1) := by
    rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
  rw [hstep] at heqB
  have hidxeq : (d0 - Int32.ofNat j - 1) = (d0 - Int32.ofNat i - 2) := by
    have e1 : Int32.ofNat j = Int32.ofNat i + 1 := by
      rw [hij, Int32.ofNat_add, show Int32.ofNat 1 = 1 from rfl]
    have e2 : (Int32.ofNat i + 1) + 1 = Int32.ofNat i + 2 := by
      rw [Int32.add_assoc]; congr 1
    rw [e1, Int32.sub_sub, Int32.sub_sub, e2]
  rw [hidxeq]
  exact ⟨h5, by rw [hij]; exact heqB⟩

/-- If a card's `card2depth` entry is at least its own pile's current live
    depth (read via `card2pile`), the card is free.  General shape of the
    `isFreeCard`-unfolding used to read freeness off a `freedGuard`/`mergeGuard`
    fact (mirrors the inline argument in `freed_below_other_boundary`). -/
theorem isFree_of_card2depth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (h : (g.card2depth[c.toNat]'hc64).toNat ≥
      (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
        (hwf.card2pile_lt c.toNat hc64)).toInt32.toInt.toNat) :
    isFreeCard g game c := by
  unfold isFreeCard
  simp only [dif_pos hc64]
  have hpileEq' : g.card2pile.get ⟨c.toNat, hc64⟩ = cardPile g c := by
    unfold cardPile; simp [hc64]
  have hp64 : (cardPile g c).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt c.toNat hc64
  simp only [hpileEq', dif_pos hp64]
  have hpileEqGE : (g.card2pile[c.toNat]'hc64).toNat = (cardPile g c).toNat := by
    have : g.card2pile[c.toNat]'hc64 = g.card2pile.get ⟨c.toNat, hc64⟩ := rfl
    rw [this, hpileEq']
  have hdepthEqGE : (g.card2depth[c.toNat]'hc64).toNat =
      (g.card2depth.get ⟨c.toNat, hc64⟩).toNat := by
    have : g.card2depth[c.toNat]'hc64 = g.card2depth.get ⟨c.toNat, hc64⟩ := rfl
    rw [this]
  have keyEqV : game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
      (hwf.card2pile_lt c.toNat hc64) = game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩ := by
    congr 1
  have keyEq : (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
      (hwf.card2pile_lt c.toNat hc64)).toInt32.toInt.toNat =
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat := by
    rw [keyEqV]
    show (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt32.toInt.toNat =
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat
    rw [UInt8.toInt_toInt32]
  show (g.card2depth.get ⟨c.toNat, hc64⟩).toNat ≥
    (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat
  rw [← hdepthEqGE, ← keyEq]
  exact h

/-- Convenience form of `isFree_of_card2depth_ge` stated via `cardPile`/`cardDepth`
    directly — what `WellFormedLayout.round_trip_inv` produces. -/
theorem isFree_of_cardDepth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hp64 : (cardPile g c).toNat < 10)
    (h : (cardDepth g c).toNat ≥ (game.pileDepth[(cardPile g c).toNat]'hp64).toNat) :
    isFreeCard g game c := by
  apply isFree_of_card2depth_ge g game hwf c hc64
  have e1 : (g.card2depth[c.toNat]'hc64) = cardDepth g c := by
    unfold cardDepth; rw [dif_pos hc64]; rfl
  have e2 : (g.card2pile[c.toNat]'hc64) = cardPile g c := by
    unfold cardPile; rw [dif_pos hc64]; rfl
  have e3 : game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'(hwf.card2pile_lt c.toNat hc64)
      = game.pileDepth[(cardPile g c).toNat]'hp64 := by
    congr 1
    rw [e2]
  rw [e1, e3]
  show (cardDepth g c).toNat ≥ (game.pileDepth[(cardPile g c).toNat]'hp64).toInt32.toInt.toNat
  rw [UInt8.toInt_toInt32]
  exact h

/-- Converse of `isFree_of_card2depth_ge`: unfolds a KNOWN `isFreeCard` fact
    back into the raw `card2depth`/`card2pile` inequality (the "unfold +
    `dif_pos`" steps run the same either as a goal or as a hypothesis). -/
theorem isFree_to_card2depth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hfree : isFreeCard g game c) :
    (g.card2depth[c.toNat]'hc64).toNat ≥
      (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
        (hwf.card2pile_lt c.toNat hc64)).toNat := by
  unfold isFreeCard at hfree
  simp only [dif_pos hc64] at hfree
  have hpileEq' : g.card2pile.get ⟨c.toNat, hc64⟩ = cardPile g c := by
    unfold cardPile; simp [hc64]
  have hp64 : (cardPile g c).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt c.toNat hc64
  simp only [hpileEq', dif_pos hp64] at hfree
  have hpileEqGE : (g.card2pile[c.toNat]'hc64).toNat = (cardPile g c).toNat := by
    have : g.card2pile[c.toNat]'hc64 = g.card2pile.get ⟨c.toNat, hc64⟩ := rfl
    rw [this, hpileEq']
  have hdepthEqGE : (g.card2depth[c.toNat]'hc64).toNat =
      (g.card2depth.get ⟨c.toNat, hc64⟩).toNat := by
    have : g.card2depth[c.toNat]'hc64 = g.card2depth.get ⟨c.toNat, hc64⟩ := rfl
    rw [this]
  have keyEq : (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
      (hwf.card2pile_lt c.toNat hc64)).toNat =
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toNat := by
    have hidx : (⟨(g.card2pile[c.toNat]'hc64).toNat, hwf.card2pile_lt c.toNat hc64⟩ : Fin 10) =
        ⟨(cardPile g c).toNat, hp64⟩ := Fin.ext hpileEqGE
    show (game.pileDepth.get ⟨(g.card2pile[c.toNat]'hc64).toNat,
      hwf.card2pile_lt c.toNat hc64⟩).toNat = _
    rw [hidx]
  rw [← hdepthEqGE, ← keyEq] at hfree
  exact hfree

/-- Convenience form of `isFree_to_card2depth_ge` stated via `cardPile`/
    `cardDepth` directly. -/
theorem isFree_to_cardDepth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hp64 : (cardPile g c).toNat < 10) (hfree : isFreeCard g game c) :
    (cardDepth g c).toNat ≥ (game.pileDepth[(cardPile g c).toNat]'hp64).toNat := by
  have hraw := isFree_to_card2depth_ge g game hwf c hc64 hfree
  have e1 : (g.card2depth[c.toNat]'hc64) = cardDepth g c := by
    unfold cardDepth; rw [dif_pos hc64]; rfl
  have e2 : (g.card2pile[c.toNat]'hc64) = cardPile g c := by
    unfold cardPile; rw [dif_pos hc64]; rfl
  have e3 : game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'(hwf.card2pile_lt c.toNat hc64)
      = game.pileDepth[(cardPile g c).toNat]'hp64 := by
    congr 1
    rw [e2]
  rwa [e1, e3] at hraw

end SolverSpec
