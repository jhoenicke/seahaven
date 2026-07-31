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
  pile.toNat < 10 ∧ toPile.toNat ≤ 14 ∧ (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toInt.toNat > 0

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
    (h : PileBase g p i) (x : Int8) : PileBase g { p with freePiles := x } i :=
  ⟨h.pileDepth_bound, h.pileDepth_nonneg, h.flute_pos, h.flute_empty,
   h.flute_cards_free, h.flute_not_aces⟩

private theorem pileBase_setBusyAces {g : Globals} {p : SolverPosType} {i : Fin 10}
    (h : PileBase g p i) (y : UInt8) : PileBase g { p with busyAces := p.busyAces ||| y } i :=
  ⟨h.pileDepth_bound, h.pileDepth_nonneg, h.flute_pos, h.flute_empty,
   h.flute_cards_free, h.flute_not_aces⟩

/-- The base layer ignores `freePiles`, so it transfers across a `freePiles` write. -/
private theorem nf_setFreePiles {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (x : Int8) : SolverInvBase g { p with freePiles := x } :=
  ⟨fun i => pileBase_setFreePiles (h.pileBase i) x,
   fun s => ⟨h.aces_kings_valid s, h.foundation_cards_free s, h.foundation_maximal_weak s, h.king_frontier s⟩,
   h.hash_def, h.usedSpace_def, h.busyAces_lt16⟩

/-- Setting more bits in a bitmask can't clear an already-set bit. -/
private theorem uint8_and_ne_zero_of_or_left {a b c : UInt8} (h : a &&& c ≠ 0) :
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
private theorem uint8_and_ne_zero_of_or_right {a b c : UInt8} (h : b &&& c ≠ 0) :
    (a ||| b) &&& c ≠ 0 := by
  rw [UInt8.or_comm]
  exact uint8_and_ne_zero_of_or_left h

/-- A single shifted bit, ANDed with itself, is nonzero (as long as the shift
    doesn't push it out of the byte). -/
private theorem uint8_shift_self_ne_zero (x : UInt8) (hx : x.toNat < 4) :
    ((1 : UInt8) <<< x) &&& ((1 : UInt8) <<< x) ≠ 0 := by
  have hxe : x = UInt8.ofNat x.toNat := by simp
  rw [hxe]
  set b := x.toNat with hb
  clear_value b
  interval_cases b <;> decide

/-- `a ||| b < 16` whenever both operands are, since OR-ing two 4-bit values
    (`< 2^4`) stays `< 2^4` (`Nat.or_lt_two_pow`). -/
private theorem uint8_or_lt16_of_lt16 {a b : UInt8} (ha : a < 16) (hb : b < 16) :
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
private theorem nf_setBusyAces {g : Globals} {p : SolverPosType}
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
private theorem pm_setFreePiles {g : Globals} {p : SolverPosType} {i : Fin 10}
    {bound : (p.pileDepth.get i).toInt.toNat ≤ 5}
    (h : PileMerged g p i bound) (x : Int8) :
    PileMerged g { p with freePiles := x } i bound :=
  ⟨h.merge_complete, h.flute_maximal, h.busyAces_complete⟩

/-- Freeness is monotone under pointwise pile-depth decrease: `SolverCleanupPile`
    only ever lowers depths, so no card loses its freeness. -/
theorem isFreeCard_mono {g : Globals} {p p' : SolverPosType} {c : UInt8}
    (hdepth : ∀ i : Fin 10, (p'.pileDepth.get i).toInt.toNat ≤
      (p.pileDepth.get i).toInt.toNat)
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
private theorem uint32_sub_add (a b c : UInt32) : a - (b + c) = a - b - c := by
  simp only [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.add_assoc]

/-- Updating one pile's depth changes the hash dot-product by exactly that
    pile's coefficient times the depth change (additive form, so no wraparound
    conditions are needed). -/
private theorem hash_foldl_set (v : Vector Int8 10) (k : Nat) (hk : k < 10) (x : Int8) :
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
private theorem depth_sum_foldl_set (d : Vector Int8 10) (k : Nat) (hk : k < 10) (xd : Int8) :
    (d.set k xd hk).toList.foldl (fun acc x => acc + x.toInt.toNat) 0 + (d[k]'hk).toInt.toNat =
    d.toList.foldl (fun acc x => acc + x.toInt.toNat) 0 + xd.toInt.toNat := by
  rw [show (d.set k xd hk).toList.foldl (fun acc x => acc + x.toInt.toNat) 0
        = ((d.set k xd hk).toList.map (fun x => x.toInt.toNat)).foldl (·+·) 0 from
      (List.foldl_map ..).symm,
    show d.toList.foldl (fun acc x => acc + x.toInt.toNat) 0
        = (d.toList.map (fun x => x.toInt.toNat)).foldl (·+·) 0 from (List.foldl_map ..).symm,
    Vector.toList_set, List.map_set, ← List.sum_eq_foldl_nat, ← List.sum_eq_foldl_nat]
  have hk' : k < (d.toList.map (fun x => x.toInt.toNat)).length := by
    rw [List.length_map, Vector.length_toList]; omega
  have h := list_sum_set_eq (d.toList.map (fun x => x.toInt.toNat)) k hk' xd.toInt.toNat
  rw [List.getElem_map, Vector.getElem_toList] at h
  exact h

/-- Updating one pile's depth AND flute simultaneously changes `usedSpace_def`'s
    `ΣFluteTerm` sum by exactly that pile's term change (additive form). -/
private theorem usedSpace_term_foldl_set (d : Vector Int8 10) (fl : Vector UInt8 10)
    (k : Nat) (hk : k < 10) (xd : Int8) (xf : UInt8) :
    (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        (d.set k xd hk).toList (fl.set k xf hk).toList).foldl (·+·) 0
      + (if (d[k]'hk) ≠ (0 : Int8) then (fl[k]'hk).toNat - 1 else 0) =
    (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        d.toList fl.toList).foldl (·+·) 0
      + (if xd ≠ (0 : Int8) then xf.toNat - 1 else 0) := by
  rw [Vector.toList_set, Vector.toList_set]
  have hlen : d.toList.length = fl.toList.length := by
    rw [Vector.length_toList, Vector.length_toList]
  rw [zipWith_set_eq d.toList fl.toList _ k xd xf hlen, ← List.sum_eq_foldl_nat,
    ← List.sum_eq_foldl_nat]
  have hk' : k < (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
      d.toList fl.toList).length := by
    rw [List.length_zipWith, Vector.length_toList, Vector.length_toList]; omega
  have h := list_sum_set_eq
    (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0) d.toList fl.toList)
    k hk' (if xd ≠ (0 : Int8) then xf.toNat - 1 else 0)
  rw [List.getElem_zipWith] at h
  rw [Vector.getElem_toList, Vector.getElem_toList] at h
  exact h

/-- Updating one entry of `aces` changes `usedSpace_def`'s `ΣAces` sum by
    exactly that entry's `VALUE`-of-`toUInt8` change (additive form) — the
    `aces`-analogue of `depth_sum_foldl_set`, needed when the foundation walk
    (`SolverMoveAces`, `cardDepth == 0` case) writes a new value into
    `aces[suit]`. -/
private theorem aces_sum_foldl_set (v : Vector Int8 4) (k : Nat) (hk : k < 4) (x : Int8) :
    (v.set k x hk).toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 +
        (VALUE (v[k]'hk).toUInt8).toNat =
      v.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 +
        (VALUE x.toUInt8).toNat := by
  rw [show (v.set k x hk).toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0
        = ((v.set k x hk).toList.map (fun a => (VALUE a.toUInt8).toNat)).foldl (·+·) 0 from
      (List.foldl_map ..).symm,
    show v.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0
        = (v.toList.map (fun a => (VALUE a.toUInt8).toNat)).foldl (·+·) 0 from (List.foldl_map ..).symm,
    Vector.toList_set, List.map_set, ← List.sum_eq_foldl_nat, ← List.sum_eq_foldl_nat]
  have hk' : k < (v.toList.map (fun a => (VALUE a.toUInt8).toNat)).length := by
    rw [List.length_map, Vector.length_toList]; omega
  have h := list_sum_set_eq (v.toList.map (fun a => (VALUE a.toUInt8).toNat)) k hk'
    (VALUE x.toUInt8).toNat
  rw [List.getElem_map, Vector.getElem_toList] at h
  exact h

/-- `Vector.ext` restated with `Fin`-indexed `.get` (matching the shape of the
    field-access facts established throughout this file), avoiding the
    raw-index/proof-irrelevance friction of the primed `[i]'hi` form. -/
private theorem vector_ext_get {α : Type} {n : Nat} (v w : Vector α n)
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
private theorem depth_sub_ofNat_eq {d0 : Int32} {i : Nat}
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
private theorem depth_sub_ofNat_sub_one_eq {d0 : Int32} {i : Nat}
    (hd0 : d0.toInt ≤ 5) (hi : (i : Int) + 1 ≤ d0.toInt) :
    (d0 - Int32.ofNat i - 1).toInt = d0.toInt - i - 1 := by
  have h1 : (d0 - Int32.ofNat i).toInt = d0.toInt - i := depth_sub_ofNat_eq hd0 (by omega)
  rw [Int32.toInt_sub_of_le _ _ (by decide)
    (by rw [Int32.le_iff_toInt_le, h1, show ((1 : Int32).toInt = 1) from by decide]; omega),
    show ((1 : Int32).toInt = 1) from by decide, h1]

/-- `(d0 - ofNat i - 2).toInt = d0.toInt - i - 2`, wrap-free (the "two below the
    boundary" counterpart of `depth_sub_ofNat_sub_one_eq`, needed for
    `merge_complete`'s own index). -/
private theorem depth_sub_ofNat_sub_two_eq {d0 : Int32} {i : Nat}
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

/-- `x.toInt8.toInt = x.toNat` for a `UInt8` `x` known to stay under `128`
    (so the signed cast doesn't wrap negative).  Reused everywhere a UInt8
    card value needs to be compared as a plain integer (`haces_lt_B`-style
    arguments) — `Int.bmod_eq_of_le`'s "no wraparound" range is `[0, 128)`. -/
private theorem uint8_toInt8_toInt_of_lt128 {x : UInt8} (hx : x.toNat < 128) :
    x.toInt8.toInt = (x.toNat : Int) := by
  have h' : x.toInt8.toInt = ((x.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
    show x.toInt8.toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_bmod]
    rfl
  rw [UInt8.toUInt8_toInt8] at h'
  rw [h', Int.bmod_eq_of_le (by omega) (by omega)]

/-- `x.toInt = x.toUInt8.toNat` for a nonnegative `Int8` `x`: the unsigned
    reinterpretation just reads off the (already-nonnegative) value.  Paired
    with `uint8_toInt8_toInt_of_lt128` to compare an `Int8` field (e.g.
    `aces`/`kings`) against a plain `UInt8` card byte via `Int8.lt_iff_toInt_lt`/
    `Int8.le_iff_toInt_le`. -/
private theorem int8_toInt_eq_toUInt8_toNat_of_nonneg {x : Int8} (hx : (0 : Int8) ≤ x) :
    x.toInt = (x.toUInt8.toNat : Int) := by
  have h1 := Int8.toNat_toUInt8_of_le hx
  have h2 := Int8.toNat_toInt x
  have h3 : (0 : Int) ≤ x.toInt := by
    have := Int8.le_iff_toInt_le.mp hx
    rwa [Int8.toInt_zero] at this
  omega

/-- **Split a flute-interior offset `j` (`0 < j.toNat < 1+m+f`) into either a
    merge-absorbed card (`j.toNat ≤ m`, giving `B+m-j = B+k` for some `k < m`)
    or a freed-predecessor card (`j.toNat > m`, giving `B+m-j = B-l` for some
    `1 ≤ l ≤ f`).**  Shared by `flute_cards_free`/`flute_not_aces` (own-pile
    case): both need exactly this case split before invoking their respective
    per-card fact (`hfree_interior`/`hfree_freed`, or `haces_lt_Bk`/`hffree`). -/
private theorem flute_offset_split (B : UInt8) (m f : Nat) (hBrange : B.toNat ≤ 61)
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
private theorem merge_real_chain (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
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
private theorem merge_real_chain' (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
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
private theorem merge_pos_chain (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
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
private theorem isFree_of_card2depth_ge (g : Globals) (game : SolverPosType)
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
    rw [Int8.toInt_toInt32]
  show (g.card2depth.get ⟨c.toNat, hc64⟩).toNat ≥
    (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat
  rw [← hdepthEqGE, ← keyEq]
  exact h

/-- Convenience form of `isFree_of_card2depth_ge` stated via `cardPile`/`cardDepth`
    directly — what `WellFormedLayout.round_trip_inv` produces. -/
private theorem isFree_of_cardDepth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hp64 : (cardPile g c).toNat < 10)
    (h : (cardDepth g c).toNat ≥ (game.pileDepth[(cardPile g c).toNat]'hp64).toInt.toNat) :
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
  rw [Int8.toInt_toInt32]
  exact h

/-- Converse of `isFree_of_card2depth_ge`: unfolds a KNOWN `isFreeCard` fact
    back into the raw `card2depth`/`card2pile` inequality (the "unfold +
    `dif_pos`" steps run the same either as a goal or as a hypothesis). -/
private theorem isFree_to_card2depth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hfree : isFreeCard g game c) :
    (g.card2depth[c.toNat]'hc64).toNat ≥
      (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
        (hwf.card2pile_lt c.toNat hc64)).toInt32.toInt.toNat := by
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
  have keyEqV : game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
      (hwf.card2pile_lt c.toNat hc64) = game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩ := by
    congr 1
  have keyEq : (game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'
      (hwf.card2pile_lt c.toNat hc64)).toInt32.toInt.toNat =
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat := by
    rw [keyEqV]
    show (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt32.toInt.toNat =
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp64⟩).toInt.toNat
    rw [Int8.toInt_toInt32]
  rw [← hdepthEqGE, ← keyEq] at hfree
  exact hfree

/-- Convenience form of `isFree_to_card2depth_ge` stated via `cardPile`/
    `cardDepth` directly. -/
private theorem isFree_to_cardDepth_ge (g : Globals) (game : SolverPosType)
    (hwf : WellFormedLayout g) (c : UInt8) (hc64 : c.toNat < 64)
    (hp64 : (cardPile g c).toNat < 10) (hfree : isFreeCard g game c) :
    (cardDepth g c).toNat ≥ (game.pileDepth[(cardPile g c).toNat]'hp64).toInt.toNat := by
  have hraw := isFree_to_card2depth_ge g game hwf c hc64 hfree
  have e1 : (g.card2depth[c.toNat]'hc64) = cardDepth g c := by
    unfold cardDepth; rw [dif_pos hc64]; rfl
  have e2 : (g.card2pile[c.toNat]'hc64) = cardPile g c := by
    unfold cardPile; rw [dif_pos hc64]; rfl
  have e3 : game.pileDepth[(g.card2pile[c.toNat]'hc64).toNat]'(hwf.card2pile_lt c.toNat hc64)
      = game.pileDepth[(cardPile g c).toNat]'hp64 := by
    congr 1
    rw [e2]
  rw [e1, e3] at hraw
  rwa [Int8.toInt_toInt32] at hraw

/-- **`cleanupRunResult` only ever decreases `pileDepth`**, pointwise across all
    ten piles.  Piles other than `pile` are literally untouched (the function
    only ever writes `pileDepth[pile]`, in either branch); `pile`'s own depth
    either drops to `0` (lone-king branch) or to `d0 - m` (`m ≥ 0`, still within
    `Int8` range given `hd5`/`hm`, so no wraparound).  This is the building
    block for showing `PileBase`/`PileMerged` survive cleanup at every OTHER
    pile via `isFreeCard_mono`. -/
theorem cleanupRunResult_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt) (i : Fin 10) :
    ((cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2.pileDepth.get i).toInt.toNat ≤
      (p.pileDepth.get i).toInt.toNat := by
  have hd5' : ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt ≤ 5 := by
    rw [Int8.toInt_toInt32]; exact hd5
  have hm' : (m : Int) ≤ ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt := by
    rw [Int8.toInt_toInt32]; exact hm
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [depth_sub_ofNat_eq hd5' hm', Int8.toInt_toInt32]
  show (((cleanupRunResult pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2).pileDepth[i.val]'i.isLt).toInt.toNat ≤
    (p.pileDepth[i.val]'i.isLt).toInt.toNat
  simp only [cleanupRunResult]
  -- `pileDepth` doesn't depend on the `busyAces` branch at all, but that
  -- (unresolved) inner `if` still blocks `reduceIte` from reducing the OUTER
  -- (king) `if` unless it too is split — mirrors the `hk`/`hba` double split
  -- already used to discharge `cleanupPile_base` itself (its "Lone-king
  -- branch"/"No lone king" cases).
  by_cases hk : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1
      && VALUE (B + UInt8.ofNat m) == 13) = true
  · by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true
    · simp only [hk, hba, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [show (((0 : Int32).toInt8).toInt.toNat = 0) from rfl]
        exact Nat.zero_le _
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        rw [show (((0 : Int32).toInt8).toInt.toNat = 0) from rfl]
        exact Nat.zero_le _
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
  · rw [Bool.not_eq_true] at hk
    by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true
    · simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat ≤
          (p.pileDepth[pile.toNat]'hpile).toInt.toNat
        rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      by_cases hip : pile.toNat = i.val
      · simp only [← hip, Vector.getElem_set_self]
        show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat ≤
          (p.pileDepth[pile.toNat]'hpile).toInt.toNat
        rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega)]
        omega
      · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]

/-- Specialization of `cleanupRunResult_pileDepth_le` to piles `j ≠ pile`:
    `pileDepth[j]` is literally unchanged (not merely `≤`). -/
theorem cleanupRunResult_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2.pileDepth.get j =
      p.pileDepth.get j := by
  show ((cleanupRunResult pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2).pileDepth[j.val]'j.isLt =
    p.pileDepth[j.val]'j.isLt
  simp only [cleanupRunResult]
  by_cases hk : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1
      && VALUE (B + UInt8.ofNat m) == 13) = true
  · by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true
    · simp only [hk, hba, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
  · rw [Bool.not_eq_true] at hk
    by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true
    · simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]
    · rw [Bool.not_eq_true] at hba
      simp only [hk, hba, Bool.false_eq_true, reduceIte]
      rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `preCleanupPile`'s output `pileDepth` is pointwise `≤` the input, for every
    pile — same fact as `cleanupRunResult_pileDepth_le`, but for the simpler
    no-king write (a single `busyAces`-branch `if`, not a nested one, so no
    `hk` split is needed). -/
theorem preCleanupPile_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt) (i : Fin 10) :
    ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i).toInt.toNat ≤
      (p.pileDepth.get i).toInt.toNat := by
  have hd5' : ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt ≤ 5 := by
    rw [Int8.toInt_toInt32]; exact hd5
  have hm' : (m : Int) ≤ ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt := by
    rw [Int8.toInt_toInt32]; exact hm
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [depth_sub_ofNat_eq hd5' hm', Int8.toInt_toInt32]
  show (((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth[i.val]'i.isLt).toInt.toNat ≤
    (p.pileDepth[i.val]'i.isLt).toInt.toNat
  simp only [preCleanupPile]
  by_cases hip : pile.toNat = i.val
  · simp only [← hip, Vector.getElem_set_self]
    show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat ≤
      (p.pileDepth[pile.toNat]'hpile).toInt.toNat
    rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]

/-- Specialization to `j ≠ pile`: `pileDepth[j]` is literally unchanged. -/
theorem preCleanupPile_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j =
      p.pileDepth.get j := by
  show ((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth[j.val]'j.isLt =
    p.pileDepth[j.val]'j.isLt
  simp only [preCleanupPile]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- Specialization to `j ≠ pile`: `pileFlute[j]` is literally unchanged. -/
theorem preCleanupPile_pileFlute_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.get j =
      p.pileFlute.get j := by
  show ((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileFlute[j.val]'j.isLt =
    p.pileFlute[j.val]'j.isLt
  simp only [preCleanupPile]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `preCleanupPile` never touches `aces` (only `hash`/`usedSpace`/`busyAces`/
    `pileDepth`/`pileFlute`) — true in both `busyAces`-branches, so needs the
    same `hba` split as the field-projection lemmas above (the `if` on
    `busyAces` doesn't block `rfl` here — `aces` isn't in the goal's
    `simp only [preCleanupPile]`-unfolded form at all, but the two branches
    are still distinct terms until the `if` is resolved). -/
theorem preCleanupPile_aces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).aces = p.aces := by
  simp only [preCleanupPile]

/-- `preCleanupPile` never touches `kings`. -/
theorem preCleanupPile_kings_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat) :
    (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).kings = p.kings := by
  simp only [preCleanupPile]

/-- **`PileBase` survives `preCleanupPile` at every OTHER pile `j ≠ pile`.**
    `j`'s own depth/flute are literally unchanged
    (`preCleanupPile_pileDepth_eq_of_ne`/`_pileFlute_eq_of_ne`), so the
    "shape" clauses transfer directly; the freeness clause
    (`flute_cards_free`) transfers via `isFreeCard_mono` using
    `preCleanupPile_pileDepth_le` (depths only ever decrease, so anything free
    before stays free); `flute_not_aces` doesn't even mention freeness (`aces`
    is untouched by `preCleanupPile_aces_eq`), so it transfers verbatim. -/
theorem preCleanupPile_pileBase_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) (hb : PileBase g p j) :
    PileBase g (preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) j := by
  have hdeq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj
  have hfeq := preCleanupPile_pileFlute_eq_of_ne pile hpile B ph hs4 p m f j hj
  have haeq := preCleanupPile_aces_eq pile hpile B ph hs4 p m f
  have hdmono := preCleanupPile_pileDepth_le pile hpile B ph hs4 p m f hd5 hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeq]; exact hb.pileDepth_bound
  · rw [hdeq]; exact hb.pileDepth_nonneg
  · rw [hfeq]; exact hb.flute_pos
  · intro h0
    rw [hfeq]
    apply hb.flute_empty
    rwa [hdeq] at h0
  · intro k hdpos hk0 hklt
    have hdpos' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdpos
    have hklt' : k.toNat < (p.pileFlute.get j).toNat := by rw [← hfeq]; exact hklt
    have hidxEq : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    rw [hXeq]
    exact isFreeCard_mono hdmono (hb.flute_cards_free k hdpos' hk0 hklt')
  · intro hdpos
    have hdpos' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdpos
    have hidxEq : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `preCleanupPile`
    -- terms first (so the `let boundary` in the field's own statement gets
    -- expanded concretely, rather than staying an opaque `intro`-introduced
    -- local), THEN reduce those wrappers uniformly.
    show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat < 4,
      ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).aces.get
        ⟨(SUIT ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
            by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat, hs⟩).toUInt8.toNat +
        ((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.get j).toNat ≤
      UInt8.toNat ((g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)
    rw [hXeq, hfeq, haeq]
    intro hs
    exact hb.flute_not_aces hdpos' hs

/-- **`kingMove` always leaves the drained pile `PileClean`.**  No hypotheses
    on the entry position are needed at all: `kingMove` unconditionally sets
    `pileDepth[pile] := 0`/`pileFlute[pile] := 1`, and every `PileBase`/
    `PileMerged` clause for pile `i` is either immediate from `flute = 1` or
    vacuous once `depth = 0` (the `flute_cards_free`/`flute_not_aces`/
    `busyAces_complete` clauses all have `depth > 0` as a hypothesis; the
    `merge_complete`/`flute_maximal` clauses have a `depth ≤ 1`/`depth = 0`
    escape-hatch disjunct). -/
theorem kingMove_pileClean_self (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    PileClean g (kingMove pile hpile suit hs4 ph p) ⟨pile.toNat, hpile⟩ := by
  have hd0 : (kingMove pile hpile suit hs4 ph p).pileDepth.get ⟨pile.toNat, hpile⟩ = 0 := by
    show (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile = 0
    unfold kingMove
    rw [Vector.getElem_set_self]
    rfl
  have hf1 : (kingMove pile hpile suit hs4 ph p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
    show (kingMove pile hpile suit hs4 ph p).pileFlute[pile.toNat]'hpile = 1
    unfold kingMove
    rw [Vector.getElem_set_self]
    rfl
  exact {
    pileDepth_bound := by rw [hd0]; decide
    pileDepth_nonneg := by rw [hd0]; decide
    flute_pos := by rw [hf1]; decide
    flute_empty := fun _ => hf1
    flute_cards_free := fun _ hpos _ _ => absurd hpos (by rw [hd0]; decide)
    flute_not_aces := fun hpos _ => absurd hpos (by rw [hd0]; decide)
    merge_complete := Or.inl (by rw [hd0]; decide)
    flute_maximal := Or.inl hd0
    busyAces_complete := fun hpos => absurd hpos (by rw [hd0]; decide) }

-- ---------------------------------------------------------------------------
-- `kingMove` field-projection helpers, mirroring the `preCleanupPile` family
-- above (`preCleanupPile_pileDepth_eq_of_ne` etc.): `kingMove` only ever
-- writes `freePiles`/`usedSpace`/`kings[suit]`/`hash`/`pileDepth[pile]`/
-- `pileFlute[pile]`, so every other field/index is literally untouched.
-- ---------------------------------------------------------------------------

/-- `kingMove` never touches `aces`. -/
theorem kingMove_aces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).aces = p.aces := by
  simp only [kingMove]

/-- `kingMove` never touches `busyAces`. -/
theorem kingMove_busyAces_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).busyAces = p.busyAces := by
  simp only [kingMove]

/-- `kingMove` leaves `kings[s]` literally unchanged for every suit `s ≠ suit`. -/
theorem kingMove_kings_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (s : Fin 4) (hs : s.val ≠ suit.toUInt32.toNat) :
    (kingMove pile hpile suit hs4 ph p).kings.get s = p.kings.get s := by
  show (kingMove pile hpile suit hs4 ph p).kings[s.val]'s.isLt = p.kings[s.val]'s.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hs4 s.isLt (Ne.symm hs)]

/-- `kingMove`'s exact effect on `kings[suit]`: it drops by the drained
    pile's flute length. -/
theorem kingMove_kings_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).kings.get (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) =
      p.kings.get (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) -
        (p.pileFlute[pile.toNat]'hpile).toInt8 := by
  show (kingMove pile hpile suit hs4 ph p).kings[suit.toUInt32.toNat]'hs4 =
    p.kings[suit.toUInt32.toNat]'hs4 - (p.pileFlute[pile.toNat]'hpile).toInt8
  simp only [kingMove]
  rw [Vector.getElem_set_self]

/-- `kingMove` literally leaves `pileDepth[j]` unchanged at every `j ≠ pile`. -/
theorem kingMove_pileDepth_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (kingMove pile hpile suit hs4 ph p).pileDepth.get j = p.pileDepth.get j := by
  show (kingMove pile hpile suit hs4 ph p).pileDepth[j.val]'j.isLt = p.pileDepth[j.val]'j.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `kingMove` literally leaves `pileFlute[j]` unchanged at every `j ≠ pile`. -/
theorem kingMove_pileFlute_eq_of_ne (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) :
    (kingMove pile hpile suit hs4 ph p).pileFlute.get j = p.pileFlute.get j := by
  show (kingMove pile hpile suit hs4 ph p).pileFlute[j.val]'j.isLt = p.pileFlute[j.val]'j.isLt
  simp only [kingMove]
  rw [Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)]

/-- `kingMove` unconditionally sets `pileDepth[pile] := 0`. -/
theorem kingMove_pileDepth_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := by
  show (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile = 0
  simp only [kingMove]
  rw [Vector.getElem_set_self]
  rfl

/-- `kingMove` unconditionally sets `pileFlute[pile] := 1`. -/
theorem kingMove_pileFlute_self (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) :
    (kingMove pile hpile suit hs4 ph p).pileFlute.get (⟨pile.toNat, hpile⟩ : Fin 10) = 1 := by
  show (kingMove pile hpile suit hs4 ph p).pileFlute[pile.toNat]'hpile = 1
  simp only [kingMove]
  rw [Vector.getElem_set_self]
  rfl

/-- `kingMove` only ever decreases `pileDepth`, pointwise across all ten piles:
    `pile`'s own depth drops (to `0`); every other pile is literally untouched.
    The direct `kingMove` counterpart of `preCleanupPile_pileDepth_le`, needed
    for the same `isFreeCard_mono` transfer argument. -/
theorem kingMove_pileDepth_le (pile : UInt32) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (i : Fin 10) :
    ((kingMove pile hpile suit hs4 ph p).pileDepth.get i).toInt.toNat ≤
      (p.pileDepth.get i).toInt.toNat := by
  by_cases hip : i.val = pile.toNat
  · have hi : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hip
    rw [hi, kingMove_pileDepth_self]
    exact Nat.zero_le _
  · rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip]

/-- **A real card, other than the just-revealed boundary `K`, keeps its
    freeness status across `kingMove`.**  `kingMove` only ever changes
    `pileDepth[pile]` (from `1` to `0`), which only newly frees the single
    card sitting at depth-index `0` — exactly `K` (`pile`'s sole remaining
    boundary card, per `hd1`).  For any OTHER real card `C ≠ K`: if `C`'s home
    pile isn't `pile`, `kingMove` doesn't touch it at all; if it IS `pile`,
    `round_trip` would force `C` to sit at index `0` too (the only occupied
    slot), i.e. `C = K`, contradicting `hne`.  So `C`'s home pile is
    genuinely untouched either way, and `¬isFreeCard`/`isFreeCard` transfer by
    the usual `cardDepth`-vs-`pileDepth` bridge. -/
private theorem kingMove_not_free_of_ne (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g) (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32)
    (p : SolverPosType) (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (C : UInt8) (hCreal : IsRealCard C) (hne : C ≠ K) (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (kingMove pile hpile suit hs4 ph p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
  have hcp_ne : (cardPile g C).toNat ≠ pile.toNat := by
    intro hcp
    apply hne
    have hcd0 : (cardDepth g C).toNat = 0 := by
      by_contra hcdne
      apply hnfree
      apply isFree_of_cardDepth_ge g p hwf C hc64 hp64
      have hpdEq : p.pileDepth[(cardPile g C).toNat]'hp64 = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hpdEq, hd1]
      show (cardDepth g C).toNat ≥ ((1 : Int8)).toInt.toNat
      have h1 : ((1 : Int8)).toInt.toNat = 1 := by decide
      omega
    have hcd_lt5 : (cardDepth g C).toNat < 5 := by omega
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) =
        (⟨0, by omega⟩ : Fin 5) := Fin.ext hcd0
    rw [hcpEq, hcdEq] at hround
    rw [hKdef]
    exact hround.symm
  intro hfree
  have hge := isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
  have hpdEq' : (kingMove pile hpile suit hs4 ph p).pileDepth[(cardPile g C).toNat]'hp64 =
      p.pileDepth[(cardPile g C).toNat]'hp64 :=
    kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p ⟨(cardPile g C).toNat, hp64⟩ hcp_ne
  rw [hpdEq'] at hge
  exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)

/-- **`PileBase` survives `kingMove` at every OTHER pile `j ≠ pile`.**  Easier
    than the `preCleanupPile` counterpart (`preCleanupPile_pileBase_ne`):
    `kingMove` only ever drops `pile`'s own depth to `0` (never partially
    reveals a range the way `preCleanupPile`'s `m`/`f` do), so `j`'s own
    depth/flute are literally unchanged
    (`kingMove_pileDepth_eq_of_ne`/`_pileFlute_eq_of_ne`) and the freeness
    clause (`flute_cards_free`) transfers via `isFreeCard_mono` using
    `kingMove_pileDepth_le` (depths only ever decrease everywhere, so anything
    free before stays free); `flute_not_aces` doesn't even mention freeness
    (`aces` is untouched by `kingMove_aces_eq`), so it transfers verbatim. -/
theorem kingMove_pileBase_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (j : Fin 10) (hj : j.val ≠ pile.toNat) (hb : PileBase g p j) :
    PileBase g (kingMove pile hpile suit hs4 ph p) j := by
  have hdeq := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj
  have hfeq := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p j hj
  have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
  have hdmono := kingMove_pileDepth_le pile hpile suit hs4 ph p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeq]; exact hb.pileDepth_bound
  · rw [hdeq]; exact hb.pileDepth_nonneg
  · rw [hfeq]; exact hb.flute_pos
  · intro h0
    rw [hfeq]
    apply hb.flute_empty
    rwa [hdeq] at h0
  · intro k hdpos hk0 hklt
    have hdpos' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdpos
    have hklt' : k.toNat < (p.pileFlute.get j).toNat := by rw [← hfeq]; exact hklt
    have hidxEq : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toInt.toNat - 1, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    rw [hXeq]
    exact isFreeCard_mono hdmono (hb.flute_cards_free k hdpos' hk0 hklt')
  · intro hdpos
    have hdpos' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdpos
    have hidxEq : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hXeq : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toInt.toNat - 1, by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ =
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq
    -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `kingMove` terms
    -- first (so the `let boundary` in the field's own statement gets expanded
    -- concretely), THEN reduce those wrappers uniformly.
    show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
        ).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat < 4,
      ((kingMove pile hpile suit hs4 ph p).aces.get
        ⟨(SUIT ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
            ).pileDepth.get j).toInt.toNat - 1,
            by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat, hs⟩).toUInt8.toNat +
        ((kingMove pile hpile suit hs4 ph p).pileFlute.get j).toNat ≤
      UInt8.toNat ((g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
          ).pileDepth.get j).toInt.toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)
    rw [hXeq, hfeq, haeq]
    intro hs
    exact hb.flute_not_aces hdpos' hs

/-- **`PileMerged` survives `kingMove` at every OTHER pile `j ≠ pile`.**
    `merge_complete`/`busyAces_complete` are even more trivial than in the
    `preCleanupPile` counterpart (`preCleanupPile_pileMerged_ne`): `kingMove`
    doesn't touch `busyAces` at all (`kingMove_busyAces_eq`), and doesn't
    touch `pos2card`/`pileDepth[j]`/`pileFlute[j]`/`aces` for `j ≠ pile`
    (all literal equalities, not just index-shift ones).  `flute_maximal[j]`
    is the one clause needing real work, but it's EASIER here than in
    `preCleanupPile_pileMerged_ne`: `kingMove` reveals exactly ONE card
    (`pile`'s own boundary `K`, going from not-free to free as depth drops
    from `1` to `0`).  The key sub-argument, `kingMove_prevCard_ne_K`-style
    (inlined below): pile `j`'s own flute-bottom `prevCard` can never equal
    `K`, because `K` has `VALUE = 13` (`hVK13`) — if `prevCard = K` then
    `VALUE boundary_j = VALUE prevCard + pileFlute[j] = 13 + pileFlute[j] ≥ 14`
    (`flute_pos : pileFlute[j] ≥ 1`), contradicting `boundary_j`'s own
    realness (`VALUE ≤ 13`, from `pos2card_real`).  So `prevCard ≠ K`
    unconditionally, and `¬isFreeCard` transfers via `kingMove_not_free_of_ne`
    — no round-trip/uniqueness reasoning needed at all (simpler than
    `preCleanupPile_pileMerged_ne`'s `k`-indexed exclusion argument, which had
    to rule out a whole absorbed *range* rather than a single card). -/
theorem kingMove_pileMerged_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (hVK13 : (VALUE K).toNat = 13)
    (hak : ∀ s : Fin 4, SUIT (p.aces.get s).toUInt8 = s.val.toUInt8)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hb : PileBase g p j) (hpm : PileMerged g p j hb.pileDepth_bound) :
    PileMerged g (kingMove pile hpile suit hs4 ph p) j
      (by rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj]
          exact hb.pileDepth_bound) := by
  have hdeq := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p j hj
  have hfeq := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p j hj
  have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
  have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete: transfers verbatim (only reads `pos2card`/`pileDepth[j]`).
    have hidxEq2 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 2 =
        (p.pileDepth.get j).toInt.toNat - 2 := by rw [hdeq]
    have hidxEq1 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hX2 : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toInt.toNat - 2, by have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq2
    have hX1 : (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p).pileDepth.get j
          ).toInt.toNat - 1, by have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq1
    rw [hX2, hX1, hdeq]
    exact hpm.merge_complete
  · -- (3b) flute_maximal: the hard clause.
    by_cases hd0 : p.pileDepth.get j = 0
    · left
      rw [hdeq]
      exact hd0
    · have hdj : (p.pileDepth.get j).toInt.toNat > 0 := by
        have h1 := hb.pileDepth_nonneg
        rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at h1
        have h2 : (p.pileDepth.get j).toInt ≠ 0 := by
          intro hz
          apply hd0
          apply Int8.toInt_inj.mp
          rw [hz, show ((0 : Int8).toInt = 0) from rfl]
        omega
      right
      set boundaryNew := (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
            ).pileDepth.get j).toInt.toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew_def
      set prevCardNew := boundaryNew -
          (kingMove pile hpile suit hs4 ph p).pileFlute.get j with hprevCardNew_def
      show (∃ hs : (SUIT boundaryNew).toNat < 4,
          (kingMove pile hpile suit hs4 ph p).aces.get ⟨(SUIT boundaryNew).toNat, hs⟩ =
            prevCardNew.toInt8) ∨
        ¬ isFreeCard g (kingMove pile hpile suit hs4 ph p) prevCardNew
      set boundary := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
          by have := hb.pileDepth_bound; omega⟩ with hboundary_def
      set prevCard := boundary - p.pileFlute.get j with hprevCard_def
      have hidxEqB : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 1 =
          (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
      have hboundEq : boundaryNew = boundary := by
        rw [hboundaryNew_def, hboundary_def]
        congr 1
        exact Fin.ext hidxEqB
      have hprevEq : prevCardNew = prevCard := by
        rw [hprevCardNew_def, hprevCard_def, hboundEq, hfeq]
      rw [hboundEq, hprevEq, haeq]
      have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
      have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
      have hBDrange : boundary.toNat ≤ 61 := by
        have hsn := SUIT_toNat boundary
        have hvn := VALUE_toNat boundary
        have h1 := hrealBd.1; have h2 := hrealBd.2.1; have h3 := hrealBd.2.2
        omega
      have hflv : (p.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
        hb.flute_le_value hwf hak hdj
      have hVsn_bd := VALUE_toNat boundary
      have hSsn_bd := SUIT_toNat boundary
      have hfleB : p.pileFlute.get j ≤ boundary := by
        rw [UInt8.le_iff_toNat_le]
        have := Nat.mod_le boundary.toNat 16
        omega
      have hprevNat : prevCard.toNat = boundary.toNat - (p.pileFlute.get j).toNat :=
        UInt8.toNat_sub_of_le _ _ hfleB
      have hSUITeq : SUIT prevCard = SUIT boundary := by
        apply UInt8.toNat_inj.mp
        rw [SUIT_toNat, SUIT_toNat, hprevNat]
        omega
      have hVALeq : (VALUE prevCard).toNat =
          (VALUE boundary).toNat - (p.pileFlute.get j).toNat := by
        rw [VALUE_toNat, hprevNat]
        omega
      have hsuiteq : SUIT boundary = (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 := by
        show SUIT boundary = ((SUIT boundary).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      rcases hpm.flute_maximal.resolve_left hd0 with hOldA | hOldNF
      · left
        exact hOldA
      · by_cases hV0 : (VALUE prevCard).toNat = 0
        · -- `prevCard` is the suit's own zero-value sentinel: the NEW
          -- unconditional Nat-based `flute_not_aces` upper bound (`hb`, no
          -- offset/case-split needed), combined with the suit-block lower
          -- bound, pins `aces = prevCard` exactly (no old `≥`/inequality
          -- special-casing needed anymore).
          left
          refine ⟨hs4', ?_⟩
          have haces0 : (0 : Int8) ≤ p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩ :=
            int8_nonneg_of_suit (hak ⟨(SUIT boundary).toNat, hs4'⟩)
          have hSuitAcesEq :
              SUIT ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8) = SUIT boundary := by
            rw [hak ⟨(SUIT boundary).toNat, hs4'⟩, ← hsuiteq]
          have hVBnat := VALUE_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
          have hSBnat := SUIT_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
          have hSeq := congrArg UInt8.toNat hSuitAcesEq
          have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
          have hacesGeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat ≥ prevCard.toNat := by
            rw [hprevNat0]; omega
          have hboundUpper : (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat +
              (p.pileFlute.get j).toNat ≤ boundary.toNat := hb.flute_not_aces hdj hs4'
          have hacesLeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat ≤ prevCard.toNat := by
            rw [hprevNat]; omega
          have hacesEqNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat = prevCard.toNat :=
            le_antisymm hacesLeNat hacesGeNat
          have hprevlt128 : prevCard.toNat < 128 := by omega
          apply Int8.toInt_inj.mp
          rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
          have haces0' : (0 : Int) ≤ (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt := by
            rw [← show ((0 : Int8).toInt = 0) from rfl]
            exact Int8.le_iff_toInt_le.mp haces0
          have hcast : ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt.toNat : Int) =
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt := Int.toNat_of_nonneg haces0'
          have hacesIntEqUInt8Nat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt.toNat =
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat := by
            rw [Int8.toNat_toUInt8_of_le haces0]
            rfl
          omega
        · -- `prevCard` is a genuine real card: it can't equal `K` (the only
          -- card `kingMove` newly reveals), so `¬isFreeCard` transfers via
          -- `kingMove_not_free_of_ne` directly — no need to rule out a whole
          -- absorbed range as in `preCleanupPile_pileMerged_ne`.
          right
          have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
          have hVle : (VALUE prevCard).toNat ≤ 13 := by
            have := hrealBd.2.2
            omega
          have hCrealPrev : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
          have hne : prevCard ≠ K := by
            intro hpeqK
            have hVKeq : (VALUE prevCard).toNat = 13 := by rw [hpeqK]; exact hVK13
            have hflpos : 1 ≤ (p.pileFlute.get j).toNat := hb.flute_pos
            have hBle13 := hrealBd.2.2
            omega
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef
            prevCard hCrealPrev hne hOldNF
  · -- (6) busyAces_complete
    intro hdi
    have hdi' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdi
    set boundaryNew2 := (g.pos2card.get j).get ⟨((kingMove pile hpile suit hs4 ph p
          ).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew2_def
    show ∀ hs : (SUIT boundaryNew2).toNat < 4,
        ((kingMove pile hpile suit hs4 ph p
          ).aces.get ⟨(SUIT boundaryNew2).toNat, hs⟩).toUInt8 =
          boundaryNew2 - (kingMove pile hpile suit hs4 ph p).pileFlute.get j →
        (kingMove pile hpile suit hs4 ph p
          ).busyAces &&& ((1 : UInt8) <<< SUIT boundaryNew2) ≠ 0
    set boundaryOld2 := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ with hboundaryOld2_def
    have hidxEqB2 : ((kingMove pile hpile suit hs4 ph p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hboundEq2 : boundaryNew2 = boundaryOld2 := by
      rw [hboundaryNew2_def, hboundaryOld2_def]
      congr 1
      exact Fin.ext hidxEqB2
    rw [hboundEq2, hfeq, haeq, hbeq]
    exact hpm.busyAces_complete hdi'

/-- Invariant-free twin of `depth_card_not_free`: the same argument, but
    without the (unused) `SolverInvBase g p` hypothesis, so it applies at
    positions where only a `PileClean`/`PileBase` fact (not the full tower) is
    available — exactly what `kingMove_suitClean` has for pile `pile`. -/
private theorem depth_card_not_free_of_wf {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (i : Fin 10) (d : Fin 5)
    (hd : d.val < (p.pileDepth.get i).toInt.toNat) :
    ¬ isFreeCard g p ((g.pos2card.get i).get d) := by
  set c := (g.pos2card.get i).get d with hcdef
  have hreal : IsRealCard c := hwf.pos2card_real i d
  have h64 : c.toNat < 64 := by
    have hsn := SUIT_toNat c
    have h1 := hreal.1
    omega
  obtain ⟨hpileEq, hdepthEq⟩ := hwf.round_trip_inv i d
  unfold isFreeCard
  simp only [dif_pos h64]
  have hpileEq' : g.card2pile.get ⟨c.toNat, h64⟩ = cardPile g c := by unfold cardPile; simp [h64]
  have hpile64 : (cardPile g c).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt c.toNat h64
  simp only [hpileEq', dif_pos hpile64]
  have hdepthEq' : g.card2depth.get ⟨c.toNat, h64⟩ = cardDepth g c := by
    unfold cardDepth; simp [h64]
  rw [hdepthEq']
  have hpileI : (⟨(cardPile g c).toNat, hpile64⟩ : Fin 10) = i := Fin.ext hpileEq
  rw [show (p.pileDepth.get ⟨(cardPile g c).toNat, hpile64⟩) = p.pileDepth.get i from
    congrArg p.pileDepth.get hpileI]
  have hdepthEq2 : (cardDepth g c).toNat = d.val := hdepthEq
  show ¬ (cardDepth g c).toNat ≥ (p.pileDepth.get i).toInt.toNat
  omega

set_option maxHeartbeats 1000000 in
/-- **`SuitClean` holds for every suit `s` after `kingMove`.**  Split on
    whether `s` is the drained suit (`s.val = (SUIT K).toUInt32.toNat`, where
    `K` is `pile`'s sole remaining boundary card, the king being drained) or
    not.

    **Other suits**: trivial — `kings`/`aces` for suit `s` are completely
    untouched by `kingMove` (it only ever writes `kings[suit]` for the ONE
    passed-in `suit`), and the only way a fact about suit `s` could break is a
    freeness claim about a suit-`s` card colliding with the one newly-revealed
    card `K` — ruled out immediately since `K` has the DRAINED suit, not `s`.

    **Drained suit**: needs the full derivation chain — `K`'s old value at
    `kings[suit]` is pinned down exactly (`hsc.king_frontier` forces
    `kings[suit] = K`), the new `kings[suit] = K - pileFlute[pile] = prevCard`
    matches `kingMove`'s own formula, and `hnfreeprev`/`hsc.foundation_cards_free`
    together place `aces[suit]` at or below `prevCard` (mirroring the
    `PileMerged.flute_maximal` "sentinel vs genuine" split from
    `kingMove_pileMerged_ne`: when `prevCard`'s value is exactly `0`,
    `aces[suit] = prevCard` follows from `flute_cards_free`/`busyAces_complete`
    rather than a strict inequality). -/
theorem kingMove_suitClean (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType)
    (hpdb : ∀ i : Fin 10, (p.pileDepth.get i).toInt.toNat ≤ 5)
    (hd1 : (p.pileDepth[pile.toNat]'hpile) = 1)
    (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
    (hVK13 : (VALUE K).toNat = 13)
    (hsuiteq : suit = SUIT K)
    (hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8)
    (hc : PileClean g p ⟨pile.toNat, hpile⟩)
    (s : Fin 4) (hsc : SuitClean g p s hpdb) :
    SuitClean g (kingMove pile hpile suit hs4 ph p) s
      (fun i => le_trans (kingMove_pileDepth_le pile hpile suit hs4 ph p i) (hpdb i)) := by
  have hsK : (SUIT K).toUInt32.toNat < 4 := by rw [← hsuiteq]; exact hs4
  have hd1' : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat = 1 := by
    show (p.pileDepth[pile.toNat]'hpile).toInt.toNat = 1
    rw [hd1]; decide
  have hidxpf : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1 < 5 := by omega
  have hboundIdx : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1 = 0 := by omega
  have hdpilepos : (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat > 0 := by omega
  have hKeqBoundary : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩ = K := by
    rw [hKdef]; congr 1; exact Fin.ext hboundIdx
  have hKreal : IsRealCard K :=
    hKeqBoundary ▸ hwf.pos2card_real (⟨pile.toNat, hpile⟩ : Fin 10)
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩
  have hsBoundary4 : (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat < 4 := by
    rw [hKeqBoundary]; exact hKreal.1
  -- Bridges the pile's own internally-computed `SUIT boundary`-indexed `Fin 4`
  -- (as used by `PileBase`/`PileMerged` fields like `flute_not_aces`/
  -- `busyAces_complete`) to the `SUIT K`-indexed one used throughout this
  -- proof — needed as its own `have` (rather than a direct `rw`) since `K`
  -- appears both as the `Fin 4` value AND inside the embedded `< 4` proof,
  -- the usual dependent-rewrite gotcha.
  have hFinEqBd : (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat,
      hsBoundary4⟩ : Fin 4) = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := by
    apply Fin.ext
    show (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat =
      (SUIT K).toUInt32.toNat
    rw [hKeqBoundary, UInt8.toNat_toUInt32]
  have hKnotfree : ¬ isFreeCard g p K := by
    rw [← hKeqBoundary]
    exact depth_card_not_free_of_wf hwf (⟨pile.toNat, hpile⟩ : Fin 10)
      ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩ (by
        show (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1 <
          (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat
        omega)
  -- `pileFlute[pile] ≤ VALUE K = 13`, so `SUIT (K - pileFlute[pile]) = SUIT K`
  -- (no suit-block underflow) — needed regardless of which suit we're proving.
  have hflv : (p.pileFlute.get (⟨pile.toNat, hpile⟩ : Fin 10)).toNat ≤
      (VALUE ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat :=
    hc.flute_le_value hwf hak hdpilepos
  have hflv13 : (p.pileFlute[pile.toNat]'hpile).toNat ≤ 13 := by
    rw [hKeqBoundary, hVK13] at hflv
    exact hflv
  have hfleK : p.pileFlute[pile.toNat]'hpile ≤ K := by
    rw [UInt8.le_iff_toNat_le]
    have hVKn := VALUE_toNat K
    omega
  have hprevNat : (K - p.pileFlute[pile.toNat]'hpile).toNat =
      K.toNat - (p.pileFlute[pile.toNat]'hpile).toNat := UInt8.toNat_sub_of_le _ _ hfleK
  have hSUITprev : SUIT (K - p.pileFlute[pile.toNat]'hpile) = SUIT K := by
    apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hprevNat]
    have hVKn := VALUE_toNat K
    omega
  have hVprev : (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat =
      13 - (p.pileFlute[pile.toNat]'hpile).toNat := by
    rw [VALUE_toNat, hprevNat]
    have hVKn := VALUE_toNat K
    omega
  by_cases hsame : s.val = (SUIT K).toUInt32.toNat
  · -- **Drained suit.**
    have hseq : s = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := Fin.ext hsame
    subst hseq
    have hSKeqSval : SUIT K = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4).val.toUInt8 := by
      show SUIT K = ((SUIT K).toUInt32.toNat).toUInt8
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have h2 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
      have hsn := SUIT_toNat K
      omega
    -- Step 2: `kings[suit] = K` exactly, from `hsc.king_frontier`'s `∀c`
    -- clause at `c := K` (contrapositive: `K` not free forces
    -- `VALUE(kings[suit]) ≥ 13`, hence `= 13` by `aces_kings_valid`).
    have hVKge13 : 13 ≤ (VALUE (p.kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8).toNat := by
      by_contra hlt
      push Not at hlt
      exact hKnotfree (hsc.king_frontier.2 K hSKeqSval (by omega) (by omega))
    have hVKeq13 : (VALUE (p.kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8).toNat = 13 := by
      have hle := hsc.aces_kings_valid.2.2.2.1
      omega
    have hSKingsEqK : SUIT (p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 =
        SUIT K := hsc.aces_kings_valid.2.2.1.trans hSKeqSval.symm
    have hKingsEqK : (p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 = K :=
      card_eq_of_suit_value _ _ hSKingsEqK (hVKeq13.trans hVK13.symm)
    -- Step 3: `new_kings[suit] = K - pileFlute[pile] = prevCard`.
    have hnewkings8 : ((kingMove pile hpile suit hs4 ph p).kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 =
        K - p.pileFlute[pile.toNat]'hpile := by
      have hsFinEq : (⟨suit.toUInt32.toNat, hs4⟩ : Fin 4) =
          (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := Fin.ext (by
        show suit.toUInt32.toNat = (SUIT K).toUInt32.toNat
        rw [hsuiteq])
      have step1 := kingMove_kings_self pile hpile suit hs4 ph p
      rw [hsFinEq] at step1
      have hOldEq : p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) = K.toInt8 := by
        have h := congrArg (fun x : UInt8 => x.toInt8) hKingsEqK
        rwa [Int8.toInt8_toUInt8] at h
      rw [step1, hOldEq, ← UInt8.toInt8_sub, UInt8.toUInt8_toInt8]
    have hnewkingsInt8 : (kingMove pile hpile suit hs4 ph p).kings.get
        (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
        (K - p.pileFlute[pile.toNat]'hpile).toInt8 := by
      have h := congrArg (fun x : UInt8 => x.toInt8) hnewkings8
      rwa [Int8.toInt8_toUInt8] at h
    have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
    have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
    -- Step 4: `aces[suit] ≤ prevCard`, with equality forced (via
    -- `busyAces_complete`) exactly when `prevCard` is the suit's own
    -- zero-value sentinel (`pileFlute[pile] = 13`); a genuine strict `<`
    -- otherwise (via `foundation_cards_free`'s contrapositive).
    have hprevlt64 : (K - p.pileFlute[pile.toNat]'hpile).toNat < 64 := by
      have hb1 := SUIT_toNat (K - p.pileFlute[pile.toNat]'hpile)
      have hb2 := VALUE_toNat (K - p.pileFlute[pile.toNat]'hpile)
      have hb3 := congrArg UInt8.toNat hSUITprev
      have h1 := hKreal.1
      have hsn2 := SUIT_toNat K
      omega
    have hbusyRaw := hc.busyAces_complete hdpilepos hsBoundary4
    have hbusyEq : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
        (K - p.pileFlute[pile.toNat]'hpile).toInt8 →
        p.busyAces &&& ((1 : UInt8) <<< SUIT K) ≠ 0 := by
      intro haceq
      rw [← hKeqBoundary]
      apply hbusyRaw
      have hFinEq : (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat,
          hsBoundary4⟩ : Fin 4) = (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) := by
        apply Fin.ext
        show (SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat =
          (SUIT K).toUInt32.toNat
        rw [hKeqBoundary, UInt8.toNat_toUInt32]
      have hgetEq : p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat,
          hsBoundary4⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) :=
        congrArg p.aces.get hFinEq
      rw [hgetEq, haceq, UInt8.toUInt8_toInt8, hKeqBoundary]
      rfl
    have hprevlt128 : (K - p.pileFlute[pile.toNat]'hpile).toNat < 128 := by omega
    have hKlt128 : K.toNat < 128 := by
      have h1 := hKreal.1; have h2 := hKreal.2.1; have h3 := hKreal.2.2
      have hsn := SUIT_toNat K
      omega
    have hSacesEqK : SUIT (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 =
        SUIT K := by
      rw [hak (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4), ← hSKeqSval]
    have hacesnn : (0 : Int8) ≤ p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) :=
      int8_nonneg_of_suit (hak (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4))
    have hkey : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
          (K - p.pileFlute[pile.toNat]'hpile).toInt8 ∨
        (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) <
          (K - p.pileFlute[pile.toNat]'hpile).toInt8 ∧
          IsRealCard (K - p.pileFlute[pile.toNat]'hpile) ∧
          ¬ isFreeCard g p (K - p.pileFlute[pile.toNat]'hpile)) := by
      have hne : p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) ≠ 0 := by
        intro hz
        rw [hz] at hd1'
        exact absurd hd1' (by decide)
      -- Unconditional upper bound (the new Nat-based `flute_not_aces`, no
      -- case-split on `pileFlute`/sentinel needed at all): `aces ≤ prevCard`
      -- always. Combined with the suit-block lower bound, this pins down
      -- whether we're in the equality or strict-`<` case WITHOUT relying on
      -- which disjunct `hc.flute_maximal`'s own proof term happens to use
      -- (the two disjuncts of `flute_maximal` are not mutually exclusive, so
      -- deciding via `aces` vs `prevCard` directly is the robust approach).
      have hboundUpperNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat +
          (p.pileFlute[pile.toNat]'hpile).toNat ≤ K.toNat := by
        have h := hc.flute_not_aces hdpilepos hsBoundary4
        rwa [show p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
              ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat,
            hsBoundary4⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) from
          congrArg p.aces.get hFinEqBd, hKeqBoundary] at h
      have hacesLeNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat ≤
          (K - p.pileFlute[pile.toNat]'hpile).toNat := by
        rw [hprevNat]; omega
      have hacesGeNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat ≥
          16 * (SUIT K).toNat := by
        have hb1 := SUIT_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8
        have hb2 := congrArg UInt8.toNat hSacesEqK
        have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
        omega
      by_cases haceqNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat =
          (K - p.pileFlute[pile.toNat]'hpile).toNat
      · -- Equality case: `aces = prevCard.toInt8` directly from the Nat equality.
        left
        apply Int8.toInt_inj.mp
        rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
        have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat : Int) =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
          Int.toNat_of_nonneg (by
            rw [← show ((0 : Int8).toInt = 0) from rfl]; exact Int8.le_iff_toInt_le.mp hacesnn)
        have hacesIntEqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat := by
          rw [Int8.toNat_toUInt8_of_le hacesnn]; rfl
        omega
      · -- Strict case: `aces ≠ prevCard` (Nat) forces `VALUE(prevCard) ≥ 1`
        -- (else both would be pinned to the suit's zero-sentinel, forcing
        -- equality) — so `foundation_cards_free`'s contrapositive route is
        -- safe here. `¬isFreeCard(prevCard)` itself comes from
        -- `hc.flute_maximal`: its equality disjunct is impossible (would
        -- force `aces = prevCard`, contradicting `haceqNat`), so the
        -- not-free disjunct must hold.
        right
        have hVprev_pos : 1 ≤ (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat := by
          have hKsn := SUIT_toNat K
          have hKvn := VALUE_toNat K
          have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
          omega
        have hnfreeprev : ¬ isFreeCard g p (K - p.pileFlute[pile.toNat]'hpile) := by
          rcases hc.flute_maximal.resolve_left hne with ⟨hsB, heq⟩ | hnf'
          · exfalso
            apply haceqNat
            have hEq2 : p.aces.get (⟨(SUIT ((g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                  ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩)).toNat,
                hsB⟩ : Fin 4) = p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) :=
              congrArg p.aces.get hFinEqBd
            rw [← hEq2, heq, hKeqBoundary, UInt8.toUInt8_toInt8]
            rfl
          · rwa [hKeqBoundary] at hnf'
        have hSprevSval : SUIT (K - p.pileFlute[pile.toNat]'hpile) =
            (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4).val.toUInt8 := by
          rw [hSUITprev]; exact hSKeqSval
        refine ⟨?_, ⟨by rw [hSUITprev]; exact hKreal.1, hVprev_pos, by omega⟩, hnfreeprev⟩
        rw [Int8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128]
        have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat : Int) =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
          Int.toNat_of_nonneg (by
            rw [← show ((0 : Int8).toInt = 0) from rfl]; exact Int8.le_iff_toInt_le.mp hacesnn)
        have hacesIntEqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat =
            (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat := by
          rw [Int8.toNat_toUInt8_of_le hacesnn]; rfl
        omega
    have haces_le_prevCard : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) ≤
        (K - p.pileFlute[pile.toNat]'hpile).toInt8 := by
      rcases hkey with h | h
      · exact Int8.le_iff_toInt_le.mpr (le_of_eq (congrArg Int8.toInt h))
      · exact Int8.le_iff_toInt_le.mpr (le_of_lt (Int8.lt_iff_toInt_lt.mp h.1))
    have hprevLtK : (K - p.pileFlute[pile.toNat]'hpile).toInt8 < K.toInt8 := by
      rw [Int8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128,
        uint8_toInt8_toInt_of_lt128 hKlt128]
      have hflpos : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat := hc.flute_pos
      have hVKn := VALUE_toNat K
      omega
    have hacesLtK : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) < K.toInt8 := by
      rw [Int8.lt_iff_toInt_lt]
      have h1 := Int8.le_iff_toInt_le.mp haces_le_prevCard
      have h2 := Int8.lt_iff_toInt_lt.mp hprevLtK
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) aces_kings_valid
      rw [haeq, hnewkingsInt8]
      refine ⟨hsc.aces_kings_valid.1, hsc.aces_kings_valid.2.1, ?_, ?_, haces_le_prevCard⟩
      · rw [UInt8.toUInt8_toInt8]; exact hSUITprev.trans hSKeqSval
      · rw [UInt8.toUInt8_toInt8]; omega
    · -- (4a) foundation_cards_free
      intro c h1 h2 h3
      rw [haeq] at h3
      exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
        (hsc.foundation_cards_free c h1 h2 h3)
    · -- (4b-weak) foundation_maximal_weak
      rw [haeq]
      rcases hkey with haceq | ⟨hacest, hCrealPrev, _⟩
      · -- `aces = prevCard` forces the busy bit via `busyAces_complete`
        -- (packaged above as `hbusyEq`), and `kingMove` never touches
        -- `busyAces` (`hbeq`), so the bit is still set in the output.
        rw [hbeq, ← hSKeqSval]
        exact Or.inr (Or.inr (hbusyEq haceq))
      · rcases hsc.foundation_maximal_weak with h13 | hnfreeA | hbusy
        · exfalso
          have hAeqK : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 = K :=
            card_eq_of_suit_value _ _ hSacesEqK (h13.trans hVK13.symm)
          have hAeqKInt8 : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) = K.toInt8 := by
            have h := congrArg (fun x : UInt8 => x.toInt8) hAeqK
            rwa [Int8.toInt8_toUInt8] at h
          rw [hAeqKInt8] at hacesLtK
          have := Int8.lt_iff_toInt_lt.mp hacesLtK
          omega
        · -- disjunct 2: transfers, since `aces + 1 ≠ K` (strict `hacest` gives
          -- `aces + 1 ≤ prevCard < K`).
          have hacesNat_lt_prevNat : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
              ).toUInt8.toNat < (K - p.pileFlute[pile.toNat]'hpile).toNat := by
            rw [Int8.lt_iff_toInt_lt, uint8_toInt8_toInt_of_lt128 hprevlt128] at hacest
            have hcast : ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat
                : Int) = (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt :=
              Int.toNat_of_nonneg (by
                rw [← show ((0 : Int8).toInt = 0) from rfl]
                exact Int8.le_iff_toInt_le.mp hacesnn)
            have heqU8 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toInt.toNat =
                (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8.toNat := by
              rw [Int8.toNat_toUInt8_of_le hacesnn]; rfl
            omega
          have hflpos : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat := hc.flute_pos
          have hne : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 + 1 ≠ K := by
            intro heq
            have hlt256 : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
                ).toUInt8.toNat + 1 < 2 ^ 8 := by omega
            have h2 := congrArg UInt8.toNat heq
            rw [UInt8.toNat_add, show (1 : UInt8).toNat = 1 from rfl,
              Nat.mod_eq_of_lt hlt256] at h2
            omega
          have hAV12 : (VALUE (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8
              ).toNat ≤ 12 := by
            have hb1 := SUIT_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8
            have hb2 := VALUE_toNat (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8
            have hb3 := congrArg UInt8.toNat hSacesEqK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hlt := hacesNat_lt_prevNat
            have heqp := hprevNat
            omega
          have hrealA : IsRealCard ((p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)
              ).toUInt8 + 1) := by
            have hVsucc := VALUE_succ (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8
              (by omega)
            refine ⟨?_, by omega, by omega⟩
            rw [SUIT_succ _ (by omega), hSacesEqK]; exact hsK
          exact Or.inr (Or.inl (kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K
            hKdef _ hrealA hne hnfreeA))
        · -- busy bit already set for this suit before the move; `kingMove`
          -- never touches `busyAces`, so it stays set in the output.
          rw [hbeq]
          exact Or.inr (Or.inr hbusy)
    · -- (9) king_frontier
      constructor
      · rw [hnewkingsInt8, haeq, hbeq]
        rcases hkey with haceq | ⟨hacest, hCrealPrev, hnfreeprev⟩
        · left
          exact ⟨haceq.symm, Or.inr (hSKeqSval ▸ hbusyEq haceq)⟩
        · right
          refine ⟨hacest, ?_⟩
          have hprevNeK : (K - p.pileFlute[pile.toNat]'hpile) ≠ K := by
            intro heq
            rw [heq] at hprevLtK
            have := Int8.lt_iff_toInt_lt.mp hprevLtK
            omega
          rw [UInt8.toUInt8_toInt8]
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef _
            hCrealPrev hprevNeK hnfreeprev
      · intro c hSc hgt hle
        rw [hnewkingsInt8, UInt8.toUInt8_toInt8] at hgt
        by_cases hcK : c = K
        · subst hcK
          have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
            ⟨(p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10)).toInt.toNat - 1, hidxpf⟩
          rw [hKeqBoundary] at hrt
          have hc64K : c.toNat < 64 := by
            have h1 := hKreal.1
            have hsn := SUIT_toNat c
            omega
          have hp64K : (cardPile g c).toNat < 10 := by rw [hrt.1]; exact hpile
          show isFreeCard g (kingMove pile hpile suit hs4 ph p) c
          apply isFree_of_cardDepth_ge g _ hwf c hc64K hp64K
          have hpdK : (kingMove pile hpile suit hs4 ph p).pileDepth[(cardPile g c).toNat]'hp64K
              = 0 := by
            have hstep : (kingMove pile hpile suit hs4 ph p
                ).pileDepth[(cardPile g c).toNat]'hp64K =
                (kingMove pile hpile suit hs4 ph p).pileDepth[pile.toNat]'hpile := by
              congr 1; exact hrt.1
            rw [hstep]
            exact kingMove_pileDepth_self pile hpile suit hs4 ph p
          rw [hpdK]
          have hcdK0 : (cardDepth g c).toNat = 0 := by rw [hrt.2]; exact hboundIdx
          have hz0 : (0 : Int8).toInt.toNat = 0 := by decide
          omega
        · have hScK : SUIT c = SUIT K := hSc.trans hSKeqSval.symm
          have hle' : (VALUE c).toNat ≤ 13 := hle
          have hcLeK : c.toNat ≤ K.toNat := by
            have hb1 := SUIT_toNat c; have hb2 := VALUE_toNat c
            have hb3 := congrArg UInt8.toNat hScK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hVK13' := hVK13
            omega
          have hcLtK : c.toNat < K.toNat := lt_of_le_of_ne hcLeK (fun heq => hcK (UInt8.toNat_inj.mp heq))
          have hoffsetPos : 0 < K.toNat - c.toNat := by omega
          have hgt' : (VALUE c).toNat > (VALUE (K - p.pileFlute[pile.toNat]'hpile)).toNat := hgt
          have hoffsetLtFlute : K.toNat - c.toNat < (p.pileFlute[pile.toNat]'hpile).toNat := by
            have hb1 := SUIT_toNat c
            have hb2 := VALUE_toNat c
            have hb3 := congrArg UInt8.toNat hScK
            have hVKn := VALUE_toNat K
            have hsnK := SUIT_toNat K
            have hVK13' := hVK13
            have hVpr := hVprev
            omega
          have hoff8 : (UInt8.ofNat (K.toNat - c.toNat)).toNat = K.toNat - c.toNat := by
            rw [UInt8.toNat_ofNat']; omega
          have hCeqKMinusOffset : c = K - UInt8.ofNat (K.toNat - c.toNat) := by
            apply UInt8.toNat_inj.mp
            rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hoff8]; omega), hoff8]
            omega
          have hfree_old : isFreeCard g p c := by
            rw [hCeqKMinusOffset]
            have h := hc.flute_cards_free (UInt8.ofNat (K.toNat - c.toNat)) hdpilepos
              (by rw [hoff8]; omega) (by rw [hoff8]; omega)
            rwa [hKeqBoundary] at h
          exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p) hfree_old
  · -- **Other suits.**
    have hsne : s.val ≠ suit.toUInt32.toNat := by rw [hsuiteq]; exact hsame
    have hkingsEq := kingMove_kings_eq_of_ne pile hpile suit hs4 ph p s hsne
    have haeq := kingMove_aces_eq pile hpile suit hs4 ph p
    have hbeq := kingMove_busyAces_eq pile hpile suit hs4 ph p
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [haeq, hkingsEq]; exact hsc.aces_kings_valid
    · intro c h1 h2 h3
      rw [haeq] at h3
      exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
        (hsc.foundation_cards_free c h1 h2 h3)
    · rw [haeq]
      by_cases hAV13 : (VALUE (p.aces.get s).toUInt8).toNat = 13
      · exact Or.inl hAV13
      · have hAV12 : (VALUE (p.aces.get s).toUInt8).toNat ≤ 12 := by
          have := hsc.aces_kings_valid.2.1
          omega
        rcases hsc.foundation_maximal_weak with h13 | hnfreeA | hbusy
        · exact absurd h13 hAV13
        · have hVsucc := VALUE_succ (p.aces.get s).toUInt8 (by omega)
          have hrealA : IsRealCard ((p.aces.get s).toUInt8 + 1) := by
            refine ⟨?_, ?_, ?_⟩
            · rw [SUIT_succ _ (by omega), hsc.aces_kings_valid.1]
              show (s.val.toUInt8).toNat < 4
              rw [UInt8.toNat_ofNat']
              have := s.isLt
              omega
            · rw [hVsucc]; omega
            · rw [hVsucc]; omega
          have hne : (p.aces.get s).toUInt8 + 1 ≠ K := by
            intro heq
            apply hsame
            have hSA := SUIT_succ (p.aces.get s).toUInt8 (by omega)
            rw [heq] at hSA
            have hSKeqSval2 : SUIT K = s.val.toUInt8 := hSA.trans hsc.aces_kings_valid.1
            have hb1 := congrArg UInt8.toNat hSKeqSval2
            have hb2 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
            omega
          exact Or.inr (Or.inl (kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K
            hKdef _ hrealA hne hnfreeA))
        · -- busy bit already set for this suit before the move; `kingMove`
          -- never touches `busyAces`, so it stays set in the output.
          rw [hbeq]
          exact Or.inr (Or.inr hbusy)
    · constructor
      · rcases hsc.king_frontier.1 with ⟨hkeqA, hcase⟩ | ⟨hv1, hnfree⟩
        · left
          rw [hkingsEq, haeq, hbeq]
          exact ⟨hkeqA, hcase⟩
        · right
          rw [hkingsEq, haeq]
          refine ⟨hv1, ?_⟩
          have hne : (p.kings.get s).toUInt8 ≠ K := by
            intro heq
            apply hsame
            have hSKeq : SUIT (p.kings.get s).toUInt8 = SUIT K := by rw [heq]
            have hSKeqSval2 := hsc.aces_kings_valid.2.2.1
            have hb1 := congrArg UInt8.toNat (hSKeqSval2.symm.trans hSKeq)
            have hb2 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
            omega
          have hrealK : IsRealCard (p.kings.get s).toUInt8 := by
            have hSAs : SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 := hsc.aces_kings_valid.1
            have hSs : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
              hsc.aces_kings_valid.2.2.1
            have haces_nonneg : (0 : Int8) ≤ p.aces.get s := int8_nonneg_of_suit hSAs
            have hkings_nonneg : (0 : Int8) ≤ p.kings.get s := int8_nonneg_of_suit hSs
            have hAKlt : (p.aces.get s).toUInt8.toNat < (p.kings.get s).toUInt8.toNat := by
              have h1 := Int8.lt_iff_toInt_lt.mp hv1
              have h2 : (p.aces.get s).toUInt8.toNat = (p.aces.get s).toInt.toNat :=
                Int8.toNat_toUInt8_of_le haces_nonneg
              have h3 : (p.kings.get s).toUInt8.toNat = (p.kings.get s).toInt.toNat :=
                Int8.toNat_toUInt8_of_le hkings_nonneg
              rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces_nonneg
              rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at hkings_nonneg
              omega
            have hb1 := VALUE_toNat (p.aces.get s).toUInt8
            have hb2 := SUIT_toNat (p.aces.get s).toUInt8
            have hb3 := congrArg UInt8.toNat hSAs
            have hb4 := VALUE_toNat (p.kings.get s).toUInt8
            have hb5 := SUIT_toNat (p.kings.get s).toUInt8
            have hb6 := congrArg UInt8.toNat hSs
            have hb7 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hsval := s.isLt
            have hVKge1 : 1 ≤ (VALUE (p.kings.get s).toUInt8).toNat := by omega
            have hs4' : (SUIT (p.kings.get s).toUInt8).toNat < 4 := by omega
            exact ⟨hs4', hVKge1, hsc.aces_kings_valid.2.2.2.1⟩
          exact kingMove_not_free_of_ne g pile hpile hwf suit hs4 ph p hd1 K hKdef _
            hrealK hne hnfree
      · intro c hSc hgt hle
        rw [hkingsEq] at hgt
        exact isFreeCard_mono (kingMove_pileDepth_le pile hpile suit hs4 ph p)
          (hsc.king_frontier.2 c hSc hgt hle)

/-- **A real card strictly below the merged-away range keeps its freeness
    status across `preCleanupPile`.**  The merge-absorbed slots hold exactly
    `B, …, B+m-1` (`hmcards`); a real card `C < B` can't be any of those, so
    if `C`'s own home pile isn't `pile`, cleanup doesn't touch it at all, and
    if it *is* `pile`, `round_trip` forces its home depth to be strictly below
    the new (shrunk) depth too — so `¬isFreeCard` transfers either way.  This
    is the "wrong direction" of `isFreeCard_mono` (needed for `flute_maximal`'s
    `¬isFreeCard` disjunct, not just its `isFreeCard` one), which only holds
    because `C` is provably outside the range cleanup could have freed. -/
private theorem preCleanupPile_not_free_of_lt_boundary
    (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (hBrange : B.toNat ≤ 61)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (C : UInt8) (hCreal : IsRealCard C) (hClt : C.toNat < B.toNat)
    (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  by_cases hcp : (cardPile g C).toNat = pile.toNat
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
        rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
          (p.pileDepth[pile.toNat]'hpile).toInt - m := by
        rw [Int32.toInt_sub_of_le _ _
          (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
          (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
          hmofI, Int8.toInt_toInt32]
      rw [Int32.toInt_toInt8, hdepth1I]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    have hnfreeLt : (cardDepth g C).toNat <
        (p.pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat := by
      by_contra hge
      push Not at hge
      exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)
    have hpdEq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[(cardPile g C).toNat]'hp64
        = ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
      have hstep : (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64
          = (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hstep]
      simp only [preCleanupPile]
      rw [Vector.getElem_set_self]
    rw [hpdEq, hdI8] at hfreeGe
    have hpEq : (p.pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat =
        (p.pileDepth[pile.toNat]'hpile).toInt.toNat := by
      have h : (p.pileDepth[(cardPile g C).toNat]'hp64) = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [h]
    rw [hpEq] at hnfreeLt
    set cd := (cardDepth g C).toNat with hcddef
    have hcd5 : cd < 5 := by omega
    obtain ⟨k, hkm, hkeq⟩ : ∃ k, k < m ∧
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat = cd := by
      refine ⟨(p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd, by omega, ?_⟩
      have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
          ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1).toInt = (cd : Int) := by
        rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
          (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
        omega
      have hikn : (0 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
          ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1 := by
        rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
      rw [Int32.toNat_toUInt32_of_le hikn]
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
        ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1).toInt.toNat) = cd
      rw [hik]
      omega
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hcd_lt5 : (cardDepth g C).toNat < 5 := hcd5
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) = (⟨cd, hcd5⟩ : Fin 5) := Fin.ext rfl
    rw [hcpEq, hcdEq] at hround
    have hgetEq : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get (⟨cd, hcd5⟩ : Fin 5) =
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'hidxk := by
      congr 1
      exact Fin.ext hkeq.symm
    rw [hgetEq, heqk] at hround
    have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
    have hlt : B.toNat + k < 256 := by omega
    have hBkB : (B + UInt8.ofNat k).toNat = B.toNat + k := by
      rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hlt]
    have hCeq := congrArg UInt8.toNat hround
    rw [hBkB] at hCeq
    omega
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hj : (⟨(cardPile g C).toNat, hp64⟩ : Fin 10).val ≠ pile.toNat := hcp
    have hpdEq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f
      ⟨(cardPile g C).toNat, hp64⟩ hj
    have hpdEq' : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[(cardPile g C).toNat]'hp64
        = p.pileDepth[(cardPile g C).toNat]'hp64 := hpdEq
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    rw [hpdEq'] at hfreeGe
    exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hfreeGe)

/-- **Generalized form of `preCleanupPile_not_free_of_lt_boundary`**: instead of
    requiring `C < B` (which only rules out `C` being one of `B, …, B+m-1` when
    `C` is numerically below the whole merge-absorbed run), takes the direct
    hypothesis that `C` isn't literally any of `B, …, B+m-1`.  This covers both
    the old numeric case (`C.toNat < B.toNat`) and the new "different suit"
    case needed by `SuitClean` (`SUIT C ≠ SUIT B` rules out `C = B+k` for every
    `k ≤ m`, since `merge_real_chain'` shows every such card has suit `SUIT B`,
    even when `C` is numerically *above* `B+m-1`, which can happen for a higher
    suit). -/
private theorem preCleanupPile_not_free_of_ne_absorbed
    (g : Globals) (pile : UInt32) (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (hBrange : B.toNat ≤ 61)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (C : UInt8) (hCreal : IsRealCard C) (hne : ∀ k, k ≤ m → C ≠ B + UInt8.ofNat k)
    (hnfree : ¬ isFreeCard g p C) :
    ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) C := by
  have hc64 : C.toNat < 64 := by
    have h1 := hCreal.1; have h2 := hCreal.2.1; have h3 := hCreal.2.2
    have hsn := SUIT_toNat C; have hvn := VALUE_toNat C
    omega
  by_cases hcp : (cardPile g C).toNat = pile.toNat
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
        rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
          (p.pileDepth[pile.toNat]'hpile).toInt - m := by
        rw [Int32.toInt_sub_of_le _ _
          (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
          (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
          hmofI, Int8.toInt_toInt32]
      rw [Int32.toInt_toInt8, hdepth1I]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    have hnfreeLt : (cardDepth g C).toNat <
        (p.pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat := by
      by_contra hge
      push Not at hge
      exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hge)
    have hpdEq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[(cardPile g C).toNat]'hp64
        = ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
      have hstep : (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64
          = (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [hstep]
      simp only [preCleanupPile]
      rw [Vector.getElem_set_self]
    rw [hpdEq, hdI8] at hfreeGe
    have hpEq : (p.pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat =
        (p.pileDepth[pile.toNat]'hpile).toInt.toNat := by
      have h : (p.pileDepth[(cardPile g C).toNat]'hp64) = p.pileDepth[pile.toNat]'hpile := by
        congr 1
      rw [h]
    rw [hpEq] at hnfreeLt
    set cd := (cardDepth g C).toNat with hcddef
    have hcd5 : cd < 5 := by omega
    obtain ⟨k, hkm, hkeq⟩ : ∃ k, k < m ∧
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat = cd := by
      refine ⟨(p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd, by omega, ?_⟩
      have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
          ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1).toInt = (cd : Int) := by
        rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
          (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
        omega
      have hikn : (0 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
          ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1 := by
        rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
      rw [Int32.toNat_toUInt32_of_le hikn]
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat
        ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 - cd) - 1).toInt.toNat) = cd
      rw [hik]
      omega
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hcd_lt5 : (cardDepth g C).toNat < 5 := hcd5
    have hround := hwf.round_trip C hCreal hcd_lt5
    have hcpEq : (⟨(cardPile g C).toNat, hwf.pile_lt C hCreal⟩ : Fin 10) =
        (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hcp
    have hcdEq : (⟨(cardDepth g C).toNat, hcd_lt5⟩ : Fin 5) = (⟨cd, hcd5⟩ : Fin 5) := Fin.ext rfl
    rw [hcpEq, hcdEq] at hround
    have hgetEq : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get (⟨cd, hcd5⟩ : Fin 5) =
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'hidxk := by
      congr 1
      exact Fin.ext hkeq.symm
    rw [hgetEq, heqk] at hround
    -- `hround : B + UInt8.ofNat k = C`; directly contradicts `hne`.
    exact hne k (by omega) hround.symm
  · intro hfree
    have hp64 : (cardPile g C).toNat < 10 := hwf.pile_lt C hCreal
    have hj : (⟨(cardPile g C).toNat, hp64⟩ : Fin 10).val ≠ pile.toNat := hcp
    have hpdEq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f
      ⟨(cardPile g C).toNat, hp64⟩ hj
    have hpdEq' : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[(cardPile g C).toNat]'hp64
        = p.pileDepth[(cardPile g C).toNat]'hp64 := hpdEq
    have hfreeGe : (cardDepth g C).toNat ≥
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g C).toNat]'hp64).toInt.toNat :=
      isFree_to_cardDepth_ge g _ hwf C hc64 hp64 hfree
    rw [hpdEq'] at hfreeGe
    exact hnfree (isFree_of_cardDepth_ge g p hwf C hc64 hp64 hfreeGe)

/-- **`PileBase` holds for `pile` itself after `preCleanupPile`.**  Takes
    the boundary card `B` and semantic facts about the merge/freed runs
    directly — not the raw `mergeGuard`/`freedGuard` machinery — matching the
    user's simplified interface: for `m`, the `m` successive ascending cards
    starting at `B` (`hmcards`); for `f`, that the `f` predecessor cards are
    all free *and* above the foundation ace (`hffree`).  `ph` is always just
    `pileHashes.get pile`, so it's no longer a separate parameter either.
    This is a restatement of the "No lone king" branch's own-pile reasoning
    out of the (structurally stale) monolithic `cleanupPile_base`, purely in
    terms of `preCleanupPile`. -/
theorem preCleanupPile_pileBase_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hf_le : f ≤ B.toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8) :
    PileBase g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) ⟨pile.toNat, hpile⟩ := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1
    have h2 := hreal.2.1
    have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have haces0 : (0 : Int8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 :=
    int8_nonneg_of_suit (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
  have h1le : (1 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 := by
    rw [Int32.le_iff_toInt_le, Int32.toInt_one, Int8.toInt_toInt32]; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by
    rw [Int32.toInt_sub_of_le _ _ (by decide) h1le, Int32.toInt_one, Int8.toInt_toInt32]
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B.toInt8 := by
    by_contra hge
    rw [Int8.lt_iff_toInt_lt] at hge
    rw [not_lt] at hge
    have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
    have h1 : (B.toNat : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
      rwa [htiB] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
      rw [Int8.toNat_toUInt8_of_le haces0]
      have hbdg : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNatClampNeg =
          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat := rfl
      omega
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      hnf.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          rw [Int32.toNat_toUInt32_of_le (by
            rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]
            omega)]
          have hbdg1 : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          omega)
    exact hnfB hfree
  have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_sub_of_le _ _
      (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
      (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
      hmofI, Int8.toInt_toInt32]
  have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hfof8 : (UInt8.ofNat f).toNat = f := by
    rw [UInt8.toNat_ofNat']; omega
  have h1mI : ((1 : Int32) + Int32.ofNat m).toInt = 1 + (m : Int) := by
    rw [Int32.toInt_add, Int32.toInt_one, hmofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hfl32I : ((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toInt = 1 + (m : Int) + f := by
    rw [Int32.toInt_add, h1mI, hfofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hflnn : (0 : Int32) ≤ 1 + Int32.ofNat m + Int32.ofNat f := by
    rw [Int32.le_iff_toInt_le, hfl32I, show ((0 : Int32).toInt = 0) from by decide]; omega
  have hfl8 : ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat = 1 + m + f := by
    rw [UInt32.toNat_toUInt8, Int32.toNat_toUInt32_of_le hflnn]
    show ((1 + Int32.ofNat m + Int32.ofNat f).toInt.toNat) % 2 ^ 8 = 1 + m + f
    rw [hfl32I]
    omega
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile =
      (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  -- Merge-absorbed cards `B+k` (`k < m`) sit past the shrunk depth, hence free.
  have hfree_interior : ∀ k, k < m → isFreeCard g
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
      (B + UInt8.ofNat k) := by
    intro k hkm
    obtain ⟨hidxk, heqk⟩ := hmcards k (by omega)
    have hreal_k : IsRealCard (B + UInt8.ofNat k) := heqk ▸ hwf.pos2card_real _ _
    have hc64 : (B + UInt8.ofNat k).toNat < 64 := by
      have hsn := SUIT_toNat (B + UInt8.ofNat k); have h1 := hreal_k.1; omega
    have heqk' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
        (⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat,
          hidxk⟩ : Fin 5) = B + UInt8.ofNat k := heqk
    have hrt := hwf.round_trip_inv ⟨pile.toNat, hpile⟩ ⟨((p.pileDepth[pile.toNat
        ]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat, hidxk⟩
    rw [heqk'] at hrt
    have hp64 : (cardPile g (B + UInt8.ofNat k)).toNat < 10 := by
      rw [hrt.1]; exact hpile
    apply isFree_of_cardDepth_ge g _ hwf _ hc64 hp64
    have hgoal2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
        ).pileDepth[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
        = ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
      have hstep : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
          = (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile := by
        congr 1
        exact hrt.1
      rw [hstep, hpd]
    rw [hrt.2, hgoal2]
    show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat ≥
      (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat
    have hik0 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt32.toInt - k - 1 :=
      depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
        (by rw [Int8.toInt_toInt32]; omega)
    have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - k - 1 := by
      rw [hik0, Int8.toInt_toInt32]
    have hikn : (0 : Int32) ≤
        (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1 := by
      rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
    rw [Int32.toNat_toUInt32_of_le hikn]
    show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toInt.toNat ≥
      (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat
    rw [hik, hdI8]
    omega
  -- Freed-predecessor cards `B-l` (`1 ≤ l ≤ f`) were already free in `p`
  -- (`hffree`), and freeness is monotone under the pile's depth decrease.
  have hfree_freed : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
      (B - UInt8.ofNat l) := fun l hl1 hlf =>
    isFreeCard_mono
      (preCleanupPile_pileDepth_le pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f hd5
        (by omega))
      (hffree l hl1 hlf).1
  -- `aces[suit] < B` extends forward to `aces[suit] < B+k` for `k ≤ m` (the
  -- merge-absorbed range never crosses the foundation, since it only grows).
  have haces_lt_Bk : ∀ k, k ≤ m →
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B + UInt8.ofNat k).toInt8 := by
    intro k hkm
    have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
    have hadd : (B + UInt8.ofNat k).toNat = B.toNat + k := by
      rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt (by omega)]
    have htiBk : (B + UInt8.ofNat k).toInt8.toInt = (B.toNat + k : Int) := by
      rw [uint8_toInt8_toInt_of_lt128 (by omega), hadd]
      push_cast
      ring
    have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
    have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
    rw [htiB] at hlt
    rw [Int8.lt_iff_toInt_lt, htiBk]
    omega
  -- Shared by `flute_cards_free`/`flute_not_aces`: the cleaned pile's new
  -- boundary slot's index (`hbidx`) and its card value `B + m` (`hcardEq`,
  -- via `hmcards` at `k := m`), plus the same facts restated about
  -- `preCleanupPile`'s own (already-written) `pileDepth` field (`hboundOut`/
  -- `hcardEqOut`) so both clauses can `rw` them directly instead of
  -- re-deriving the `Vector.set`-vs-raw bridge twice.
  have hbidx : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat := by
    have e1 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m := by
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = _
      rw [hdI8]
      omega
    have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
      rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
        (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
    have hikn : (0 : Int32) ≤
        (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
      rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
      omega
    have e2 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
        ).toUInt32.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m - 1 := by
      rw [Int32.toNat_toUInt32_of_le hikn]
      show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat = _
      rw [hik]
      omega
    rw [e1, e2]
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
      ).toInt.toNat - 1 < 5 := by
    rw [hpd]
    show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 < 5
    omega
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
      ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
        ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  -- `SUIT(B+m) = SUIT B`: the merge-absorbed range never crosses a suit
  -- boundary (`merge_real_chain'` gives the `VALUE` progression from
  -- `hmcards` directly, no loop-guard unfolding needed).
  have hrcm := merge_real_chain' g pile hpile hwf B
    (p.pileDepth[pile.toNat]'hpile).toInt32 m hreal hmcards m (le_refl m)
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := by
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat m)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat m)
    have hb4 := VALUE_toNat B
    have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + m < 256 := by omega
    have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
    have hvm := hrcm.2
    omega
  exact {
    pileDepth_bound := by
      show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
          ).toInt.toNat ≤ 5
      rw [hpd]
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat ≤ 5
      omega
    pileDepth_nonneg := by
      show (0 : Int8) ≤ (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
      rw [hpd, Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl, hdI8]
      omega
    flute_pos := by
      show 1 ≤ ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile).toNat
      rw [hpf, hfl8]
      omega
    flute_empty := by
      intro hdep
      exfalso
      have hdep' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile = 0 := hdep
      rw [hpd] at hdep'
      have hz := congrArg Int8.toInt hdep'
      rw [hdI8, show ((0 : Int8).toInt = 0) from rfl] at hz
      omega
    flute_cards_free := by
      intro j hdi hj0 hjlt
      have hjlt' : j.toNat < ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile).toNat :=
        hjlt
      rw [hpf, hfl8] at hjlt'
      show isFreeCard g _
        ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut - j)
      rw [hcardEqOut]
      rcases flute_offset_split B m f hBrange.2 (by omega) hf_le j hj0 (by omega)
        with ⟨k, hkm, hval⟩ | ⟨l, hl1, hlf, hval⟩
      · rw [hval]; exact hfree_interior k hkm
      · rw [hval]; exact hfree_freed l hl1 hlf
    flute_not_aces := by
      intro hdi _
      -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `preCleanupPile`
      -- terms first, THEN reduce those wrappers uniformly, BEFORE `intro`-ing the
      -- dependent `hs` binder — mirrors the recipe from
      -- `preCleanupPile_pileBase_ne`'s own `flute_not_aces` (rewriting `boundary`
      -- AFTER `hs` is fixed hits "motive is not type correct", since `hs`'s own
      -- type embeds the pre-rewrite `boundary` expression).
      show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toNat < 4,
        ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).aces.get
            ⟨(SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
                (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
                ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toNat, hs⟩).toUInt8.toNat +
          ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile).toNat ≤
          UInt8.toNat ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
              ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)
      rw [preCleanupPile_aces_eq, hcardEqOut, hpf, hfl8]
      intro hs
      have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
      have hidxEq : (⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ : Fin 4) =
          ⟨(SUIT B).toNat, hs4'⟩ := Fin.ext (congrArg UInt8.toNat hSm)
      have hEq2 : p.aces.get ⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
        rw [hidxEq]; congr 1
      rw [hEq2]
      -- New Nat-based bound: `aces[SUIT B].toUInt8.toNat + f < B.toNat`, tightest
      -- at the largest valid offset (`f = 0` falls back to `haces_lt_B`; `f > 0`
      -- uses the freed-predecessor bound at its largest index `l = f`).
      have haces_nonneg' : (0 : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt :=
        Int8.le_iff_toInt_le.mp haces0
      have hbUInt8 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat
          = (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
        Int8.toNat_toUInt8_of_le haces0
      have hAB_lt : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat + f < B.toNat := by
        rcases Nat.eq_zero_or_pos f with hf0 | hfpos
        · subst hf0
          simp only [Nat.add_zero]
          have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
          rw [uint8_toInt8_toInt_of_lt128 (show B.toNat < 128 by omega)] at hlt
          omega
        · have hf' := (hffree f hfpos (le_refl f)).2
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hfBle : UInt8.ofNat f ≤ B := by rw [UInt8.le_iff_toNat_le, hfof]; omega
          have hBf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
            rw [UInt8.toNat_sub_of_le _ _ hfBle, hfof]
          have hlt := Int8.lt_iff_toInt_lt.mp hf'
          rw [uint8_toInt8_toInt_of_lt128 (show (B - UInt8.ofNat f).toNat < 128 by omega),
            hBf] at hlt
          omega
      have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
      have hBmAdd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
        rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt (by omega)]
      rw [hBmAdd]
      omega }

set_option maxHeartbeats 1000000 in
/-- **`PileMerged` holds for `pile` itself after `preCleanupPile`.**  Genuinely
    new content (never proved anywhere before, unlike `preCleanupPile_pileBase_self`
    which ports the old monolithic proof): `merge_complete`/`flute_maximal` each
    need one more semantic "stopping" fact beyond `hmcards`/`hffree` — `hmstop`
    (either the pile ends at depth `≤ 1`, or the card two below the new boundary
    doesn't continue the ascending run) and `hfstop` (either the ace has already
    reached `B-1-f`, or that card is genuinely not free — this is the "why the
    freed loop actually stopped" fact, the counterpart to `hffree`'s "why it kept
    going"). `busyAces_complete`'s antecedent turns out to be *exactly*
    `preCleanupPile`'s own `busyAces`-setting condition, so it's essentially
    definitional once unfolded. -/
theorem preCleanupPile_pileMerged_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hmstop : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1 ∨
      (1 < (p.pileDepth[pile.toNat]'hpile).toInt - m ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
    (hbound : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get ⟨pile.toNat, hpile⟩
        ).toInt.toNat ≤ 5) :
    PileMerged g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) ⟨pile.toNat, hpile⟩ hbound := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1; have h2 := hreal.2.1; have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have haces0 : (0 : Int8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 :=
    int8_nonneg_of_suit (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
  have h1le : (1 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 := by
    rw [Int32.le_iff_toInt_le, Int32.toInt_one, Int8.toInt_toInt32]; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by
    rw [Int32.toInt_sub_of_le _ _ (by decide) h1le, Int32.toInt_one, Int8.toInt_toInt32]
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B.toInt8 := by
    by_contra hge
    rw [Int8.lt_iff_toInt_lt] at hge
    rw [not_lt] at hge
    have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
    have h1 : (B.toNat : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
      rwa [htiB] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
      rw [Int8.toNat_toUInt8_of_le haces0]
      have hbdg : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNatClampNeg =
          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat := rfl
      omega
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      hnf.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          rw [Int32.toNat_toUInt32_of_le (by
            rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]
            omega)]
          have hbdg1 : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          omega)
    exact hnfB hfree
  have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_sub_of_le _ _
      (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
      (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
      hmofI, Int8.toInt_toInt32]
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile =
      (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have h1mI : ((1 : Int32) + Int32.ofNat m).toInt = 1 + (m : Int) := by
    rw [Int32.toInt_add, Int32.toInt_one, hmofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hfl32I : ((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toInt = 1 + (m : Int) + f := by
    rw [Int32.toInt_add, h1mI, hfofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hflnn : (0 : Int32) ≤ 1 + Int32.ofNat m + Int32.ofNat f := by
    rw [Int32.le_iff_toInt_le, hfl32I, show ((0 : Int32).toInt = 0) from by decide]; omega
  have hfl8 : ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat = 1 + m + f := by
    rw [UInt32.toNat_toUInt8, Int32.toNat_toUInt32_of_le hflnn]
    show ((1 + Int32.ofNat m + Int32.ofNat f).toInt.toNat) % 2 ^ 8 = 1 + m + f
    rw [hfl32I]
    omega
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
      ).toInt.toNat - 1 < 5 := by
    rw [hpd]
    show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 < 5
    omega
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hbidx : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat := by
    have e1 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m := by
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = _
      rw [hdI8]
      omega
    have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
      rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
        (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
    have hikn : (0 : Int32) ≤
        (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
      rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
      omega
    have e2 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
        ).toUInt32.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m - 1 := by
      rw [Int32.toNat_toUInt32_of_le hikn]
      show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat = _
      rw [hik]
      omega
    rw [e1, e2]
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
      ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
        ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m).toInt8).toInt.toNat - 1]'(by
            show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
              ).toInt.toNat - 1 < 5
            omega) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  have hrcm := merge_real_chain' g pile hpile hwf B
    (p.pileDepth[pile.toNat]'hpile).toInt32 m hreal hmcards m (le_refl m)
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := by
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat m)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat m)
    have hb4 := VALUE_toNat B
    have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + m < 256 := by omega
    have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
    have hvm := hrcm.2
    omega
  -- `prevCard` (`flute_maximal`'s own `boundary - flute2`) is exactly
  -- `B - 1 - f` — a UInt8 group identity, no range condition needed.
  have hprevEq : (B + UInt8.ofNat m) - (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8
      = B - 1 - UInt8.ofNat f := by
    have hfl8' : (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 = UInt8.ofNat (1 + m + f) := by
      apply UInt8.toNat_inj.mp
      rw [hfl8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [hfl8']
    apply UInt8.toNat_inj.mp
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
    have hsumof : (UInt8.ofNat (1 + m + f)).toNat = 1 + m + f := by
      rw [UInt8.toNat_ofNat']; omega
    have hlt1 : B.toNat + m < 256 := by omega
    have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof, Nat.mod_eq_of_lt hlt1]
    have hle1 : UInt8.ofNat (1 + m + f) ≤ B + UInt8.ofNat m := by
      rw [UInt8.le_iff_toNat_le, hsumof, hBmB]; omega
    have hle2 : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hle3 : UInt8.ofNat f ≤ B - 1 := by
      rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2,
        show ((1 : UInt8).toNat = 1) from rfl]
      omega
    rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ hle3,
      UInt8.toNat_sub_of_le _ _ hle2, hBmB, hsumof, hfof,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete
    show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile ≤ 1 ∨
      (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 2]'(by rw [hpd]; omega) ≠
        (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut + 1
    rcases hmstop with hmA | ⟨hgt2, hidx2, hmB⟩
    · left
      rw [hpd, Int8.le_iff_toInt_le, hdI8]
      show (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ (1 : Int8).toInt
      rw [show ((1 : Int8).toInt = 1) from rfl]
      omega
    · right
      have hidxEq : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
          ).toInt.toNat - 2 =
          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat := by
        have h1 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
            ).toInt.toNat - 2 =
            ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat := by
          have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toInt =
              (p.pileDepth[pile.toNat]'hpile).toInt - m - 2 := by
            rw [depth_sub_ofNat_sub_two_eq (by rw [Int8.toInt_toInt32]; exact hd5)
              (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
          have hikn : (0 : Int32) ≤
              (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2 := by
            rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
            omega
          rw [Int32.toNat_toUInt32_of_le hikn]
          show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 2 =
            ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toInt.toNat
          rw [hik, hdI8]
          omega
        rw [hpd]; exact h1
      intro heq
      apply hmB
      have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 2]'(by rw [hpd]; omega)
          = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 2).toUInt32.toNat]'hidx2 := by
        congr 1
      rw [hstep] at heq
      rw [heq, hcardEqOut]
      have hstepB : B + UInt8.ofNat m + 1 = B + UInt8.ofNat (m + 1) := by
        rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
      rw [hstepB]
  · -- (3b) flute_maximal
    show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile = 0 ∨
      let boundary := (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut
      let prevCard := boundary - (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile)
          hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile
      (∃ hs : (SUIT boundary).toUInt32.toNat < 4,
        p.aces[(SUIT boundary).toUInt32.toNat]'hs = prevCard.toInt8) ∨
      ¬ isFreeCard g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) prevCard
    right
    simp only [hcardEqOut, hSm, hpf, hprevEq]
    rcases hfstop with hge | hnfree
    · left
      exact ⟨hs4, hge⟩
    · -- `hf_le_tight` only guarantees `f ≤ VALUE(B) - 1`: the residual case
      -- `f = VALUE(B) - 1` makes `prevCard = B - 1 - f` the suit's own
      -- value-0 sentinel, which isn't a real card, so the general
      -- not-free-preserved argument (needing `IsRealCard`) below doesn't
      -- apply there.  Handle it directly instead: the sentinel value is
      -- pinned between `aces[suit]`'s suit-block lower bound
      -- (`aces_kings_valid`) and the freed-loop's own upper bound at the
      -- last step, forcing `aces[suit] = prevCard` exactly (the *other*
      -- disjunct) rather than needing to transport `hnfree`.
      have hle2 : (1 : UInt8) ≤ B := by
        rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
      have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
      have hle3 : UInt8.ofNat f ≤ B - 1 := by
        rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2,
          show ((1 : UInt8).toNat = 1) from rfl]
        omega
      have hprevNat : (B - 1 - UInt8.ofNat f).toNat = B.toNat - 1 - f := by
        rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ hle2,
          show ((1 : UInt8).toNat = 1) from rfl, hfof]
      have hsn := SUIT_toNat B
      have hvn := VALUE_toNat B
      have hs1 : (SUIT B).toNat < 4 := hreal.1
      have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
      have hv2 : (VALUE B).toNat ≤ 13 := hreal.2.2
      have hBdecomp : B.toNat = 16 * (SUIT B).toNat + (VALUE B).toNat := by omega
      by_cases hfeq : f = (VALUE B).toNat - 1
      · left
        refine ⟨hs4, ?_⟩
        have hprevlt128 : (B - 1 - UInt8.ofNat f).toNat < 128 := by omega
        have hacesLt : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat f).toInt8 := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · rw [hf0, show UInt8.ofNat 0 = 0 from rfl, UInt8.sub_zero]
            exact haces_lt_B
          · exact (hffree f hfpos (le_refl f)).2
        have hbf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
          have hlef : UInt8.ofNat f ≤ B := by
            rw [UInt8.le_iff_toNat_le, hfof]; omega
          rw [UInt8.toNat_sub_of_le _ _ hlef, hfof]
        have hbflt128 : (B - UInt8.ofNat f).toNat < 128 := by omega
        have hacesLeNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat ≤
            (B - 1 - UInt8.ofNat f).toNat := by
          have hlt := Int8.lt_iff_toInt_lt.mp hacesLt
          rw [uint8_toInt8_toInt_of_lt128 hbflt128] at hlt
          have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
              (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
            Int8.toNat_toUInt8_of_le haces0
          rw [hacesNat, hprevNat]
          omega
        have hacesGeNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat ≥
            16 * (SUIT B).toNat := by
          have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
          have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
          have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
              p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
          have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
          have hSAeq : (SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat =
              (SUIT B).toUInt32.toNat := by
            rw [← hgetEq, hak.1]
            show (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat
            rw [UInt8.toNat_ofNat']
            omega
          have hAdecomp : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
              16 * (SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat +
                (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat := by
            have h1 := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
            have h2 := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
            omega
          omega
        have hprevSentinelNat : (B - 1 - UInt8.ofNat f).toNat = 16 * (SUIT B).toNat := by
          rw [hprevNat, hBdecomp, hfeq]; omega
        have hEqNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
            (B - 1 - UInt8.ofNat f).toNat := by omega
        apply Int8.toInt_inj.mp
        rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
        have hcast : ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat : Int) =
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt :=
          Int.toNat_of_nonneg (by
            rw [← show ((0 : Int8).toInt = 0) from rfl]; exact Int8.le_iff_toInt_le.mp haces0)
        have hacesNat2 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
          Int8.toNat_toUInt8_of_le haces0
        omega
      · right
        exact preCleanupPile_not_free_of_lt_boundary g pile hpile hwf B
          (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
          (B - 1 - UInt8.ofNat f) (by
            have hsn' := SUIT_toNat (B - 1 - UInt8.ofNat f)
            have hvn' := VALUE_toNat (B - 1 - UInt8.ofNat f)
            have hprevVal : (VALUE (B - 1 - UInt8.ofNat f)).toNat = (VALUE B).toNat - 1 - f := by
              rw [hvn', hprevNat, hBdecomp]
              omega
            have hprevSuit : (SUIT (B - 1 - UInt8.ofNat f)).toNat = (SUIT B).toNat := by
              rw [hsn', hprevNat, hBdecomp]
              omega
            refine ⟨?_, ?_, ?_⟩
            · omega
            · omega
            · omega)
          (by omega) hnfree
  · -- (6) busyAces_complete
    intro hdi
    show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
        ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toUInt32.toNat < 4,
      (p.aces[(SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toUInt32.toNat]'hs
        ).toUInt8 =
        (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut -
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile →
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces &&&
        ((1 : UInt8) <<< (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut))) ≠ 0
    rw [hcardEqOut, hSm, hpf, hprevEq]
    intro hs heq
    have hbusy : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces =
        if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8 then
          p.busyAces ||| (1 : UInt8) <<< SUIT B
        else p.busyAces := by
      simp only [preCleanupPile]
    have heq' : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 := by
      rw [← Int8.toInt8_toUInt8 (x := p.aces[(SUIT B).toUInt32.toNat]'hs4), heq]
    have hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true := by
      rw [heq']; exact beq_self_eq_true _
    rw [hbusy, hcond]
    simp only [reduceIte]
    have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
    exact uint8_and_ne_zero_of_or_right (uint8_shift_self_ne_zero (SUIT B) hs4')

/-- **`PileMerged` survives `preCleanupPile` at every OTHER pile `j ≠ pile`.**
    Counterpart of `preCleanupPile_pileBase_ne` for the merged layer.
    `merge_complete` transfers verbatim (only reads `pos2card`/`pileDepth[j]`,
    both untouched). `busyAces_complete` transfers because `preCleanupPile`'s
    `busyAces` write only ever ORs in one more bit
    (`uint8_and_ne_zero_of_or_left`). `flute_maximal` is the hard clause: its
    `¬isFreeCard` disjunct needs `prevCard` (pile `j`'s own flute predecessor)
    to never coincide with one of the `m` merge-absorbed cards `B, …, B+m-1`
    (which the cleanup step reveals as newly free) — proved via
    `hb.flute_cards_free`/`WellFormedLayout.round_trip_inv` case analysis on
    `p.pileFlute.get j`, then `preCleanupPile_not_free_of_ne_absorbed` carries
    the rest across. -/
theorem preCleanupPile_pileMerged_ne (pile : UInt32) (g : Globals) (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (p : SolverPosType) (m f : Nat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hak : ∀ s : Fin 4, SUIT (p.aces.get s).toUInt8 = s.val.toUInt8)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hb : PileBase g p j) (hpm : PileMerged g p j hb.pileDepth_bound) :
    PileMerged g (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) j
      (by rw [preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj]
          exact hb.pileDepth_bound) := by
  have hdeq := preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f j hj
  have hfeq := preCleanupPile_pileFlute_eq_of_ne pile hpile B ph hs4 p m f j hj
  have haeq := preCleanupPile_aces_eq pile hpile B ph hs4 p m f
  have hm : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt := by omega
  have hdmono := preCleanupPile_pileDepth_le pile hpile B ph hs4 p m f hd5 hm
  -- `B` is real, from `hmcards` at `k = 0` (its own boundary slot).
  obtain ⟨hidx0, heq0⟩ := hmcards 0 (Nat.zero_le _)
  have hBcard : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
      Int32.ofNat 0 - 1).toUInt32.toNat]'hidx0 = B := by
    rw [heq0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
  have hreal : IsRealCard B :=
    hBcard ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat 0 - 1).toUInt32.toNat, hidx0⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1; have h2 := hreal.2.1; have h3 := hreal.2.2
    omega
  -- The shrunk depth, as a plain integer fact, reused by both the `hkeqm`
  -- direct argument in `flute_maximal` and (implicitly) by the private lemma
  -- calls below.
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · -- (2) merge_complete: transfers verbatim (only reads `pos2card`/`pileDepth[j]`).
    have hidxEq2 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 2 =
        (p.pileDepth.get j).toInt.toNat - 2 := by rw [hdeq]
    have hidxEq1 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hX2 : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 2,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq2
    have hX1 : (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ =
        (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ := by
      congr 1
      exact Fin.ext hidxEq1
    rw [hX2, hX1, hdeq]
    exact hpm.merge_complete
  · -- (3b) flute_maximal: the hard clause.
    by_cases hd0 : p.pileDepth.get j = 0
    · left
      rw [hdeq]
      exact hd0
    · have hdj : (p.pileDepth.get j).toInt.toNat > 0 := by
        have h1 := hb.pileDepth_nonneg
        rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at h1
        have h2 : (p.pileDepth.get j).toInt ≠ 0 := by
          intro hz
          apply hd0
          apply Int8.toInt_inj.mp
          rw [hz, show ((0 : Int8).toInt = 0) from rfl]
        omega
      right
      set boundaryNew := (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
          by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew_def
      set prevCardNew := boundaryNew - (preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.get j with hprevCardNew_def
      show (∃ hs : (SUIT boundaryNew).toNat < 4,
          (preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).aces.get ⟨(SUIT boundaryNew).toNat, hs⟩ = prevCardNew.toInt8) ∨
        ¬ isFreeCard g (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) prevCardNew
      set boundary := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
          by have := hb.pileDepth_bound; omega⟩ with hboundary_def
      set prevCard := boundary - p.pileFlute.get j with hprevCard_def
      have hidxEqB : ((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1 =
          (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
      have hboundEq : boundaryNew = boundary := by
        rw [hboundaryNew_def, hboundary_def]
        congr 1
        exact Fin.ext hidxEqB
      have hprevEq : prevCardNew = prevCard := by
        rw [hprevCardNew_def, hprevCard_def, hboundEq, hfeq]
      rw [hboundEq, hprevEq, haeq]
      have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
      have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
      have hBDrange : boundary.toNat ≤ 61 := by
        have hsn := SUIT_toNat boundary
        have hvn := VALUE_toNat boundary
        have h1 := hrealBd.1; have h2 := hrealBd.2.1; have h3 := hrealBd.2.2
        omega
      have hflv : (p.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
        hb.flute_le_value hwf hak hdj
      have hVsn_bd := VALUE_toNat boundary
      have hSsn_bd := SUIT_toNat boundary
      have hfleB : p.pileFlute.get j ≤ boundary := by
        rw [UInt8.le_iff_toNat_le]
        have := Nat.mod_le boundary.toNat 16
        omega
      have hprevNat : prevCard.toNat = boundary.toNat - (p.pileFlute.get j).toNat :=
        UInt8.toNat_sub_of_le _ _ hfleB
      have hSUITeq : SUIT prevCard = SUIT boundary := by
        apply UInt8.toNat_inj.mp
        rw [SUIT_toNat, SUIT_toNat, hprevNat]
        omega
      have hVALeq : (VALUE prevCard).toNat =
          (VALUE boundary).toNat - (p.pileFlute.get j).toNat := by
        rw [VALUE_toNat, hprevNat]
        omega
      have hsuiteq : SUIT boundary = (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 := by
        show SUIT boundary = ((SUIT boundary).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      rcases hpm.flute_maximal.resolve_left hd0 with hOldA | hOldNF
      · left
        exact hOldA
      · by_cases hV0 : (VALUE prevCard).toNat = 0
        · -- `prevCard` is the suit's own zero-value sentinel: the NEW
          -- unconditional Nat-based `flute_not_aces` upper bound (`hb`, no
          -- offset/case-split needed), combined with the suit-block lower
          -- bound, pins `aces = prevCard` exactly (no old `≥`/inequality
          -- special-casing needed anymore).
          left
          refine ⟨hs4', ?_⟩
          have haces0 : (0 : Int8) ≤ p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩ :=
            int8_nonneg_of_suit (hak ⟨(SUIT boundary).toNat, hs4'⟩)
          have hSuitAcesEq :
              SUIT ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8) = SUIT boundary := by
            rw [hak ⟨(SUIT boundary).toNat, hs4'⟩, ← hsuiteq]
          have hVBnat := VALUE_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
          have hSBnat := SUIT_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
          have hSeq := congrArg UInt8.toNat hSuitAcesEq
          have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
          have hacesGeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat ≥ prevCard.toNat := by
            rw [hprevNat0]; omega
          have hboundUpper : (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat +
              (p.pileFlute.get j).toNat ≤ boundary.toNat := hb.flute_not_aces hdj hs4'
          have hacesLeNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat ≤ prevCard.toNat := by
            rw [hprevNat]; omega
          have hacesEqNat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat = prevCard.toNat :=
            le_antisymm hacesLeNat hacesGeNat
          have hprevlt128 : prevCard.toNat < 128 := by omega
          apply Int8.toInt_inj.mp
          rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
          have haces0' : (0 : Int) ≤ (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt := by
            rw [← show ((0 : Int8).toInt = 0) from rfl]
            exact Int8.le_iff_toInt_le.mp haces0
          have hcast : ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt.toNat : Int) =
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt := Int.toNat_of_nonneg haces0'
          have hacesIntEqUInt8Nat :
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt.toNat =
              (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat := by
            rw [Int8.toNat_toUInt8_of_le haces0]
            rfl
          omega
        · -- `prevCard` is a genuine real card: transfer `¬isFreeCard` across
          -- cleanup via `preCleanupPile_not_free_of_ne_absorbed`, once we've
          -- ruled out `prevCard = B + k` for every `k ≤ m`.
          right
          have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
          have hVle : (VALUE prevCard).toNat ≤ 13 := by
            have := hrealBd.2.2
            omega
          have hCrealPrev : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
          by_cases hkeqm : prevCard = B + UInt8.ofNat m
          · -- `prevCard` is exactly pile `pile`'s NEW boundary card: it stays
            -- resident (not free) directly, no need to rule out any `k`.
            rw [hkeqm]
            obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
            have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
              ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat,
                hidxm⟩
            have heqm' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                (⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat,
                  hidxm⟩ : Fin 5) = B + UInt8.ofNat m := heqm
            rw [heqm'] at hrt
            have hrealBm : IsRealCard (B + UInt8.ofNat m) := heqm ▸ hwf.pos2card_real _ _
            have hc64 : (B + UInt8.ofNat m).toNat < 64 := by
              have := hrealBm.1
              have hsn := SUIT_toNat (B + UInt8.ofNat m)
              omega
            have hp64 : (cardPile g (B + UInt8.ofNat m)).toNat < 10 := by
              rw [hrt.1]; exact hpile
            intro hfree
            have hge := isFree_to_cardDepth_ge g (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) hwf
              (B + UInt8.ofNat m) hc64 hp64 hfree
            have hstepD : (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
                ).pileDepth[(cardPile g (B + UInt8.ofNat m)).toNat]'hp64 =
                (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile := by
              congr 1
              exact hrt.1
            rw [hstepD] at hge
            have hpdNew : (preCleanupPile pile hpile B ph hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
                ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
              simp only [preCleanupPile]
              rw [Vector.getElem_set_self]
            have hcdEqIdxM : (cardDepth g (B + UInt8.ofNat m)).toNat =
                ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat :=
              hrt.2
            rw [hpdNew, hcdEqIdxM] at hge
            have hidxmI : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                Int32.ofNat m - 1).toInt = (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
              rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
            have hidxmNN : (0 : Int32) ≤
                (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
              rw [Int32.le_iff_toInt_le, hidxmI, show ((0 : Int32).toInt = 0) from by decide]
              omega
            have hidxmNat : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m -
                1).toUInt32.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m - 1 := by
              rw [Int32.toNat_toUInt32_of_le hidxmNN]
              show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat = _
              rw [hidxmI]; omega
            rw [hidxmNat] at hge
            have hdI8Nat : (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                Int32.ofNat m).toInt8).toInt.toNat =
                (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m := by
              rw [hdI8]; omega
            rw [hdI8Nat] at hge
            omega
          · -- `prevCard ≠ B + m`; combined with the shift-argument for `k < m`,
            -- rule out `prevCard = B + k` for the FULL range `k ≤ m`.
            have hne : ∀ k, k ≤ m → prevCard ≠ B + UInt8.ofNat k := by
              intro k hkm heq
              rcases Nat.lt_or_eq_of_le hkm with hklt | hkeq
              · -- `k < m`: shift by one, landing on a card known to sit
                -- strictly inside pile `pile`'s (still fully occupied) OLD
                -- range, contradicting either `flute_cards_free` (pileFlute
                -- ≥ 2) or the cross-pile clash `j = pile` (pileFlute = 1).
                obtain ⟨hidxk1, heqk1⟩ := hmcards (k + 1) (by omega)
                set C := B + UInt8.ofNat (k + 1) with hCdef
                have hrealC : IsRealCard C := heqk1 ▸ hwf.pos2card_real _ _
                have hc64C : C.toNat < 64 := by
                  have := hrealC.1
                  have hsn := SUIT_toNat C
                  omega
                have hrtC := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
                  ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat (k + 1) - 1).toUInt32.toNat, hidxk1⟩
                have heqk1' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                    (⟨((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (k + 1) - 1).toUInt32.toNat, hidxk1⟩ : Fin 5) = C := heqk1
                rw [heqk1'] at hrtC
                have hp64C : (cardPile g C).toNat < 10 := by rw [hrtC.1]; exact hpile
                have hCnotfree : ¬ isFreeCard g p C := by
                  intro hfreeC
                  have hgeC := isFree_to_cardDepth_ge g p hwf C hc64C hp64C hfreeC
                  have hstepDC : p.pileDepth[(cardPile g C).toNat]'hp64C =
                      p.pileDepth[pile.toNat]'hpile := by
                    congr 1; exact hrtC.1
                  have hcdEqIdx : (cardDepth g C).toNat =
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat (k + 1) - 1).toUInt32.toNat := hrtC.2
                  rw [hstepDC, hcdEqIdx] at hgeC
                  have hidxk1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (k + 1) - 1).toInt =
                      (p.pileDepth[pile.toNat]'hpile).toInt - (k + 1) - 1 := by
                    rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                      (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                    push_cast
                    ring
                  have hidxk1NN : (0 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (k + 1) - 1 := by
                    rw [Int32.le_iff_toInt_le, hidxk1I,
                      show ((0 : Int32).toInt = 0) from by decide]
                    omega
                  have hidxk1Nat : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (k + 1) - 1).toUInt32.toNat =
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat - (k + 1) - 1 := by
                    rw [Int32.toNat_toUInt32_of_le hidxk1NN]
                    show ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (k + 1) - 1).toInt.toNat = _
                    rw [hidxk1I]; omega
                  rw [hidxk1Nat] at hgeC
                  omega
                have hCeqPrevSucc : C = prevCard + 1 := by
                  rw [hCdef, heq]
                  have hstepB : B + UInt8.ofNat k + 1 = B + UInt8.ofNat (k + 1) := by
                    rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
                  rw [← hstepB]
                by_cases hflj : (2 : UInt8) ≤ p.pileFlute.get j
                · -- pileFlute[j] ≥ 2: `boundary - (pileFlute - 1) = prevCard + 1`
                  -- is a flute-interior card, hence free — contradicting
                  -- `hCnotfree` (`C = prevCard + 1`).
                  have h1le : (1 : UInt8) ≤ p.pileFlute.get j := by
                    rw [UInt8.le_iff_toNat_le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (1 : UInt8).toNat = 1 := rfl
                    have h4 : (2 : UInt8).toNat = 2 := rfl
                    omega
                  have hoffLt : (p.pileFlute.get j - 1).toNat < (p.pileFlute.get j).toNat := by
                    rw [UInt8.toNat_sub_of_le _ _ h1le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (2 : UInt8).toNat = 2 := rfl
                    have h4 : (1 : UInt8).toNat = 1 := rfl
                    omega
                  have hoffPos : 0 < (p.pileFlute.get j - 1).toNat := by
                    rw [UInt8.toNat_sub_of_le _ _ h1le]
                    have h2 : (2 : UInt8).toNat ≤ (p.pileFlute.get j).toNat :=
                      UInt8.le_iff_toNat_le.mp hflj
                    have h3 : (2 : UInt8).toNat = 2 := rfl
                    have h4 : (1 : UInt8).toNat = 1 := rfl
                    omega
                  have hfreeInterior :
                      isFreeCard g p (boundary - (p.pileFlute.get j - 1)) :=
                    hb.flute_cards_free (p.pileFlute.get j - 1) hdj hoffPos hoffLt
                  have hcardEq : boundary - (p.pileFlute.get j - 1) = prevCard + 1 := by
                    rw [hprevCard_def]
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    have hfleBNat : (p.pileFlute.get j).toNat ≤ boundary.toNat :=
                      UInt8.le_iff_toNat_le.mp hfleB
                    have hfm1le : p.pileFlute.get j - 1 ≤ boundary := by
                      rw [UInt8.le_iff_toNat_le, UInt8.toNat_sub_of_le _ _ h1le, h1]
                      omega
                    apply UInt8.toNat_inj.mp
                    rw [UInt8.toNat_sub_of_le _ _ hfm1le, UInt8.toNat_sub_of_le _ _ h1le, h1]
                    have hlt256 : boundary.toNat - (p.pileFlute.get j).toNat + 1 < 2 ^ 8 := by omega
                    rw [UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hfleB, h1,
                      Nat.mod_eq_of_lt hlt256]
                    omega
                  rw [hcardEq] at hfreeInterior
                  exact hCnotfree (hCeqPrevSucc ▸ hfreeInterior)
                · -- pileFlute[j] = 1 (`flute_pos` rules out 0): `prevCard + 1 =
                  -- boundary` exactly, so `C = boundary` — but `boundary`'s own
                  -- pile is `j`, while `C`'s is `pile`, forcing `j = pile`.
                  have hfl1 : p.pileFlute.get j = 1 := by
                    have hpos := hb.flute_pos
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    have h2 : (2 : UInt8).toNat = 2 := rfl
                    have hlt2 : (p.pileFlute.get j).toNat < 2 := by
                      by_contra hge
                      apply hflj
                      rw [UInt8.le_iff_toNat_le, h2]
                      omega
                    apply UInt8.toNat_inj.mp
                    omega
                  have hCeqBoundary : C = boundary := by
                    have hle1 : (1 : UInt8) ≤ boundary := by
                      rw [UInt8.le_iff_toNat_le]
                      have h1' : (1 : UInt8).toNat = 1 := rfl
                      have := hrealBd.2.1
                      omega
                    rw [hCeqPrevSucc, hprevCard_def, hfl1]
                    have h1 : (1 : UInt8).toNat = 1 := rfl
                    apply UInt8.toNat_inj.mp
                    rw [UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle1, h1]
                    have hlt256 : boundary.toNat - 1 + 1 < 2 ^ 8 := by omega
                    rw [Nat.mod_eq_of_lt hlt256]
                    omega
                  have hrtBd := hwf.round_trip_inv j ⟨(p.pileDepth.get j).toInt.toNat - 1,
                    by have := hb.pileDepth_bound; omega⟩
                  have hjEqPile : j.val = pile.toNat := by
                    rw [hCeqBoundary, hboundary_def] at hrtC
                    rw [hrtBd.1] at hrtC
                    exact hrtC.1
                  exact hj hjEqPile
              · rw [hkeq] at heq; exact hkeqm heq
            exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B ph hs4 hBrange.2
              p m f hd5 hm_le hmcards prevCard hCrealPrev hne hOldNF
  · -- (6) busyAces_complete
    intro hdi
    have hdi' : (p.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdi
    set boundaryNew2 := (g.pos2card.get j).get ⟨((preCleanupPile pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
        by rw [hdeq]; have := hb.pileDepth_bound; omega⟩ with hboundaryNew2_def
    show ∀ hs : (SUIT boundaryNew2).toNat < 4,
        ((preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).aces.get ⟨(SUIT boundaryNew2).toNat, hs⟩).toUInt8 =
          boundaryNew2 - (preCleanupPile pile hpile B ph hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.get j →
        (preCleanupPile pile hpile B ph hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).busyAces &&& ((1 : UInt8) <<< SUIT boundaryNew2) ≠ 0
    set boundaryOld2 := (g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩ with hboundaryOld2_def
    have hidxEqB2 : ((preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1 =
        (p.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
    have hboundEq2 : boundaryNew2 = boundaryOld2 := by
      rw [hboundaryNew2_def, hboundaryOld2_def]
      congr 1
      exact Fin.ext hidxEqB2
    rw [hboundEq2, hfeq, haeq]
    intro hs heq
    have hbusy_eq : (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces =
        if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8 then
          p.busyAces ||| (1 : UInt8) <<< SUIT B
        else p.busyAces := by
      simp only [preCleanupPile]
    rw [hbusy_eq]
    split
    · exact uint8_and_ne_zero_of_or_left (hpm.busyAces_complete hdi' hs heq)
    · exact hpm.busyAces_complete hdi' hs heq

/-- **`preCleanupPile` leaves the pile it just wrote `PileClean`.**  Combines
    `preCleanupPile_pileBase_self` and `preCleanupPile_pileMerged_self` into the
    full per-pile bundle. -/
theorem preCleanupPile_pileClean_self (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hmstop : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1 ∨
      (1 < (p.pileDepth[pile.toNat]'hpile).toInt - m ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f)) :
    PileClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) ⟨pile.toNat, hpile⟩ := by
  have hb := preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hf_le hffree
  have hm := preCleanupPile_pileMerged_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hmstop hf_le hf_le_tight hffree hfstop hb.pileDepth_bound
  exact { hb, hm with }

/-- **`preCleanupPile`'s output has bounded depth everywhere**, not just at
    `pile` itself — the parameter `SuitClean` needs (its `king_frontier`/
    `foundation_maximal_weak` clauses index into whichever pile happens to
    witness a flute-top, which may be any pile, not just `pile`).  At `pile`
    itself this is `preCleanupPile_pileBase_self`'s own `pileDepth_bound`
    field; everywhere else the depth is untouched
    (`preCleanupPile_pileDepth_eq_of_ne`), so it's just `hnf`'s own bound. -/
theorem preCleanupPile_pileDepth_bound_all (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hf_le : f ≤ B.toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8) :
    ∀ i : Fin 10, ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i).toInt.toNat ≤ 5 := by
  intro i
  by_cases hip : i.val = pile.toNat
  · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip
    subst hii
    exact (preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
      m f hm_le hmcards hf_le hffree).pileDepth_bound
  · rw [preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
      i hip]
    exact hnf.pileDepth_bound i

set_option maxHeartbeats 1000000 in
/-- **`SuitClean` holds for every suit `s` after `preCleanupPile`.**  The
    hardest part of the per-pile/per-suit tower split: unlike `PileBase`/
    `PileMerged` (which only ever look at `pile` itself), `SuitClean`'s
    `foundation_maximal_weak`/`king_frontier` clauses quantify over an
    arbitrary suit `s` and reference a `¬isFreeCard` fact about the
    foundation-successor / king-frontier card, which `preCleanupPile` can
    only possibly disturb if that card happens to be one of the `m`
    merge-absorbed cards `B, …, B+m-1` — all of suit `SUIT B`
    (`merge_real_chain'`).  So for `s ≠ SUIT B` the witness card provably
    isn't in the revealed range (different suit ⟹ can't equal `B+k`) and
    `preCleanupPile_not_free_of_ne_absorbed` transfers `¬isFreeCard` directly;
    for `s = SUIT B` a delicate case analysis (ported from the old monolithic
    `cleanupPile_baseNF`'s non-king branch) pins the witness down to exactly
    `B` itself when it IS in the revealed range, forcing `f = 0`
    (`hAeqB_implies_f0`) and landing the argument in the "flute-top witness is
    `pile` itself" disjunct instead. -/
theorem preCleanupPile_suitClean (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
    (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
        ).toUInt32.toNat]'hidx = B)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
    (hmstop : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1 ∨
      (1 < (p.pileDepth[pile.toNat]'hpile).toInt - m ∧
        ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat < 5,
          (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
    (hf_le : f ≤ B.toNat - 1)
    (hf_le_tight : f ≤ (VALUE B).toNat - 1)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
    (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
    (s : Fin 4) :
    SuitClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) s
        (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
          m f hm_le hmcards hf_le hffree) := by
  have hreal : IsRealCard B :=
    hBdef ▸ hwf.pos2card_real ⟨pile.toNat, hpile⟩
      ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩
  have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
    have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
    have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
    have h1 := hreal.1
    have h2 := hreal.2.1
    have h3 := hreal.2.2
    omega
  have h1B : (1 : UInt8) ≤ B := by
    rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have haces0 : (0 : Int8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 :=
    int8_nonneg_of_suit (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).aces_kings_valid.1
  have h1le : (1 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 := by
    rw [Int32.le_iff_toInt_le, Int32.toInt_one, Int8.toInt_toInt32]; omega
  have hsubd : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by
    rw [Int32.toInt_sub_of_le _ _ (by decide) h1le, Int32.toInt_one, Int8.toInt_toInt32]
  have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
    show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
    apply UInt8.toNat_inj.mp
    have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
      rw [UInt8.toNat_ofNat']
    have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
    omega
  have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B.toInt8 := by
    by_contra hge
    rw [Int8.lt_iff_toInt_lt] at hge
    rw [not_lt] at hge
    have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
    have h1 : (B.toNat : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
      rwa [htiB] at hge
    have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
      rw [Int8.toNat_toUInt8_of_le haces0]
      have hbdg : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNatClampNeg =
          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat := rfl
      omega
    have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
    have hak := hacesEq ▸ (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).aces_kings_valid
    have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
        p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
    have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
      rw [← hgetEq, hak.1, ← hsuiteq]
    have hVBS : (VALUE B).toNat ≤
        (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat := by
      have hb1 := VALUE_toNat B
      have hb2 := SUIT_toNat B
      have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hsEq := congrArg UInt8.toNat hSuitAces
      omega
    have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
      (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).foundation_cards_free B hsuiteq hreal.2.1
        hVBS
    have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
      rw [← hBdef]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩ (by
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          rw [Int32.toNat_toUInt32_of_le (by
            rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]
            omega)]
          have hbdg1 : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat <
            (p.pileDepth[pile.toNat]'hpile).toInt.toNat
          omega)
    exact hnfB hfree
  -- Arithmetic facts (identical to `preCleanupPile_pileMerged_self`'s preamble).
  have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_sub_of_le _ _
      (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
      (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
      hmofI, Int8.toInt_toInt32]
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
    rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have h1mI : ((1 : Int32) + Int32.ofNat m).toInt = 1 + (m : Int) := by
    rw [Int32.toInt_add, Int32.toInt_one, hmofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hfl32I : ((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toInt = 1 + (m : Int) + f := by
    rw [Int32.toInt_add, h1mI, hfofI]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hflnn : (0 : Int32) ≤ 1 + Int32.ofNat m + Int32.ofNat f := by
    rw [Int32.le_iff_toInt_le, hfl32I, show ((0 : Int32).toInt = 0) from by decide]; omega
  have hfl8 : ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat = 1 + m + f := by
    rw [UInt32.toNat_toUInt8, Int32.toNat_toUInt32_of_le hflnn]
    show ((1 + Int32.ofNat m + Int32.ofNat f).toInt.toNat) % 2 ^ 8 = 1 + m + f
    rw [hfl32I]
    omega
  have hpd : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hpf : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile =
      (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 := by
    simp only [preCleanupPile]
    rw [Vector.getElem_set_self]
  have hboundOut : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile
      ).toInt.toNat - 1 < 5 := by
    rw [hpd]
    show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 < 5
    omega
  obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
  have hbidx : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ).toInt.toNat - 1 =
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat := by
    have e1 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m := by
      show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat = _
      rw [hdI8]
      omega
    have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
      rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
        (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
    have hikn : (0 : Int32) ≤
        (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
      rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
      omega
    have e2 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
        ).toUInt32.toNat = (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m - 1 := by
      rw [Int32.toNat_toUInt32_of_le hikn]
      show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat = _
      rw [hik]
      omega
    rw [e1, e2]
  have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
      ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
      = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
          ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
      congr 1
    rw [hstep, heqm]
  have hcardEqOut : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
      ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut = B + UInt8.ofNat m := by
    have hstep : (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
        (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
        ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut
        = (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat m).toInt8).toInt.toNat - 1]'(by
            show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
              ).toInt.toNat - 1 < 5
            omega) := by
      congr 1
      rw [hpd]
    rw [hstep]
    exact hcardEq
  have hprevEq : (B + UInt8.ofNat m) - (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8
      = B - 1 - UInt8.ofNat f := by
    have hfl8' : (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 =
        UInt8.ofNat (1 + m + f) := by
      apply UInt8.toNat_inj.mp
      rw [hfl8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [hfl8']
    apply UInt8.toNat_inj.mp
    have hmof : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
    have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
    have hsumof : (UInt8.ofNat (1 + m + f)).toNat = 1 + m + f := by
      rw [UInt8.toNat_ofNat']; omega
    have hlt1 : B.toNat + m < 256 := by omega
    have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
      rw [UInt8.toNat_add, hmof, Nat.mod_eq_of_lt hlt1]
    have hle1 : UInt8.ofNat (1 + m + f) ≤ B + UInt8.ofNat m := by
      rw [UInt8.le_iff_toNat_le, hsumof, hBmB]; omega
    have hle2 : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hle3 : UInt8.ofNat f ≤ B - 1 := by
      rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ hle2,
        show ((1 : UInt8).toNat = 1) from rfl]
      omega
    rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ hle3,
      UInt8.toNat_sub_of_le _ _ hle2, hBmB, hsumof, hfof,
      show ((1 : UInt8).toNat = 1) from rfl]
    omega
  -- Depth-monotonicity bridge (`fluteNorm p` → the cleaned position), used by
  -- `isFreeCard_mono` everywhere below (mirrors `preCleanupPile_pileBase_ne`'s
  -- own `hdmono`).
  have hdec : ∀ i : Fin 10, ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i).toInt.toNat ≤
      ((fluteNorm pile hpile p).pileDepth.get i).toInt.toNat :=
    preCleanupPile_pileDepth_le pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f hd5
      (by omega)
  -- `aces`/`kings` are entirely untouched by `preCleanupPile`.
  have haeq := preCleanupPile_aces_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
  have hkeqV := preCleanupPile_kings_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
  -- `SUIT(B+j) = SUIT B`/`VALUE(B+j) = VALUE B + j` for every `j ≤ m` (not just
  -- `j = m`): the merge-absorbed run never crosses a suit boundary.
  have hRCgen : ∀ j : Nat, j ≤ m →
      (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
    (merge_real_chain' g pile hpile hwf B (p.pileDepth[pile.toNat]'hpile).toInt32 m hreal
      hmcards j hjm).2
  have hSjEq : ∀ j : Nat, j ≤ m → SUIT (B + UInt8.ofNat j) = SUIT B := by
    intro j hjm
    apply UInt8.toNat_inj.mp
    have hb1 := SUIT_toNat (B + UInt8.ofNat j)
    have hb2 := SUIT_toNat B
    have hb3 := VALUE_toNat (B + UInt8.ofNat j)
    have hb4 := VALUE_toNat B
    have hjB : (UInt8.ofNat j).toNat = j := by rw [UInt8.toNat_ofNat']; omega
    have hlt256 : B.toNat + j < 256 := by omega
    have hadd : (B + UInt8.ofNat j).toNat = B.toNat + j := by
      rw [UInt8.toNat_add, hjB, Nat.mod_eq_of_lt hlt256]
    have hvj := hRCgen j hjm
    omega
  have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := hSjEq m (le_refl m)
  -- `f = 0` whenever the ace-successor witness pins `A = B` exactly (else the
  -- freed loop's own `l = 1` fact would force the strict inequality
  -- `aces[SUIT B] < B - 1`, contradicting `aces[SUIT B] = B - 1`).
  -- Pure UInt8 group arithmetic: `A + 1 = B ⟹ A = B - 1`, via `toNat`
  -- injection (needs `A.toUInt8.toNat < 255`, from the suit/value bound).
  have hAeqBm1_of : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B →
      (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = B - 1 := by
    intro hAB
    have hak1 : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
        ((SUIT B).toUInt32.toNat).toUInt8 :=
      (hnf.suitClean ⟨(SUIT B).toUInt32.toNat, hs4⟩).aces_kings_valid.1
    have hb1 := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
    have hb2 := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
    have hb3 := congrArg UInt8.toNat hak1
    have hb4 : ((SUIT B).toUInt32.toNat).toUInt8.toNat = (SUIT B).toUInt32.toNat := by
      rw [UInt8.toNat_ofNat']; omega
    have hacesLt255 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat < 255 := by omega
    have htoNatSucc : ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1).toNat =
        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat + 1 :=
      toNat_succ _ hacesLt255
    have hABn := congrArg UInt8.toNat hAB
    rw [htoNatSucc] at hABn
    have hBm1 : (B - 1).toNat = B.toNat - 1 := UInt8.toNat_sub_of_le _ _ h1B
    apply UInt8.toNat_inj.mp
    rw [hBm1]; omega
  have hAeqB_implies_f0 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B →
      f = 0 := by
    intro hAB
    by_contra hfne
    have hf1 : 1 ≤ f := by omega
    have hg := (hffree 1 (le_refl 1) hf1).2
    have h1eq : (UInt8.ofNat 1 : UInt8) = 1 := rfl
    rw [h1eq] at hg
    have hUeq := hAeqBm1_of hAB
    have h2 := congrArg UInt8.toInt8 hUeq
    rw [Int8.toInt8_toUInt8] at h2
    rw [h2] at hg
    have hlt := Int8.lt_iff_toInt_lt.mp hg
    omega
  -- `busyAces` monotonicity: `preCleanupPile` either leaves it alone or ORs in
  -- one more bit, so an already-set bit stays set (mirrors `nf_setBusyAces`).
  have hbusyMono : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
      (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces &&& mask ≠ 0 := by
    intro mask hmask
    show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8 then
        p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&& mask ≠ 0
    by_cases hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
        (B - 1 - UInt8.ofNat f).toInt8) = true
    · simp only [hcond, reduceIte]
      exact uint8_and_ne_zero_of_or_left hmask
    · rw [Bool.not_eq_true] at hcond
      simp only [hcond, Bool.false_eq_true, reduceIte]
      exact hmask
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) aces_kings_valid: `aces`/`kings` untouched.
    rw [haeq, hkeqV]
    exact (hnf.suitClean s).aces_kings_valid
  · -- (4a) foundation_cards_free: aces unchanged, freeness monotone.
    intro c h1 h2 h3
    rw [haeq] at h3
    exact isFreeCard_mono hdec ((hnf.suitClean s).foundation_cards_free c h1 h2 h3)
  · -- (4b-weak) foundation_maximal_weak: `aces` untouched, so only the
    -- `¬isFreeCard`/busy disjuncts need real work, and only for `s = SUIT B`
    -- (any other suit's witness can't be a merge-absorbed card).
    rw [haeq]
    by_cases hAV13 : (VALUE (p.aces.get s).toUInt8).toNat = 13
    · exact Or.inl hAV13
    · have hvalid : SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 ∧
          (VALUE (p.aces.get s).toUInt8).toNat ≤ 13 ∧
          SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 ∧
          (VALUE (p.kings.get s).toUInt8).toNat ≤ 13 ∧
          p.aces.get s ≤ p.kings.get s := (hnf.suitClean s).aces_kings_valid
      have hAV12 : (VALUE (p.aces.get s).toUInt8).toNat ≤ 12 := by
        have := hvalid.2.1; omega
      have hVlt15 : (VALUE (p.aces.get s).toUInt8).toNat < 15 := by omega
      have hSA : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT (p.aces.get s).toUInt8 :=
        SUIT_succ _ hVlt15
      have hVA : (VALUE ((p.aces.get s).toUInt8 + 1)).toNat =
          (VALUE (p.aces.get s).toUInt8).toNat + 1 := VALUE_succ _ hVlt15
      have hSAeqSval : SUIT ((p.aces.get s).toUInt8 + 1) = s.val.toUInt8 :=
        hSA.trans hvalid.1
      rcases (hnf.suitClean s).foundation_maximal_weak with h13 | hnfreeA | hbusy
      · exact absurd h13 hAV13
      · -- disjunct 2: the successor was already not free.
        by_cases hexists : ∃ k, k ≤ m ∧ (p.aces.get s).toUInt8 + 1 = B + UInt8.ofNat k
        · obtain ⟨k, hkm, hkeqA⟩ := hexists
          have hSAeqBk : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT B := by
            rw [hkeqA]; exact hSjEq k hkm
          have hSBeqSval : SUIT B = s.val.toUInt8 := hSAeqBk.symm.trans hSAeqSval
          have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
            have hb1 := congrArg UInt8.toNat hSBeqSval
            have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
            have hb3 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
          subst hseq
          have hAB' : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B + UInt8.ofNat k :=
            hkeqA
          by_cases hk0 : k = 0
          · have hAB : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B := by
              rw [hk0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero] at hAB'
              exact hAB'
            have hf0 := hAeqB_implies_f0 hAB
            subst hf0
            -- The successor sits exactly at the fresh boundary `B`, i.e.
            -- `aces = B - 1 - f` with `f = 0`: exactly `preCleanupPile`'s own
            -- busy-write condition, so the busy bit for `SUIT B` is set.
            refine Or.inr (Or.inr ?_)
            rw [← hsuiteq]
            show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                (B - 1 - UInt8.ofNat 0).toInt8 then
                p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&&
              (1 <<< SUIT B) ≠ 0
            have hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                (B - 1 - UInt8.ofNat 0).toInt8) = true := by
              rw [show UInt8.ofNat 0 = 0 from rfl, UInt8.sub_zero, beq_iff_eq]
              have h := congrArg (fun x : UInt8 => x.toInt8) (hAeqBm1_of hAB)
              rwa [Int8.toInt8_toUInt8] at h
            rw [hcond]
            simp only [reduceIte]
            have hSBlt4 : (SUIT B).toNat < 4 := by
              have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
              omega
            exact uint8_and_ne_zero_of_or_right (uint8_shift_self_ne_zero (SUIT B) hSBlt4)
          · exfalso
            have hb1 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
            have hb0v := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
            have hb0s := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
            have hb4 := SUIT_toNat B
            have hb5' := VALUE_toNat B
            have hSA' : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 := hSA
            have hSAeqAces : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = SUIT B :=
              hSA'.symm.trans hSAeqBk
            have hb3' := congrArg UInt8.toNat hSAeqAces
            have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
            have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
            rw [htiB] at hlt
            have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
              Int8.toNat_toUInt8_of_le haces0
            rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
            have hVeqCard := congrArg (fun x : UInt8 => (VALUE x).toNat) hAB'
            have hVeq2 := hRCgen k hkm
            have hVA' : (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat =
                (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat + 1 := hVA
            omega
        · refine Or.inr (Or.inl ?_)
          have hne : ∀ k, k ≤ m → (p.aces.get s).toUInt8 + 1 ≠ B + UInt8.ofNat k := by
            intro k hkm heq
            exact hexists ⟨k, hkm, heq⟩
          have hrealA : IsRealCard ((p.aces.get s).toUInt8 + 1) := by
            refine ⟨?_, by omega, by omega⟩
            have hSct := congrArg UInt8.toNat hSAeqSval
            have hb9 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B
            (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
            ((p.aces.get s).toUInt8 + 1) hrealA hne hnfreeA
      · -- busy bit already set before cleanup; `preCleanupPile` only ORs in
        -- more bits (`hbusyMono`), so it stays set.
        exact Or.inr (Or.inr (hbusyMono _ hbusy))
  · -- (9) king_frontier: `kings`/`aces` untouched; `busyAces` only gains bits
    -- (`hbusyMono`); the frontier witness `kings[s]` can only lose its
    -- not-free status if it happens to be one of the `m` merge-absorbed cards
    -- `B, …, B+m-1`, ruled out via suit/value matching against the entry's
    -- own `king_frontier` (`hVKge`) — except `kings[s]` could BE the
    -- still-boundary card `B+m` itself, handled directly as an ordinary
    -- "current pile boundary is never free" fact.
    rw [haeq, hkeqV]
    obtain ⟨hidxbm, heqbm⟩ := hmcards m (le_refl m)
    have hnfreeBm : ¬ isFreeCard g (fluteNorm pile hpile p) (B + UInt8.ofNat m) := by
      rw [← heqbm]
      exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩ (by
        have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
            (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
          rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
            (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
        have hikn : (0 : Int32) ≤
            (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
          rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
        show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat <
          (p.pileDepth[pile.toNat]'hpile).toInt.toNat
        rw [Int32.toNat_toUInt32_of_le hikn]
        show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat <
          (p.pileDepth[pile.toNat]'hpile).toInt.toNat
        rw [hik]
        omega)
    have hrealBm : IsRealCard (B + UInt8.ofNat m) := by
      rw [← heqbm]; exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩
    have hVKge : (VALUE (p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat ≥
        (VALUE (B + UInt8.ofNat m)).toNat := by
      by_contra hlt
      push_neg at hlt
      apply hnfreeBm
      have hall := (hnf.suitClean (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).king_frontier.2
      exact hall _ ((hSjEq m (le_refl m)).trans hsuiteq) hlt hrealBm.2.2
    refine ⟨?_, ?_⟩
    · rcases (hnf.suitClean s).king_frontier.1 with ⟨hkeqA, hcase⟩ | ⟨hv1, hnfree⟩
      · exact Or.inl ⟨hkeqA, hcase.imp id (fun hb => hbusyMono _ hb)⟩
      · refine Or.inr ⟨hv1, ?_⟩
        by_cases hkm_eq : (p.kings.get s).toUInt8 = B + UInt8.ofNat m
        · -- `kings[s]` is exactly the still-boundary card `B+m`: forces
          -- `s = SUIT B`; the freshly-written boundary is never free.
          have hSKeqB : SUIT (p.kings.get s).toUInt8 = SUIT B := by
            rw [hkm_eq]; exact hSjEq m (le_refl m)
          have hSKeqSval : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
            (hnf.suitClean s).aces_kings_valid.2.2.1
          have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
            have hb1 := congrArg UInt8.toNat (hSKeqB.symm.trans hSKeqSval)
            have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
            have hb3 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
          subst hseq
          have hkm_eq' : (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = B + UInt8.ofNat m :=
            hkm_eq
          intro hfree
          have hrt := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10) ⟨_, hidxbm⟩
          have heqbm' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
              ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat,
                hidxbm⟩ = B + UInt8.ofNat m := heqbm
          rw [heqbm', ← hkm_eq'] at hrt
          have hc64 : (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat < 64 := by
            have hreal' := hrealBm
            rw [← hkm_eq'] at hreal'
            have h1 := hreal'.1
            have h2 := hreal'.2.1
            have h3 := hreal'.2.2
            have hsn := SUIT_toNat (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8
            omega
          have hp64 : (cardPile g (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat < 10 := by
            rw [hrt.1]; exact hpile
          have hge := isFree_to_cardDepth_ge g _ hwf _ hc64 hp64 hfree
          have hgoal2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
              ).pileDepth[(cardPile g (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat]'hp64
              = ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
            have hstep : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
                ).pileDepth[(cardPile g
                  (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat]'hp64
                = (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile := by
              congr 1
              exact hrt.1
            rw [hstep, hpd]
          rw [hrt.2, hgoal2] at hge
          have hge' : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
              ).toUInt32.toNat ≥
              (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat :=
            hge
          have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
              (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
            rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
              (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
          have hikn : (0 : Int32) ≤
              (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
            rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
          rw [Int32.toNat_toUInt32_of_le hikn] at hge'
          have hgeNat : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
              ).toInt.toNat ≥
              (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat :=
            hge'
          rw [hik, hdI8] at hgeNat
          omega
        · -- `kings[s]` is genuinely NOT the still-boundary card: either a
          -- different suit entirely, or (same suit) provably below `B+m` in
          -- value — either way it's not one of the `m` absorbed cards.
          have hne : ∀ k, k ≤ m → (p.kings.get s).toUInt8 ≠ B + UInt8.ofNat k := by
            intro k hkm heq
            by_cases hkeqm : k = m
            · exact hkm_eq (hkeqm ▸ heq)
            · have hklm : k < m := by omega
              by_cases hSK : SUIT (p.kings.get s).toUInt8 = SUIT B
              · have hSKeqSval : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
                  (hnf.suitClean s).aces_kings_valid.2.2.1
                have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
                  have hb1 := congrArg UInt8.toNat (hSK.symm.trans hSKeqSval)
                  have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                    UInt8.toNat_toUInt32 (SUIT B)
                  have hb3 : s.val.toUInt8.toNat = s.val := by
                    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
                  omega
                have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
                subst hseq
                have hVeq := congrArg (fun x : UInt8 => (VALUE x).toNat) heq
                have hVeqk := hRCgen k hkm
                have hVeqm := hRCgen m (le_refl m)
                omega
              · exact hSK (heq ▸ hSjEq k hkm)
          have hrealK : IsRealCard (p.kings.get s).toUInt8 := by
            have hSAs : SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 :=
              (hnf.suitClean s).aces_kings_valid.1
            have hSs : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
              (hnf.suitClean s).aces_kings_valid.2.2.1
            have haces_nonneg : (0 : Int8) ≤ p.aces.get s := int8_nonneg_of_suit hSAs
            have hkings_nonneg : (0 : Int8) ≤ p.kings.get s := int8_nonneg_of_suit hSs
            have hAKlt : (p.aces.get s).toUInt8.toNat < (p.kings.get s).toUInt8.toNat := by
              have hv1' : p.aces.get s < p.kings.get s := hv1
              have h1 := Int8.lt_iff_toInt_lt.mp hv1'
              have h2 : (p.aces.get s).toUInt8.toNat = (p.aces.get s).toInt.toNat :=
                Int8.toNat_toUInt8_of_le haces_nonneg
              have h3 : (p.kings.get s).toUInt8.toNat = (p.kings.get s).toInt.toNat :=
                Int8.toNat_toUInt8_of_le hkings_nonneg
              rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces_nonneg
              rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at hkings_nonneg
              omega
            have hb1 := VALUE_toNat (p.aces.get s).toUInt8
            have hb2 := SUIT_toNat (p.aces.get s).toUInt8
            have hb3 := congrArg UInt8.toNat hSAs
            have hb4 := VALUE_toNat (p.kings.get s).toUInt8
            have hb5 := SUIT_toNat (p.kings.get s).toUInt8
            have hb6 := congrArg UInt8.toNat hSs
            have hb7 : s.val.toUInt8.toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hsval := s.isLt
            have hVKge1 : 1 ≤ (VALUE (p.kings.get s).toUInt8).toNat := by omega
            have hs4' : (SUIT (p.kings.get s).toUInt8).toNat < 4 := by omega
            exact ⟨hs4', hVKge1, (hnf.suitClean s).aces_kings_valid.2.2.2.1⟩
          exact preCleanupPile_not_free_of_ne_absorbed g pile hpile hwf B
            (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
            (p.kings.get s).toUInt8 hrealK hne hnfree
    · intro c hSc hgt hle
      exact isFreeCard_mono hdec ((hnf.suitClean s).king_frontier.2 c hSc hgt hle)

/-- **`preCleanupPile` preserves the `hash_def` field of `SolverInvBase`.**  The
    hash only depends on `pileDepth` (via the fixed `pileHashes` dot product),
    so only the depth-shrink arithmetic (`hd5`/`hm_le` ⇒ `hdI8`) is needed: the
    merge loop subtracted `m·ph` from `p.hash`, matching the depth decrease of
    exactly `m` at `pile` in the dot product (`hash_foldl_set` isolates that
    one term, then `UInt32.ofNat_add`/`mul_add` splits off the `m` part to
    match `preCleanupPile`'s own `hash := p.hash - UInt32.ofNat m * ph` field). -/
theorem preCleanupPile_hash_def (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1) :
    (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).hash =
      (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
        ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i
          ).toInt.toNat.toUInt32) 0 := by
  show p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) =
    (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
      (((p.pileDepth.set pile.toNat
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile).get i)
        ).toInt.toNat.toUInt32) 0
  have hhd : p.hash = (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
      (p.pileDepth.get i).toInt.toNat.toUInt32) 0 := hnf.hash_def
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hclamp : (p.pileDepth[pile.toNat]'hpile).toInt.toNat =
      (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat + m := by
    rw [hdI8]
    omega
  have hadd := hash_foldl_set p.pileDepth pile.toNat hpile
    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
  rw [hclamp,
    show ((((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat + m).toUInt32 =
      UInt32.ofNat ((((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat + m) from rfl,
    UInt32.ofNat_add, UInt32.mul_add] at hadd
  have h2 := congrArg
    (· - ((pileHashes[pile.toNat]'hpile) *
      UInt32.ofNat ((((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
        ).toInt.toNat) +
      (pileHashes[pile.toNat]'hpile) * UInt32.ofNat m)) hadd
  rw [UInt32.add_sub_cancel, uint32_sub_add, UInt32.add_sub_cancel] at h2
  rw [hhd, UInt32.mul_comm (UInt32.ofNat m) (pileHashes[pile.toNat]'hpile), ← h2]

set_option maxHeartbeats 1000000 in
/-- **`preCleanupPile` preserves the `usedSpace_def` field of `SolverInvBase`.**
    Both `pileDepth` and `pileFlute` change at `pile`: depth shrinks by `m`
    (`depth_sum_foldl_set`), and the flute-term goes from `0` (normalized
    entry: depth `d0 > 0`, flute `1`) to `m+f` (depth `d0-m > 0` — still
    nonzero since `hd5`/`hm_le` bound `m ≤ d0-1` — flute `1+m+f`,
    `usedSpace_term_foldl_set`); combined with the `f` lost from `usedSpace`
    itself (`preCleanupPile`'s own `usedSpace := p.usedSpace - Int8.ofNat f`
    field), the ledger balances exactly.  The final `Int8` arithmetic
    (`usedSpace - f`) doesn't wrap because `usedSpace_nonneg` bounds
    `p.usedSpace.toInt ∈ [0,52]` and `f ≤ B.toNat - 1 ≤ 60`. -/
theorem preCleanupPile_usedSpace_def (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p))
    (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hd : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8))
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
    (m f : Nat)
    (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
    (hf_le : f ≤ B.toNat - 1)
    (hBrange2 : B.toNat ≤ 61) :
    (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.toInt =
      (52 : Int)
      - ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
      - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
      - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.toList
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.toList
          |>.foldl (·+·) 0 : Nat)) := by
  have hfl8 : ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat = 1 + m + f := by
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have h1mI : ((1 : Int32) + Int32.ofNat m).toInt = 1 + (m : Int) := by
      rw [Int32.toInt_add, Int32.toInt_one, hmofI]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hfl32I : ((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toInt = 1 + (m : Int) + f := by
      rw [Int32.toInt_add, h1mI, hfofI]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hflnn : (0 : Int32) ≤ 1 + Int32.ofNat m + Int32.ofNat f := by
      rw [Int32.le_iff_toInt_le, hfl32I, show ((0 : Int32).toInt = 0) from by decide]; omega
    rw [UInt32.toNat_toUInt8, Int32.toNat_toUInt32_of_le hflnn]
    show ((1 + Int32.ofNat m + Int32.ofNat f).toInt.toNat) % 2 ^ 8 = 1 + m + f
    rw [hfl32I]
    omega
  have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
      (p.pileDepth[pile.toNat]'hpile).toInt - m := by
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
    rw [Int32.toInt_toInt8, hdepth1I]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  show (p.usedSpace - Int8.ofNat f).toInt =
    (52 : Int)
    - ((p.pileDepth.set pile.toNat
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
        ).toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
    - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
    - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        (p.pileDepth.set pile.toNat
          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile).toList
        (p.pileFlute.set pile.toNat
          ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile).toList
        |>.foldl (·+·) 0 : Nat))
  have hud : p.usedSpace.toInt = (52 : Int)
      - (p.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
      - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
          p.pileDepth.toList (p.pileFlute.set pile.toNat 1 hpile).toList
          |>.foldl (·+·) 0 : Nat) :=
    hnf.usedSpace_def
  have hds := depth_sum_foldl_set p.pileDepth pile.toNat hpile
    (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8)
  have hft_norm : (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        p.pileDepth.toList (p.pileFlute.set pile.toNat 1 hpile).toList
        |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
          (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
          (1 : UInt8).toNat - 1 else 0) := by
    have h := usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
      (p.pileDepth[pile.toNat]'hpile) (1 : UInt8)
    rwa [Vector.set_getElem_self hpile] at h
  have hft_new : (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        (p.pileDepth.set pile.toNat
          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile).toList
        (p.pileFlute.set pile.toNat
          ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile).toList
        |>.foldl (·+·) 0 : Nat)
      + (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
          (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList |>.foldl (·+·) 0 : Nat)
      + (if (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8)
          ≠ (0 : Int8) then
          ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat - 1 else 0) :=
    usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
      (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8)
      ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8)
  have hd' : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) := hd
  have ho : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
      (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
      (p.pileFlute[pile.toNat]'hpile).toNat - 1 := if_pos hd'
  have hn : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
      (1 : UInt8).toNat - 1 else 0) = 0 := if_pos hd'
  have hne1 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
      ≠ (0 : Int8) := by
    intro heq
    have hz0 := congrArg Int8.toInt heq
    rw [hdI8, show ((0 : Int8).toInt = 0) from rfl] at hz0
    omega
  have hz : (if (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8)
      ≠ (0 : Int8) then
      ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat - 1 else 0) = m + f := by
    rw [if_pos hne1, hfl8]
    omega
  simp only [ho, hn] at hft_norm
  simp only [ho, hz] at hft_new
  have hspace_bound : 0 ≤ p.usedSpace.toInt ∧ p.usedSpace.toInt ≤ 52 := by
    have h := usedSpace_nonneg hwf hnf
    rwa [show (fluteNorm pile hpile p).usedSpace = p.usedSpace from rfl] at h
  have hfInt : (Int8.ofNat f).toInt = (f : Int) := by
    rw [Int8.toInt_ofNat', show Int8.size = 256 from rfl]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hsub : (p.usedSpace - Int8.ofNat f).toInt = p.usedSpace.toInt - f := by
    rw [Int8.toInt_sub, hfInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  omega

-- `cleanupPile_baseNF`'s discharge has grown large enough (12 clauses × 2
-- branches, each needing its own index/arithmetic bookkeeping) that the
-- default 200000-heartbeat budget is exceeded on unrelated later bullets
-- purely from the theorem's overall size — confirmed by reproducing the
-- timeout even with the newest clause `sorry`'d out (so it isn't a specific
-- broken `rfl`/`exact` looping forever; it's cumulative elaboration cost).
-- Same remedy already used elsewhere in this file's `rfl`-twin proofs.
set_option maxHeartbeats 4000000 in
/-- **Shared guard-derivation preamble for `SolverCleanupPile`**, factored out of
    `cleanupPile_base`/`solverCleanupPile_step` (which used to duplicate an
    identical ~400-line derivation, differing only by a `pile ↦ UInt32.ofNat k`
    substitution).  Given the flute-normalized `SolverInvBase` precondition, this
    produces the exact symbolic run of `SolverCleanupPile pile` together with
    every fact its two callers need to reassemble their own (stronger) tower
    layer: the empty-pile case is a plain `freePiles += 1` no-op; the
    loop-bearing case exposes the boundary card `B`, the merge/freed loop
    counts `m`/`f`, and (for each of the non-king/king sub-branches) the
    resulting position's `PileClean`/`SuitClean`/`hash_def`/`usedSpace_def`
    facts and the "other piles' depths are untouched" frame condition. -/
theorem cleanupPile_eq (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p)) :
    (∃ (hd : p.pileDepth[pile.toNat]'hpile = 0)
       (hsd : p.pileDepth.set pile.toNat 0 hpile = p.pileDepth),
       EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff
         (g, { p with
               freePiles := p.freePiles + 1,
               pileDepth := p.pileDepth.set pile.toNat 0 hpile,
               pileFlute := p.pileFlute.set pile.toNat 1 hpile }))
    ∨
    (∃ (B : UInt8) (hs4 : (SUIT B).toUInt32.toNat < 4)
       (hd : p.pileDepth[pile.toNat]'hpile ≠ 0)
       (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt)
       (hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5)
       (hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5)
       (hBdef : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
           ).toUInt32.toNat]'hidx = B)
       (hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61)
       (hnfp : ∀ i : Fin 10, i.val ≠ pile.toNat → PileBase g p i)
       (m f : Nat)
       (hm_le : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1)
       (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
             Int32.ofNat k - 1).toUInt32.toNat < 5,
         (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
             Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k)
       (hmstop : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1 ∨
         (1 < (p.pileDepth[pile.toNat]'hpile).toInt - m ∧
           ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2
             ).toUInt32.toNat < 5,
             (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
               Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)))
       (hf_le : f ≤ B.toNat - 1)
       (hf_le_tight : f ≤ (VALUE B).toNat - 1)
       (hffree : ∀ l, 1 ≤ l → l ≤ f →
         isFreeCard g p (B - UInt8.ofNat l) ∧
         p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
       (hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 ∨
         ¬ isFreeCard g p (B - 1 - UInt8.ofNat f))
       (hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8),
       (∃ (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat →
             (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
               (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j = p.pileDepth.get j)
          (hpc : PileClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) ⟨pile.toNat, hpile⟩)
          (hsuit : ∀ s : Fin 4, SuitClean g (preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) s
              (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
                m f hm_le hmcards hf_le hffree))
          (hhash : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).hash =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i
                ).toInt.toNat.toUInt32) 0)
          (hused : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.toInt =
            (52 : Int)
            - ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
                ).pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
            - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.toList
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.toList
                |>.foldl (·+·) 0 : Nat)),
          EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff
            (g, preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p))
       ∨
       (∃ (hd1' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
             (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile = 1)
          (K : UInt8) (hKdef : K = (g.pos2card[pile.toNat]'hpile)[0]'(by omega))
          (hVK13 : (VALUE K).toNat = 13)
          (hsuiteq : SUIT B = SUIT K)
          (hKeq : K = B + UInt8.ofNat m)
          (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat →
            (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.get j = p.pileDepth.get j)
          (hpc : PileClean g (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)) ⟨pile.toNat, hpile⟩)
          (hsuit : ∀ s : Fin 4, SuitClean g (kingMove pile hpile (SUIT B) hs4
              (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)) s
              (fun i => le_trans (kingMove_pileDepth_le pile hpile (SUIT B) hs4
                  (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) i)
                (preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
                  m f hm_le hmcards hf_le hffree i)))
          (hhash : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).hash =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.get i
                ).toInt.toNat.toUInt32) 0)
          (hused : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).usedSpace.toInt =
            (52 : Int)
            - ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
                ).pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
            - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.toList
                (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileFlute.toList
                |>.foldl (·+·) 0 : Nat))),
          EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok
            (0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4)
            (g, kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)))) := by
  by_cases hd : p.pileDepth[pile.toNat]'hpile = 0
  · -- Empty pile: transplanted verbatim from `cleanupPile_base`'s old empty case.
    left
    have hrun := cleanupPile_empty_eq pile g p hpile hd
    have hsd : p.pileDepth.set pile.toNat 0 hpile = p.pileDepth := by
      conv_lhs => rw [← hd]
      exact Vector.set_getElem_self hpile
    exact ⟨hd, hsd, hrun⟩
  · -- Loop-bearing case: `pileDepth[pile] > 0`.
    -- (`fluteNorm` only changes `pileFlute`, so all depth/aces facts of `hnf`
    -- transfer to `p` definitionally.)
    right
    have hnn : (0 : Int8) ≤ p.pileDepth[pile.toNat]'hpile :=
      hnf.pileDepth_nonneg ⟨pile.toNat, hpile⟩
    have hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toInt := by
      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at hnn
      have hne : (p.pileDepth[pile.toNat]'hpile).toInt ≠ 0 :=
        fun h => hd (Int8.toInt_inj.mp h)
      omega
    have hd5 : (p.pileDepth[pile.toNat]'hpile).toInt ≤ 5 := by
      have hb := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩
      have : (p.pileDepth[pile.toNat]'hpile).toInt.toNat ≤ 5 := hb
      omega
    have h1le : (1 : Int32) ≤ (p.pileDepth[pile.toNat]'hpile).toInt32 := by
      rw [Int32.le_iff_toInt_le, Int32.toInt_one, Int8.toInt_toInt32]; omega
    have hsubd : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by
      rw [Int32.toInt_sub_of_le _ _ (by decide) h1le, Int32.toInt_one, Int8.toInt_toInt32]
    have hidx : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat < 5 := by
      rw [Int32.toNat_toUInt32_of_le (by
        rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]; omega)]
      show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat < 5
      omega
    -- The boundary card is a real card (WellFormedLayout).
    have hreal : IsRealCard ((g.pos2card[pile.toNat]'hpile)[
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat]'hidx) :=
      hwf.pos2card_real ⟨pile.toNat, hpile⟩
        ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩
    set B := (g.pos2card[pile.toNat]'hpile)[
      ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat]'hidx with hBdef
    have hs4 : (SUIT B).toUInt32.toNat < 4 := by
      rw [UInt8.toNat_toUInt32]; exact hreal.1
    have hBrange : 1 ≤ B.toNat ∧ B.toNat ≤ 61 := by
      have hsn : (SUIT B).toNat = B.toNat / 16 := SUIT_toNat B
      have hvn : (VALUE B).toNat = B.toNat % 16 := VALUE_toNat B
      have h1 := hreal.1
      have h2 := hreal.2.1
      have h3 := hreal.2.2
      omega
    have h1B : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
    have hprev64 : (B - 1).toNat < 64 := by
      rw [UInt8.toNat_sub_of_le _ _ h1B]; omega
    have haces0 : (0 : Int8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 :=
      int8_nonneg_of_suit
        (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
    -- The boundary card is still physically in the pile (`boundary_not_free`,
    -- via `depth_card_not_free`), so `foundation_cards_free`'s contrapositive
    -- forces `aces[SUIT B] < B`: if `aces[SUIT B]` had already reached `B`,
    -- `B` itself would satisfy `foundation_cards_free`'s hypotheses and hence
    -- be free, contradicting `boundary_not_free`.
    have hsuiteq : SUIT B = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
      show SUIT B = ((SUIT B).toUInt32.toNat).toUInt8
      apply UInt8.toNat_inj.mp
      have h1 : (((SUIT B).toUInt32.toNat).toUInt8).toNat = (SUIT B).toUInt32.toNat % 256 := by
        rw [UInt8.toNat_ofNat']
      have h2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      omega
    have haces_lt_B : p.aces[(SUIT B).toUInt32.toNat]'hs4 < B.toInt8 := by
      by_contra hge
      rw [Int8.lt_iff_toInt_lt] at hge
      rw [not_lt] at hge
      have htiB : B.toInt8.toInt = (B.toNat : Int) := uint8_toInt8_toInt_of_lt128 (by omega)
      have h1 : (B.toNat : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
        rwa [htiB] at hge
      have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
        rw [Int8.toNat_toUInt8_of_le haces0]
        have hbdg : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toNatClampNeg =
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat := rfl
        omega
      have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
      have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
      have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
      have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
        rw [← hgetEq, hak.1, ← hsuiteq]
      have hVBS : (VALUE B).toNat ≤
          (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat := by
        have hb1 := VALUE_toNat B
        have hb2 := SUIT_toNat B
        have hb3 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
        have hb4 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
        have hsEq := congrArg UInt8.toNat hSuitAces
        omega
      have hfree : isFreeCard g (fluteNorm pile hpile p) B :=
        hnf.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
      have hnfB : ¬ isFreeCard g (fluteNorm pile hpile p) B := by
        rw [hBdef]
        exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩
          ⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat, hidx⟩ (by
            show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat <
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat
            rw [Int32.toNat_toUInt32_of_le (by
              rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]
              omega)]
            show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat <
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat
            omega)
      exact hnfB hfree
    -- Every same-suit card `aces[SUIT B]` represents lies within `SUIT B`'s
    -- own 16-wide code block (never below it) — the counterpart lower bound
    -- to `foundation_cards_free`'s implicit upper range, needed to rule out
    -- the freed loop crossing into a different suit's card block.
    have haces_ge : (16 : Nat) * (SUIT B).toUInt32.toNat ≤
        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
      have hacesEq : (fluteNorm pile hpile p).aces = p.aces := rfl
      have hak := hacesEq ▸ hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
      have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
      have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
        rw [← hgetEq, hak.1, ← hsuiteq]
      have hb1 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hsEq := congrArg UInt8.toNat hSuitAces
      have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      omega
    -- `fluteNorm` only ever changes `pileFlute[pile]`, so `hnf`'s `PileBase`
    -- facts about any OTHER pile transfer to `p` (not `fluteNorm pile hpile p`)
    -- verbatim — needed since `preCleanupPile_pileBase_ne`/`kingMove_pileBase_ne`
    -- are stated about `p` directly (they don't take the full `SolverInvBase`
    -- and re-derive the bridge themselves).
    have hnfp : ∀ i : Fin 10, i.val ≠ pile.toNat → PileBase g p i := by
      intro i hij
      have hfeq : (fluteNorm pile hpile p).pileFlute.get i = p.pileFlute.get i := by
        show (fluteNorm pile hpile p).pileFlute[i.val]'i.isLt = p.pileFlute[i.val]'i.isLt
        simp only [fluteNorm]
        exact Vector.getElem_set_ne hpile i.isLt (Ne.symm hij)
      have hb := hnf.pileBase i
      refine ⟨hb.pileDepth_bound, hb.pileDepth_nonneg, ?_, ?_, ?_, ?_⟩
      · rw [← hfeq]; exact hb.flute_pos
      · intro h0; rw [← hfeq]; exact hb.flute_empty h0
      · intro j hdi hj0 hjlt
        rw [← hfeq] at hjlt
        exact hb.flute_cards_free j hdi hj0 hjlt
      · exact fun hdi hs => by
          have h2 := hb.flute_not_aces hdi hs
          rwa [hfeq] at h2
    obtain ⟨m, f, hmg, hmx, hfg, hfx, hrun⟩ :=
      cleanupPile_nonempty_eq pile g p B (pileHashes[pile.toNat]'hpile) hpile rfl
        hd1 hd5 hidx hBdef.symm hs4 hprev64 hwf.card2pile_lt haces0
    -- ------------------------------------------------------------------
    -- Guard-derived arithmetic: bounds on the iteration counts (no wraps).
    -- ------------------------------------------------------------------
    -- The merge loop runs at most depth−1 times: the guard at step
    -- `depth.toNat − 1` would need `1 < depth − (depth−1) = 1`.
    have hm_le : m ≤ (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hg := (hmg ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1) (by omega)).1
      simp only [mergeIter_eq] at hg
      rw [Int32.lt_iff_toInt_lt, Int32.toInt_one] at hg
      have hofk : (Int32.ofNat ((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1)).toInt =
          (((p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 : Nat) : Int) := by
        rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hofk, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hofk, Int8.toInt_toInt32]; omega),
        hofk, Int8.toInt_toInt32] at hg
      omega
    have hm4 : m ≤ 4 := by omega
    -- The freed loop runs at most B.toNat−1 times: at step B.toNat−1 the
    -- walked card would be 0, contradicting `0 ≤ aces < prevCard`.
    have hf_le : f ≤ B.toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hof : (UInt8.ofNat (B.toNat - 1)).toNat = B.toNat - 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hprev0 : B - 1 - UInt8.ofNat (B.toNat - 1) = 0 := by
        have hle : UInt8.ofNat (B.toNat - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hof, UInt8.toNat_sub_of_le _ _ h1B,
            show ((1 : UInt8).toNat = 1) from rfl]
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_sub_of_le _ _ h1B, hof,
          show ((1 : UInt8).toNat = 1) from rfl, show ((0 : UInt8).toNat = 0) from rfl]
        omega
      have hg := (hfg (B.toNat - 1) (by omega)).1 hs4
      simp only [freedIter_eq, hprev0] at hg
      rw [show ((0 : UInt8).toInt8 = 0) from rfl, Int8.lt_iff_toInt_lt,
        show ((0 : Int8).toInt = 0) from rfl] at hg
      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
      omega
    -- Weaker form (mirrors the old monolithic proof exactly): the freed loop
    -- never crosses into a lower suit's card block either — at step
    -- `VALUE(B)−1` the walked card would be exactly the value-0 sentinel of
    -- `SUIT B`, contradicting `haces_ge`.
    have hf_le_tight : f ≤ (VALUE B).toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hvB := VALUE_toNat B
      have hsB := SUIT_toNat B
      have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
      have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      have hof : (UInt8.ofNat ((VALUE B).toNat - 1)).toNat = (VALUE B).toNat - 1 := by
        rw [UInt8.toNat_ofNat']; omega
      have hprevEq : B - 1 - UInt8.ofNat ((VALUE B).toNat - 1) =
          UInt8.ofNat (16 * (SUIT B).toUInt32.toNat) := by
        apply UInt8.toNat_inj.mp
        have hle : UInt8.ofNat ((VALUE B).toNat - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hof, UInt8.toNat_sub_of_le _ _ h1B,
            show ((1 : UInt8).toNat = 1) from rfl]
          omega
        have h16x : 16 * (SUIT B).toUInt32.toNat < 256 := by omega
        rw [UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_sub_of_le _ _ h1B, hof,
          show ((1 : UInt8).toNat = 1) from rfl, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h16x]
        omega
      have hg := (hfg ((VALUE B).toNat - 1) (by omega)).1 hs4
      simp only [freedIter_eq, hprevEq] at hg
      have h16x : 16 * (SUIT B).toUInt32.toNat < 256 := by omega
      have hcardnat : (UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toNat =
          16 * (SUIT B).toUInt32.toNat := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h16x]
      have hti : (UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toInt8.toInt =
          ((UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toNat : Int) :=
        uint8_toInt8_toInt_of_lt128 (by omega)
      have hlt := Int8.lt_iff_toInt_lt.mp hg
      rw [hti, hcardnat] at hlt
      have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
        Int8.toNat_toUInt8_of_le haces0
      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
      omega
    -- ------------------------------------------------------------------
    -- Semantic bridges: raw `mergeGuard`/`freedGuard` facts (`hmg`/`hmx`/
    -- `hfg`/`hfx`) restated in the shape the modular `preCleanupPile_*`
    -- lemmas expect (`hmcards`/`hffree`/`hmstop`/`hfstop`).
    -- ------------------------------------------------------------------
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
    have hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat < 5,
        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
          Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k := by
      intro k hkm
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        refine ⟨by simpa using hidx, ?_⟩
        simp only [show Int32.ofNat 0 = 0 from rfl, Int32.sub_zero,
          show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
        exact hBdef.symm
      · have hd0 : ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt ≤ 5 := by
          rw [Int8.toInt_toInt32]; exact hd5
        have hmlt : (m : Int) < ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt := by
          rw [Int8.toInt_toInt32]; omega
        exact merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
          (p.pileDepth[pile.toNat]'hpile).toInt32 m p hd0 hmlt hmg k hkpos hkm
    -- The freed-loop guard held for every step below `f`: unfold each into the
    -- semantic per-`l` fact `hffree` needs.
    have hffree : ∀ l, 1 ≤ l → l ≤ f →
        isFreeCard g p (B - UInt8.ofNat l) ∧
        p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8 := by
      intro l hl1 hlf
      have hg1 := (hfg (l - 1) (by omega)).1 hs4
      have hg2 := (hfg (l - 1) (by omega)).2
      simp only [freedIter_eq] at hg1 hg2
      simp only [UInt8.toNat_toUInt32] at hg2
      have hstepId : B - 1 - UInt8.ofNat (l - 1) = B - UInt8.ofNat l := by
        apply UInt8.toNat_inj.mp
        have hl1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by rw [UInt8.toNat_ofNat']; omega
        have hlof : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
        have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
          rw [UInt8.le_iff_toNat_le, hl1of, UInt8.toNat_sub_of_le _ _ h1B,
            show ((1 : UInt8).toNat = 1) from rfl]
          omega
        have hleB' : UInt8.ofNat l ≤ B := by
          rw [UInt8.le_iff_toNat_le, hlof]; omega
        rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B, hl1of,
          show ((1 : UInt8).toNat = 1) from rfl, UInt8.toNat_sub_of_le _ _ hleB', hlof]
        omega
      rw [← hstepId]
      have hl1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by rw [UInt8.toNat_ofNat']; omega
      have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
        rw [UInt8.le_iff_toNat_le, hl1of, UInt8.toNat_sub_of_le _ _ h1B,
          show ((1 : UInt8).toNat = 1) from rfl]
        omega
      have hBl64 : (B - 1 - UInt8.ofNat (l - 1)).toNat < 64 := by
        rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B,
          show ((1 : UInt8).toNat = 1) from rfl]
        omega
      exact ⟨isFree_of_card2depth_ge g p hwf (B - 1 - UInt8.ofNat (l - 1)) hBl64
        (hg2 hBl64 (hwf.card2pile_lt _ hBl64)), hg1⟩
    -- The merge loop stopped either because depth (after `m` steps) reached
    -- `≤ 1`, or because the card two below the new boundary doesn't continue
    -- the ascending run.
    have hmstop : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1 ∨
        (1 < (p.pileDepth[pile.toNat]'hpile).toInt - m ∧
          ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2
            ).toUInt32.toNat < 5,
            (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
              Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)) := by
      by_cases hle1 : (p.pileDepth[pile.toNat]'hpile).toInt - m ≤ 1
      · exact Or.inl hle1
      · push_neg at hle1
        right
        have h1lt : (1 : Int32) < (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m := by
          rw [Int32.lt_iff_toInt_lt, Int32.toInt_one, hdepth1I]; omega
        have hidx2 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2
            ).toUInt32.toNat < 5 := by
          have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toInt =
              (p.pileDepth[pile.toNat]'hpile).toInt - m - 2 := by
            rw [depth_sub_ofNat_sub_two_eq (by rw [Int8.toInt_toInt32]; exact hd5)
              (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
          have hikn : (0 : Int32) ≤
              (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2 := by
            rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
          rw [Int32.toNat_toUInt32_of_le hikn]
          show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toInt.toNat < 5
          rw [hik]; omega
        refine ⟨hle1, hidx2, ?_⟩
        intro heq
        apply hmx
        rw [mergeIter_eq]
        refine ⟨h1lt, fun h10 h5 => ?_⟩
        have hSame : (g.pos2card[pile.toNat]'hpile)[
            ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat]'h5 =
            (g.pos2card[pile.toNat]'hpile)[
            ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 2).toUInt32.toNat]'hidx2 := by
          congr 1
        have hstepB : B + UInt8.ofNat m + 1 = B + UInt8.ofNat (m + 1) := by
          rw [UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]
        rw [hSame, heq, hstepB]
    -- The freed loop stopped either because `aces` had already reached the
    -- stopping card exactly, or that card genuinely isn't free.
    have hfstop : p.aces[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8 ∨
        ¬ isFreeCard g p (B - 1 - UInt8.ofNat f) := by
      have hg := hfx
      simp only [freedIter_eq] at hg
      by_cases hcase : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1 - UInt8.ofNat f).toInt8
      · right
        intro hfree
        apply hg
        refine ⟨fun _ => hcase, fun h64 h10 => ?_⟩
        simp only [UInt8.toNat_toUInt32]
        have hXnat64 : (B - 1 - UInt8.ofNat f).toNat < 64 := by
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hle3 : UInt8.ofNat f ≤ B - 1 := by
            rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ h1B,
              show ((1 : UInt8).toNat = 1) from rfl]
            omega
          rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ h1B, hfof,
            show ((1 : UInt8).toNat = 1) from rfl]
          omega
        exact isFree_to_card2depth_ge g p hwf (B - 1 - UInt8.ofNat f) hXnat64 hfree
      · left
        have hcase : (B - 1 - UInt8.ofNat f).toInt8 ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
          rw [Int8.le_iff_toInt_le]
          by_contra hlt
          rw [not_le] at hlt
          exact ‹¬ p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1 - UInt8.ofNat f).toInt8›
            (Int8.lt_iff_toInt_lt.mpr hlt)
        have h1B : (1 : UInt8) ≤ B := by
          rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
        have hfle : f ≤ B.toNat - 1 := hf_le
        have hXnat : (B - 1 - UInt8.ofNat f).toNat = B.toNat - 1 - f := by
          have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
          have hle3 : UInt8.ofNat f ≤ B - 1 := by
            rw [UInt8.le_iff_toNat_le, hfof, UInt8.toNat_sub_of_le _ _ h1B,
              show ((1 : UInt8).toNat = 1) from rfl]
            omega
          rw [UInt8.toNat_sub_of_le _ _ hle3, UInt8.toNat_sub_of_le _ _ h1B, hfof,
            show ((1 : UInt8).toNat = 1) from rfl]
        have haces_le : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat ≤
            (B - 1 - UInt8.ofNat f).toNat := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · subst hf0
            have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
            rw [uint8_toInt8_toInt_of_lt128 (by omega)] at hlt
            have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
              Int8.toNat_toUInt8_of_le haces0
            rw [hXnat]
            omega
          · have hf' := (hffree f hfpos (le_refl f)).2
            have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
            have hfBle : UInt8.ofNat f ≤ B := by rw [UInt8.le_iff_toNat_le, hfof]; omega
            have hBf : (B - UInt8.ofNat f).toNat = B.toNat - f := by
              rw [UInt8.toNat_sub_of_le _ _ hfBle, hfof]
            have hlt := Int8.lt_iff_toInt_lt.mp hf'
            rw [uint8_toInt8_toInt_of_lt128 (show (B - UInt8.ofNat f).toNat < 128 by omega),
              hBf] at hlt
            have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
              Int8.toNat_toUInt8_of_le haces0
            rw [hXnat]
            omega
        have hgeNat : (B - 1 - UInt8.ofNat f).toNat ≤
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
          have hle := Int8.le_iff_toInt_le.mp hcase
          rw [uint8_toInt8_toInt_of_lt128 (by
            have := hXnat; omega)] at hle
          have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
              (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
            Int8.toNat_toUInt8_of_le haces0
          omega
        apply Int8.toInt_inj.mp
        rw [uint8_toInt8_toInt_of_lt128 (by
          have := hXnat; omega)]
        have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
          Int8.toNat_toUInt8_of_le haces0
        have haces0' : (0 : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt :=
          Int8.le_iff_toInt_le.mp haces0
        omega
    have hmf128 : (1 + (m : Int) + f) < 128 := by
      have h1 := hm4
      have h2 := hf_le
      have h3 := hBrange.2
      omega
    -- ------------------------------------------------------------------
    -- Package the shared preamble facts (`hpc`/`hpdb_all`/`hak` don't depend
    -- on the non-king/king split, so they're computed once here and reused
    -- by both sub-branches below).
    -- ------------------------------------------------------------------
    have hm_le_int : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by omega
    have hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8 :=
      fun t => (hnf.suitClean t).aces_kings_valid.1
    have hpc := preCleanupPile_pileClean_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx
      hBdef.symm m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop
    have hpdb_all := preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5
      hidx hBdef.symm m f hm_le_int hmcards hf_le hffree
    refine ⟨B, hs4, hd, hd1, hd5, hidx, hBdef.symm, hBrange, hnfp, m, f, hm_le_int, hmcards,
      hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, ?_⟩
    -- ------------------------------------------------------------------
    -- Reconnect to the real run via `cleanupRunResult_eq`, then case-split
    -- on the lone-king condition.
    -- ------------------------------------------------------------------
    rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hmf128] at hrun
    cases hk : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1 &&
        VALUE (B + UInt8.ofNat m) == 13) with
    | false =>
      simp only [hk, Bool.false_eq_true, reduceIte] at hrun
      left
      exact ⟨fun j hj => preCleanupPile_pileDepth_eq_of_ne pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 p m f j hj,
        hpc,
        preCleanupPile_suitClean pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef.symm
          m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop,
        preCleanupPile_hash_def pile g p hpile hnf B hs4 hd5 m f hm_le_int,
        preCleanupPile_usedSpace_def pile g p hpile hwf hnf B hs4 hd hd5 m f hm_le_int
          hf_le hBrange.2,
        hrun⟩
    | true =>
      simp only [hk, reduceIte] at hrun
      right
      rw [Bool.and_eq_true] at hk
      have hk1 := hk.1
      have hk2 := hk.2
      have hpdEq : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hpfEq : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile =
          (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hd1' : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile = 1 := by
        rw [hpdEq, eq_of_beq hk1]; decide
      have hVK13 : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by
        rw [eq_of_beq hk2]; decide
      have hrcm := merge_real_chain' g pile hpile hwf B (p.pileDepth[pile.toNat]'hpile).toInt32 m
        hreal hmcards m (le_refl m)
      have hSm : SUIT (B + UInt8.ofNat m) = SUIT B := by
        apply UInt8.toNat_inj.mp
        have hb1 := SUIT_toNat (B + UInt8.ofNat m)
        have hb2 := SUIT_toNat B
        have hb3 := VALUE_toNat (B + UInt8.ofNat m)
        have hb4 := VALUE_toNat B
        have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
        have hlt256 : B.toNat + m < 256 := by omega
        have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
          rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
        have hvm := hrcm.2
        omega
      have hidx0 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1
          ).toUInt32.toNat = 0 := by
        have he1 := eq_of_beq hk1
        rw [he1]
        decide
      obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
      have hKeq : B + UInt8.ofNat m = (g.pos2card[pile.toNat]'hpile)[0]'(by omega) := by
        rw [← heqm]
        congr 1
      refine ⟨hd1', B + UInt8.ofNat m, hKeq, hVK13, hSm.symm, rfl, ?_, ?_, ?_, ?_, ?_, hrun⟩
      · intro j hj
        rw [kingMove_pileDepth_eq_of_ne pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) j hj,
          preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
            j hj]
      · exact kingMove_pileClean_self pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
      · exact fun s => kingMove_suitClean pile g hpile hwf (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
          hpdb_all hd1' (B + UInt8.ofNat m) hKeq hVK13 hSm.symm hak hpc s
          (preCleanupPile_suitClean pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef.symm
            m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop s)
      · -- hash_def for the king branch: compose `preCleanupPile_hash_def` with
        -- `kingMove`'s own simple `hash -= ph` write, isolating `pile`'s own
        -- term (now `0`) via `hash_foldl_set`.
        have hqhash := preCleanupPile_hash_def pile g p hpile hnf B hs4 hd5 m f hm_le_int
        show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).hash -
            (pileHashes[pile.toNat]'hpile) =
          (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
            ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.get i
              ).toInt.toNat.toUInt32) 0
        have hpdeq : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth =
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.set
              pile.toNat (0 : Int8) hpile := by
          simp only [kingMove]
          congr 1
        rw [hpdeq, hqhash]
        have hadd := hash_foldl_set (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile)
          hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth pile.toNat hpile (0 : Int8)
        rw [hd1'] at hadd
        simp only [show ((1 : Int8).toInt.toNat = 1) from rfl,
          show ((0 : Int8).toInt.toNat = 0) from rfl,
          show (Nat.toUInt32 0 = 0) from rfl, show (Nat.toUInt32 1 = 1) from rfl,
          UInt32.mul_one, UInt32.mul_zero, UInt32.add_zero] at hadd
        rw [← hadd, UInt32.add_sub_cancel]
      · -- usedSpace_def for the king branch: compose `preCleanupPile_usedSpace_def`
        -- with `kingMove`'s own `usedSpace += pileFlute[pile]` write, isolating
        -- `pile`'s own depth/flute terms (now `0`/`1`) the same way.
        have hqused := preCleanupPile_usedSpace_def pile g p hpile hwf hnf B hs4 hd hd5 m f
          hm_le_int hf_le hBrange.2
        have hfl8 : ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8).toNat = 1 + m + f := by
          have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
            rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
            rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have h1mI : ((1 : Int32) + Int32.ofNat m).toInt = 1 + (m : Int) := by
            rw [Int32.toInt_add, Int32.toInt_one, hmofI]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hfl32I : ((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toInt =
              1 + (m : Int) + f := by
            rw [Int32.toInt_add, h1mI, hfofI]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hflnn : (0 : Int32) ≤ 1 + Int32.ofNat m + Int32.ofNat f := by
            rw [Int32.le_iff_toInt_le, hfl32I, show ((0 : Int32).toInt = 0) from by decide]
            omega
          rw [UInt32.toNat_toUInt8, Int32.toNat_toUInt32_of_le hflnn]
          show ((1 + Int32.ofNat m + Int32.ofNat f).toInt.toNat) % 2 ^ 8 = 1 + m + f
          rw [hfl32I]
          omega
        have hds := depth_sum_foldl_set (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth pile.toNat hpile (0 : Int8)
        rw [hd1'] at hds
        simp only [show ((1 : Int8).toInt.toNat = 1) from rfl,
          show ((0 : Int8).toInt.toNat = 0) from rfl] at hds
        have hft := usedSpace_term_foldl_set (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
            ).pileDepth
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute
          pile.toNat hpile (0 : Int8) (1 : UInt8)
        rw [hd1', hpfEq] at hft
        simp only [show ((0 : Int8) ≠ (0 : Int8)) = False from by simp,
          show ((1 : Int8) ≠ (0 : Int8)) = True from by simp, reduceIte] at hft
        rw [hfl8] at hft
        show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace +
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile
              ).toInt8).toInt =
          (52 : Int)
          - ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
              ).pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
          - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
          - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
              (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.toList
              (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileFlute.toList
              |>.foldl (·+·) 0 : Nat))
        have hpdeqL : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.toList =
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.set
              pile.toNat (0 : Int8) hpile).toList := by
          simp only [kingMove]
          congr 1
        have hpfeqL : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileFlute.toList =
            ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.set
              pile.toNat (1 : UInt8) hpile).toList := by
          simp only [kingMove]
          congr 1
        rw [hpdeqL, hpfeqL]
        have hfl8Int : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile
            ).toInt8.toInt = (1 + (m : Int) + f) := by
          rw [hpfEq]
          have hb128 : (((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8
              ).toNat < 128 := by rw [hfl8]; omega
          rw [uint8_toInt8_toInt_of_lt128 hb128, hfl8]
          push_cast
          ring
        have hqb_le : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.toInt ≤ 127 := by
          have h := (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.toInt_le
          rw [Int8.toInt_maxValue] at h
          omega
        have hqb_ge : (-128 : Int) ≤ (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile)
            hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.toInt := by
          have h := (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).usedSpace.le_toInt
          omega
        rw [Int8.toInt_add, hfl8Int, Int.bmod_eq_of_le (by omega) (by omega)]
        omega

/-- `1 <<< x < 16` whenever the shift amount `x.toNat < 4` (the bit set sits
    among the low 4 positions) — finite check via `native_decide`. -/
private theorem uint8_one_shl_lt16_nat :
    ∀ n : Nat, n < 256 → n < 4 → ((1 : UInt8) <<< UInt8.ofNat n).toNat < 16 := by
  native_decide

private theorem uint8_one_shl_lt16_of_lt4 (x : UInt8) (hx : x.toNat < 4) :
    ((1 : UInt8) <<< x) < 16 := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have h := uint8_one_shl_lt16_nat x.toNat h256 hx
  rw [UInt8.ofNat_toNat] at h
  rwa [UInt8.lt_iff_toNat_lt, show (16 : UInt8).toNat = 16 from by decide]

/-- `preCleanupPile`'s only `busyAces` write ORs in `1 <<< SUIT B`, a bit
    position `< 4` (`hs4`) — so the result stays `< 16` whenever the input
    did. -/
private theorem preCleanupPile_busyAces_lt16 (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d32 : Int32) (m f : Nat) (p : SolverPosType) (hp16 : p.busyAces < 16) :
    (preCleanupPile pile hpile B ph hs4 d32 m f p).busyAces < 16 := by
  have hs4' : (SUIT B).toNat < 4 := by rwa [UInt8.toNat_toUInt32] at hs4
  simp only [preCleanupPile]
  split
  · exact uint8_or_lt16_of_lt16 hp16 (uint8_one_shl_lt16_of_lt4 (SUIT B) hs4')
  · exact hp16

set_option maxHeartbeats 4000000 in
/-- **`SolverCleanupPile` preserves the base invariant layer** (up to the
    `freePiles` field, which `SolverInvBase` deliberately omits).

    The precondition is stated about the *flute-normalized* entry position
    `{ p with pileFlute[pile] := 1 }` rather than `p` itself: the callers
    (convert's cleanup loop, `SolverRemoveFlute`) leave a stale `pileFlute[pile]`
    behind — the function never reads it and overwrites it at the end — and the
    invariant's `usedSpace`/flute clauses are only true of the normalized
    position.  (The freed loop re-frees the old flute interiors; with a stale
    flute in the formula, `usedSpace_def` would double-count them.)

    No further hypotheses are needed: `aces_kings_valid` now allows the value-0
    `kings` sentinel (see its docstring), so the lone-king branch is fine — the
    freed-loop exit gives `aces[s] ≤ kings'[s]` directly, and the `busyAces` bit
    set in that case pends the foundation drain that restores `VALUE ≥ 1`.

    Proof status: the empty-pile case is complete; the loop-bearing case rests on
    `cleanupPile_nonempty_eq` (the exact symbolic run, fully proved) and its
    clause-by-clause discharge is `sorry` (documented inline). -/
theorem cleanupPile_base (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hnf : SolverInvBase g (fluteNorm pile hpile p)) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok fk (g, p') ∧
      SolverInvBase g p' := by
  rcases cleanupPile_eq pile g p hpile hwf hnf with
    ⟨hd, hsd, hrun⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- Empty pile: the depth write is a no-op; the base layer ignores `freePiles`.
    exact ⟨0xffff, _, hrun, by simp only [hsd]; exact nf_setFreePiles hnf _⟩
  · -- Loop-bearing case: reassemble `SolverInvBase` from `cleanupPile_eq`'s
    -- non-king/king bundle — `hsuit`/`hhash`/`hused` are already in exactly the
    -- shape `SolverInvBase`'s fields need; only `pileBase` (for `pile` itself
    -- via `hpc.toPileBase`, for other piles via the modular `_ne` lemmas
    -- chained through `hnfp`) and `busyAces_lt16` need assembling here.
    have hp16 : p.busyAces < 16 := hnf.busyAces_lt16
    rcases hbranch with
      ⟨hframe, hpc, hsuit, hhash, hused, hrun⟩ |
      ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
    · refine ⟨0xffff, _, hrun, fun i => ?_, hsuit, hhash, hused,
        preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hp16⟩
      by_cases hij : i.val = pile.toNat
      · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
        subst hii
        exact hpc.toPileBase
      · exact preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p
          m f hd5 (by omega) i hij (hnfp i hij)
    · refine ⟨_, _, hrun, fun i => ?_, hsuit, hhash, hused, ?_⟩
      · by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact kingMove_pileBase_ne pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile) _ i
            hij (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
              hd5 (by omega) i hij (hnfp i hij))
      · rw [kingMove_busyAces_eq]
        exact preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hp16

/-- Pure combinatorics: splitting a `List.finRange n`-indexed count at one
    excluded index `k` into the filtered count (over `j ≠ k`) plus the
    indicator of `k` itself.  Proved by induction on `n`, peeling the front
    element via `List.finRange_succ` and case-splitting on whether `k` is that
    front element (`k = 0`) or lies in the tail (`k = k' + 1`). -/
private theorem finRange_countP_ite_split : ∀ (n k : Nat) (hk : k < n) (f : Fin n → Bool),
    (List.finRange n).countP (fun j => (j.val != k) && f j) +
      (if f ⟨k, hk⟩ then 1 else 0) = (List.finRange n).countP f
  | 0, k, hk, _f => absurd hk (by omega)
  | (n+1), k, hk, f => by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [List.finRange_succ, List.countP_cons_of_neg (by simp), List.countP_cons,
          List.countP_map, List.countP_map, Function.comp_def, Function.comp_def]
        have h3 : (List.finRange n).countP (fun j : Fin n => (Fin.succ j).val != 0 &&
            f (Fin.succ j)) = (List.finRange n).countP (fun j : Fin n => f (Fin.succ j)) := by
          apply List.countP_congr
          intro j' _
          simp
        have h0eq : f ⟨0, hk⟩ = f (0 : Fin (n+1)) := by congr 1
        rw [h0eq]
        omega
      · obtain ⟨k', hkval⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        have hkeq1 : k = k' + 1 := by omega
        subst hkeq1
        have hk' : k' < n := by omega
        rw [List.finRange_succ, List.countP_cons, List.countP_cons, List.countP_map,
          List.countP_map, Function.comp_def, Function.comp_def]
        have hpred0 : ((0:Fin (n+1)).val != k'+1 && f 0) = f 0 := by simp
        rw [hpred0]
        have hkeq : (⟨k'+1, hk⟩ : Fin (n+1)) = Fin.succ ⟨k', hk'⟩ := by
          apply Fin.ext; simp
        rw [hkeq]
        have hcomp : (List.finRange n).countP (fun j : Fin n => (Fin.succ j).val != k'+1 &&
            f (Fin.succ j)) =
            (List.finRange n).countP (fun j : Fin n => j.val != k' && f (Fin.succ j)) := by
          apply List.countP_congr
          intro j' _
          have heqv : ((Fin.succ j').val != k' + 1) = (j'.val != k') := by
            simp only [Fin.val_succ]
            by_cases h : j'.val = k'
            · simp [h]
            · have hne : j'.val + 1 ≠ k' + 1 := by omega
              simp [h, hne]
          rw [heqv]
        rw [hcomp]
        have hstep := finRange_countP_ite_split n k' hk' (fun j => f (Fin.succ j))
        omega

/-- `CleanupReady`'s `freePiles` formula (which excludes `pile`) plus the
    indicator of `pile`'s own current emptiness equals `SolverInvMerged`'s
    formula (over all 10 piles) — the arithmetic bridge the plan calls for.
    Combines `finRange_countP_ite_split` with the fact that `Vector.toList`'s
    `countP` agrees with the `List.finRange`-indexed `countP` via `Vector.get`. -/
private theorem cleanupReady_freePiles_split (pile : UInt32) (hpile : pile.toNat < 10)
    (q : SolverPosType) (fpCount : Nat)
    (hcount : fpCount = ((List.finRange 10).countP
        (fun j => j.val != pile.toNat && (q.pileDepth.get j == 0)) : Nat)) :
    q.pileDepth.toList.countP (· == 0) =
      fpCount + (if q.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) == 0 then 1 else 0) := by
  have hlistEq : q.pileDepth.toList = (List.finRange 10).map (fun j => q.pileDepth.get j) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [Vector.getElem_toList, List.getElem_map, List.getElem_finRange]
      rfl
  rw [hlistEq, List.countP_map, Function.comp_def, hcount]
  have hsplit := finRange_countP_ite_split 10 pile.toNat hpile
    (fun j => q.pileDepth.get j == 0)
  omega

/-- The `j ≠ pile` part of `CleanupReady`'s `freePiles` formula only reads
    `q.pileDepth.get j` for `j ≠ pile` (the `&&` short-circuits to `false` at
    `j = pile` regardless), so it transfers unchanged across any frame
    condition agreeing with a reference position outside `pile`. -/
private theorem cleanupReady_freePiles_frame_eq (pile : UInt32) (p q : SolverPosType)
    (hframe : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileDepth.get j = p.pileDepth.get j) :
    (List.finRange 10).countP (fun j => j.val != pile.toNat && (q.pileDepth.get j == 0)) =
    (List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) := by
  apply List.countP_congr
  intro j _
  by_cases hij : j.val = pile.toNat
  · simp [hij]
  · rw [hframe j hij]

/-- **`SolverCleanupPile` re-establishes the Merged layer** from the midpoint
    predicate.  On top of `cleanupPile_baseNF`'s clause discharge this adds, at
    the same discharge site:

    * `PileMerged` for `pile` itself, from `cleanupRunResult`'s loop exit facts
      (`¬mergeGuard` ⇒ merge_complete, `¬freedGuard` ⇒ flute_maximal) and the
      busyAces branch condition (⇒ busyAces_complete);
    * preservation of the other piles' `PileMerged` — the nontrivial part is
      `flute_maximal[j]`: if pile `j`'s extension card were among the freshly
      freed cards `T..T+m−1`, `j`'s interiors would have to include the
      *non-free* new boundary `T+m`, contradicting `flute_cards_free[j]`;
    * `freePiles_def`, restored by cleanup itself (the empty and lone-king
      branches do `+1` and leave depth 0; otherwise the pile keeps depth ≥ 1). -/
theorem cleanupPile_merged (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hwf : WellFormedLayout g)
    (hready : CleanupReady g (fluteNorm pile hpile p) pile) :
    ∃ fk p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' ∧ p'.aces = p.aces ∧
      (∀ mask : UInt8, p.busyAces &&& mask ≠ 0 → p'.busyAces &&& mask ≠ 0) := by
  obtain ⟨hnf, hpmOther, hfpCount⟩ := hready
  -- Restate `hfpCount` in terms of `p` directly (rather than
  -- `fluteNorm pile hpile p`): a `have`-with-explicit-type cast needing only
  -- the two sides' *defeq* (fluteNorm doesn't touch `pileDepth`/`freePiles`),
  -- not syntactic equality — needed because plain `rw`/`omega` match atoms
  -- syntactically and would otherwise treat the two spellings as unrelated.
  have hfpCount' : p.freePiles.toInt = ((List.finRange 10).countP
      (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) : Nat) := hfpCount
  -- Reusable overflow-safety bound: `CleanupReady`'s prefix count is a `countP`
  -- over the 10-element `List.finRange 10`, hence trivially ≤ 10 — enough
  -- headroom for the `Int8` `+1` arithmetic in the empty/king branches below.
  have hfp_le' : ((List.finRange 10).countP
      (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)) : Nat) ≤ 10 :=
    le_trans List.countP_le_length (by simp)
  -- Bridge `hpmOther` (about `fluteNorm pile hpile p`) down to a fact about
  -- `p` itself — exactly the same idea as `cleanupPile_eq`'s own `hnfp`
  -- bridges `PileBase`, needed because `preCleanupPile_pileMerged_ne`/
  -- `kingMove_pileMerged_ne` are stated about `p` directly.
  have hpmOtherP : ∀ j : Fin 10, j.val ≠ pile.toNat →
      PileMerged g p j (hnf.pileDepth_bound j) := by
    intro j hij
    have hfeq : (fluteNorm pile hpile p).pileFlute.get j = p.pileFlute.get j := by
      show (fluteNorm pile hpile p).pileFlute[j.val]'j.isLt = p.pileFlute[j.val]'j.isLt
      simp only [fluteNorm]
      exact Vector.getElem_set_ne hpile j.isLt (Ne.symm hij)
    have hb := hpmOther j hij
    refine ⟨hb.merge_complete, ?_, ?_⟩
    · have h2 := hb.flute_maximal
      rwa [hfeq] at h2
    · -- `busyAces_complete`'s field type has a `let boundary := …` before the
      -- real `∀ hs, …` binder; `intro` consumes one name PER binder including
      -- that `let`, so naming just `hpos hs heq` would bind `hs` to the *let*
      -- (a card, not a proof) and shift everything else — avoid the whole
      -- naming hazard by rewriting the goal (via `hfeq`) down to `hb`'s own
      -- shape instead of introducing further.
      intro hpos
      rw [show p.pileFlute.get j = (fluteNorm pile hpile p).pileFlute.get j from hfeq.symm]
      exact hb.busyAces_complete hpos
  have hp16 : p.busyAces < 16 := hnf.busyAces_lt16
  rcases cleanupPile_eq pile g p hpile hwf hnf with
    ⟨hd, hsd, hrun⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- Empty pile.
    refine ⟨0xffff, _, hrun, ?_, rfl, fun mask hmask => hmask⟩
    have hbase' : SolverInvBase g { p with freePiles := p.freePiles + 1, pileDepth := p.pileDepth.set pile.toNat 0 hpile, pileFlute := p.pileFlute.set pile.toNat 1 hpile } := by
      simp only [hsd]; exact nf_setFreePiles hnf _
    refine SolverInvMerged.of_base hbase' (fun i => ?_) ?_
    · -- (2)/(3b)/(6) `PileMerged` for every pile.
      by_cases hij : i.val = pile.toNat
      · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
        subst hii
        have hp'd0 : (p.pileDepth.set pile.toNat 0 hpile).get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := by
          rw [hsd]; exact hd
        exact ⟨Or.inl (by rw [hp'd0]; decide), Or.inl hp'd0,
          fun h => absurd h (by rw [hp'd0]; decide)⟩
      · simp only [hsd]
        exact pm_setFreePiles (hpmOther i hij) _
    · -- (9) `freePiles_def`: `pileDepth` is unchanged (`hsd`), and `pile` itself
      -- (already empty, `hd`) newly contributes to the count, matching the `+1`.
      show (p.freePiles + 1).toInt =
        ((p.pileDepth.set pile.toNat 0 hpile).toList.countP (· == 0) : Nat)
      rw [hsd]
      have hsplit := cleanupReady_freePiles_split pile hpile p
        ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
        rfl
      have hd' : p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) = 0 := hd
      have hind : (if p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : Int8) then
          (1 : Nat) else 0) = 1 := by simp [hd']
      rw [hind] at hsplit
      have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
        rw [Int8.toInt_add, Int8.toInt_one]
        exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
      omega
  · -- Loop-bearing case: reassemble `SolverInvMerged` from `cleanupPile_eq`'s
    -- non-king/king bundle — `hsuit`/`hhash`/`hused` are already the shape
    -- `SolverInvBase` needs; `pileBase`/`pileMerged` come from `hpc` (for
    -- `pile` itself) chained with the modular `_ne` lemmas through `hnfp`/
    -- `hpmOtherP` (for the others); `freePiles_def` from the two helper
    -- lemmas above plus the branch's own frame/depth facts.
    rcases hbranch with
      ⟨hframe, hpc, hsuit, hhash, hused, hrun⟩ |
      ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
    · -- NON-KING sub-branch.
      have hbase' : SolverInvBase g (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) := by
        refine ⟨fun i => ?_, hsuit, hhash, hused,
          preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hp16⟩
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p
            m f hd5 (by omega) i hij (hnfp i hij)
      have hpmAll : ∀ i : Fin 10, PileMerged g (preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) i
          (hbase'.pileDepth_bound i) := by
        intro i
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileMerged
        · exact preCleanupPile_pileMerged_ne pile g hpile hwf B (pileHashes[pile.toNat]'hpile) hs4
            p m f hd5 hm_le hmcards hak i hij (hnfp i hij) (hpmOtherP i hij)
      have hpdEqNK : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile =
          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hpdNeNK : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) ≠ 0 := by
        show (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth[pile.toNat]'hpile ≠ 0
        rw [hpdEqNK]
        intro heq
        have h' := congrArg Int8.toInt heq
        have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
          rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
          exact Int.bmod_eq_of_le (by omega) (by omega)
        have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
            (p.pileDepth[pile.toNat]'hpile).toInt - m := by
          rw [Int32.toInt_sub_of_le _ _
            (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]
                omega)
            (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
            hmofI, Int8.toInt_toInt32]
        rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega),
          show ((0 : Int8).toInt = 0) from rfl] at h'
        omega
      have hfp : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).freePiles.toInt =
          ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.toList.countP (· == 0) :
            Nat) := by
        have hfeq2 : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).freePiles = p.freePiles := by
          simp only [preCleanupPile]
        have hframeEq := cleanupReady_freePiles_frame_eq pile p
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) hframe
        have hsplit := cleanupReady_freePiles_split pile hpile
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
          ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
          hframeEq.symm
        have hind : (if (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : Int8) then (1 : Nat) else 0) = 0 := by
          simp [beq_eq_false_iff_ne.mpr hpdNeNK]
        rw [hind] at hsplit
        rw [hfeq2]
        omega
      -- `busyAces` monotonicity: `preCleanupPile` either leaves it alone or
      -- ORs in one more bit, so an already-set bit stays set.
      have hbusyMonoNK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces &&& mask ≠ 0 := by
        intro mask hmask
        show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8 then
            p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&& mask ≠ 0
        by_cases hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
            (B - 1 - UInt8.ofNat f).toInt8) = true
        · simp only [hcond, reduceIte]
          exact uint8_and_ne_zero_of_or_left hmask
        · rw [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, reduceIte]
          exact hmask
      exact ⟨0xffff, _, hrun, SolverInvMerged.of_base hbase' hpmAll hfp, rfl, hbusyMonoNK⟩
    · -- KING sub-branch.
      have hbase' : SolverInvBase g (kingMove pile hpile (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile) (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)) := by
        refine ⟨fun i => ?_, hsuit, hhash, hused, ?_⟩
        swap
        · rw [kingMove_busyAces_eq]
          exact preCleanupPile_busyAces_lt16 pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hp16
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileBase
        · exact kingMove_pileBase_ne pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile) _ i
            hij (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
              hd5 (by omega) i hij (hnfp i hij))
      have hpmAll : ∀ i : Fin 10, PileMerged g (kingMove pile hpile (SUIT B) hs4
          (pileHashes[pile.toNat]'hpile) (preCleanupPile pile hpile B
            (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)) i
          (hbase'.pileDepth_bound i) := by
        intro i
        by_cases hij : i.val = pile.toNat
        · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
          subst hii
          exact hpc.toPileMerged
        · exact kingMove_pileMerged_ne pile g hpile hwf (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              _ hd1' K hKdef hVK13 hak i hij
              (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
                hd5 (by omega) i hij (hnfp i hij))
              (preCleanupPile_pileMerged_ne pile g hpile hwf B (pileHashes[pile.toNat]'hpile) hs4
                p m f hd5 hm_le hmcards hak i hij (hnfp i hij) (hpmOtherP i hij))
      have hkmfp : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).freePiles = p.freePiles + 1 := by
        simp only [kingMove, preCleanupPile]
      have hkd0 : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) = 0 :=
        kingMove_pileDepth_self pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)
      have hfp : (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).freePiles.toInt =
          ((kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.toList.countP (· == 0) :
            Nat) := by
        have hframeEq := cleanupReady_freePiles_frame_eq pile p
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)) hframe
        have hsplit := cleanupReady_freePiles_split pile hpile
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p))
          ((List.finRange 10).countP (fun j => j.val != pile.toNat && (p.pileDepth.get j == 0)))
          hframeEq.symm
        have hind : (if (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).pileDepth.get
            (⟨pile.toNat, hpile⟩ : Fin 10) == (0 : Int8) then (1 : Nat) else 0) = 1 := by
          simp [hkd0]
        rw [hind] at hsplit
        rw [hkmfp]
        have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
          rw [Int8.toInt_add, Int8.toInt_one]
          exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
        omega
      have hbusyMonoNK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).busyAces &&& mask ≠ 0 := by
        intro mask hmask
        show (if p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8 then
            p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces) &&& mask ≠ 0
        by_cases hcond : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
            (B - 1 - UInt8.ofNat f).toInt8) = true
        · simp only [hcond, reduceIte]
          exact uint8_and_ne_zero_of_or_left hmask
        · rw [Bool.not_eq_true] at hcond
          simp only [hcond, Bool.false_eq_true, reduceIte]
          exact hmask
      have hbusyMonoK : ∀ mask : UInt8, p.busyAces &&& mask ≠ 0 →
          (kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
            (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).busyAces &&& mask ≠ 0 := by
        intro mask hmask
        rw [kingMove_busyAces_eq]
        exact hbusyMonoNK mask hmask
      exact ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4, _, hrun,
        SolverInvMerged.of_base hbase' hpmAll hfp, rfl, hbusyMonoK⟩

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
        rw [freePilesUpTo, freePilesUpTo, List.take_add_one, List.countP_append,
          List.getElem?_eq_getElem hlen]
        simp [Option.toList, hlk]
      have hle : p.freePiles.toInt ≤ 9 := by rw [hfp]; exact_mod_cast hb
      have hge : 0 ≤ p.freePiles.toInt := by rw [hfp]; exact Int.natCast_nonneg _
      have hadd : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
        rw [Int8.toInt_add, Int8.toInt_one]
        exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
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
      simp only [hsd, hsf]
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
      rw [List.take_succ_eq_append_getElem hlenq, List.countP_append, htake, List.countP_singleton,
        Vector.getElem_toList]
      rw [show (q.pileDepth[k]'hk == (0 : Int8)) = false from beq_eq_false_iff_ne.mpr hne']
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
      rw [List.take_succ_eq_append_getElem hlenq, List.countP_append, htake, List.countP_singleton,
        Vector.getElem_toList]
      rw [show (q.pileDepth[k]'hk == (0 : Int8)) = true from by rw [beq_iff_eq]; exact heq']
      simp
    rcases cleanupPile_eq (UInt32.ofNat k) g p hk_ hwf hnf_ with
      ⟨hd0, hsd0, hrun0⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
        hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
    · -- Impossible: we're in the `¬hdk` (nonempty) case, but `cleanupPile_eq`
      -- took the empty branch.
      exact absurd (hfinEq ▸ hd0) hdk
    · rcases hbranch with
        ⟨hframe, hpc, hsuit, hhash, hused, hrun⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, hframe, hpc, hsuit, hhash, hused, hrun⟩
      · -- NON-KING sub-branch.
        have hframeNK : ∀ j : Fin 10, j.val ≠ k →
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth.get j =
            p.pileDepth.get j :=
          fun j hj => hframe j (by rw [hpkn]; exact hj)
        refine ⟨0xffff, preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
            (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p, hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ⟨fun i => ?_, hsuit, hhash, hused,
            preCleanupPile_busyAces_lt16 (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p hp16⟩
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
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).freePiles = p.freePiles := by
            simp only [preCleanupPile]
          have hpdEqNK : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ =
              ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m).toInt8 := by
            simp only [preCleanupPile]
            rw [Vector.getElem_set_self]
          have hpdNeNK : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth.get
                (⟨k, hk⟩ : Fin 10) ≠ 0 := by
            rw [← hfinEq]
            show (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ ≠ 0
            rw [hpdEqNK]
            intro heq
            have h' := congrArg Int8.toInt heq
            have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
              rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
              exact Int.bmod_eq_of_le (by omega) (by omega)
            have hdepth1I : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m).toInt =
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m := by
              rw [Int32.toInt_sub_of_le _ _
                (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]
                    omega)
                (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
                hmofI, Int8.toInt_toInt32]
            rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega),
              show ((0 : Int8).toInt = 0) from rfl] at h'
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
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.get j =
            p.pileDepth.get j :=
          fun j hj => hframe j (by rw [hpkn]; exact hj)
        refine ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
          kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p), hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ⟨fun i => ?_, hsuit, hhash, hused, ?_⟩
          swap
          · rw [kingMove_busyAces_eq]
            exact preCleanupPile_busyAces_lt16 (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p hp16
          by_cases hij : i.val = (UInt32.ofNat k).toNat
          · have hii : i = ⟨(UInt32.ofNat k).toNat, hk_⟩ := Fin.ext hij
            subst hii
            exact hpc.toPileBase
          · exact kingMove_pileBase_ne (UInt32.ofNat k) g hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p) i hij
              (preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B
                (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 (by omega) i hij (hnfp i hij))
        · -- (2) prefix free-piles count: `kingMove` empties pile `k` and bumps
          -- `freePiles` by one — mirrors the base case's `hadd`/`hle`/`hge` block.
          have hkmfp : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).freePiles = p.freePiles + 1 := by
            simp only [kingMove, preCleanupPile]
          have hkd0 : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.get
                (⟨k, hk⟩ : Fin 10) = 0 := by
            rw [← hfinEq]
            exact kingMove_pileDepth_self (UInt32.ofNat k) hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)
          have haddFP : (p.freePiles + 1).toInt = p.freePiles.toInt + 1 := by
            rw [Int8.toInt_add, Int8.toInt_one]
            exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
          have hstepEq := hfreePilesStep1 _ hframeK hkd0
          show (p.freePiles + 1).toInt = (freePilesUpTo (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4
            (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)) (k + 1) : Nat)
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
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)
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
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p) i hine,
            preCleanupPile_pileFlute_eq_of_ne (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f i hine]
          exact hfluteRest i (by omega)
        · -- frame: other piles' depths untouched.
          exact hframeK

-- ---------------------------------------------------------------------------
-- `SolverMoveAces` — the foundation-walk loop invariant and its machinery
-- ---------------------------------------------------------------------------

/-- The lowest set bit of `UInt8.ofNat n` lies strictly below position 4
    whenever its low nibble is nonzero — a finite check over all 256 `UInt8`
    values, run via `native_decide` (already an accepted idiom in this
    codebase, see `BitmapProofs.lean`/`LayoutProofs.lean`). -/
private theorem ctz_lt_four_of_low_nibble_nat :
    ∀ n : Nat, n < 256 → (UInt8.ofNat n) &&& 0x0F ≠ 0 → ctz (UInt8.ofNat n) < 4 := by
  native_decide

/-- `UInt8` form: if `x`'s low nibble is nonzero, `ctz x < 4`. -/
private theorem ctz_lt_four_of_low_nibble (x : UInt8) (hx : x &&& 0x0F ≠ 0) :
    ctz x < 4 := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have h := ctz_lt_four_of_low_nibble_nat x.toNat h256 (by rwa [UInt8.ofNat_toNat])
  rwa [UInt8.ofNat_toNat] at h

/-- `x`'s own `ctz`-th bit is actually set in `x`, whenever `x ≠ 0` — again a
    finite check over all 256 `UInt8` values. -/
private theorem ctz_bit_self_nat :
    ∀ n : Nat, n < 256 → (UInt8.ofNat n) ≠ 0 →
      (UInt8.ofNat n) &&& ((1 : UInt8) <<< UInt8.ofNat (ctz (UInt8.ofNat n))) ≠ 0 := by
  native_decide

/-- `UInt8` form: `x`'s own `ctz`-th bit is set in `x`, whenever `x ≠ 0`. -/
private theorem ctz_bit_self (x : UInt8) (hx : x ≠ 0) :
    x &&& ((1 : UInt8) <<< UInt8.ofNat (ctz x)) ≠ 0 := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have h := ctz_bit_self_nat x.toNat h256 (by rwa [UInt8.ofNat_toNat])
  rwa [UInt8.ofNat_toNat] at h

/-- `x < 16` means bits `4..7` are already clear, so ANDing with the low-nibble
    mask `0x0F` is a no-op. -/
private theorem uint8_and_0xF_eq_self_of_lt16_nat :
    ∀ n : Nat, n < 256 → n < 16 → (UInt8.ofNat n) &&& 0x0F = UInt8.ofNat n := by
  native_decide

private theorem uint8_and_0xF_eq_self_of_lt16 (x : UInt8) (hx : x < 16) :
    x &&& 0x0F = x := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have hxnat : x.toNat < 16 := by
    rwa [UInt8.lt_iff_toNat_lt, show (16 : UInt8).toNat = 16 from by decide] at hx
  have h := uint8_and_0xF_eq_self_of_lt16_nat x.toNat h256 hxnat
  rwa [UInt8.ofNat_toNat] at h

/-- **Loop invariant for `SolverMoveAces`'s foundation walk**, carried through
    every iteration of `moveAcesBody suitU32` on the accumulator
    `(card, forcedKings, found, game)` for the fixed suit `suit`:

    * `SolverInvMerged` holds *literally* for `game` (no ghost/adjustment);
    * `card` sits exactly `found` past `A + 1`, where `A := game.aces.get suit`
      is the *current* foundation top for `suit` (an `Int`-valued equation,
      to avoid `Int8`/`UInt8` wraparound bookkeeping at every step);
    * every card strictly between `A` and `card` (the `found`-many already
      walked, already-free candidates) is free;
    * `suit`'s `busyAces` bit stays set throughout (nothing clears it until
      the walk returns, see `moveAcesExplicit`'s `finish`). -/
def MoveAcesInv (g : Globals) (suit : Fin 4) (card : UInt8) (found : Int8)
    (game : SolverPosType) : Prop :=
  SolverInvMerged g game ∧
  0 ≤ found.toInt ∧ found.toInt ≤ 13 ∧
  SUIT card = suit.val.toUInt8 ∧
  1 ≤ (VALUE card).toNat ∧ (VALUE card).toNat ≤ 14 ∧
  (card.toNat : Int) = (game.aces.get suit).toUInt8.toNat + 1 + found.toInt ∧
  (∀ l : Nat, 1 ≤ l → (l : Int) ≤ found.toInt →
    isFreeCard g game ((game.aces.get suit).toUInt8 + UInt8.ofNat l)) ∧
  game.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0

/-- **Key arithmetic fact for the walk invariant.**  Any card `X` of the same
    suit as the walk, not equal to the current position `card`, and not free,
    must sit strictly ABOVE `card` in value: it can't be at or below the
    foundation top `A` (`foundation_cards_free` would make it free), and it
    can't be one of the `found`-many already-walked candidates either (the
    invariant's own freeness fact would make it free). -/
private theorem moveAces_lt_of_not_free (g : Globals) (suit : Fin 4) (card : UInt8)
    (found : Int8) (game : SolverPosType) (hinv : MoveAcesInv g suit card found game)
    (X : UInt8) (hSuitX : SUIT X = suit.val.toUInt8) (hXreal : 1 ≤ (VALUE X).toNat)
    (hXnotfree : ¬ isFreeCard g game X) (hXne : X ≠ card) :
    card.toNat < X.toNat := by
  obtain ⟨hmerged, _hfound0, _hfound13, hsuitcard, _hval1, _hval14, hcardeq, hfoundfree, _hbit⟩ :=
    hinv
  set A := (game.aces.get suit).toUInt8 with hAdef
  have hSuitA : SUIT A = suit.val.toUInt8 := (hmerged.aces_kings_valid suit).1
  have hXlt256 : X.toNat < 256 := X.toNat_lt
  have hAlt256 : A.toNat < 256 := A.toNat_lt
  by_contra hcon
  push Not at hcon
  have hXnecard : X.toNat ≠ card.toNat := fun h => hXne (UInt8.toNat_inj.mp h)
  have hXltcard : X.toNat < card.toNat := by omega
  by_cases hle : X.toNat ≤ A.toNat
  · -- `X` is on the foundation already (or the ace itself) ⇒ free.
    have hblockEq : (SUIT X).toNat = (SUIT A).toNat := by rw [hSuitX, hSuitA]
    have hsx := SUIT_toNat X; have hvx := VALUE_toNat X
    have hsa := SUIT_toNat A; have hva := VALUE_toNat A
    have hAval : (VALUE X).toNat ≤ (VALUE A).toNat := by omega
    exact hXnotfree (hmerged.foundation_cards_free suit X hSuitX hXreal hAval)
  · -- `X` is strictly between `A` and `card` ⇒ one of the `found`-many
    -- already-walked candidates, hence free by the invariant's own fact.
    push Not at hle
    set l := X.toNat - A.toNat with hldef
    have hl1 : 1 ≤ l := by omega
    have hlfound : (l : Int) ≤ found.toInt := by omega
    have hXeq : X = A + UInt8.ofNat l := by
      apply UInt8.toNat_inj.mp
      have hlA : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
      have hAl256 : A.toNat + l < 256 := by omega
      rw [UInt8.toNat_add, hlA, Nat.mod_eq_of_lt hAl256]
      omega
    rw [hXeq] at hXnotfree
    exact hXnotfree (hfoundfree l hl1 hlfound)

/-- If `X.toNat = A.toNat + l` (no card-value wraparound), then
    `X = A + UInt8.ofNat l`.  Small reusable bridge, factored out since the
    walk invariant's maintenance needs it repeatedly. -/
private theorem uint8_eq_add_ofNat_of_toNat_eq {A X : UInt8} {l : Nat}
    (hAl : A.toNat + l < 256) (heq : X.toNat = A.toNat + l) : X = A + UInt8.ofNat l := by
  apply UInt8.toNat_inj.mp
  have hlA : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
  rw [UInt8.toNat_add, hlA, Nat.mod_eq_of_lt hAl]
  omega

private theorem finVal_toUInt8_toNat (s : Fin 4) : (s.val.toUInt8).toNat = s.val := by
  have h : (s.val.toUInt8).toNat = s.val % 2 ^ 8 := UInt8.toNat_ofNat'
  have := s.isLt
  omega

/-- If a single suit-bit is set in `busyAces` (`x &&& (1 <<< s) ≠ 0`), that bit's
    own value is `≤ x` — needed to show `busyAces - (1 <<< s)` doesn't wrap
    (subtracting a bit that's actually set never borrows). Finite check over
    `UInt8 × Fin 4` (1024 cases), same `native_decide` idiom used elsewhere in
    this file for small bitwise facts. -/
private theorem uint8_bit_le_of_and_ne_zero {x : UInt8} (hx : x.toNat < 16) (s : Fin 4)
    (h : x &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0) :
    ((1 : UInt8) <<< s.val.toUInt8) ≤ x := by
  have hall : ∀ n : Fin 16, ∀ t : Fin 4,
      n.val.toUInt8 &&& ((1 : UInt8) <<< t.val.toUInt8) ≠ 0 →
      ((1 : UInt8) <<< t.val.toUInt8) ≤ n.val.toUInt8 := by native_decide
  have hxeq : (⟨x.toNat, hx⟩ : Fin 16).val.toUInt8 = x := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    show x.toNat % 2 ^ 8 = x.toNat
    have := x.toNat_lt
    omega
  have := hall (⟨x.toNat, hx⟩ : Fin 16) s (by rw [hxeq]; exact h)
  rwa [hxeq] at this

/-- Clearing one suit-bit of `busyAces` (subtracting its own already-set mask)
    leaves every OTHER suit-bit untouched — needed for `busyAces_complete`'s
    frame across the foundation-drain postlude's `busyAces -= mask` write. -/
private theorem uint8_and_ne_zero_of_sub_ne {x : UInt8} (hx : x.toNat < 16) (s t : Fin 4)
    (hst : s ≠ t) (hsset : x &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0)
    (h : x &&& ((1 : UInt8) <<< t.val.toUInt8) ≠ 0) :
    (x - ((1 : UInt8) <<< s.val.toUInt8)) &&& ((1 : UInt8) <<< t.val.toUInt8) ≠ 0 := by
  have hall : ∀ n : Fin 16, ∀ s' t' : Fin 4, s' ≠ t' →
      n.val.toUInt8 &&& ((1 : UInt8) <<< s'.val.toUInt8) ≠ 0 →
      n.val.toUInt8 &&& ((1 : UInt8) <<< t'.val.toUInt8) ≠ 0 →
      (n.val.toUInt8 - ((1 : UInt8) <<< s'.val.toUInt8)) &&&
        ((1 : UInt8) <<< t'.val.toUInt8) ≠ 0 := by
    native_decide
  have hxeq : (⟨x.toNat, hx⟩ : Fin 16).val.toUInt8 = x := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    show x.toNat % 2 ^ 8 = x.toNat
    have := x.toNat_lt
    omega
  have := hall (⟨x.toNat, hx⟩ : Fin 16) s t hst (by rw [hxeq]; exact hsset) (by rw [hxeq]; exact h)
  rwa [hxeq] at this

/-- **`flute_not_aces`-shaped conclusion from `flute_stays_above`.**  Given a
    not-free card `C` known to sit strictly below pile `j`'s current boundary,
    extend that gap across `j`'s *whole* flute footprint (not just the
    boundary itself): `C.toNat + pileFlute[j].toNat ≤ boundary.toNat`.  This
    is exactly the shape `PileBase.flute_not_aces` needs at a NEW ace value
    `C`, reused by both the `cardDepth == 0` step and `moveAces_merged`'s
    final assembly. -/
private theorem flute_le_of_lt_and_notfree {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (j : Fin 10) (hdj : (p.pileDepth.get j).toInt.toNat > 0)
    (C : UInt8) (hCnotfree : ¬ isFreeCard g p C)
    (hClt : C.toNat < ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hbase.pileDepth_bound j; omega⟩ : UInt8).toNat) :
    C.toNat + (p.pileFlute.get j).toNat ≤
      ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hbase.pileDepth_bound j; omega⟩ : UInt8).toNat := by
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toInt.toNat - 1,
    by have := hbase.pileDepth_bound j; omega⟩ : Fin 5) with hBjdef
  have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
  have hBj64 : Bj.toNat < 64 := by
    have hsn := SUIT_toNat Bj; have h1 := hBjreal.1; omega
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE Bj).toNat := hbase.flute_le_value hwf j hdj
  have hVBj : (VALUE Bj).toNat ≤ 15 := by rw [VALUE_toNat]; omega
  have hflutepos : 1 ≤ (p.pileFlute.get j).toNat := hbase.flute_pos j
  set off : Nat := (p.pileFlute.get j).toNat - 1 with hoffdef
  have hoffLt256 : off < 256 := by omega
  have hoffNat : (UInt8.ofNat off).toNat = off := by rw [UInt8.toNat_ofNat']; omega
  have hoffLt : (UInt8.ofNat off).toNat < (p.pileFlute.get j).toNat := by
    rw [hoffNat]; omega
  have hkey := flute_stays_above hwf hbase j hdj C hCnotfree hClt (UInt8.ofNat off) hoffLt
  rw [← hBjdef] at hkey
  have hoffle : (UInt8.ofNat off) ≤ Bj := by
    rw [UInt8.le_iff_toNat_le, hoffNat]
    have hVBjle : (VALUE Bj).toNat ≤ Bj.toNat := by rw [VALUE_toNat]; omega
    omega
  have hsub : (Bj - UInt8.ofNat off).toNat = Bj.toNat - off := by
    rw [UInt8.toNat_sub_of_le _ _ hoffle, hoffNat]
  rw [hsub] at hkey
  omega

/-- **A not-free, real card of suit `t` sits strictly above `aces[t]`.**
    Direct contrapositive of `foundation_cards_free`: if `X.toNat ≤
    aces[t].toNat` (same suit block), `X` would be a foundation-eligible
    card, hence free — contradicting `hXnf`. -/
private theorem not_free_gt_ace {g : Globals} {p : SolverPosType} (h : SolverInvBase g p)
    (t : Fin 4) (X : UInt8) (hSX : SUIT X = t.val.toUInt8) (hVX : 1 ≤ (VALUE X).toNat)
    (hXnf : ¬ isFreeCard g p X) :
    (p.aces.get t).toUInt8.toNat < X.toNat := by
  by_contra hle
  push Not at hle
  apply hXnf
  apply h.foundation_cards_free t X hSX hVX
  have hSA : SUIT (p.aces.get t).toUInt8 = t.val.toUInt8 := (h.aces_kings_valid t).1
  have hblockEq : (SUIT X).toNat = (SUIT (p.aces.get t).toUInt8).toNat := by rw [hSX, hSA]
  have hsx := SUIT_toNat X; have hvx := VALUE_toNat X
  have hsa := SUIT_toNat (p.aces.get t).toUInt8; have hva := VALUE_toNat (p.aces.get t).toUInt8
  omega

/-- **Exact run of the `SolverMoveAces` foundation walk, with its invariant.**
    By induction on a `Nat` bounding `14 - VALUE(card)` (which strictly
    decreases on every continuing iteration, since `card` only ever
    increments and the loop stops once `VALUE card > 13`).

    The `cardDepth > 0` ("already free, skip") case is a pure accumulator
    step (`card += 1, found += 1`, `game` untouched) — the *easy* half of this
    proof.  The `cardDepth == 0` case (`card` is exactly its pile's current
    boundary) is the genuinely novel half: see the `sorry` below for the
    fully-worked-out (but not yet formalized) recipe. -/
private theorem moveAcesLoop_run (g : Globals) (hwf : WellFormedLayout g) (suit : Fin 4)
    (suitU32 : UInt32) (hsuitU32 : suitU32.toNat = suit.val) :
    ∀ (n : Nat) (card : UInt8) (forcedKings : UInt16) (found : Int8) (game : SolverPosType),
      14 - (VALUE card).toNat < n →
      MoveAcesInv g suit card found game →
      ∃ (card' : UInt8) (forcedKings' : UInt16) (found' : Int8) (game' : SolverPosType),
        Loop.forIn Loop.mk
            (⟨card, forcedKings, found, game, g⟩ : MoveAcesAcc) (moveAcesBody suitU32)
            (g, game) =
          .ok (⟨card', forcedKings', found', game', g⟩ : MoveAcesAcc) (g, game') ∧
        MoveAcesInv g suit card' found' game' ∧
        ((VALUE card').toNat = 14 ∨
          (¬ isFreeCard g game' card' ∧
            ∃ hp64 : (cardPile g card').toNat < 10,
              (cardDepth g card').toNat + 1 <
                (game'.pileDepth[(cardPile g card').toNat]'hp64).toInt.toNat)) ∧
        (∀ t : Fin 4, t ≠ suit → game'.aces.get t = game.aces.get t) ∧
        ((card' = card ∧ forcedKings' = forcedKings ∧ found' = found ∧ game' = game) ∨
          card.toNat < card'.toNat) := by
  intro n
  induction n with
  | zero => intro card _ _ _ hmeas _; omega
  | succ n ih =>
    intro card forcedKings found game hmeas hinv
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := (⟨card, forcedKings, found, game, g⟩ : MoveAcesAcc))
      (f := moveAcesBody suitU32)
    obtain ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
    have hsuitcardNat : (SUIT card).toNat < 4 := by
      rw [hsuitcard, finVal_toUInt8_toNat]; omega
    have h13nat : (13 : UInt8).toNat = 13 := by decide
    have hgIff : (VALUE card ≤ (13 : UInt8)) ↔ (VALUE card).toNat ≤ 13 := by
      rw [UInt8.le_iff_toNat_le, h13nat]
    by_cases hg : (VALUE card).toNat ≤ 13
    · -- guard true: read `pile`/`cd1`/`cd2`, branch on `cardDepth`'s sign.
      have hgProp : VALUE card ≤ (13 : UInt8) := hgIff.mpr hg
      have hcardVal15 : (VALUE card).toNat < 15 := by omega
      have hsuitcard1 : SUIT (card + 1) = suit.val.toUInt8 := by
        rw [SUIT_succ card hcardVal15]; exact hsuitcard
      have hval1_1 : 1 ≤ (VALUE (card + 1)).toNat := by
        rw [VALUE_succ card hcardVal15]; omega
      have hval14_1 : (VALUE (card + 1)).toNat ≤ 14 := by
        rw [VALUE_succ card hcardVal15]; omega
      have hcard1nat : (card + 1).toNat = card.toNat + 1 :=
        toNat_succ card (by have hsn := SUIT_toNat card; have hvn := VALUE_toNat card; omega)
      have hcardReal : IsRealCard card := ⟨by omega, hval1, hg⟩
      have hc64 : card.toUInt32.toNat < 64 := by
        rw [UInt8.toNat_toUInt32]
        have := hcardReal.1; have hsn := SUIT_toNat card
        omega
      have hc64' : card.toNat < 64 := by rw [← UInt8.toNat_toUInt32]; exact hc64
      set pile := g.card2pile[card.toUInt32.toNat]'hc64 with hpiledef
      have hpileEqCP : pile = cardPile g card := by
        rw [hpiledef]
        unfold cardPile
        rw [dif_pos hc64']
        congr 1
      have hp64 : (cardPile g card).toNat < 10 := hwf.pile_lt card hcardReal
      have hp10 : pile.toUInt32.toNat < 10 := by
        rw [hpileEqCP, UInt8.toNat_toUInt32]; exact hp64
      set cd1 := g.card2depth[card.toUInt32.toNat]'hc64 with hcd1def
      have hcd1EqCD : cd1 = cardDepth g card := by
        rw [hcd1def]
        unfold cardDepth
        rw [dif_pos hc64']
        congr 1
      set cd2 := game.pileDepth[pile.toUInt32.toNat]'hp10 with hcd2def
      have hcd2EqPD : cd2 = game.pileDepth[(cardPile g card).toNat]'hp64 := by
        rw [hcd2def]; congr 1; rw [hpileEqCP, UInt8.toNat_toUInt32]
      rw [hunf]
      simp only [moveAcesBody, hgProp, decide_true, bind, EStateM.bind, andM, toBool, pure,
        EStateM.pure, Vector.getE, getElem?_pos, hc64, hp10, reduceIte, ← hpiledef, ← hcd1def,
        ← hcd2def]
      have hcd2nonneg : 0 ≤ cd2 := by
        rw [hcd2EqPD]; exact hmerged.pileDepth_nonneg ⟨(cardPile g card).toNat, hp64⟩
      have hcd2nonneg' : (0 : Int) ≤ cd2.toInt := by
        rw [Int8.le_iff_toInt_le] at hcd2nonneg
        simpa using hcd2nonneg
      -- Bridge the `Int32` sign test on `cd1.toUInt32.toInt32 + 1 - cd2.toInt32`
      -- down to a plain `Int` equation relating `cd1`/`cd2`, wrap-free (both
      -- are tiny: `cd1 ≤ 5`, `0 ≤ cd2 ≤ 5`).
      have hcd1le5 : cd1.toNat ≤ 5 := by rw [hcd1EqCD]; exact hwf.depth_le card hcardReal
      have hcd2le5 : cd2.toInt ≤ 5 := by
        have hb := hmerged.pileDepth_bound ⟨(cardPile g card).toNat, hp64⟩
        have hshow : game.pileDepth[(cardPile g card).toNat]'hp64 =
            game.pileDepth.get ⟨(cardPile g card).toNat, hp64⟩ := by congr 1
        rw [hcd2EqPD, hshow]
        omega
      have hcd1small : (cd1.toUInt32.toInt32).toInt = (cd1.toNat : Int) := by
        have hbmod : (cd1.toUInt32.toInt32).toInt = ((cd1.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
          show (cd1.toUInt32.toInt32).toBitVec.toInt = _
          rw [BitVec.toInt_eq_toNat_bmod]; rfl
        rw [hbmod, UInt8.toNat_toUInt32]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hcd2Int32 : (cd2.toInt32).toInt = cd2.toInt := Int8.toInt_toInt32 cd2
      have h1add : (cd1.toUInt32.toInt32 + 1).toInt = (cd1.toNat : Int) + 1 := by
        rw [Int32.toInt_add, hcd1small, Int32.toInt_one]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hcardDepthI : (cd1.toUInt32.toInt32 + 1 - cd2.toInt32).toInt =
          (cd1.toNat : Int) + 1 - cd2.toInt := by
        rw [Int32.toInt_sub, h1add, hcd2Int32]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      by_cases hcdpos : cd1.toUInt32.toInt32 + 1 - cd2.toInt32 > 0
      · -- SKIP: `card` already free; `card += 1, found += 1`, `game` untouched.
        have hcdpos' : cd2.toInt ≤ (cd1.toNat : Int) := by
          have hcdpos2 : (0 : Int32).toInt < (cd1.toUInt32.toInt32 + 1 - cd2.toInt32).toInt :=
            Int32.lt_iff_toInt_lt.mp hcdpos
          rw [show ((0 : Int32).toInt = 0) from by decide, hcardDepthI] at hcdpos2
          omega
        have hcardFree : isFreeCard g game card := by
          apply isFree_of_cardDepth_ge g game hwf card hc64' hp64
          rw [← hcd1EqCD, ← hcd2EqPD]
          omega
        simp only [hcdpos, reduceIte, EStateM.pure]
        have hfound1 : (found + 1).toInt = found.toInt + 1 := by
          rw [Int8.toInt_add, Int8.toInt_one]
          exact Int.bmod_eq_of_le (by omega) (by omega)
        have hnewcardeq : ((card + 1).toNat : Int) =
            ((game.aces.get suit).toUInt8.toNat : Int) + 1 + (found + 1).toInt := by
          have hci : ((card.toNat : Int)) = (game.aces.get suit).toUInt8.toNat + 1 + found.toInt :=
            hcardeq
          rw [hcard1nat, hfound1]
          push_cast
          push_cast at hci
          omega
        have hfound1le13 : (found + 1).toInt ≤ 13 := by
          have hsx1 := SUIT_toNat (card + 1); have hvx1 := VALUE_toNat (card + 1)
          have hSuitA : SUIT (game.aces.get suit).toUInt8 = suit.val.toUInt8 :=
            (hmerged.aces_kings_valid suit).1
          have hsa := SUIT_toNat (game.aces.get suit).toUInt8
          have hva := VALUE_toNat (game.aces.get suit).toUInt8
          have hblockEq : (SUIT (card + 1)).toNat = (SUIT (game.aces.get suit).toUInt8).toNat := by
            rw [hsuitcard1, hSuitA]
          have hnc : ((card + 1).toNat : Int) =
              ((game.aces.get suit).toUInt8.toNat : Int) + 1 + (found + 1).toInt := hnewcardeq
          omega
        have hnewfoundfree : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ (found + 1).toInt →
            isFreeCard g game ((game.aces.get suit).toUInt8 + UInt8.ofNat l) := by
          intro l hl1 hlle
          by_cases hlold : (l : Int) ≤ found.toInt
          · exact hfoundfree l hl1 hlold
          · have hleq : (l : Int) = found.toInt + 1 := by omega
            have hAl256 : (game.aces.get suit).toUInt8.toNat + l < 256 := by
              have := card.toNat_lt; omega
            have hcardEqA : card = (game.aces.get suit).toUInt8 + UInt8.ofNat l :=
              uint8_eq_add_ofNat_of_toNat_eq hAl256 (by
                have hci : (card.toNat : Int) =
                    (game.aces.get suit).toUInt8.toNat + 1 + found.toInt := hcardeq
                omega)
            rw [← hcardEqA]
            exact hcardFree
        have hnewinv : MoveAcesInv g suit (card + 1) (found + 1) game :=
          ⟨hmerged, by omega, hfound1le13, hsuitcard1, hval1_1, hval14_1, hnewcardeq,
            hnewfoundfree, hbit⟩
        have hnewmeas : 14 - (VALUE (card + 1)).toNat < n := by
          have := VALUE_succ card hcardVal15; omega
        obtain ⟨card', fk', found', game', heq, hinv', hexit', hframe', hdich'⟩ :=
          ih (card + 1) forcedKings (found + 1) game hnewmeas hnewinv
        have hdich : card.toNat < card'.toNat := by
          rcases hdich' with ⟨hce, _, _, _⟩ | hgt
          · have h2 := congrArg UInt8.toNat hce
            omega
          · omega
        exact ⟨card', fk', found', game', heq, hinv', hexit', hframe', Or.inr hdich⟩
      · -- NOT `> 0`: either `card` is exactly its pile's boundary (`== 0`, the
        -- genuinely novel case — see the `sorry` below) or genuinely buried
        -- (`< 0`, `.done`, unchanged accumulator).
        by_cases hcd0 : (cd1.toUInt32.toInt32 + 1 - cd2.toInt32 == 0) = true
        · -- THE KEY STEP (design's "why `SolverInvMerged` needs no ghost").
          -- `card` is exactly `pile`'s current boundary.  Writing
          -- `aces[suit] := card` then calling `SolverRemoveFlute pile`
          -- restores `MoveAcesInv` at `(card + 1, 0, gameF)` for the
          -- resulting `gameF`, via:
          --  1. `hmerged.pileMerged pile` gives `flute_maximal` at this
          --     boundary; `PileBase.flute_not_aces` gives
          --     `A.toUInt8.toNat + pileFlute[pile].toNat ≤ card.toNat`, i.e.
          --     `prevCard := card - pileFlute[pile] ≥ A`.
          --  2. `prevCard = A` exactly: if `prevCard ∈ (A, card)` strictly,
          --     `moveAces_lt_of_not_free`-style reasoning (fact 3: cards
          --     `A+1..A+found` are free) contradicts `flute_maximal`'s
          --     `¬isFreeCard prevCard` disjunct, forcing its OTHER disjunct
          --     `aces[suit] = prevCard`, i.e. `prevCard = A`.  This gives
          --     `pileFlute[pile] = found + 1` exactly (from `card = A + 1 +
          --     found` and `prevCard = card - pileFlute[pile] = A`).
          --  3. At the composed point `fluteNorm pile hpile (removeFlutePre
          --     pile hpile gameA)` (`gameA := game` with `aces[suit] :=
          --     card`), `usedSpace` balances EXACTLY using this
          --     `pileFlute[pile] = found + 1` fact (verified by hand twice,
          --     see the task's design notes): the `+1` (depth decrement) and
          --     `-found` (flute-term zeroed) cancel the `-(1+found)` ace
          --     jump.
          --  4. `SolverInvBase` for the WHOLE position at that point needs,
          --     for OTHER piles `j ≠ pile` sharing `suit`, that their
          --     `flute_not_aces` still holds against the NEW ace `card`
          --     (bigger than `A`) — this is where `flute_stays_above`
          --     (`SolverInvariant.lean`) applies directly: any other pile's
          --     boundary of suit `suit` must be `> card` (else, being a
          --     pile's own boundary, it's not free, but it would fall in the
          --     `foundation_cards_free`/fact-3 "must be free" range —
          --     contradiction), and `flute_stays_above` then extends this
          --     past the WHOLE of that pile's own flute footprint.
          --  5. `pile` itself, after `removeFlutePre` (depth -= 1) +
          --     `fluteNorm` (flute := 1), needs its OWN new boundary (if any,
          --     i.e. if the old depth was > 1) to satisfy the same
          --     `flute_not_aces` fact — via `merge_complete`/the same
          --     not-free/fact-3 argument (this new boundary can't equal
          --     `card` or `card + 1`, and can't fall in `(A, card)`, so it's
          --     `> card`).
          --  6. `removeFlute_merged`'s `CleanupReady` precondition then
          --     assembles from: the above `SolverInvBase`, the `∀ j ≠ pile`
          --     `PileMerged` bundle (all OTHER piles, unaffected by the
          --     depth/flute writes to `pile`, transfer directly from
          --     `hmerged`), and the `freePiles` count formula (`pile`'s own
          --     depth just decreased by exactly 1, so is nonzero unless it
          --     was already 1 — either way the prefix-excluding-`pile`
          --     count is untouched).
          --
          set pileFin : Fin 10 := ⟨(cardPile g card).toNat, hp64⟩ with hpileFindef
          have heq0 : cd1.toUInt32.toInt32 + 1 - cd2.toInt32 = 0 := by
            have h := hcd0; rwa [beq_iff_eq] at h
          have hcd2eqI : cd2.toInt = (cd1.toNat : Int) + 1 := by
            have hcc := congrArg Int32.toInt heq0
            rw [hcardDepthI, show ((0 : Int32).toInt = 0) from by decide] at hcc
            omega
          have hpdEq : game.pileDepth.get pileFin = cd2 := by
            show game.pileDepth[(cardPile g card).toNat]'hp64 = cd2
            rw [hcd2EqPD]
          have hpdEqNat : (game.pileDepth.get pileFin).toInt.toNat = cd1.toNat + 1 := by
            rw [hpdEq]; omega
          have hcd1lt5 : cd1.toNat < 5 := by omega
          have hcd1lt5CD : (cardDepth g card).toNat < 5 := by rw [← hcd1EqCD]; exact hcd1lt5
          have hdepthPos : 0 < (game.pileDepth.get pileFin).toInt.toNat := by omega
          have hpm := hmerged.pileMerged pileFin
          have hpb := hmerged.pileBase pileFin
          -- `card` is exactly `pileFin`'s current boundary: the `pileDepth-1`
          -- index matches `cardDepth g card` (`= cd1`) exactly.
          have hidxeq : (game.pileDepth.get pileFin).toInt.toNat - 1 = cd1.toNat := by omega
          have hcd1EqCDnat : cd1.toNat = (cardDepth g card).toNat := congrArg UInt8.toNat hcd1EqCD
          have hboundaryEq : (g.pos2card.get pileFin).get
              ⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by omega⟩ = card := by
            have hr := hwf.round_trip card hcardReal hcd1lt5CD
            have hfineq : (⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by omega⟩ : Fin 5) =
                ⟨(cardDepth g card).toNat, hcd1lt5CD⟩ := by
              apply Fin.ext
              show (game.pileDepth.get pileFin).toInt.toNat - 1 = (cardDepth g card).toNat
              omega
            rw [hfineq]
            exact hr
          rcases hpm.flute_maximal with hd0 | hbig
          · exact absurd hd0 (by
              intro hz
              rw [hz] at hpdEqNat
              have : ((0 : Int8).toInt.toNat) = 0 := by decide
              omega)
          · rw [hboundaryEq] at hbig
            set pileFlute := game.pileFlute.get pileFin with hpileFlutedef
            set prevCard := card - pileFlute with hprevCarddef
            have hfluteposUInt : 1 ≤ pileFlute.toNat := hpb.flute_pos
            have hSuitCard : SUIT card = suit.val.toUInt8 := hsuitcard
            -- `prevCard = A` exactly (`A := (game.aces.get suit).toUInt8`).
            set Araw := game.aces.get suit with hArawdef
            set A := Araw.toUInt8 with hAdef
            have hs4card : (SUIT card).toNat < 4 := hsuitcardNat
            have hSuitEqFin2 : (⟨(SUIT card).toNat, hs4card⟩ : Fin 4) = suit := by
              apply Fin.ext
              show (SUIT card).toNat = suit.val
              rw [hSuitCard, finVal_toUInt8_toNat]
            have hprevEqA : prevCard = A := by
              rcases hbig with ⟨hs, heq⟩ | hnf
              · have hSuitEqFin : (⟨(SUIT card).toNat, hs⟩ : Fin 4) = suit := by
                  apply Fin.ext
                  show (SUIT card).toNat = suit.val
                  rw [hSuitCard, finVal_toUInt8_toNat]
                rw [hSuitEqFin] at heq
                have hh := congrArg Int8.toUInt8 heq
                rw [UInt8.toUInt8_toInt8] at hh
                exact hh.symm
              · -- Rule out `prevCard ≠ A`: `flute_not_aces` gives
                -- `A.toNat + pileFlute.toNat ≤ card.toNat`, i.e.
                -- `prevCard.toNat ≥ A.toNat`; if strictly `>`, `prevCard` is
                -- one of the `found`-many already-free candidates (by
                -- `card`'s own invariant fact), contradicting `hnf`.
                have hnotaces := hpb.flute_not_aces
                  (show (game.pileDepth.get pileFin).toInt.toNat > 0 by omega)
                simp only [hboundaryEq] at hnotaces
                have hnotaces' := hnotaces hs4card
                rw [hSuitEqFin2] at hnotaces'
                have hnotaces'' : A.toNat + pileFlute.toNat ≤ card.toNat := by
                  rw [hAdef, hArawdef]; exact hnotaces'
                have hpfle : pileFlute ≤ card := by
                  rw [UInt8.le_iff_toNat_le]
                  omega
                have hsub : prevCard.toNat = card.toNat - pileFlute.toNat := by
                  rw [hprevCarddef]; exact UInt8.toNat_sub_of_le _ _ hpfle
                have hprevGeA : A.toNat ≤ prevCard.toNat := by omega
                have hprevLtCard : prevCard.toNat < card.toNat := by
                  have := hfluteposUInt; omega
                by_contra hne
                have hprevneA : prevCard.toNat ≠ A.toNat := fun h => hne (UInt8.toNat_inj.mp h)
                have hprevGtA : A.toNat < prevCard.toNat := by omega
                set l := prevCard.toNat - A.toNat with hldef
                have hl1 : 1 ≤ l := by omega
                have hci : (card.toNat : Int) = (Araw.toUInt8.toNat : Int) + 1 + found.toInt :=
                  hcardeq
                have hlfound : (l : Int) ≤ found.toInt := by
                  rw [← hAdef] at hci
                  omega
                have hAl256 : A.toNat + l < 256 := by
                  have := card.toNat_lt; omega
                have hprevEq' : prevCard = A + UInt8.ofNat l :=
                  uint8_eq_add_ofNat_of_toNat_eq hAl256 (by omega)
                rw [← hprevCarddef, hprevEq'] at hnf
                exact hnf (hfoundfree l hl1 hlfound)
            -- `pileFlute[pileFin] = found + 1` exactly.
            have hflv : pileFlute.toNat ≤ (VALUE card).toNat := by
              have h := hmerged.flute_le_value hwf pileFin
                (show (game.pileDepth.get pileFin).toInt.toNat > 0 by omega)
              rw [hboundaryEq] at h
              exact h
            have hVcardlecard : (VALUE card).toNat ≤ card.toNat := by
              rw [VALUE_toNat]; omega
            have hpfleCard : pileFlute ≤ card := by
              rw [UInt8.le_iff_toNat_le]; omega
            have hsubOuter : prevCard.toNat = card.toNat - pileFlute.toNat := by
              rw [hprevCarddef]; exact UInt8.toNat_sub_of_le _ _ hpfleCard
            have hprevNatEqA : prevCard.toNat = A.toNat := congrArg UInt8.toNat hprevEqA
            have hciOuter : (card.toNat : Int) = (A.toNat : Int) + 1 + found.toInt := hcardeq
            have hpileFluteEq : pileFlute.toNat = found.toInt.toNat + 1 := by omega
            -- `card` itself is not free (it's `pileFin`'s own current
            -- boundary) — the other structural fact `flute_stays_above`
            -- needs, together with `moveAces_lt_of_not_free`, to show every
            -- OTHER pile's same-suit boundary (and its whole flute
            -- footprint) sits above `card + pileFlute[j]`, restoring
            -- `flute_not_aces` at the new ace value `card` for every pile
            -- `j ≠ pileFin`.
            have hcardNotFree : ¬ isFreeCard g game card := by
              rw [← hboundaryEq]
              exact boundary_not_free hwf hmerged.toSolverInvBase pileFin hdepthPos
            -- **Remaining work (not completed in this session): the full
            -- `SolverInvBase`/`CleanupReady` reconstruction at the composed
            -- point `fluteNorm pile.toUInt32 hp10 (removeFlutePre pile.toUInt32
            -- hp10 { game with aces := game.aces.set suit.val card.toInt8
            -- suit.isLt })`, then `removeFlute_merged` to finish this branch.**
            -- The arithmetic core above (`hpileFluteEq : pileFlute[pileFin] =
            -- found + 1`, `hboundaryEq : card = pileFin`'s boundary,
            -- `hcardNotFree`) is exactly what the remaining reconstruction
            -- needs, fully proved:
            --  * pile `pileFin` itself (after `removeFlutePre`/`fluteNorm`):
            --    `PileBase` — its own new boundary (if depth was `> 1`) must
            --    be `> card` by the SAME not-free/fact-3 elimination as
            --    `moveAces_lt_of_not_free` (that lemma, applied with
            --    `X :=` the new boundary, directly gives this, since the new
            --    boundary is real, same-suit iff `SUIT = suit`, and not free
            --    via `boundary_not_free` on the decremented depth).
            --  * every OTHER pile `j ≠ pileFin`: `flute_not_aces` at the new
            --    ace `card` — if `SUIT (boundary j) ≠ suit` it's untouched;
            --    otherwise `moveAces_lt_of_not_free X := boundary j` (real,
            --    not free via `boundary_not_free`, `≠ card` via
            --    `WellFormedLayout.pos2card_inj` cross-pile injectivity)
            --    gives `card.toNat < (boundary j).toNat`, and
            --    `flute_stays_above hwf hmerged.toSolverInvBase j hdj card
            --    hcardNotFree (this) (pileFlute[j] - 1) (...)` extends it
            --    across `j`'s whole flute footprint, giving exactly
            --    `card.toNat + pileFlute[j].toNat ≤ (boundary j).toNat`.
            --  * `suitClean suit`'s three real-content fields
            --    (`foundation_cards_free`/`foundation_maximal_weak`/
            --    `king_frontier`) at the new ace `card`, and `usedSpace_def`
            --    (balances exactly via `hpileFluteEq`, per the design's hand
            --    -verified formula) — not yet attempted.
            --  * `pileMerged`/`freePiles_def` for `CleanupReady`'s own
            --    obligations (piles `≠ pileFin` transfer directly from
            --    `hmerged`; the prefix count is untouched since `pileFin`'s
            --    depth only decreases by 1 and stays `> 0` unless it was
            --    already `1`, either way not newly counted in the
            --    `j ≠ pileFin` prefix).
            have hsuitU32lt4 : suitU32.toNat < 4 := by rw [hsuitU32]; exact suit.isLt
            simp only [hcdpos, hcd0, reduceIte, Vector.setE, dif_pos hsuitU32lt4,
              bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get,
              set, EStateM.set]
            set gameA : SolverPosType :=
              { game with aces := game.aces.set suitU32.toNat card.toInt8 hsuitU32lt4 } with
              hgameAdef
            have hinvBundle : MoveAcesInv g suit card found game :=
              ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩
            have hpileFinEqP32 : pileFin = (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := by
              apply Fin.ext
              show (cardPile g card).toNat = pile.toUInt32.toNat
              rw [← hpileEqCP, UInt8.toNat_toUInt32]
            have hgameDepthLit : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                ).toInt.toNat = cd1.toNat + 1 := by
              rw [← hpileFinEqP32]; exact hpdEqNat
            -- `X` real, same suit as `suit`, not free (w.r.t. `game`), and
            -- `≠ card` ⟹ `X` sits strictly above `card`: exactly
            -- `moveAces_lt_of_not_free` at `hinvBundle`, packaged for reuse.
            have hAboveCard : ∀ X : UInt8, SUIT X = suit.val.toUInt8 → 1 ≤ (VALUE X).toNat →
                ¬ isFreeCard g game X → X ≠ card → card.toNat < X.toNat :=
              fun X hSX hVX hXnf hXne => moveAces_lt_of_not_free g suit card found game
                hinvBundle X hSX hVX hXnf hXne
            set p1 : SolverPosType :=
              fluteNorm pile.toUInt32 hp10 (removeFlutePre pile.toUInt32 hp10 gameA) with hp1def
            -- Field-by-field access facts for `p1` (the composed
            -- `fluteNorm ∘ removeFlutePre` point `removeFlute_merged` needs).
            have hp1_aces : p1.aces = gameA.aces := by
              rw [hp1def]; simp only [fluteNorm, removeFlutePre]
            have hsuitValEq : suit.val = suitU32.toNat := hsuitU32.symm
            have hp1AcesSuit : p1.aces.get suit = card.toInt8 := by
              rw [hp1_aces, hgameAdef]
              show (game.aces.set suitU32.toNat card.toInt8 hsuitU32lt4)[suit.val]'suit.isLt =
                card.toInt8
              have hfin : (⟨suit.val, suit.isLt⟩ : Fin 4) = (⟨suitU32.toNat, hsuitU32lt4⟩ : Fin 4) :=
                Fin.ext hsuitValEq
              have hget : (game.aces.set suitU32.toNat card.toInt8 hsuitU32lt4)[suit.val]'suit.isLt =
                  (game.aces.set suitU32.toNat card.toInt8 hsuitU32lt4).get
                    (⟨suit.val, suit.isLt⟩ : Fin 4) := rfl
              rw [hget, hfin]
              exact Vector.getElem_set_self hsuitU32lt4
            have hp1AcesNe : ∀ t : Fin 4, t ≠ suit → p1.aces.get t = game.aces.get t := by
              intro t ht
              rw [hp1_aces, hgameAdef]
              show (game.aces.set suitU32.toNat card.toInt8 hsuitU32lt4)[t.val]'t.isLt =
                game.aces[t.val]'t.isLt
              apply Vector.getElem_set_ne hsuitU32lt4 t.isLt
              intro hcon
              exact ht (Fin.ext (hsuitValEq.trans hcon)).symm
            have hp1_kings : p1.kings = game.kings := by
              rw [hp1def]; simp only [fluteNorm, removeFlutePre, hgameAdef]
            have hp1_usedSpace : p1.usedSpace = game.usedSpace := by
              rw [hp1def]; simp only [fluteNorm, removeFlutePre, hgameAdef]
            have hp1_busyAces : p1.busyAces = game.busyAces := by
              rw [hp1def]; simp only [fluteNorm, removeFlutePre, hgameAdef]
            have hp1_freePiles : p1.freePiles = game.freePiles := by
              rw [hp1def]; simp only [fluteNorm, removeFlutePre, hgameAdef]
            have hp1_pileDepth_ne : ∀ i : Fin 10, i.val ≠ pile.toUInt32.toNat →
                p1.pileDepth.get i = game.pileDepth.get i := by
              intro i hi
              rw [hp1def]
              show (removeFlutePre pile.toUInt32 hp10 gameA).pileDepth[i.val]'i.isLt =
                game.pileDepth[i.val]'i.isLt
              simp only [removeFlutePre]
              show (gameA.pileDepth.set pile.toUInt32.toNat _ hp10)[i.val]'i.isLt =
                game.pileDepth[i.val]'i.isLt
              rw [Vector.getElem_set_ne hp10 i.isLt (Ne.symm hi)]
            have hp1_pileDepth_self : p1.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) =
                game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) - 1 := by
              rw [hp1def]
              show (removeFlutePre pile.toUInt32 hp10 gameA).pileDepth.get
                (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) =
                game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) - 1
              simp only [removeFlutePre]
              show (gameA.pileDepth.set pile.toUInt32.toNat
                  ((gameA.pileDepth[pile.toUInt32.toNat]'hp10) - 1) hp10)[pile.toUInt32.toNat]'hp10 =
                game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) - 1
              rw [Vector.getElem_set_self]
              rfl
            have hp1_pileFlute_ne : ∀ i : Fin 10, i.val ≠ pile.toUInt32.toNat →
                p1.pileFlute.get i = game.pileFlute.get i := by
              intro i hi
              rw [hp1def]
              show (fluteNorm pile.toUInt32 hp10 (removeFlutePre pile.toUInt32 hp10 gameA)
                ).pileFlute[i.val]'i.isLt = game.pileFlute[i.val]'i.isLt
              simp only [fluteNorm]
              show ((removeFlutePre pile.toUInt32 hp10 gameA).pileFlute.set
                pile.toUInt32.toNat 1 hp10)[i.val]'i.isLt = game.pileFlute[i.val]'i.isLt
              rw [Vector.getElem_set_ne hp10 i.isLt (Ne.symm hi)]
              show (removeFlutePre pile.toUInt32 hp10 gameA).pileFlute[i.val]'i.isLt =
                game.pileFlute[i.val]'i.isLt
              simp only [removeFlutePre]
              show gameA.pileFlute[i.val]'i.isLt = game.pileFlute[i.val]'i.isLt
              rw [hgameAdef]
            have hp1_pileFlute_self : p1.pileFlute.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = 1 := by
              rw [hp1def]
              show (fluteNorm pile.toUInt32 hp10 (removeFlutePre pile.toUInt32 hp10 gameA)
                ).pileFlute.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = 1
              simp only [fluteNorm]
              show ((removeFlutePre pile.toUInt32 hp10 gameA).pileFlute.set
                pile.toUInt32.toNat 1 hp10)[pile.toUInt32.toNat]'hp10 = 1
              rw [Vector.getElem_set_self]
            -- `p1`'s `pileDepth` is pointwise `≤ game`'s (only `pileFin` drops,
            -- by exactly `1`), so any freeness fact already established for
            -- `game` transfers to `p1` via `isFreeCard_mono`.
            have hp1_depth_mono : ∀ k : Fin 10,
                (p1.pileDepth.get k).toInt.toNat ≤ (game.pileDepth.get k).toInt.toNat := by
              intro k
              by_cases hkP : k.val = pile.toUInt32.toNat
              · have hkeq : k = (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := Fin.ext hkP
                rw [hkeq, hp1_pileDepth_self]
                have hnn := hmerged.pileDepth_nonneg (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                have hpos : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat
                    > 0 := by
                  have : (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = pileFin := hpileFinEqP32.symm
                  rw [this]; omega
                have h1 : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                    (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt - 1 := by
                  rw [Int8.toInt_sub_of_le _ _ (by decide)
                    (by rw [Int8.le_iff_toInt_le, Int8.toInt_one]; omega),
                    Int8.toInt_one]
                omega
              · rw [hp1_pileDepth_ne k hkP]
            -- Shared subtraction fact: `pileFin`'s depth decrement by exactly `1`,
            -- wrap-free (since its depth is `> 0`, established by `hdepthPos`).
            have hDepthSubEq : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                ).toInt = (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt - 1 := by
              rw [Int8.toInt_sub_of_le _ _ (by decide)
                (by rw [Int8.le_iff_toInt_le, Int8.toInt_one]
                    have : (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = pileFin := hpileFinEqP32.symm
                    rw [this]; omega),
                Int8.toInt_one]
            have hp1PileBase : ∀ i : Fin 10, PileBase g p1 i := by
              intro i
              by_cases hiP : i.val = pile.toUInt32.toNat
              · -- `i = pileFin`: own pile, decremented depth + reset flute.
                have hieq : i = (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := Fin.ext hiP
                rw [hieq]
                have hbOld := hmerged.pileBase (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                have hboldDepthPos :
                    (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat > 0 := by
                  have h := hpileFinEqP32.symm
                  rw [h]; exact hdepthPos
                have hbound5 :
                    (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat ≤ 5 :=
                  hbOld.pileDepth_bound
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                · -- pileDepth_bound
                  rw [hp1_pileDepth_self, hDepthSubEq]; omega
                · -- pileDepth_nonneg
                  rw [hp1_pileDepth_self]
                  rw [Int8.le_iff_toInt_le, hDepthSubEq, show ((0:Int8).toInt = 0) from rfl]
                  omega
                · -- flute_pos
                  rw [hp1_pileFlute_self]; decide
                · -- flute_empty
                  intro _; rw [hp1_pileFlute_self]
                · -- flute_cards_free: vacuous, `pileFlute = 1`.
                  intro j _ hj0 hjlt
                  rw [hp1_pileFlute_self] at hjlt
                  have h1 : (1 : UInt8).toNat = 1 := by decide
                  omega
                · -- flute_not_aces: the new boundary (if any) sits `> card`.
                  intro hnewDepthPos boundary hs
                  have hgameDepthNonneg :
                      (0 : Int) ≤ (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt := by
                    have h4 := hmerged.pileDepth_nonneg (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                    rw [Int8.le_iff_toInt_le] at h4
                    simpa using h4
                  have hp1DepthEq : (p1.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat = cd1.toNat := by
                    have h1 := hp1_pileDepth_self
                    have h2 := hDepthSubEq
                    have h3 := hgameDepthLit
                    rw [h1]
                    omega
                  have hidxlt5 : cd1.toNat - 1 < 5 := by omega
                  have hidxeqBoundary : (⟨(p1.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat - 1, by
                      have := hbOld.pileDepth_bound; omega⟩ : Fin 5) = ⟨cd1.toNat - 1, hidxlt5⟩ := by
                    apply Fin.ext
                    show (p1.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat - 1 = cd1.toNat - 1
                    rw [hp1DepthEq]
                  have hboundaryEqIdx : boundary =
                      (g.pos2card.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).get
                        ⟨cd1.toNat - 1, hidxlt5⟩ := by
                    rw [← hidxeqBoundary]
                  have hboundaryEq2 : boundary = (g.pos2card.get pileFin).get ⟨cd1.toNat - 1, hidxlt5⟩ := by
                    rw [hboundaryEqIdx, hpileFinEqP32]
                  have hNBreal : IsRealCard boundary := by
                    rw [hboundaryEq2]; exact hwf.pos2card_real pileFin _
                  have hNBnotfree : ¬ isFreeCard g game boundary := by
                    rw [hboundaryEq2]
                    have hidx4lt : (cd1.toNat - 1 : Nat) < (game.pileDepth.get pileFin).toInt.toNat := by
                      have h9 := hpdEqNat
                      omega
                    exact depth_card_not_free hwf hmerged.toSolverInvBase pileFin
                      ⟨cd1.toNat - 1, hidxlt5⟩ hidx4lt
                  have hcardIdxEq : (⟨cd1.toNat, hcd1lt5⟩ : Fin 5) =
                      ⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by
                        have := hmerged.pileDepth_bound pileFin; omega⟩ := by
                    apply Fin.ext
                    show cd1.toNat = (game.pileDepth.get pileFin).toInt.toNat - 1
                    omega
                  have hcardAtIdx : card = (g.pos2card.get pileFin).get ⟨cd1.toNat, hcd1lt5⟩ := by
                    rw [hcardIdxEq]; exact hboundaryEq.symm
                  have hNBnecard : boundary ≠ card := by
                    rw [hboundaryEq2, hcardAtIdx]
                    intro hcon
                    have hinj := hwf.pos2card_inj pileFin pileFin ⟨cd1.toNat - 1, hidxlt5⟩
                      ⟨cd1.toNat, hcd1lt5⟩ hcon
                    have hval := congrArg Fin.val hinj.2
                    simp only at hval
                    omega
                  by_cases hSNB : SUIT boundary = suit.val.toUInt8
                  · have hlt := hAboveCard boundary hSNB hNBreal.2.1 hNBnotfree hNBnecard
                    have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
                      apply Fin.ext
                      show (SUIT boundary).toNat = suit.val
                      rw [hSNB, finVal_toUInt8_toNat]
                    rw [hEqFin, hp1AcesSuit,
                      show (card.toInt8).toUInt8 = card from UInt8.toUInt8_toInt8 card,
                      hp1_pileFlute_self]
                    have h1 : (1 : UInt8).toNat = 1 := by decide
                    omega
                  · have hSX : SUIT boundary = (⟨(SUIT boundary).toNat, hs⟩ : Fin 4).val.toUInt8 :=
                      (UInt8.ofNat_toNat).symm
                    have hlt := not_free_gt_ace hmerged.toSolverInvBase ⟨(SUIT boundary).toNat, hs⟩
                      boundary hSX hNBreal.2.1 hNBnotfree
                    have hNeFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) ≠ suit := by
                      intro hcon
                      apply hSNB
                      apply UInt8.toNat_inj.mp
                      rw [finVal_toUInt8_toNat]
                      exact congrArg Fin.val hcon
                    rw [hp1AcesNe _ hNeFin, hp1_pileFlute_self]
                    have h1 : (1 : UInt8).toNat = 1 := by decide
                    omega
              · -- `i ≠ pileFin`: frame (only `flute_not_aces` needs real work).
                have hdeq := hp1_pileDepth_ne i hiP
                have hfeq := hp1_pileFlute_ne i hiP
                have hbOld := hmerged.pileBase i
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                · rw [hdeq]; exact hbOld.pileDepth_bound
                · rw [hdeq]; exact hbOld.pileDepth_nonneg
                · rw [hfeq]; exact hbOld.flute_pos
                · intro h; rw [hfeq]; exact hbOld.flute_empty (hdeq ▸ h)
                · intro j hdj hj0 hjlt
                  rw [hdeq] at hdj
                  rw [hfeq] at hjlt
                  apply isFreeCard_mono hp1_depth_mono
                  have hfc := hbOld.flute_cards_free j hdj hj0 hjlt
                  have hboundaryEqNe : (g.pos2card.get i).get
                      ⟨(p1.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ =
                      (g.pos2card.get i).get
                      ⟨(game.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                    have hfin : (⟨(p1.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ : Fin 5) =
                        ⟨(game.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                      apply Fin.ext
                      show (p1.pileDepth.get i).toInt.toNat - 1 =
                        (game.pileDepth.get i).toInt.toNat - 1
                      rw [hdeq]
                    rw [hfin]
                  rw [hboundaryEqNe]
                  exact hfc
                · -- flute_not_aces: frame if `SUIT boundary ≠ suit`, else the
                  -- cross-pile `hAboveCard`/`flute_le_of_lt_and_notfree` argument.
                  intro hdj boundary hs
                  have hboundaryEqNe2 : boundary = (g.pos2card.get i).get
                      ⟨(game.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                    show (g.pos2card.get i).get ⟨(p1.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ =
                      (g.pos2card.get i).get ⟨(game.pileDepth.get i).toInt.toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩
                    congr 1
                    apply Fin.ext
                    show (p1.pileDepth.get i).toInt.toNat - 1 =
                      (game.pileDepth.get i).toInt.toNat - 1
                    rw [hdeq]
                  have hgameHdj : (game.pileDepth.get i).toInt.toNat > 0 := by rw [← hdeq]; exact hdj
                  have hs' : (SUIT ((g.pos2card.get i).get ⟨(game.pileDepth.get i).toInt.toNat - 1,
                      by have := hbOld.pileDepth_bound; omega⟩ : UInt8)).toNat < 4 := by
                    rw [← hboundaryEqNe2]; exact hs
                  have hbig' := hbOld.flute_not_aces hgameHdj hs'
                  by_cases hSB : SUIT boundary = suit.val.toUInt8
                  · -- Same suit as the new ace: `card < boundary` via
                    -- `hAboveCard`, extended across the whole flute footprint.
                    have hine : i ≠ pileFin := by
                      intro h
                      apply hiP
                      rw [h]
                      exact congrArg Fin.val hpileFinEqP32
                    have hboundaryNotFree : ¬ isFreeCard g game boundary := by
                      rw [hboundaryEqNe2]
                      exact boundary_not_free hwf hmerged.toSolverInvBase i
                        (by have := hbOld.pileDepth_bound; omega)
                    have hboundaryReal : IsRealCard boundary := by
                      rw [hboundaryEqNe2]; exact hwf.pos2card_real i _
                    have hboundaryNeCard : boundary ≠ card := by
                      intro hcon
                      rw [hboundaryEqNe2] at hcon
                      have hcon2 : (g.pos2card.get i).get ⟨(game.pileDepth.get i).toInt.toNat - 1,
                          by have := hbOld.pileDepth_bound; omega⟩ =
                        (g.pos2card.get pileFin).get ⟨(game.pileDepth.get pileFin).toInt.toNat - 1,
                          by have := hmerged.pileDepth_bound pileFin; omega⟩ :=
                        hcon.trans hboundaryEq.symm
                      have hinj := hwf.pos2card_inj i pileFin
                        ⟨(game.pileDepth.get i).toInt.toNat - 1, by
                          have := hbOld.pileDepth_bound; omega⟩
                        ⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by
                          have := hmerged.pileDepth_bound pileFin; omega⟩ hcon2
                      exact hine hinj.1
                    have hclt := hAboveCard boundary hSB hboundaryReal.2.1 hboundaryNotFree
                      hboundaryNeCard
                    have hle := flute_le_of_lt_and_notfree hwf hmerged.toSolverInvBase i
                      (by have := hbOld.pileDepth_bound; omega) card hcardNotFree
                      (by rw [← hboundaryEqNe2]; exact hclt)
                    have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
                      apply Fin.ext
                      show (SUIT boundary).toNat = suit.val
                      rw [hSB, finVal_toUInt8_toNat]
                    rw [hEqFin, hp1AcesSuit,
                      show (card.toInt8).toUInt8 = card from UInt8.toUInt8_toInt8 card, hfeq]
                    rw [hboundaryEqNe2]
                    exact hle
                  · -- Different suit: `p1.aces` at that index is untouched.
                    have hNeFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) ≠ suit := by
                      intro hcon
                      apply hSB
                      apply UInt8.toNat_inj.mp
                      rw [finVal_toUInt8_toNat]
                      exact congrArg Fin.val hcon
                    rw [hp1AcesNe _ hNeFin, hfeq]
                    clear_value boundary
                    exact hboundaryEqNe2 ▸ hbig'
            -- `card` sits exactly at `(g.pos2card.get pileFin).get ⟨cd1.toNat,_⟩`
            -- (bridges `hboundaryEq`'s index down to `cd1.toNat` via `hidxeq`).
            have hcardAtIdx : (g.pos2card.get pileFin).get ⟨cd1.toNat, hcd1lt5⟩ = card := by
              have hfin : (⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by
                  have := hmerged.pileDepth_bound pileFin; omega⟩ : Fin 5) =
                  ⟨cd1.toNat, hcd1lt5⟩ := Fin.ext hidxeq
              rw [← hfin]; exact hboundaryEq
            -- **`X ≠ card` freeness transfer.**  `p1`'s pileDepth is pointwise
            -- `≤ game`'s with the ONLY difference being that `card` itself
            -- newly becomes free (`pileFin`'s depth drops by exactly `1`, at
            -- exactly `card`'s own slot) — so for any REAL `X ≠ card`,
            -- `¬isFreeCard g game X → ¬isFreeCard g p1 X`.
            have hfreeTransfer : ∀ X : UInt8, IsRealCard X → X ≠ card →
                ¬ isFreeCard g game X → ¬ isFreeCard g p1 X := by
              intro X hXreal hXne hnf hf
              apply hnf
              have hX64 : X.toNat < 64 := by
                have hsn := SUIT_toNat X; have h1 := hXreal.1; omega
              have hXp64 : (cardPile g X).toNat < 10 := hwf.pile_lt X hXreal
              by_cases hXP : (cardPile g X).toNat = pile.toUInt32.toNat
              · -- `X`'s home pile is `pileFin`.
                have hge := isFree_to_cardDepth_ge g p1 hwf X hX64 hXp64 hf
                have hp1EqLit : p1.pileDepth[(cardPile g X).toNat]'hXp64 =
                    p1.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := by
                  congr 1
                rw [hp1EqLit, hp1_pileDepth_self] at hge
                have hcd1le : (cardDepth g X).toNat ≥ cd1.toNat := by
                  have h2 := hDepthSubEq
                  have h3 := hgameDepthLit
                  omega
                by_cases heqd : (cardDepth g X).toNat = cd1.toNat
                · exfalso
                  apply hXne
                  have hd5 : (cardDepth g X).toNat < 5 := by omega
                  have hr := hwf.round_trip X hXreal hd5
                  have hfin1 : (⟨(cardPile g X).toNat, hXp64⟩ : Fin 10) = pileFin := by
                    apply Fin.ext
                    show (cardPile g X).toNat = (cardPile g card).toNat
                    rw [hXP, ← hpileEqCP, UInt8.toNat_toUInt32]
                  have hfin2 : (⟨(cardDepth g X).toNat, hd5⟩ : Fin 5) = ⟨cd1.toNat, hcd1lt5⟩ :=
                    Fin.ext heqd
                  rw [hfin1, hfin2] at hr
                  rw [← hr]
                  exact hcardAtIdx
                · apply isFree_of_cardDepth_ge g game hwf X hX64 hXp64
                  have hgePD : (game.pileDepth[(cardPile g X).toNat]'hXp64).toInt.toNat =
                      (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat := by
                    have heq2 : game.pileDepth[(cardPile g X).toNat]'hXp64 =
                        game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := by congr 1
                    rw [heq2]
                  rw [hgePD]
                  have h3 := hgameDepthLit
                  omega
              · have hne : (⟨(cardPile g X).toNat, hXp64⟩ : Fin 10).val ≠ pile.toUInt32.toNat :=
                  hXP
                have heq := hp1_pileDepth_ne ⟨(cardPile g X).toNat, hXp64⟩ hne
                have hge := isFree_to_cardDepth_ge g p1 hwf X hX64 hXp64 hf
                apply isFree_of_cardDepth_ge g game hwf X hX64 hXp64
                have hgePD : (game.pileDepth[(cardPile g X).toNat]'hXp64).toInt.toNat =
                    (p1.pileDepth[(cardPile g X).toNat]'hXp64).toInt.toNat := by
                  have heq2 : p1.pileDepth[(cardPile g X).toNat]'hXp64 =
                      game.pileDepth[(cardPile g X).toNat]'hXp64 := by
                    show p1.pileDepth.get (⟨(cardPile g X).toNat, hXp64⟩ : Fin 10) =
                      game.pileDepth.get (⟨(cardPile g X).toNat, hXp64⟩ : Fin 10)
                    exact heq
                  rw [heq2]
                rw [hgePD]
                exact hge
            -- A card of a suit `t ≠ suit` is automatically `≠ card`.
            have hSuitNeCard : ∀ (X : UInt8) (t : Fin 4), SUIT X = t.val.toUInt8 → t ≠ suit →
                X ≠ card := by
              intro X t hSX htne hcon
              apply htne
              apply Fin.ext
              have h1 : t.val.toUInt8 = suit.val.toUInt8 := by rw [← hSX, hcon, hsuitcard]
              have h2 := congrArg UInt8.toNat h1
              rwa [finVal_toUInt8_toNat, finVal_toUInt8_toNat] at h2
            have hp1SuitClean : ∀ s : Fin 4,
                SuitClean g p1 s (fun i => (hp1PileBase i).pileDepth_bound) := by
              intro s
              by_cases hsS : s = suit
              · -- `s = suit`: the real content.
                subst hsS
                have hbOldS := hmerged.suitClean s
                have hacesEq := hp1AcesSuit
                set K := game.kings.get s with hKdef
                have hKSuit : SUIT K.toUInt8 = s.val.toUInt8 := hbOldS.aces_kings_valid.2.2.1
                have hKVal13 : (VALUE K.toUInt8).toNat ≤ 13 := hbOldS.aces_kings_valid.2.2.2.1
                have hKnonneg : (0 : Int8) ≤ K := int8_nonneg_of_suit hKSuit
                -- `card` itself becomes free in `p1`: its home pile's depth
                -- has been decremented to sit exactly at `card`'s `cardDepth`.
                have hcardFreeP1 : isFreeCard g p1 card := by
                  apply isFree_of_cardDepth_ge g p1 hwf card hc64' hp64
                  have heq : (p1.pileDepth[(cardPile g card).toNat]'hp64) =
                      p1.pileDepth.get pileFin := by congr 1
                  rw [heq, hpileFinEqP32, hp1_pileDepth_self]
                  have hpdEqNat' : (game.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat = cd1.toNat + 1 := by
                    rw [← hpileFinEqP32]; exact hpdEqNat
                  rw [hDepthSubEq]
                  omega
                -- `card ≤ kings[s]` (byte-wise): otherwise `card` would be
                -- free in `game` by `king_frontier`'s `∀c` clause, contradicting
                -- `hcardNotFree`.
                have hcardLeK : card.toNat ≤ K.toUInt8.toNat := by
                  by_contra hgt
                  push_neg at hgt
                  have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
                  have hsk := SUIT_toNat K.toUInt8; have hvk := VALUE_toNat K.toUInt8
                  have hVgt : (VALUE K.toUInt8).toNat < (VALUE card).toNat := by
                    rw [hsuitcard] at hsc; rw [hKSuit] at hsk; omega
                  exact hcardNotFree (hbOldS.king_frontier.2 card hsuitcard hVgt hg)
                refine ⟨?_, ?_, ?_, ?_⟩
                · -- aces_kings_valid
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · rw [hacesEq, UInt8.toUInt8_toInt8]; exact hsuitcard
                  · rw [hacesEq, UInt8.toUInt8_toInt8]; exact hg
                  · rw [hp1_kings]; exact hKSuit
                  · rw [hp1_kings]; exact hKVal13
                  · rw [hacesEq, hp1_kings]
                    apply Int8.le_iff_toInt_le.mpr
                    rw [uint8_toInt8_toInt_of_lt128 (by omega : card.toNat < 128),
                      int8_toInt_eq_toUInt8_toNat_of_nonneg hKnonneg]
                    exact_mod_cast hcardLeK
                · -- foundation_cards_free
                  intro c hSc hVc1 hVc2
                  rw [hacesEq, UInt8.toUInt8_toInt8] at hVc2
                  by_cases hcOld : (VALUE c).toNat ≤ (VALUE (game.aces.get s).toUInt8).toNat
                  · exact isFreeCard_mono hp1_depth_mono
                      (hbOldS.foundation_cards_free c hSc hVc1 hcOld)
                  · by_cases hcCard : c = card
                    · rw [hcCard]; exact hcardFreeP1
                    · push_neg at hcOld
                      have hSuitA : SUIT (game.aces.get s).toUInt8 = s.val.toUInt8 :=
                        hbOldS.aces_kings_valid.1
                      have hsc := SUIT_toNat c; have hvc := VALUE_toNat c
                      have hsa := SUIT_toNat (game.aces.get s).toUInt8
                      have hva := VALUE_toNat (game.aces.get s).toUInt8
                      have hSameSuit :
                          (SUIT c).toNat = (SUIT (game.aces.get s).toUInt8).toNat := by
                        rw [hSc, hSuitA]
                      set l := c.toNat - (game.aces.get s).toUInt8.toNat with hldef
                      have hl1 : 1 ≤ l := by omega
                      have hlfound : (l : Int) ≤ found.toInt := by
                        have hci : (card.toNat : Int) =
                            (game.aces.get s).toUInt8.toNat + 1 + found.toInt := hcardeq
                        have hcne : c.toNat ≠ card.toNat := fun h => hcCard (UInt8.toNat_inj.mp h)
                        have hscard := SUIT_toNat card; have hvcard := VALUE_toNat card
                        have hSuitCardEq : (SUIT card).toNat = (SUIT (game.aces.get s).toUInt8).toNat := by
                          rw [hsuitcard, hSuitA]
                        omega
                      have hAl256 : (game.aces.get s).toUInt8.toNat + l < 256 := by
                        have := c.toNat_lt; omega
                      have hceq : c = (game.aces.get s).toUInt8 + UInt8.ofNat l :=
                        uint8_eq_add_ofNat_of_toNat_eq hAl256 (by omega)
                      rw [hceq]
                      exact isFreeCard_mono hp1_depth_mono (hfoundfree l hl1 hlfound)
                · -- foundation_maximal_weak: the busy bit alone suffices,
                  -- carried unchanged from `game` (`MoveAcesInv` keeps it set
                  -- throughout the walk).
                  exact Or.inr (Or.inr (by rw [hp1_busyAces]; exact hbit))
                · -- king_frontier
                  rw [hp1_kings]
                  refine ⟨?_, ?_⟩
                  · rcases Nat.lt_or_eq_of_le hcardLeK with hlt | heqv
                    · -- `card < kings[s]`: keep disjunct (B).
                      refine Or.inr ⟨?_, ?_⟩
                      · rw [hacesEq]
                        apply Int8.lt_iff_toInt_lt.mpr
                        rw [uint8_toInt8_toInt_of_lt128 (by omega : card.toNat < 128),
                          int8_toInt_eq_toUInt8_toNat_of_nonneg hKnonneg]
                        exact_mod_cast hlt
                      · have hKreal : IsRealCard K.toUInt8 := by
                          refine ⟨?_, ?_, hKVal13⟩
                          · rw [hKSuit]
                            have := s.isLt; have := finVal_toUInt8_toNat s; omega
                          · have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
                            have hsk := SUIT_toNat K.toUInt8; have hvk := VALUE_toNat K.toUInt8
                            rw [hsuitcard] at hsc; rw [hKSuit] at hsk; omega
                        have hKneCard : K.toUInt8 ≠ card := fun hEq => by
                          rw [hEq] at hlt; omega
                        rcases hbOldS.king_frontier.1 with ⟨hKeqA, _⟩ | ⟨_, hKnf⟩
                        · -- Case (A) `kings[s] = aces[s]` is impossible:
                          -- `card > aces[s] = kings[s]` would make
                          -- `card` free via the `∀c` clause, contradicting
                          -- `hcardNotFree`.
                          exfalso
                          have hAeqK : K.toUInt8.toNat = (game.aces.get s).toUInt8.toNat :=
                            congrArg (fun x => x.toUInt8.toNat) hKeqA
                          have hci : (card.toNat : Int) =
                              (game.aces.get s).toUInt8.toNat + 1 + found.toInt := hcardeq
                          omega
                        · exact hfreeTransfer K.toUInt8 hKreal hKneCard hKnf
                    · -- `card = kings[s]` (byte-wise): the busy bit alone
                      -- justifies disjunct (A).
                      have hEq : K.toUInt8 = card := by
                        apply UInt8.toNat_inj.mp; omega
                      refine Or.inl ⟨?_, Or.inr (by rw [hp1_busyAces]; exact hbit)⟩
                      rw [hacesEq, ← hEq, Int8.toInt8_toUInt8]
                  · intro c hSc hVc1 hVc2
                    exact isFreeCard_mono hp1_depth_mono
                      (hbOldS.king_frontier.2 c hSc hVc1 hVc2)
              · -- `s ≠ suit`: frame.
                have haces_eq : p1.aces.get s = game.aces.get s := hp1AcesNe s hsS
                have hkings_eq : p1.kings.get s = game.kings.get s := by rw [hp1_kings]
                have hbOldS := hmerged.suitClean s
                refine ⟨?_, ?_, ?_, ?_⟩
                · rw [haces_eq, hkings_eq]; exact hbOldS.aces_kings_valid
                · intro c hSc hVc1 hVc2
                  rw [haces_eq] at hVc2
                  apply isFreeCard_mono hp1_depth_mono
                  exact hbOldS.foundation_cards_free c hSc hVc1 hVc2
                · rw [haces_eq]
                  by_cases hVal13 : (VALUE (game.aces.get s).toUInt8).toNat = 13
                  · exact Or.inl hVal13
                  · rcases hbOldS.foundation_maximal_weak with h13 | hnf | hbusy
                    · exact absurd h13 hVal13
                    · refine Or.inr (Or.inl ?_)
                      have hSAs : SUIT (game.aces.get s).toUInt8 = s.val.toUInt8 :=
                        (hbOldS.aces_kings_valid).1
                      have hVAs13 : (VALUE (game.aces.get s).toUInt8).toNat ≤ 13 :=
                        (hbOldS.aces_kings_valid).2.1
                      have hVAslt15 : (VALUE (game.aces.get s).toUInt8).toNat < 15 := by omega
                      have hSAs1 : SUIT ((game.aces.get s).toUInt8 + 1) = s.val.toUInt8 := by
                        rw [SUIT_succ _ hVAslt15]; exact hSAs
                      have hVAs1 : (VALUE ((game.aces.get s).toUInt8 + 1)).toNat ≤ 13 := by
                        rw [VALUE_succ _ hVAslt15]; omega
                      have hVAs1pos : 1 ≤ (VALUE ((game.aces.get s).toUInt8 + 1)).toNat := by
                        rw [VALUE_succ _ hVAslt15]; omega
                      apply hfreeTransfer _
                        ⟨by rw [hSAs1]; have := s.isLt; have := finVal_toUInt8_toNat s; omega,
                          hVAs1pos, hVAs1⟩
                        (hSuitNeCard _ s hSAs1 hsS) hnf
                    · exact Or.inr (Or.inr (by rw [hp1_busyAces]; exact hbusy))
                · rw [haces_eq, hkings_eq]
                  obtain ⟨hdisj, hall⟩ := hbOldS.king_frontier
                  refine ⟨?_, ?_⟩
                  · rcases hdisj with ⟨heqAK, h13orBusy⟩ | ⟨hlt, hnf⟩
                    · refine Or.inl ⟨heqAK, ?_⟩
                      rcases h13orBusy with h13 | hbusy
                      · exact Or.inl h13
                      · exact Or.inr (by rw [hp1_busyAces]; exact hbusy)
                    · refine Or.inr ⟨hlt, ?_⟩
                      have hSK : SUIT (game.kings.get s).toUInt8 = s.val.toUInt8 :=
                        (hbOldS.aces_kings_valid).2.2.1
                      have hVK13 : (VALUE (game.kings.get s).toUInt8).toNat ≤ 13 :=
                        (hbOldS.aces_kings_valid).2.2.2.1
                      have hAnonneg : (0 : Int8) ≤ game.aces.get s :=
                        int8_nonneg_of_suit (hbOldS.aces_kings_valid).1
                      have hKnonneg : (0 : Int8) ≤ game.kings.get s := int8_nonneg_of_suit hSK
                      have hVKpos : 1 ≤ (VALUE (game.kings.get s).toUInt8).toNat := by
                        have hsa := SUIT_toNat (game.aces.get s).toUInt8
                        have hva := VALUE_toNat (game.aces.get s).toUInt8
                        have hsk := SUIT_toNat (game.kings.get s).toUInt8
                        have hvk := VALUE_toNat (game.kings.get s).toUInt8
                        have hsuitEq : (SUIT (game.aces.get s).toUInt8).toNat =
                            (SUIT (game.kings.get s).toUInt8).toNat := by
                          rw [(hbOldS.aces_kings_valid).1, hSK]
                        have hlt' : (game.aces.get s).toUInt8.toNat <
                            (game.kings.get s).toUInt8.toNat := by
                          rw [Int8.toNat_toUInt8_of_le hAnonneg, Int8.toNat_toUInt8_of_le hKnonneg]
                          show (game.aces.get s).toInt.toNat < (game.kings.get s).toInt.toNat
                          have hltI := Int8.lt_iff_toInt_lt.mp hlt
                          have hAnn : (0:Int) ≤ (game.aces.get s).toInt := by
                            have := Int8.le_iff_toInt_le.mp hAnonneg
                            rw [Int8.toInt_zero] at this; exact this
                          have hKnn : (0:Int) ≤ (game.kings.get s).toInt := by
                            have := Int8.le_iff_toInt_le.mp hKnonneg
                            rw [Int8.toInt_zero] at this; exact this
                          omega
                        omega
                      exact hfreeTransfer _
                        ⟨by rw [hSK]; have := s.isLt; have := finVal_toUInt8_toNat s; omega,
                          hVKpos, hVK13⟩
                        (hSuitNeCard _ s hSK hsS) hnf
                  · intro c hSc hVc1 hVc2
                    apply isFreeCard_mono hp1_depth_mono
                    exact hall c hSc hVc1 hVc2
            -- `p1`'s three touched fields, reconstructed in `.set` form (for
            -- `hash_foldl_set`/`depth_sum_foldl_set`/`usedSpace_term_foldl_set`/
            -- `aces_sum_foldl_set`), plus the hash shift.
            have hp1_pileDepth_eq : p1.pileDepth =
                game.pileDepth.set pile.toUInt32.toNat
                  ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) hp10 := by
              rw [hp1def]
              show (removeFlutePre pile.toUInt32 hp10 gameA).pileDepth =
                game.pileDepth.set pile.toUInt32.toNat
                  ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) hp10
              simp only [removeFlutePre, hgameAdef]
              rfl
            have hp1_pileFlute_eq : p1.pileFlute =
                game.pileFlute.set pile.toUInt32.toNat 1 hp10 := by
              rw [hp1def]
              show (fluteNorm pile.toUInt32 hp10 (removeFlutePre pile.toUInt32 hp10 gameA)
                ).pileFlute = game.pileFlute.set pile.toUInt32.toNat 1 hp10
              simp only [fluteNorm, removeFlutePre, hgameAdef]
            have hp1_aces_eq : p1.aces = game.aces.set suit.val card.toInt8 suit.isLt := by
              apply vector_ext_get
              intro t
              by_cases htS : t = suit
              · rw [htS, hp1AcesSuit]
                show card.toInt8 = (game.aces.set suit.val card.toInt8 suit.isLt)[suit.val]'suit.isLt
                rw [Vector.getElem_set_self]
              · rw [hp1AcesNe t htS]
                show game.aces[t.val]'t.isLt =
                  (game.aces.set suit.val card.toInt8 suit.isLt)[t.val]'t.isLt
                have hne2 : suit.val ≠ t.val := fun hcon => htS (Fin.ext hcon.symm)
                exact (Vector.getElem_set_ne suit.isLt t.isLt hne2).symm
            have hp1_hash : p1.hash =
                game.hash - (pileHashes[pile.toUInt32.toNat]'hp10) := by
              rw [hp1def]
              show (removeFlutePre pile.toUInt32 hp10 gameA).hash =
                game.hash - (pileHashes[pile.toUInt32.toNat]'hp10)
              simp only [removeFlutePre, hgameAdef]
            -- Shared arithmetic facts (`old`/`new` depth, `Nat`-form).
            have hpdOldNat : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                ).toInt.toNat = cd1.toNat + 1 := by rw [← hpileFinEqP32]; exact hpdEqNat
            have hpdNewNat : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                ).toInt.toNat = cd1.toNat := by
              have h1 := hDepthSubEq
              omega
            have hash_def_p1 : p1.hash = (List.finRange 10).foldl
                (fun acc i => acc + pileHashes.get i * (p1.pileDepth.get i).toInt.toNat.toUInt32)
                0 := by
              have hadd := hash_foldl_set game.pileDepth pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1)
              rw [← hp1_pileDepth_eq] at hadd
              have hnewCast : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                  ).toInt.toNat.toUInt32 = cd1.toNat.toUInt32 := by rw [hpdNewNat]
              have holdCast : (game.pileDepth[pile.toUInt32.toNat]'hp10).toInt.toNat.toUInt32
                  = (cd1.toNat + 1).toUInt32 := by
                have : (game.pileDepth[pile.toUInt32.toNat]'hp10) =
                    game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [this, hpdOldNat]
              rw [hnewCast, holdCast] at hadd
              have huint : (cd1.toNat + 1 : Nat).toUInt32 = cd1.toNat.toUInt32 + 1 := by
                have h1 : (cd1.toNat.toUInt32).toNat = cd1.toNat := by
                  rw [UInt32.toNat_ofNat']; have := cd1.toNat_lt; omega
                have h2 : ((cd1.toNat + 1 : Nat).toUInt32).toNat = cd1.toNat + 1 := by
                  rw [UInt32.toNat_ofNat']; have := cd1.toNat_lt; omega
                have h4 : (1 : UInt32).toNat = 1 := by decide
                have h3 : (cd1.toNat.toUInt32 + 1).toNat =
                    (cd1.toNat.toUInt32.toNat + (1 : UInt32).toNat) % 2 ^ 32 :=
                  UInt32.toNat_add _ _
                apply UInt32.toNat_inj.mp
                rw [h2, h3, h1, h4]
                have := cd1.toNat_lt
                rw [Nat.mod_eq_of_lt (show cd1.toNat + 1 < 2 ^ 32 by omega)]
              rw [huint, UInt32.mul_add, UInt32.mul_one] at hadd
              -- `hadd : Fnew + (ph*cd1.toNat.toUInt32 + ph) = Fold_game + ph*cd1.toNat.toUInt32`.
              have h2 := congrArg (· - ((pileHashes[pile.toUInt32.toNat]'hp10) *
                cd1.toNat.toUInt32 + (pileHashes[pile.toUInt32.toNat]'hp10))) hadd
              rw [UInt32.add_sub_cancel, uint32_sub_add, UInt32.add_sub_cancel] at h2
              rw [hp1_hash, hmerged.hash_def]
              exact h2.symm
            -- `usedSpace_def`: the three sum shifts (depth `-1`, aces
            -- `+(1+found)`, flute `+found`) cancel exactly, matching
            -- `p1.usedSpace = game.usedSpace`.
            have hpileFluteVal : (game.pileFlute.get pileFin).toNat =
                found.toInt.toNat + 1 := hpileFluteEq
            have usedSpace_def_p1 : p1.usedSpace.toInt = (52 : Int)
                - (p1.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
                - (p1.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
                - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                    p1.pileDepth.toList p1.pileFlute.toList |>.foldl (· + ·) 0 : Nat) := by
              have hds := depth_sum_foldl_set game.pileDepth pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1)
              rw [← hp1_pileDepth_eq] at hds
              have has_ := aces_sum_foldl_set game.aces suit.val suit.isLt card.toInt8
              rw [← hp1_aces_eq] at has_
              have hft := usedSpace_term_foldl_set game.pileDepth game.pileFlute
                pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) 1
              rw [← hp1_pileDepth_eq, ← hp1_pileFlute_eq] at hft
              have holdD : (game.pileDepth[pile.toUInt32.toNat]'hp10) ≠ (0 : Int8) := by
                intro hz
                have : (game.pileDepth[pile.toUInt32.toNat]'hp10).toInt.toNat = 0 := by
                  rw [hz]; decide
                have hlit : (game.pileDepth[pile.toUInt32.toNat]'hp10) =
                    game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [hlit, hpdOldNat] at this
                omega
              have hnewD : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                  ) ≠ (0 : Int8) ∨
                  ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) = 0 :=
                (em (((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) = 0)).symm
              have hgameOldFluteVal : (game.pileFlute[pile.toUInt32.toNat]'hp10).toNat =
                  found.toInt.toNat + 1 := by
                have hlit : (game.pileFlute[pile.toUInt32.toNat]'hp10) =
                    game.pileFlute.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [hlit, ← hpileFinEqP32]; exact hpileFluteVal
              have hOldTerm : (if (game.pileDepth[pile.toUInt32.toNat]'hp10) ≠ (0 : Int8)
                  then (game.pileFlute[pile.toUInt32.toNat]'hp10).toNat - 1 else 0) =
                  found.toInt.toNat := by
                rw [if_pos holdD, hgameOldFluteVal]; omega
              have hNewTerm : (if ((game.pileDepth.get
                  (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) ≠ (0 : Int8)
                  then ((1 : UInt8)).toNat - 1 else 0) = 0 := by
                rcases hnewD with h | h
                · rw [if_pos h]; decide
                · rw [if_neg (fun hne => hne h)]
              rw [hOldTerm] at hft
              rw [hNewTerm] at hft
              have hmergedU := hmerged.usedSpace_def
              rw [hp1_usedSpace, hmergedU]
              have hOldLit : (game.pileDepth[pile.toUInt32.toNat]'hp10) =
                  game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
              rw [hOldLit, hpdOldNat, hpdNewNat] at hds
              have hAcesIdxEq : (game.aces[suit.val]'suit.isLt) = game.aces.get suit := rfl
              rw [hAcesIdxEq] at has_
              have hcardVAL : (VALUE card.toInt8.toUInt8).toNat = (VALUE card).toNat := by
                rw [UInt8.toUInt8_toInt8]
              rw [hcardVAL] at has_
              have hVAeq : (VALUE (game.aces.get suit).toUInt8).toNat + 1 + found.toInt.toNat =
                  (VALUE card).toNat := by
                have hsa := SUIT_toNat (game.aces.get suit).toUInt8
                have hva := VALUE_toNat (game.aces.get suit).toUInt8
                have hsc := SUIT_toNat card
                have hvc := VALUE_toNat card
                have hSuitEq : (SUIT (game.aces.get suit).toUInt8).toNat = (SUIT card).toNat := by
                  rw [hsuitcard, (hmerged.aces_kings_valid suit).1]
                have hci : (card.toNat : Int) =
                    (game.aces.get suit).toUInt8.toNat + 1 + found.toInt := hcardeq
                omega
              omega
            have busyAces_lt16_p1 : p1.busyAces < 16 := by
              rw [hp1_busyAces]; exact hmerged.busyAces_lt16
            have hnf : SolverInvBase g p1 :=
              ⟨hp1PileBase, hp1SuitClean, hash_def_p1, usedSpace_def_p1, busyAces_lt16_p1⟩
            -- `PileMerged` for every OTHER pile `j ≠ pileFin`: `merge_complete`
            -- is a pure frame; `flute_maximal`/`busyAces_complete` need the
            -- same cross-suit split as `hp1PileBase`'s `flute_not_aces`.
            have hframe : ∀ j : Fin 10, j.val ≠ pile.toUInt32.toNat →
                PileMerged g p1 j (hnf.pileDepth_bound j) := by
              intro j hjP
              have hdeq := hp1_pileDepth_ne j hjP
              have hfeq := hp1_pileFlute_ne j hjP
              have hbOld := hmerged.pileMerged j
              have hbOldBase := hmerged.pileBase j
              have hjneFin : j ≠ pileFin := by
                intro h; apply hjP; rw [h]; exact congrArg Fin.val hpileFinEqP32
              refine ⟨?_, ?_, ?_⟩
              · -- merge_complete
                rcases hbOld.merge_complete with hle1 | hne
                · left; rw [hdeq]; exact hle1
                · right
                  have hb1 : (⟨(p1.pileDepth.get j).toInt.toNat - 2, by
                      have := hnf.pileDepth_bound j; omega⟩ : Fin 5) =
                      ⟨(game.pileDepth.get j).toInt.toNat - 2, by
                      have := hbOldBase.pileDepth_bound; omega⟩ := by
                    apply Fin.ext
                    show (p1.pileDepth.get j).toInt.toNat - 2 =
                      (game.pileDepth.get j).toInt.toNat - 2
                    rw [hdeq]
                  have hb2 : (⟨(p1.pileDepth.get j).toInt.toNat - 1, by
                      have := hnf.pileDepth_bound j; omega⟩ : Fin 5) =
                      ⟨(game.pileDepth.get j).toInt.toNat - 1, by
                      have := hbOldBase.pileDepth_bound; omega⟩ := by
                    apply Fin.ext
                    show (p1.pileDepth.get j).toInt.toNat - 1 =
                      (game.pileDepth.get j).toInt.toNat - 1
                    rw [hdeq]
                  rw [hb1, hb2]
                  exact hne
              · -- flute_maximal
                by_cases hd0 : p1.pileDepth.get j = 0
                · left; exact hd0
                · have hgd0 : game.pileDepth.get j ≠ 0 := by rw [hdeq] at hd0; exact hd0
                  have hgdj : (game.pileDepth.get j).toInt.toNat > 0 := by
                    have h1 := hbOldBase.pileDepth_nonneg
                    rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at h1
                    have h2 : (game.pileDepth.get j).toInt ≠ 0 := by
                      intro hz; apply hgd0; apply Int8.toInt_inj.mp
                      rw [hz, show ((0 : Int8).toInt = 0) from rfl]
                    omega
                  right
                  have hidxEqB : (p1.pileDepth.get j).toInt.toNat - 1 =
                      (game.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
                  have hboundaryB : (g.pos2card.get j).get ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                      by have := hnf.pileDepth_bound j; omega⟩ =
                      (g.pos2card.get j).get ⟨(game.pileDepth.get j).toInt.toNat - 1,
                      by have := hbOldBase.pileDepth_bound; omega⟩ := by
                    congr 1; exact Fin.ext hidxEqB
                  show (∃ hs : (SUIT ((g.pos2card.get j).get
                      ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                      by have := hnf.pileDepth_bound j; omega⟩)).toNat < 4,
                      p1.aces.get ⟨(SUIT ((g.pos2card.get j).get
                        ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                        by have := hnf.pileDepth_bound j; omega⟩)).toNat, hs⟩ =
                      (((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                        by have := hnf.pileDepth_bound j; omega⟩) - p1.pileFlute.get j).toInt8) ∨
                    ¬ isFreeCard g p1 (((g.pos2card.get j).get
                      ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                      by have := hnf.pileDepth_bound j; omega⟩) - p1.pileFlute.get j)
                  rw [hboundaryB, hfeq]
                  set boundary := (g.pos2card.get j).get ⟨(game.pileDepth.get j).toInt.toNat - 1,
                    by have := hbOldBase.pileDepth_bound; omega⟩ with hboundaryDef
                  set prevCard := boundary - game.pileFlute.get j with hprevCardDef
                  have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
                  have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
                  have hflv : (game.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
                    hmerged.flute_le_value hwf j hgdj
                  have hVsn_bd := VALUE_toNat boundary
                  have hSsn_bd := SUIT_toNat boundary
                  have hfleB : game.pileFlute.get j ≤ boundary := by
                    rw [UInt8.le_iff_toNat_le]
                    have := Nat.mod_le boundary.toNat 16
                    omega
                  have hprevNat : prevCard.toNat = boundary.toNat - (game.pileFlute.get j).toNat :=
                    UInt8.toNat_sub_of_le _ _ hfleB
                  have hSUITeq : SUIT prevCard = SUIT boundary := by
                    apply UInt8.toNat_inj.mp
                    rw [SUIT_toNat, SUIT_toNat, hprevNat]; omega
                  have hVprevNat := VALUE_toNat prevCard
                  have hVALeq : (VALUE prevCard).toNat =
                      (VALUE boundary).toNat - (game.pileFlute.get j).toNat := by omega
                  by_cases hSB : SUIT boundary = suit.val.toUInt8
                  · -- Same suit as the new ace.
                    have hEqFin : (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4) = suit := by
                      apply Fin.ext; show (SUIT boundary).toNat = suit.val
                      rw [hSB, finVal_toUInt8_toNat]
                    by_cases hpc : prevCard = card
                    · left
                      refine ⟨hs4', ?_⟩
                      rw [hEqFin, hp1AcesSuit]
                      exact congrArg UInt8.toInt8 hpc.symm
                    · right
                      have hboundaryNotFree : ¬ isFreeCard g game boundary :=
                        boundary_not_free hwf hmerged.toSolverInvBase j
                          (by have := hbOldBase.pileDepth_bound; omega)
                      have hboundaryNeCard : boundary ≠ card := by
                        intro hcon
                        have hcon2 : (g.pos2card.get j).get ⟨(game.pileDepth.get j).toInt.toNat - 1,
                            by have := hbOldBase.pileDepth_bound; omega⟩ =
                          (g.pos2card.get pileFin).get ⟨(game.pileDepth.get pileFin
                            ).toInt.toNat - 1, by have := hmerged.pileDepth_bound pileFin; omega⟩ :=
                          (hboundaryDef ▸ hcon).trans hboundaryEq.symm
                        have hinj := hwf.pos2card_inj j pileFin
                          ⟨(game.pileDepth.get j).toInt.toNat - 1, by
                            have := hbOldBase.pileDepth_bound; omega⟩
                          ⟨(game.pileDepth.get pileFin).toInt.toNat - 1, by
                            have := hmerged.pileDepth_bound pileFin; omega⟩ hcon2
                        exact hjneFin hinj.1
                      have hclt := hAboveCard boundary hSB hrealBd.2.1 hboundaryNotFree
                        hboundaryNeCard
                      have hleRaw := flute_le_of_lt_and_notfree hwf hmerged.toSolverInvBase j hgdj
                        card hcardNotFree hclt
                      have hle : card.toNat + (game.pileFlute.get j).toNat ≤ boundary.toNat :=
                        hleRaw
                      have hcardLeNat : card.toNat ≤ prevCard.toNat := by rw [hprevNat]; omega
                      have hVprevNe0 : (VALUE prevCard).toNat ≠ 0 := by
                        intro hV0
                        apply hpc
                        have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
                        have hSuitCardEq : (SUIT card).toNat = (SUIT boundary).toNat := by
                          rw [hsuitcard, hSB]
                        have hsp := SUIT_toNat prevCard; have hvp := VALUE_toNat prevCard
                        have hSPeq := congrArg UInt8.toNat hSUITeq
                        apply UInt8.toNat_inj.mp
                        omega
                      have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
                      have hVle : (VALUE prevCard).toNat ≤ 13 := by
                        have := hrealBd.2.2; rw [hVALeq]; omega
                      have hprevReal : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
                      have hOldNF : ¬ isFreeCard g game prevCard := by
                        rcases hbOld.flute_maximal.resolve_left hgd0 with ⟨hs, heqOld⟩ | hOldNF
                        · exfalso
                          have hEqFinOld : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
                            apply Fin.ext; show (SUIT boundary).toNat = suit.val
                            rw [hSB, finVal_toUInt8_toNat]
                          rw [hEqFinOld] at heqOld
                          have hAeqUInt8 : (game.aces.get suit).toUInt8 = prevCard := by
                            have h1 := congrArg Int8.toUInt8 heqOld
                            rwa [UInt8.toUInt8_toInt8] at h1
                          have hAeqNat : (game.aces.get suit).toUInt8.toNat = prevCard.toNat := by
                            rw [hAeqUInt8]
                          have hci : (card.toNat : Int) =
                              (game.aces.get suit).toUInt8.toNat + 1 + found.toInt := hcardeq
                          omega
                        · exact hOldNF
                      exact hfreeTransfer prevCard hprevReal hpc hOldNF
                  · -- Different suit: `p1.aces` at that index is untouched
                    -- (`hp1AcesNe`) — but `prevCard` may still be that OTHER
                    -- suit's own value-0 sentinel, needing the same
                    -- unconditional `flute_not_aces` treatment as the
                    -- same-suit branch (mirrors
                    -- `preCleanupPile_pileMerged_ne`'s `hV0`-true case).
                    have hNeFin : (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4) ≠ suit := by
                      intro hcon
                      apply hSB
                      apply UInt8.toNat_inj.mp
                      rw [finVal_toUInt8_toNat]
                      exact congrArg Fin.val hcon
                    by_cases hV0 : (VALUE prevCard).toNat = 0
                    · left
                      refine ⟨hs4', ?_⟩
                      rw [hp1AcesNe _ hNeFin]
                      have hak : ∀ t : Fin 4, SUIT (game.aces.get t).toUInt8 = t.val.toUInt8 :=
                        fun t => (hmerged.aces_kings_valid t).1
                      have hna : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat +
                          (game.pileFlute.get j).toNat ≤ boundary.toNat :=
                        hbOldBase.flute_not_aces hgdj hs4'
                      have haces0 : (0 : Int8) ≤ game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩ :=
                        int8_nonneg_of_suit (hak ⟨(SUIT boundary).toNat, hs4'⟩)
                      have hSuitAcesEq : SUIT ((game.aces.get
                          ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8) = SUIT boundary := by
                        rw [hak ⟨(SUIT boundary).toNat, hs4'⟩]
                        apply UInt8.toNat_inj.mp
                        rw [finVal_toUInt8_toNat]
                      have hVBnat := VALUE_toNat
                        ((game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
                      have hSBnat := SUIT_toNat
                        ((game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8)
                      have hSeq := congrArg UInt8.toNat hSuitAcesEq
                      have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
                      have hacesGeNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toUInt8.toNat ≥ prevCard.toNat := by rw [hprevNat0]; omega
                      have hacesLeNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toUInt8.toNat ≤ prevCard.toNat := by rw [hprevNat]; omega
                      have hacesEqNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toUInt8.toNat = prevCard.toNat := le_antisymm hacesLeNat hacesGeNat
                      have hprevlt128 : prevCard.toNat < 128 := by omega
                      apply Int8.toInt_inj.mp
                      rw [uint8_toInt8_toInt_of_lt128 hprevlt128]
                      have haces0' : (0 : Int) ≤ (game.aces.get
                          ⟨(SUIT boundary).toNat, hs4'⟩).toInt := by
                        rw [← show ((0 : Int8).toInt = 0) from rfl]
                        exact Int8.le_iff_toInt_le.mp haces0
                      have hcast : ((game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toInt.toNat : Int) =
                          (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt :=
                        Int.toNat_of_nonneg haces0'
                      have hacesIntEqUInt8Nat :
                          (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toInt.toNat =
                          (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toUInt8.toNat := by
                        rw [Int8.toNat_toUInt8_of_le haces0]
                        rfl
                      omega
                    · have hVpos : 1 ≤ (VALUE prevCard).toNat := by omega
                      have hVle : (VALUE prevCard).toNat ≤ 13 := by
                        have := hrealBd.2.2; rw [hVALeq]; omega
                      have hprevReal : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', hVpos, hVle⟩
                      rcases hbOld.flute_maximal.resolve_left hgd0 with ⟨hs, heqOld⟩ | hOldNF
                      · left
                        refine ⟨hs4', ?_⟩
                        rw [hp1AcesNe _ hNeFin]
                        have hEqFinOld : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) =
                            (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4) := Fin.ext rfl
                        rw [← hEqFinOld]
                        exact heqOld
                      · right
                        have hSXprev : SUIT prevCard =
                            (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 :=
                          hSUITeq.trans (UInt8.ofNat_toNat).symm
                        exact hfreeTransfer prevCard hprevReal
                          (hSuitNeCard prevCard ⟨(SUIT boundary).toNat, hs4'⟩ hSXprev hNeFin)
                          hOldNF
              · -- busyAces_complete
                intro hdj0
                have hgdj : (game.pileDepth.get j).toInt.toNat > 0 := by rw [← hdeq]; exact hdj0
                have hidxEqB : (p1.pileDepth.get j).toInt.toNat - 1 =
                    (game.pileDepth.get j).toInt.toNat - 1 := by rw [hdeq]
                have hboundaryB : (g.pos2card.get j).get ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                    by have := hnf.pileDepth_bound j; omega⟩ =
                    (g.pos2card.get j).get ⟨(game.pileDepth.get j).toInt.toNat - 1,
                    by have := hbOldBase.pileDepth_bound; omega⟩ := by
                  congr 1; exact Fin.ext hidxEqB
                show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                    by have := hnf.pileDepth_bound j; omega⟩)).toNat < 4,
                  (p1.aces.get ⟨(SUIT ((g.pos2card.get j).get
                    ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                    by have := hnf.pileDepth_bound j; omega⟩)).toNat, hs⟩).toUInt8 =
                    ((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                      by have := hnf.pileDepth_bound j; omega⟩) - p1.pileFlute.get j →
                  p1.busyAces &&& ((1 : UInt8) <<< (SUIT ((g.pos2card.get j).get
                    ⟨(p1.pileDepth.get j).toInt.toNat - 1,
                    by have := hnf.pileDepth_bound j; omega⟩))) ≠ 0
                rw [hboundaryB]
                set boundary := (g.pos2card.get j).get ⟨(game.pileDepth.get j).toInt.toNat - 1,
                  by have := hbOldBase.pileDepth_bound; omega⟩ with hboundaryDef
                intro hs heqHyp
                rw [hfeq] at heqHyp
                rw [hp1_busyAces]
                have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
                by_cases hSB : SUIT boundary = suit.val.toUInt8
                · -- Same suit: the busy bit for `suit` is set throughout the
                    -- whole walk (`hbit`), regardless of `heqHyp`'s content.
                  rw [hSB]
                  exact hbit
                · have hNeFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) ≠ suit := by
                    intro hcon
                    apply hSB
                    apply UInt8.toNat_inj.mp
                    rw [finVal_toUInt8_toNat]
                    exact congrArg Fin.val hcon
                  rw [hp1AcesNe _ hNeFin] at heqHyp
                  exact hbOld.busyAces_complete hgdj hs heqHyp
            -- `freePiles_def`: `p1.freePiles = game.freePiles`, and the
            -- `j ≠ pile`-restricted count is a frame (only reads `pileDepth`
            -- away from `pile`, where `p1` and `game` agree), matching
            -- `game.freePiles`'s own full-count formula exactly since
            -- `pile`'s own contribution is `false` on both sides
            -- (`hdepthPos` ⇒ `game.pileDepth[pile] ≠ 0`).
            have hfreePilesEq : p1.freePiles.toInt = ((List.finRange 10).countP
                (fun j => j.val != pile.toUInt32.toNat && (p1.pileDepth.get j == 0)) : Nat) := by
              rw [hp1_freePiles,
                cleanupReady_freePiles_frame_eq pile.toUInt32 game p1 hp1_pileDepth_ne]
              have hsplit := cleanupReady_freePiles_split pile.toUInt32 hp10 game
                ((List.finRange 10).countP (fun j => j.val != pile.toUInt32.toNat &&
                  (game.pileDepth.get j == 0))) rfl
              have hne0 : game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) ≠ 0 := by
                intro hz
                have hz2 : (game.pileDepth.get
                    (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat = 0 := by
                  rw [hz]; decide
                omega
              have hind : (if game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) ==
                  (0 : Int8) then (1 : Nat) else 0) = 0 := by
                rw [beq_eq_false_iff_ne.mpr hne0]; decide
              rw [hind] at hsplit
              have hmergedFP := hmerged.freePiles_def
              omega
            have hready : CleanupReady g p1 pile.toUInt32 := ⟨hnf, hframe, hfreePilesEq⟩
            obtain ⟨fk, p', hrunEq, hinvP', hacesEq', hbusyMonoP⟩ :=
              removeFlute_merged pile.toUInt32 g gameA hp10 hwf hready
            have hrunEq' : _root_.SolverRemoveFlute pile.toUInt32 (g, gameA) =
                .ok fk (g, p') := hrunEq
            rw [hrunEq']
            have hp'AcesSuit : p'.aces.get suit = card.toInt8 := by
              rw [hacesEq', ← hp1_aces]; exact hp1AcesSuit
            have hp'AcesSuitUInt8 : (p'.aces.get suit).toUInt8 = card := by
              rw [hp'AcesSuit, UInt8.toUInt8_toInt8]
            have hgameAbusy : gameA.busyAces = game.busyAces := by rw [hgameAdef]
            have hp'busybit : p'.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0 :=
              hbusyMonoP _ (by rw [hgameAbusy]; exact hbit)
            have hnewcard1eq : ((card + 1).toNat : Int) =
                (p'.aces.get suit).toUInt8.toNat + 1 + (0 : Int8).toInt := by
              rw [hp'AcesSuitUInt8, hcard1nat]
              have h0 : (0 : Int8).toInt = 0 := rfl
              rw [h0]
              push_cast
              ring
            have hnewfoundfree0 : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ (0 : Int8).toInt →
                isFreeCard g p' ((p'.aces.get suit).toUInt8 + UInt8.ofNat l) := by
              intro l hl1 hlle
              exfalso
              have h0 : (0 : Int8).toInt = 0 := rfl
              omega
            have hnewinv2 : MoveAcesInv g suit (card + 1) 0 p' :=
              ⟨hinvP', by decide, by decide, hsuitcard1, hval1_1, hval14_1,
                hnewcard1eq, hnewfoundfree0, hp'busybit⟩
            have hnewmeas : 14 - (VALUE (card + 1)).toNat < n := by
              have := VALUE_succ card hcardVal15; omega
            obtain ⟨card', fk', found', game', heq, hinv', hexit', hframe'', hdich''⟩ :=
              ih (card + 1) (forcedKings &&& fk) 0 p' hnewmeas hnewinv2
            have hp'AcesNe : ∀ t : Fin 4, t ≠ suit → p'.aces.get t = game.aces.get t := by
              intro t ht
              rw [hacesEq', ← hp1_aces]
              exact hp1AcesNe t ht
            have hframe : ∀ t : Fin 4, t ≠ suit → game'.aces.get t = game.aces.get t := by
              intro t ht
              rw [hframe'' t ht]
              exact hp'AcesNe t ht
            have hdich : card.toNat < card'.toNat := by
              rcases hdich'' with ⟨hce, _, _, _⟩ | hgt
              · have h2 := congrArg UInt8.toNat hce
                omega
              · omega
            exact ⟨card', fk', found', game', heq, hinv', hexit', hframe, Or.inr hdich⟩
        · -- BURIED (`< 0`): `.done`, unchanged accumulator; `card` not free.
          have hcd0' : cd1.toUInt32.toInt32 + 1 - cd2.toInt32 ≠ 0 := by
            intro heq; exact hcd0 (by rw [heq]; decide)
          have hle0' : (cd1.toNat : Int) + 1 - cd2.toInt ≤ 0 := by
            by_contra hcon
            push Not at hcon
            apply hcdpos
            rw [gt_iff_lt, Int32.lt_iff_toInt_lt, hcardDepthI,
              show ((0 : Int32).toInt = 0) from by decide]
            omega
          have hne0' : (cd1.toNat : Int) + 1 - cd2.toInt ≠ 0 := by
            intro heq
            apply hcd0'
            apply Int32.toInt_inj.mp
            rw [hcardDepthI, show ((0 : Int32).toInt = 0) from by decide]
            exact heq
          refine ⟨card, forcedKings, found, game, ?_,
            ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩,
            Or.inr ⟨?_, hp64, ?_⟩, fun _ _ => rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
          · simp only [hcdpos, hcd0, reduceIte, EStateM.pure, Bool.false_eq_true]
          · intro hfree
            have hge := isFree_to_cardDepth_ge g game hwf card hc64' hp64 hfree
            rw [← hcd1EqCD, ← hcd2EqPD] at hge
            omega
          · rw [← hcd1EqCD, ← hcd2EqPD]
            omega
    · -- guard false: `.done`, unchanged accumulator; `VALUE card = 14`.
      have hgProp' : ¬ (VALUE card ≤ (13 : UInt8)) := fun h => hg (hgIff.mp h)
      refine ⟨card, forcedKings, found, game, ?_,
        ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩,
        Or.inl (by omega), fun _ _ => rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      rw [hunf]
      simp only [moveAcesBody, hgProp', decide_false, bind, EStateM.bind, pure, EStateM.pure,
        Bool.false_eq_true, reduceIte]

/-- **`SolverMoveAces` — one foundation advance.**  The entry state is fully
    `SolverInvMerged` (no adjustment); a pending foundation move (`busyAces ≠ 0`)
    is advanced for one suit, returning to a merged state.  Iterating this (the
    `while busyAces ≠ 0` drain) reaches `IsCanonicalPos` — see `drain_canonical`.

    Proof plan: `moveAces_eq_explicit` exposes the foundation walk as
    `Loop.forIn … moveAcesBody`.  The walk's loop invariant (internal only) is
    the *found-adjusted* base layer
    `SolverInvBase g { game with usedSpace := game.usedSpace − found }`
    plus `PileMerged` for the untouched piles and the walk equations (the passed
    cards `aces+1 … card−1` are free; `card`/`found`/`aces` relation).  Each
    `cardDepth = 0` iteration advances `aces` and discharges `removeFlute_merged`'s
    midpoint predicate; the postlude (`usedSpace −= found`, aces write,
    kings-on-13, busyAces clear) restores the unadjusted `SolverInvMerged`. -/
theorem moveAces_merged (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) (hbusy : p.busyAces ≠ 0) :
    ∃ fk p', EStateM.run _root_.SolverMoveAces (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' ∧
      (∀ s : Fin 4, s.val ≠ ctz p.busyAces → p'.aces.get s = p.aces.get s) ∧
      (∀ s : Fin 4, s.val = ctz p.busyAces →
        (VALUE (p'.aces.get s).toUInt8).toNat > (VALUE (p.aces.get s).toUInt8).toNat ∨
        (p'.aces = p.aces ∧ p'.busyAces.toNat < p.busyAces.toNat)) := by
  -- `suit := ctz p.busyAces` must be `< 4` for the real function to even
  -- typecheck through (`aces`/`kings` have only 4 entries) — now immediate
  -- from `SolverInvBase.busyAces_lt16` (bits `4..7` are always clear) plus
  -- `hbusy` (some bit IS set, so it must be among `0..3`).
  have hlow : p.busyAces &&& 0x0F ≠ 0 := by
    rw [uint8_and_0xF_eq_self_of_lt16 p.busyAces hmerged.busyAces_lt16]
    exact hbusy
  have hsuit4 : ctz p.busyAces < 4 := ctz_lt_four_of_low_nibble p.busyAces hlow
  set suit : Fin 4 := ⟨ctz p.busyAces, hsuit4⟩ with hsuitdef
  set suitU32 : UInt32 := UInt32.ofNat (ctz p.busyAces) with hsuitU32def
  have hsuitval : suit.val = ctz p.busyAces := rfl
  have hsuitU32 : suitU32.toNat = suit.val := by
    rw [hsuitU32def, UInt32.toNat_ofNat', hsuitval]
    omega
  have hidx4 : suitU32.toNat < 4 := by rw [hsuitU32]; exact suit.isLt
  rw [moveAces_eq_explicit]
  unfold moveAcesExplicit
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    Vector.getE, getElem?_pos, hidx4, ← hsuitU32def, pure, EStateM.pure]
  set A := p.aces.get suit with hAdef
  have hAeq : p.aces[suitU32.toNat]'hidx4 = A := by
    rw [hAdef]; congr 1
  rw [hAeq]
  set card0 : UInt8 := A.toInt32.toUInt32.toUInt8 + 1 with hcard0def
  set found0 : Int8 := 0 with hfound0def
  -- Establish `MoveAcesInv` at the walk's starting point.
  have hAnonneg : (0 : Int8) ≤ A := int8_nonneg_of_suit (hmerged.aces_kings_valid suit).1
  have hAsuit : SUIT A.toUInt8 = suit.val.toUInt8 := (hmerged.aces_kings_valid suit).1
  have hAval13 : (VALUE A.toUInt8).toNat ≤ 13 := (hmerged.aces_kings_valid suit).2.1
  have hroundtrip : A.toInt32.toUInt32.toUInt8 = A.toUInt8 := by
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    show (BitVec.signExtend 32 A.toBitVec).toNat % 256 = A.toBitVec.toNat
    rw [BitVec.toNat_signExtend]
    have hlt : A.toBitVec.toNat < 256 := A.toBitVec.isLt
    simp only [BitVec.toNat_setWidth]
    split <;> omega
  have hcard0eq : card0 = A.toUInt8 + 1 := by rw [hcard0def, hroundtrip]
  have hAval15 : (VALUE A.toUInt8).toNat < 15 := by omega
  have hsuitcard0 : SUIT card0 = suit.val.toUInt8 := by
    rw [hcard0eq, SUIT_succ A.toUInt8 hAval15]; exact hAsuit
  have hval1_0 : 1 ≤ (VALUE card0).toNat := by
    rw [hcard0eq, VALUE_succ A.toUInt8 hAval15]; omega
  have hval14_0 : (VALUE card0).toNat ≤ 14 := by
    rw [hcard0eq, VALUE_succ A.toUInt8 hAval15]; omega
  have hAtoNat255 : A.toUInt8.toNat < 255 := by
    have hsn := SUIT_toNat A.toUInt8; have hs4 : (SUIT A.toUInt8).toNat < 4 := by
      rw [hAsuit]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
    omega
  have hcard0nat : card0.toNat = A.toUInt8.toNat + 1 := by
    rw [hcard0eq]; exact toNat_succ A.toUInt8 hAtoNat255
  have hcard0eqInv : (card0.toNat : Int) = (p.aces.get suit).toUInt8.toNat + 1 + found0.toInt := by
    rw [hcard0nat, hfound0def, hAdef]
    push_cast
    ring
  have hfoundfree0 : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ found0.toInt →
      isFreeCard g p ((p.aces.get suit).toUInt8 + UInt8.ofNat l) := by
    intro l hl1 hlle
    exfalso
    have hf0 : found0.toInt = 0 := by rw [hfound0def]; decide
    omega
  have hbusybit : p.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0 := by
    rw [hsuitval]
    exact ctz_bit_self p.busyAces hbusy
  have hinv0 : MoveAcesInv g suit card0 found0 p :=
    ⟨hmerged, by rw [hfound0def]; decide, by rw [hfound0def]; decide, hsuitcard0, hval1_0,
      hval14_0, hcard0eqInv, hfoundfree0, hbusybit⟩
  obtain ⟨cardF, forcedKingsF, foundF, gameF, hloopeq, hloopinv, hloopexit, hloopframe,
      hloopdich⟩ :=
    moveAcesLoop_run g hwf suit suitU32 hsuitU32 15 card0 0xffff found0 p
      (by have := hval14_0; omega) hinv0
  obtain ⟨hmergedF, hf0F, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩ :=
    hloopinv
  have hloopinv' : MoveAcesInv g suit cardF foundF gameF :=
    ⟨hmergedF, hf0F, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩
  set card2 := cardF - 1 with hcard2def
  have h1lecardF : (1 : UInt8) ≤ cardF := by
    rw [UInt8.le_iff_toNat_le]
    have hv := VALUE_toNat cardF
    have h1 : (1 : UInt8).toNat = 1 := by decide
    omega
  have hcard2nat : card2.toNat = cardF.toNat - 1 := by
    rw [hcard2def]; exact UInt8.toNat_sub_of_le _ _ h1lecardF
  have hcard2p1 : card2 + 1 = cardF := by
    rw [hcard2def]; exact UInt8.sub_add_cancel cardF 1
  have hSuitCard2 : SUIT card2 = suit.val.toUInt8 := by
    apply UInt8.toNat_inj.mp
    rw [finVal_toUInt8_toNat]
    have hs1 := SUIT_toNat card2; have hv1 := VALUE_toNat card2
    have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
    have hsF : (SUIT cardF).toNat = suit.val := by rw [hsuitcardF, finVal_toUInt8_toNat]
    omega
  -- `card2 = A_F + foundF` in value terms (`A_F := gameF.aces.get suit`), so
  -- shifting `usedSpace` down by `foundF` exactly compensates the ace-jump —
  -- no pile-specific compensation is needed here (nothing pile-related
  -- changes in this postlude), unlike the `cardDepth == 0` step.
  have hcard2eqA : (card2.toNat : Int) = (gameF.aces.get suit).toUInt8.toNat + foundF.toInt := by
    have h := hcardeqF; omega
  have hAFsuit : SUIT (gameF.aces.get suit).toUInt8 = suit.val.toUInt8 :=
    (hmergedF.aces_kings_valid suit).1
  have hAFval13 : (VALUE (gameF.aces.get suit).toUInt8).toNat ≤ 13 :=
    (hmergedF.aces_kings_valid suit).2.1
  have hVcard2eq13From : (VALUE cardF).toNat = 14 → (VALUE card2).toNat = 13 := by
    intro h14
    have hs1 := SUIT_toNat card2; have hv1 := VALUE_toNat card2
    have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
    have hSeq : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
    omega
  -- **Key cross-pile fact**: for any pile `i` whose CURRENT boundary shares
  -- `suit`, `card2.toNat + pileFlute[i].toNat < boundary.toNat` (strict).
  have hAboveCard2 : ∀ i : Fin 10, (gameF.pileDepth.get i).toInt.toNat > 0 →
      SUIT ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
        by have := hmergedF.pileDepth_bound i; omega⟩) = suit.val.toUInt8 →
      card2.toNat + (gameF.pileFlute.get i).toNat <
        ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
          by have := hmergedF.pileDepth_bound i; omega⟩ : UInt8).toNat := by
    intro i hdi hSB
    set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
      by have := hmergedF.pileDepth_bound i; omega⟩ with hboundaryDef
    have hboundaryReal : IsRealCard boundary := hwf.pos2card_real i _
    have hboundaryNotFree : ¬ isFreeCard g gameF boundary :=
      boundary_not_free hwf hmergedF.toSolverInvBase i hdi
    have hvacuous : (VALUE card2).toNat = 13 → False := by
      intro hVcard2eq13
      apply hboundaryNotFree
      by_cases hle : (VALUE boundary).toNat ≤ (VALUE (gameF.aces.get suit).toUInt8).toNat
      · exact hmergedF.foundation_cards_free suit boundary hSB hboundaryReal.2.1 hle
      · push_neg at hle
        set l := (VALUE boundary).toNat - (VALUE (gameF.aces.get suit).toUInt8).toNat with hldef
        have hl1 : 1 ≤ l := by omega
        have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
        have hsa0 := SUIT_toNat (gameF.aces.get suit).toUInt8
        have hva0 := VALUE_toNat (gameF.aces.get suit).toUInt8
        have hsb := SUIT_toNat boundary; have hvb := VALUE_toNat boundary
        have hVB13 := hboundaryReal.2.2
        have hSeqAFc2 : (SUIT card2).toNat = (SUIT (gameF.aces.get suit).toUInt8).toNat := by
          rw [hSuitCard2, hAFsuit]
        have hSeq2 : (SUIT boundary).toNat = (SUIT (gameF.aces.get suit).toUInt8).toNat := by
          rw [hSB, hAFsuit]
        have hlfound : (l : Int) ≤ foundF.toInt := by
          have h := hcard2eqA
          omega
        have hSA4 : (SUIT (gameF.aces.get suit).toUInt8).toNat < 4 := by
          rw [hAFsuit]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
        have hAl256 : (gameF.aces.get suit).toUInt8.toNat + l < 256 := by
          have := boundary.toNat_lt; omega
        have hXeq : boundary = (gameF.aces.get suit).toUInt8 + UInt8.ofNat l :=
          uint8_eq_add_ofNat_of_toNat_eq hAl256 (by omega)
        rw [hXeq]
        exact hfoundfreeF l hl1 hlfound
    rcases hloopexit with h14 | ⟨hnf, hp64F, hstrict⟩
    · exact absurd (hVcard2eq13From h14) hvacuous
    · by_cases hVF14 : (VALUE cardF).toNat = 14
      · exact absurd (hVcard2eq13From hVF14) hvacuous
      · have hcardFreal : IsRealCard cardF :=
          ⟨by rw [hsuitcardF]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega,
            hval1F, by omega⟩
        have hcdF5 : (cardDepth g cardF).toNat < 5 := by
          have hbound := hmergedF.pileDepth_bound (⟨(cardPile g cardF).toNat, hp64F⟩ : Fin 10)
          have hlit : gameF.pileDepth[(cardPile g cardF).toNat]'hp64F =
              gameF.pileDepth.get (⟨(cardPile g cardF).toNat, hp64F⟩ : Fin 10) := rfl
          rw [hlit] at hstrict
          omega
        have hp64F' : (cardPile g cardF).toNat < 10 := hp64F
        have hrt := hwf.round_trip cardF hcardFreal hcdF5
        have hboundaryNeCardF : boundary ≠ cardF := by
          intro hcon
          have hcon2 : (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
              by have := hmergedF.pileDepth_bound i; omega⟩ =
            (g.pos2card.get ⟨(cardPile g cardF).toNat, hp64F'⟩).get
              ⟨(cardDepth g cardF).toNat, hcdF5⟩ := (hboundaryDef ▸ hcon).trans hrt.symm
          have hinj := hwf.pos2card_inj i ⟨(cardPile g cardF).toNat, hp64F'⟩
            ⟨(gameF.pileDepth.get i).toInt.toNat - 1, by
              have := hmergedF.pileDepth_bound i; omega⟩
            ⟨(cardDepth g cardF).toNat, hcdF5⟩ hcon2
          have hii : i = (⟨(cardPile g cardF).toNat, hp64F'⟩ : Fin 10) := hinj.1
          have hdval : (gameF.pileDepth.get i).toInt.toNat - 1 = (cardDepth g cardF).toNat :=
            congrArg Fin.val hinj.2
          have hstrict' : (cardDepth g cardF).toNat + 1 <
              (gameF.pileDepth.get i).toInt.toNat := by
            rw [hii]
            show (cardDepth g cardF).toNat + 1 <
              (gameF.pileDepth[(cardPile g cardF).toNat]'hp64F').toInt.toNat
            have hpdEq : (gameF.pileDepth[(cardPile g cardF).toNat]'hp64F') =
                (gameF.pileDepth[(cardPile g cardF).toNat]'hp64F) := by congr 1
            rw [hpdEq]; exact hstrict
          omega
        have hclt := moveAces_lt_of_not_free g suit cardF foundF gameF hloopinv' boundary hSB
          hboundaryReal.2.1 hboundaryNotFree hboundaryNeCardF
        have hleRaw := flute_le_of_lt_and_notfree hwf hmergedF.toSolverInvBase i hdi cardF hnf hclt
        have hle : cardF.toNat + (gameF.pileFlute.get i).toNat ≤ boundary.toNat := hleRaw
        omega
  rw [hloopeq]
  simp only [Vector.setE, dif_pos hidx4, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, set, EStateM.set]
  set acesFinal : Vector Int8 4 := gameF.aces.set suit.val card2.toInt8 suit.isLt with
    hacesFinalDef
  -- The REAL reduced code indexes `aces`/`kings` via `suitU32.toNat` (matching
  -- `moveAcesBody`'s own `suitU32`-based writes), not `suit.val` — even though
  -- `hsuitU32 : suitU32.toNat = suit.val` holds propositionally, the two
  -- `.set` calls are not syntactically/definitionally interchangeable, so the
  -- final `SolverInvMerged.of_base` application needs an explicit bridge
  -- (`hsetEq` below) rather than matching by `rfl`/defeq alone.
  have hsuitFin : suit = (⟨suitU32.toNat, hidx4⟩ : Fin 4) := Fin.ext hsuitU32.symm
  have hsetEq : ∀ (v : Vector Int8 4) (x : Int8),
      v.set suit.val x suit.isLt = v.set suitU32.toNat x hidx4 := by
    intro v x
    apply vector_ext_get
    intro t
    by_cases htS : t = suit
    · rw [htS]
      show (v.set suit.val x suit.isLt)[suit.val]'suit.isLt = (v.set suitU32.toNat x hidx4).get suit
      rw [Vector.getElem_set_self, hsuitFin]
      show x = (v.set suitU32.toNat x hidx4)[suitU32.toNat]'hidx4
      rw [Vector.getElem_set_self]
    · have h1 : (v.set suit.val x suit.isLt).get t = v.get t := by
        show (v.set suit.val x suit.isLt)[t.val]'t.isLt = v[t.val]'t.isLt
        apply Vector.getElem_set_ne suit.isLt t.isLt
        intro hcon
        exact htS (Fin.ext hcon.symm)
      have h2 : (v.set suitU32.toNat x hidx4).get t = v.get t := by
        show (v.set suitU32.toNat x hidx4)[t.val]'t.isLt = v[t.val]'t.isLt
        apply Vector.getElem_set_ne hidx4 t.isLt
        intro hcon
        apply htS
        rw [hsuitFin]
        exact Fin.ext hcon.symm
      rw [h1, h2]
  have hacesFinalEq : acesFinal = gameF.aces.set suitU32.toNat card2.toInt8 hidx4 := by
    rw [hacesFinalDef]; exact hsetEq gameF.aces card2.toInt8
  have hbusySub : (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)).toNat =
      gameF.busyAces.toNat - ((1 : UInt8) <<< suit.val.toUInt8).toNat := by
    apply UInt8.toNat_sub_of_le
    have hlt16 : gameF.busyAces.toNat < 16 := by
      have := hmergedF.busyAces_lt16
      rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this
    exact uint8_bit_le_of_and_ne_zero hlt16 suit hbitF
  have hbusyAces_lt16Final : (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)) < 16 := by
    rw [UInt8.lt_iff_toNat_lt, hbusySub]
    have hlt16 : gameF.busyAces.toNat < 16 := by
      have := hmergedF.busyAces_lt16
      rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this
    have h16 : (16 : UInt8).toNat = 16 := by decide
    omega
  -- **Ace-transition facts exposed for the drain-loop induction**: the
  -- OTHER suits' `aces` never move throughout the whole walk (frame), and
  -- `suit`'s own ace either strictly advances (in `VALUE` terms) or, if
  -- the walk took literally zero steps (`hloopdich`'s left disjunct), the
  -- WHOLE position is untouched and only `busyAces` shrinks.
  have hacesFinalSuit0 : acesFinal.get suit = card2.toInt8 := by
    rw [hacesFinalDef]
    show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
    exact Vector.getElem_set_self suit.isLt
  have hacesFinalFrame : ∀ s : Fin 4, s.val ≠ ctz p.busyAces → acesFinal.get s = p.aces.get s := by
    intro s hs
    have hsne : s ≠ suit := by
      intro hcon; apply hs; rw [hcon]
    have hacesFinalNe : acesFinal.get s = gameF.aces.get s := by
      rw [hacesFinalDef]
      show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[s.val]'s.isLt =
        gameF.aces[s.val]'s.isLt
      apply Vector.getElem_set_ne suit.isLt s.isLt
      intro hcon
      exact hsne (Fin.ext hcon.symm)
    rw [hacesFinalNe]
    exact hloopframe s hsne
  have hDichotomy :
      (VALUE (acesFinal.get suit).toUInt8).toNat > (VALUE (p.aces.get suit).toUInt8).toNat ∨
      (acesFinal = p.aces ∧
        (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)).toNat < p.busyAces.toNat) := by
    rcases hloopdich with ⟨hcardFeq, _, _, hgameFeq⟩ | hgt
    · right
      have hcard2eqA' : card2 = A.toUInt8 := by
        apply UInt8.toNat_inj.mp
        have h1 := hcard2nat
        have h2 := hcard0nat
        have h3 := congrArg UInt8.toNat hcardFeq
        omega
      have hAcesEq : acesFinal = p.aces := by
        apply vector_ext_get
        intro t
        by_cases htS : t = suit
        · subst htS
          rw [hacesFinalSuit0, hcard2eqA', Int8.toInt8_toUInt8]
        · have h1 : acesFinal.get t = gameF.aces.get t := by
            rw [hacesFinalDef]
            show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[t.val]'t.isLt =
              gameF.aces[t.val]'t.isLt
            apply Vector.getElem_set_ne suit.isLt t.isLt
            intro hcon
            exact htS (Fin.ext hcon.symm)
          rw [h1, hgameFeq]
      refine ⟨hAcesEq, ?_⟩
      rw [hgameFeq]
      have hbit0 : p.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0 := by
        rw [hsuitval]; exact ctz_bit_self p.busyAces hbusy
      have hp16 : p.busyAces.toNat < 16 := by
        have := hmerged.busyAces_lt16
        rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this
      have hle : ((1 : UInt8) <<< suit.val.toUInt8) ≤ p.busyAces :=
        uint8_bit_le_of_and_ne_zero hp16 suit hbit0
      have hleNat : ((1 : UInt8) <<< suit.val.toUInt8).toNat ≤ p.busyAces.toNat :=
        UInt8.le_iff_toNat_le.mp hle
      have hsub : (p.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)).toNat =
          p.busyAces.toNat - ((1 : UInt8) <<< suit.val.toUInt8).toNat :=
        UInt8.toNat_sub_of_le _ _ hle
      have hbitpos : ∀ t : Fin 4, 0 < ((1 : UInt8) <<< t.val.toUInt8).toNat := by native_decide
      have hbp := hbitpos suit
      omega
    · left
      rw [hacesFinalSuit0, UInt8.toUInt8_toInt8, ← hAdef]
      have h1 := hcard2nat
      have h2 := hcard0nat
      have hSc2 := SUIT_toNat card2; have hVc2 := VALUE_toNat card2
      have hSA := SUIT_toNat A.toUInt8; have hVA := VALUE_toNat A.toUInt8
      have hSeq : (SUIT card2).toNat = (SUIT A.toUInt8).toNat := by rw [hSuitCard2, hAsuit]
      omega
  -- Shared pile/suit facts, generic over the final `kings` vector (which
  -- differs between the two `VALUE card2 == 13` branches below, but nothing
  -- pile-level or in `suitClean s` for `s ≠ suit` depends on it).  Named as a
  -- function of `K` (rather than a multi-line `{ gameF with ... }` literal
  -- spliced directly into each call site) to sidestep a parser quirk where a
  -- structure-update literal spanning multiple lines, used as a function
  -- ARGUMENT (not a `let`/`have` body), can mis-parse depending on the
  -- continuation lines' indentation relative to the opening `{`.
  let gameFinalOf : Vector Int8 4 → SolverPosType := fun K =>
    { gameF with aces := acesFinal, kings := K, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) }
  have pileBaseFinal : ∀ K : Vector Int8 4, ∀ i : Fin 10,
      PileBase g (gameFinalOf K) i := by
    intro K i
    have hbOld := hmergedF.pileBase i
    refine ⟨hbOld.pileDepth_bound, hbOld.pileDepth_nonneg, hbOld.flute_pos, hbOld.flute_empty,
      hbOld.flute_cards_free, ?_⟩
    intro hnewDepthPos boundary hs
    by_cases hSB : SUIT boundary = suit.val.toUInt8
    · have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
        apply Fin.ext; show (SUIT boundary).toNat = suit.val
        rw [hSB, finVal_toUInt8_toNat]
      have hacesFinalSuit : (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toUInt8.toNat =
          card2.toNat := by
        rw [hEqFin]
        show (acesFinal.get suit).toUInt8.toNat = card2.toNat
        have hset : acesFinal.get suit = card2.toInt8 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
          exact Vector.getElem_set_self suit.isLt
        rw [hset, UInt8.toUInt8_toInt8]
      show (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toUInt8.toNat +
        (gameF.pileFlute.get i).toNat ≤ boundary.toNat
      rw [hacesFinalSuit]
      have hlt2 : card2.toNat + (gameF.pileFlute.get i).toNat < boundary.toNat :=
        hAboveCard2 i hnewDepthPos hSB
      omega
    · have hNeFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) ≠ suit := by
        intro hcon
        apply hSB
        apply UInt8.toNat_inj.mp
        rw [finVal_toUInt8_toNat]
        exact congrArg Fin.val hcon
      have hacesFinalNe : acesFinal.get ⟨(SUIT boundary).toNat, hs⟩ =
          gameF.aces.get ⟨(SUIT boundary).toNat, hs⟩ := by
        rw [hacesFinalDef]
        show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[(SUIT boundary).toNat]'hs =
          gameF.aces[(SUIT boundary).toNat]'hs
        apply Vector.getElem_set_ne suit.isLt hs
        intro hcon
        exact hNeFin (Fin.ext hcon.symm)
      show (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toUInt8.toNat +
        (gameF.pileFlute.get i).toNat ≤ boundary.toNat
      rw [hacesFinalNe]
      exact hbOld.flute_not_aces hnewDepthPos hs
  have pileMergedFinal : ∀ K : Vector Int8 4, ∀ i : Fin 10,
      PileMerged g (gameFinalOf K) i (pileBaseFinal K i).pileDepth_bound := by
    intro K i
    have hbOld := hmergedF.pileMerged i
    have hbOldBase := hmergedF.pileBase i
    refine ⟨hbOld.merge_complete, ?_, ?_⟩
    · -- flute_maximal
      by_cases hd0 : gameF.pileDepth.get i = 0
      · left; exact hd0
      · right
        have hgdj : (gameF.pileDepth.get i).toInt.toNat > 0 := by
          have h1 := hbOldBase.pileDepth_nonneg
          rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at h1
          have h2 : (gameF.pileDepth.get i).toInt ≠ 0 := by
            intro hz; apply hd0; apply Int8.toInt_inj.mp
            rw [hz, show ((0 : Int8).toInt = 0) from rfl]
          omega
        set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
          by have := hbOldBase.pileDepth_bound; omega⟩ with hboundaryDef
        set prevCard := boundary - gameF.pileFlute.get i with hprevCardDef
        show (∃ hs : (SUIT boundary).toNat < 4,
            acesFinal.get ⟨(SUIT boundary).toNat, hs⟩ = prevCard.toInt8) ∨
          ¬ isFreeCard g gameF prevCard
        have hrealBd : IsRealCard boundary := hwf.pos2card_real i _
        have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
        have hflv : (gameF.pileFlute.get i).toNat ≤ (VALUE boundary).toNat :=
          hmergedF.flute_le_value hwf i hgdj
        have hfleB : gameF.pileFlute.get i ≤ boundary := by
          rw [UInt8.le_iff_toNat_le]
          have := Nat.mod_le boundary.toNat 16
          have hvn := VALUE_toNat boundary
          omega
        have hprevNat : prevCard.toNat = boundary.toNat - (gameF.pileFlute.get i).toNat :=
          UInt8.toNat_sub_of_le _ _ hfleB
        by_cases hSB : SUIT boundary = suit.val.toUInt8
        · right
          have hlt2 : card2.toNat + (gameF.pileFlute.get i).toNat < boundary.toNat :=
            hAboveCard2 i hgdj hSB
          have hcard2ltprev : card2.toNat < prevCard.toNat := by omega
          rcases hbOld.flute_maximal.resolve_left hd0 with ⟨hs, heqOld⟩ | hOldNF
          · exfalso
            have hEqFinOld : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
              apply Fin.ext; show (SUIT boundary).toNat = suit.val
              rw [hSB, finVal_toUInt8_toNat]
            rw [hEqFinOld] at heqOld
            have hAeq : (gameF.aces.get suit).toUInt8 = prevCard := by
              have h1 := congrArg Int8.toUInt8 heqOld
              rwa [UInt8.toUInt8_toInt8] at h1
            have hAeqNat : (gameF.aces.get suit).toUInt8.toNat = prevCard.toNat :=
              congrArg UInt8.toNat hAeq
            have hci := hcard2eqA
            omega
          · exact hOldNF
        · have hNeFin : (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4) ≠ suit := by
            intro hcon
            apply hSB
            apply UInt8.toNat_inj.mp
            rw [finVal_toUInt8_toNat]
            exact congrArg Fin.val hcon
          rcases hbOld.flute_maximal.resolve_left hd0 with ⟨hs, heqOld⟩ | hOldNF
          · left
            refine ⟨hs4', ?_⟩
            have hacesFinalNe : acesFinal.get ⟨(SUIT boundary).toNat, hs4'⟩ =
                gameF.aces.get ⟨(SUIT boundary).toNat, hs4'⟩ := by
              rw [hacesFinalDef]
              show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[
                (SUIT boundary).toNat]'hs4' = gameF.aces[(SUIT boundary).toNat]'hs4'
              apply Vector.getElem_set_ne suit.isLt hs4'
              intro hcon
              exact hNeFin (Fin.ext hcon.symm)
            rw [hacesFinalNe]
            have hEqFinOld : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) =
                (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4) := Fin.ext rfl
            rw [← hEqFinOld]
            exact heqOld
          · right; exact hOldNF
    · -- busyAces_complete
      intro hdj0
      set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toInt.toNat - 1,
        by have := hbOldBase.pileDepth_bound; omega⟩ with hboundaryDef
      show ∀ hs : (SUIT boundary).toNat < 4,
        (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toUInt8 =
          boundary - gameF.pileFlute.get i →
        (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)) &&& ((1 : UInt8) <<< SUIT boundary)
          ≠ 0
      intro hs heqHyp
      by_cases hSB : SUIT boundary = suit.val.toUInt8
      · exfalso
        have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
          apply Fin.ext; show (SUIT boundary).toNat = suit.val
          rw [hSB, finVal_toUInt8_toNat]
        have hacesFinalSuit : acesFinal.get suit = card2.toInt8 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
          exact Vector.getElem_set_self suit.isLt
        rw [hEqFin, hacesFinalSuit, UInt8.toUInt8_toInt8] at heqHyp
        have hlt2 : card2.toNat + (gameF.pileFlute.get i).toNat < boundary.toNat :=
          hAboveCard2 i hdj0 hSB
        have hflv : (gameF.pileFlute.get i).toNat ≤ (VALUE boundary).toNat :=
          hmergedF.flute_le_value hwf i hdj0
        have hfleB : gameF.pileFlute.get i ≤ boundary := by
          rw [UInt8.le_iff_toNat_le]
          have := Nat.mod_le boundary.toNat 16
          have hvn := VALUE_toNat boundary
          omega
        have hprevNat : (boundary - gameF.pileFlute.get i).toNat =
            boundary.toNat - (gameF.pileFlute.get i).toNat := UInt8.toNat_sub_of_le _ _ hfleB
        have hcardeq2 : card2.toNat = (boundary - gameF.pileFlute.get i).toNat := by
          rw [← heqHyp]
        omega
      · have hNeFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) ≠ suit := by
          intro hcon
          apply hSB
          apply UInt8.toNat_inj.mp
          rw [finVal_toUInt8_toNat]
          exact congrArg Fin.val hcon
        have hacesFinalNe : acesFinal.get ⟨(SUIT boundary).toNat, hs⟩ =
            gameF.aces.get ⟨(SUIT boundary).toNat, hs⟩ := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[
            (SUIT boundary).toNat]'hs = gameF.aces[(SUIT boundary).toNat]'hs
          apply Vector.getElem_set_ne suit.isLt hs
          intro hcon
          exact hNeFin (Fin.ext hcon.symm)
        rw [hacesFinalNe] at heqHyp
        have hOldBit := hbOld.busyAces_complete hdj0 hs heqHyp
        have hsuitNe : suit ≠ (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) := fun hcon => hSB (by
          rw [hcon]; show SUIT boundary = ((SUIT boundary).toNat).toUInt8
          exact (UInt8.ofNat_toNat).symm)
        have hSBeq : SUIT boundary = (⟨(SUIT boundary).toNat, hs⟩ : Fin 4).val.toUInt8 :=
          (UInt8.ofNat_toNat).symm
        rw [hSBeq]
        exact uint8_and_ne_zero_of_sub_ne (by
          have := hmergedF.busyAces_lt16
          rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this)
          suit ⟨(SUIT boundary).toNat, hs⟩ hsuitNe hbitF (by rw [← hSBeq]; exact hOldBit)
  have suitCleanNe : ∀ K : Vector Int8 4, (∀ s : Fin 4, s ≠ suit → K.get s = gameF.kings.get s) →
      ∀ s : Fin 4, s ≠ suit →
      SuitClean g (gameFinalOf K) s (fun i => (pileBaseFinal K i).pileDepth_bound) := by
    intro K hKframe s hsS
    have hbOld := hmergedF.suitClean s
    have hacesEq : acesFinal.get s = gameF.aces.get s := by
      rw [hacesFinalDef]
      show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[s.val]'s.isLt =
        gameF.aces[s.val]'s.isLt
      apply Vector.getElem_set_ne suit.isLt s.isLt
      intro hcon
      exact hsS (Fin.ext hcon.symm)
    have hkingsEq : K.get s = gameF.kings.get s := hKframe s hsS
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hacesEq, hkingsEq]; exact hbOld.aces_kings_valid
    · intro c hSc hVc1 hVc2
      rw [hacesEq] at hVc2
      exact hbOld.foundation_cards_free c hSc hVc1 hVc2
    · rw [hacesEq]
      rcases hbOld.foundation_maximal_weak with h13 | hnf | hbusy
      · exact Or.inl h13
      · exact Or.inr (Or.inl hnf)
      · refine Or.inr (Or.inr ?_)
        have hsuitNe : suit ≠ s := Ne.symm hsS
        exact uint8_and_ne_zero_of_sub_ne (by
          have := hmergedF.busyAces_lt16
          rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this)
          suit s hsuitNe hbitF hbusy
    · rw [hacesEq, hkingsEq]
      obtain ⟨hdisj, hall⟩ := hbOld.king_frontier
      refine ⟨?_, hall⟩
      rcases hdisj with ⟨heqAK, h13orBusy⟩ | ⟨hlt, hnf⟩
      · refine Or.inl ⟨heqAK, ?_⟩
        rcases h13orBusy with h13 | hbusy
        · exact Or.inl h13
        · refine Or.inr ?_
          have hsuitNe : suit ≠ s := Ne.symm hsS
          exact uint8_and_ne_zero_of_sub_ne (by
            have := hmergedF.busyAces_lt16
            rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this)
            suit s hsuitNe hbitF hbusy
      · exact Or.inr ⟨hlt, hnf⟩
  -- Shared facts, independent of the `VALUE card2 == 13` branch below.
  have hFoundationCardsFreeSuit : ∀ c : UInt8, SUIT c = suit.val.toUInt8 →
      1 ≤ (VALUE c).toNat → (VALUE c).toNat ≤ (VALUE card2).toNat → isFreeCard g gameF c := by
    intro c hSc hVc1 hVc2
    have hbOld := hmergedF.suitClean suit
    by_cases hcOld : (VALUE c).toNat ≤ (VALUE (gameF.aces.get suit).toUInt8).toNat
    · exact hbOld.foundation_cards_free c hSc hVc1 hcOld
    · push_neg at hcOld
      have hs_c := SUIT_toNat c; have hv_c := VALUE_toNat c
      have hs_A := SUIT_toNat (gameF.aces.get suit).toUInt8
      have hv_A := VALUE_toNat (gameF.aces.get suit).toUInt8
      have hSameSuit : (SUIT c).toNat = (SUIT (gameF.aces.get suit).toUInt8).toNat := by
        rw [hSc, hAFsuit]
      have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
      have hSeqAFc2 : (SUIT card2).toNat = (SUIT (gameF.aces.get suit).toUInt8).toNat := by
        rw [hSuitCard2, hAFsuit]
      set l := c.toNat - (gameF.aces.get suit).toUInt8.toNat with hldef
      have hl1 : 1 ≤ l := by omega
      have hlfound : (l : Int) ≤ foundF.toInt := by
        have hci := hcard2eqA
        omega
      have hAl256 : (gameF.aces.get suit).toUInt8.toNat + l < 256 := by
        have := c.toNat_lt; omega
      have hceq : c = (gameF.aces.get suit).toUInt8 + UInt8.ofNat l :=
        uint8_eq_add_ofNat_of_toNat_eq hAl256 (by omega)
      rw [hceq]
      exact hfoundfreeF l hl1 hlfound
  have hUsedSpaceDefFinal : (gameF.usedSpace - foundF).toInt = (52 : Int)
      - (gameF.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
      - (acesFinal.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
          gameF.pileDepth.toList gameF.pileFlute.toList |>.foldl (· + ·) 0 : Nat) := by
    have has_ := aces_sum_foldl_set gameF.aces suit.val suit.isLt card2.toInt8
    rw [← hacesFinalDef] at has_
    have hAFidxEq : (gameF.aces[suit.val]'suit.isLt) = gameF.aces.get suit := rfl
    rw [hAFidxEq] at has_
    have hmergedU := hmergedF.usedSpace_def
    have hVAeq : (VALUE (gameF.aces.get suit).toUInt8).toNat + foundF.toInt.toNat =
        (VALUE card2).toNat := by
      have hsa := SUIT_toNat (gameF.aces.get suit).toUInt8
      have hva := VALUE_toNat (gameF.aces.get suit).toUInt8
      have hsc := SUIT_toNat card2; have hvc := VALUE_toNat card2
      have hSeq : (SUIT (gameF.aces.get suit).toUInt8).toNat = (SUIT card2).toNat := by
        rw [hAFsuit, hSuitCard2]
      have hci := hcard2eqA
      omega
    have hcardVAL : (VALUE card2.toInt8.toUInt8).toNat = (VALUE card2).toNat := by
      rw [UInt8.toUInt8_toInt8]
    rw [hcardVAL] at has_
    have hfound_nonneg : (0 : Int) ≤ foundF.toInt := hf0F
    have husedBound := usedSpace_nonneg hwf hmergedF.toSolverInvBase
    have hsub : (gameF.usedSpace - foundF).toInt = gameF.usedSpace.toInt - foundF.toInt := by
      rw [Int8.toInt_sub]
      apply Int.bmod_eq_of_le <;> omega
    have hAcesSumEq : (acesFinal.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 :
        Nat) =
        (gameF.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat) +
          foundF.toInt.toNat := by omega
    rw [hAcesSumEq, hsub, hmergedU]
    have hfoundToNat : (foundF.toInt.toNat : Int) = foundF.toInt := by omega
    push_cast
    omega
  by_cases hVC : (VALUE card2 == (13 : UInt8)) = true
  · simp only [hVC, reduceIte, EStateM.bind, EStateM.set, EStateM.pure, ← hcard2def]
    have hVC13 : (VALUE card2).toNat = 13 := by
      have h := hVC; rw [beq_iff_eq] at h
      rw [h]; decide
    refine ⟨forcedKingsF, _, rfl, ?_, ?_, ?_⟩
    set kingsFinal : Vector Int8 4 :=
      gameF.kings.set suit.val card2.toInt8 suit.isLt with hkingsFinalDef
    have hkingsFinalEq : kingsFinal = gameF.kings.set suitU32.toNat card2.toInt8 hidx4 := by
      rw [hkingsFinalDef]; exact hsetEq gameF.kings card2.toInt8
    have hkingsFrame : ∀ s : Fin 4, s ≠ suit → kingsFinal.get s = gameF.kings.get s := by
      intro s hsS
      rw [hkingsFinalDef]
      show (gameF.kings.set suit.val card2.toInt8 suit.isLt)[s.val]'s.isLt =
        gameF.kings[s.val]'s.isLt
      apply Vector.getElem_set_ne suit.isLt s.isLt
      intro hcon
      exact hsS (Fin.ext hcon.symm)
    have hgameFinalOfEq : gameFinalOf kingsFinal = { gameF with aces := gameF.aces.set suitU32.toNat card2.toInt8 hidx4, kings := gameF.kings.set suitU32.toNat card2.toInt8 hidx4, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } := by
      show { gameF with aces := acesFinal, kings := kingsFinal, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } = _
      rw [hacesFinalEq, hkingsFinalEq]
    rw [← hgameFinalOfEq]
    refine SolverInvMerged.of_base ⟨pileBaseFinal kingsFinal, ?_, ?_, ?_, hbusyAces_lt16Final⟩
      (pileMergedFinal kingsFinal) ?_
    · intro s
      by_cases hsS : s = suit
      · subst hsS
        have hbOld := hmergedF.suitClean suit
        have hacesEq : acesFinal.get suit = card2.toInt8 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
          exact Vector.getElem_set_self suit.isLt
        have hkingsEq : kingsFinal.get suit = card2.toInt8 := by
          rw [hkingsFinalDef]
          show (gameF.kings.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
          exact Vector.getElem_set_self suit.isLt
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hacesEq, hkingsEq, UInt8.toUInt8_toInt8]
          exact ⟨hSuitCard2, hVC13.le, hSuitCard2, hVC13.le, Int8.le_refl _⟩
        · intro c hSc hVc1 hVc2
          rw [hacesEq, UInt8.toUInt8_toInt8] at hVc2
          exact hFoundationCardsFreeSuit c hSc hVc1 hVc2
        · rw [hacesEq, UInt8.toUInt8_toInt8]
          exact Or.inl hVC13
        · rw [hacesEq, hkingsEq]
          refine ⟨Or.inl ⟨rfl, Or.inl hVC13⟩, ?_⟩
          intro c hSc hVc1 hVc2
          exfalso
          rw [UInt8.toUInt8_toInt8] at hVc1
          omega
      · exact suitCleanNe kingsFinal hkingsFrame s hsS
    · -- hash_def: frame.
      exact hmergedF.hash_def
    · exact hUsedSpaceDefFinal
    · exact hmergedF.freePiles_def
    · intro s hs
      rw [← hacesFinalEq]
      exact hacesFinalFrame s hs
    · intro s hs
      have hseq : s = suit := Fin.ext (hs.trans hsuitval.symm)
      subst hseq
      rw [← hacesFinalEq]
      exact hDichotomy
  · simp only [hVC, Bool.false_eq_true, reduceIte, EStateM.bind, EStateM.set, EStateM.pure,
      ← hcard2def]
    refine ⟨forcedKingsF, _, rfl, ?_, ?_, ?_⟩
    have hVCne13 : (VALUE card2).toNat ≠ 13 := by
      intro h13
      apply hVC
      rw [beq_iff_eq]
      apply UInt8.toNat_inj.mp
      rw [h13]; decide
    have hkingsFrame : ∀ s : Fin 4, s ≠ suit → gameF.kings.get s = gameF.kings.get s :=
      fun s _ => rfl
    have hgameFinalOfEq : gameFinalOf gameF.kings = { gameF with aces := gameF.aces.set suitU32.toNat card2.toInt8 hidx4, kings := gameF.kings, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } := by
      show { gameF with aces := acesFinal, kings := gameF.kings, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } = _
      rw [hacesFinalEq]
    rw [← hgameFinalOfEq]
    refine SolverInvMerged.of_base ⟨pileBaseFinal gameF.kings, ?_, ?_, ?_, hbusyAces_lt16Final⟩
      (pileMergedFinal gameF.kings) ?_
    · intro s
      by_cases hsS : s = suit
      · subst hsS
        have hbOld := hmergedF.suitClean suit
        have hacesEq : acesFinal.get suit = card2.toInt8 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2.toInt8 suit.isLt)[suit.val]'suit.isLt = card2.toInt8
          exact Vector.getElem_set_self suit.isLt
        have hAKvalid := hbOld.aces_kings_valid
        have hVK13 := hAKvalid.2.2.2.1
        have hSK := hAKvalid.2.2.1
        have hKnonneg : (0 : Int8) ≤ gameF.kings.get suit := int8_nonneg_of_suit hSK
        -- `cardF` is real (`≤ 13`): if it were the value-14 sentinel,
        -- `card2`'s value would be exactly `13` (`hVcard2eq13From`),
        -- contradicting `hVCne13`.
        have hcardFle13 : (VALUE cardF).toNat ≤ 13 := by
          by_contra hcon
          push_neg at hcon
          exact hVCne13 (hVcard2eq13From (by omega))
        have hcardFreal : IsRealCard cardF :=
          ⟨by rw [hsuitcardF]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega,
            hval1F, hcardFle13⟩
        obtain ⟨hnf, hp64F, hstrict⟩ := hloopexit.resolve_left (by omega)
        have hVcard2le13 : (VALUE card2).toNat ≤ 13 := by
          have hs1 := SUIT_toNat card2; have hv1 := VALUE_toNat card2
          have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
          have hSeq : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
          omega
        -- King-frontier's own `∀c` clause forces `VALUE cardF ≤ VALUE
        -- kings[suit]` (else `cardF` would be free, contradicting `hnf`);
        -- combined with `card2 = cardF - 1`, this gives `card2 < kings[suit]`.
        rcases hbOld.king_frontier.1 with ⟨heqAK, _⟩ | ⟨hltAK, hnfK⟩
        · -- `kings[suit] = A_F` would force the walk to complete fully
          -- (every card above `A_F` up to 13 is free, per `king_frontier`'s
          -- own `∀c` clause), landing in the `VALUE cardF = 14` exit —
          -- excluded here (`hcardFle13`).
          exfalso
          apply hnf
          have hcardFgtA : (VALUE cardF).toNat > (VALUE (gameF.aces.get suit).toUInt8).toNat := by
            have hs_cF := SUIT_toNat cardF; have hv_cF := VALUE_toNat cardF
            have hs_A := SUIT_toNat (gameF.aces.get suit).toUInt8
            have hv_A := VALUE_toNat (gameF.aces.get suit).toUInt8
            have hSeq : (SUIT cardF).toNat = (SUIT (gameF.aces.get suit).toUInt8).toNat := by
              rw [hsuitcardF, hAFsuit]
            have hci := hcardeqF
            omega
          have hVcardFgtK : (VALUE cardF).toNat > (VALUE (gameF.kings.get suit).toUInt8).toNat :=
            by rw [heqAK]; exact hcardFgtA
          exact hbOld.king_frontier.2 cardF hsuitcardF hVcardFgtK hcardFle13
        · have hVcardFleK : (VALUE cardF).toNat ≤ (VALUE (gameF.kings.get suit).toUInt8).toNat :=
            by
            by_contra hcon
            push_neg at hcon
            exact hnf (hbOld.king_frontier.2 cardF hsuitcardF hcon hcardFle13)
          have hcard2ltK_nat : card2.toNat < (gameF.kings.get suit).toUInt8.toNat := by
            have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
            have hs_cF := SUIT_toNat cardF; have hv_cF := VALUE_toNat cardF
            have hs_K := SUIT_toNat (gameF.kings.get suit).toUInt8
            have hv_K := VALUE_toNat (gameF.kings.get suit).toUInt8
            have hSeq1 : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
            have hSeq2 : (SUIT cardF).toNat = (SUIT (gameF.kings.get suit).toUInt8).toNat := by
              rw [hsuitcardF, hSK]
            omega
          have hcard2ltK : card2.toInt8 < gameF.kings.get suit := by
            apply Int8.lt_iff_toInt_lt.mpr
            have hSC24 : (SUIT card2).toNat < 4 := by
              rw [hSuitCard2]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
            have hsvc2 := SUIT_toNat card2; have hvvc2 := VALUE_toNat card2
            rw [uint8_toInt8_toInt_of_lt128 (by omega : card2.toNat < 128),
              int8_toInt_eq_toUInt8_toNat_of_nonneg hKnonneg]
            exact_mod_cast hcard2ltK_nat
          have hcard2leK : card2.toInt8 ≤ gameF.kings.get suit :=
            Int8.le_iff_toInt_le.mpr (le_of_lt (Int8.lt_iff_toInt_lt.mp hcard2ltK))
          refine ⟨⟨?_, ?_, hSK, hVK13, ?_⟩, ?_, ?_, ?_⟩
          · rw [hacesEq, UInt8.toUInt8_toInt8]; exact hSuitCard2
          · rw [hacesEq, UInt8.toUInt8_toInt8]; exact hVcard2le13
          · rw [hacesEq]; exact hcard2leK
          · intro c hSc hVc1 hVc2
            rw [hacesEq, UInt8.toUInt8_toInt8] at hVc2
            exact hFoundationCardsFreeSuit c hSc hVc1 hVc2
          · rw [hacesEq]
            exact Or.inr (Or.inl (by rw [UInt8.toUInt8_toInt8, hcard2p1]; exact hnf))
          · rw [hacesEq]
            exact ⟨Or.inr ⟨hcard2ltK, hnfK⟩, hbOld.king_frontier.2⟩
      · exact suitCleanNe gameF.kings hkingsFrame s hsS
    · exact hmergedF.hash_def
    · exact hUsedSpaceDefFinal
    · exact hmergedF.freePiles_def
    · intro s hs
      rw [← hacesFinalEq]
      exact hacesFinalFrame s hs
    · intro s hs
      have hseq : s = suit := Fin.ext (hs.trans hsuitval.symm)
      subst hseq
      rw [← hacesFinalEq]
      exact hDichotomy

/-- **`SolverMove` re-establishes the Merged layer** (canonicity is recovered
    only after the trailing drain — see `drain_canonical`).

    Proof plan: `move_eq_explicit` exposes the structure (destination
    bookkeeping → `SolverRemoveFlute` → drain via `drainBody`/`moveAces_merged`).
    The missing pure ingredient is the *flute-transfer lemma*: from a canonical
    state, the destination write (`pileFlute[toPile] += fluteLen`, or
    `kings/usedSpace` for king/extra) followed by `removeFlutePre`/`fluteNorm`
    satisfies `CleanupReady` — moved cards become free once the source depth is
    decremented, `flute_maximal[toPile]` transfers from the source pile's old
    clause (same extension card), and the `usedSpace` ledger balances at the
    composed point. -/
theorem move_merged (g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hvalid : MoveValid g p pile toPile) :
    ∃ fk p', EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      SolverInvMerged g p' := by
  sorry

/-- **Termination measure for the `busyAces` drain loop.**  A plain sum, over
    the 4 suits, of how far each suit's foundation still has to climb to reach
    `13` (`King`), scaled by `16` and padded with `busyAces.toNat` (`< 16` via
    `busyAces_lt16`, so it never disturbs the ordering set by the first
    term).  `moveAces_merged`'s dichotomy (`rank_decrease` below) shows this
    strictly drops on every drain-loop iteration. -/
private def rank (game : SolverPosType) : Nat :=
  ((13 - (VALUE (game.aces.get (0 : Fin 4)).toUInt8).toNat) +
    (13 - (VALUE (game.aces.get (1 : Fin 4)).toUInt8).toNat) +
    (13 - (VALUE (game.aces.get (2 : Fin 4)).toUInt8).toNat) +
    (13 - (VALUE (game.aces.get (3 : Fin 4)).toUInt8).toNat)) * 16 + game.busyAces.toNat

/-- **`rank` strictly decreases across one `moveAces_merged` step.**  Uses
    exactly the dichotomy exposed by `moveAces_merged`'s strengthened
    conclusion: either the processed suit's own ace strictly advances (so the
    sum term drops by `≥ 1`, swamping any change to the `< 16` remainder), or
    the aces are entirely unchanged and `busyAces.toNat` itself strictly
    drops. -/
private theorem rank_decrease (g : Globals) (game game1 : SolverPosType)
    (hmerged : SolverInvMerged g game) (hmerged1 : SolverInvMerged g game1)
    (hbusy : game.busyAces ≠ 0)
    (hframe1 : ∀ s : Fin 4, s.val ≠ ctz game.busyAces → game1.aces.get s = game.aces.get s)
    (hdich1 : ∀ s : Fin 4, s.val = ctz game.busyAces →
      (VALUE (game1.aces.get s).toUInt8).toNat > (VALUE (game.aces.get s).toUInt8).toNat ∨
      (game1.aces = game.aces ∧ game1.busyAces.toNat < game.busyAces.toNat)) :
    rank game1 < rank game := by
  have hsuit4 : ctz game.busyAces < 4 :=
    ctz_lt_four_of_low_nibble game.busyAces (by
      rw [uint8_and_0xF_eq_self_of_lt16 game.busyAces hmerged.busyAces_lt16]; exact hbusy)
  have hb0 : (VALUE (game.aces.get (0 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 0).2.1
  have hb1 : (VALUE (game.aces.get (1 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 1).2.1
  have hb2 : (VALUE (game.aces.get (2 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 2).2.1
  have hb3 : (VALUE (game.aces.get (3 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 3).2.1
  have hb0' : (VALUE (game1.aces.get (0 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 0).2.1
  have hb1' : (VALUE (game1.aces.get (1 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 1).2.1
  have hb2' : (VALUE (game1.aces.get (2 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 2).2.1
  have hb3' : (VALUE (game1.aces.get (3 : Fin 4)).toUInt8).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 3).2.1
  have hbz16 : game1.busyAces.toNat < 16 := by
    have := hmerged1.busyAces_lt16
    rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this
  have hcase : ctz game.busyAces = 0 ∨ ctz game.busyAces = 1 ∨ ctz game.busyAces = 2 ∨
      ctz game.busyAces = 3 := by omega
  unfold rank
  rcases hcase with h | h | h | h
  · have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf1, hf2, hf3]
    rcases hdich1 0 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := by
        rw [haeq]
      rw [hf0]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf0, hf2, hf3]
    rcases hdich1 1 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := by
        rw [haeq]
      rw [hf1]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf0, hf1, hf3]
    rcases hdich1 2 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := by
        rw [haeq]
      rw [hf2]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    rw [hf0, hf1, hf2]
    rcases hdich1 3 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := by
        rw [haeq]
      rw [hf3]; omega

/-- **Exact run of the `busyAces` drain loop, with its invariant.**  By
    induction on a `Nat` bounding `rank game` (which strictly decreases on
    every continuing iteration via `rank_decrease`/`moveAces_merged`). -/
private theorem drainBody_run (g : Globals) (hwf : WellFormedLayout g) :
    ∀ (n : Nat) (forcedKings : UInt16) (game : SolverPosType),
      rank game < n →
      SolverInvMerged g game →
      ∃ (forcedKings' : UInt16) (game' : SolverPosType),
        Loop.forIn Loop.mk forcedKings drainBody (g, game) =
          .ok forcedKings' (g, game') ∧
        SolverInvMerged g game' ∧ game'.busyAces = 0 := by
  intro n
  induction n with
  | zero => intro forcedKings game hmeas _; omega
  | succ n ih =>
    intro forcedKings game hmeas hmerged
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := forcedKings) (f := drainBody)
    by_cases hbz : game.busyAces = 0
    · refine ⟨forcedKings, game, ?_, hmerged, hbz⟩
      rw [hunf]
      simp only [drainBody, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hbz,
        Bool.false_eq_true, bne_self_eq_false, reduceIte, pure, EStateM.pure]
    · obtain ⟨fk, game1, hrun1, hmerged1, hframe1, hdich1⟩ :=
        moveAces_merged g game hwf hmerged hbz
      have hrun1' : _root_.SolverMoveAces (g, game) = .ok fk (g, game1) := hrun1
      have hdec : rank game1 < rank game := rank_decrease g game game1 hmerged hmerged1 hbz
        hframe1 hdich1
      have hmeas1 : rank game1 < n := by omega
      obtain ⟨fk', game', hrun', hmerged', hbz'⟩ := ih (forcedKings &&& fk) game1 hmeas1 hmerged1
      refine ⟨fk', game', ?_, hmerged', hbz'⟩
      rw [hunf]
      simp only [drainBody, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hbz,
        bne_iff_ne, ne_eq, not_false_eq_true, reduceIte, hrun1', pure, EStateM.pure]
      exact hrun'

/-- **The drain loop reaches canonical form.**  From a merged state, draining
    `busyAces` via the real `while busyAces ≠ 0 do SolverMoveAces()` loop
    (`drainBody`, shared by `SolverMove` and `SolverConvertFromPilesKings`)
    reaches a fully canonical state. -/
theorem drain_canonical (g : Globals) (p : SolverPosType) (fk0 : UInt16)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) :
    ∃ fk p', Loop.forIn Loop.mk fk0 drainBody (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  obtain ⟨fk, p', hrun, hmerged', hbz⟩ := drainBody_run g hwf (rank p + 1) fk0 p (by omega) hmerged
  exact ⟨fk, p', hrun, IsCanonicalPos.of_merged_drained hmerged' hbz⟩

/-- **`SolverMove` preserves canonical form.**  From a canonical state, a valid
    solver move yields another canonical state (this is the per-node invariant
    maintenance behind the soundness proof). -/
theorem solverMove_canonical (g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p) (hvalid : MoveValid g p pile toPile) :
    ∃ fk p', EStateM.run (SolverModel.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

/-- **`SolverConvertFromPilesKings` produces a canonical state.**  Given a
    well-formed layout and a legal pile-depth vector, converting from the empty
    position yields a canonical `SolverPosType` (for any starting position — the
    function overwrites all fields). -/
theorem solverConvert_canonical (g : Globals) (p0 : SolverPosType) (pk : Vector UInt8 11)
    (hwf : WellFormedLayout g) (hpk : ValidDepths pk) :
    ∃ fk p', EStateM.run (SolverModel.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

/-- **A pile's freed-loop absorption range lies strictly above any other
    pile's current boundary that sits below the merge boundary.**  If pile
    `j`'s boundary `Bj` has smaller raw value than `B` (the boundary the
    freed loop walks down from) and pile `j` is non-empty, then `Bj` lies
    strictly below the *entire* range `[B-f, B-1]` the freed loop absorbs:
    if it were inside, it would equal one of the `f` consecutive walked
    values, and the freed guard at that step would assert it free —
    contradicting `boundary_not_free`. -/
theorem freed_below_other_boundary (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hnf : SolverInvBase g p)
    (suit B : UInt8) (hBreal : IsRealCard B) (f : Nat)
    (hfg : ∀ k, k < f → freedGuard g suit
      (freedIter k (⟨(1 : Int32), p, B - 1⟩ : FreedAcc)))
    (j : Fin 10) (hdj : (p.pileDepth.get j).toInt.toNat > 0)
    (hBjlt : ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hnf.pileDepth_bound j; omega⟩ : UInt8).toNat < B.toNat) :
    ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hnf.pileDepth_bound j; omega⟩ : UInt8).toNat < B.toNat - f := by
  have hB64 : B.toNat < 64 := by
    have hsn := SUIT_toNat B; have h1 := hBreal.1; omega
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toInt.toNat - 1,
    by have := hnf.pileDepth_bound j; omega⟩ : Fin 5) with hBjdef
  by_contra hge
  push Not at hge
  have hkf : B.toNat - 1 - Bj.toNat < f := by omega
  have hg := hfg (B.toNat - 1 - Bj.toNat) hkf
  obtain ⟨_, hg2⟩ := hg
  simp only [freedIter_eq] at hg2
  have h1B : (1 : UInt8) ≤ B := by rw [UInt8.le_iff_toNat_le]; show 1 ≤ B.toNat; omega
  have h1nat : ((1 : UInt8)).toNat = 1 := rfl
  have hkof : (UInt8.ofNat (B.toNat - 1 - Bj.toNat)).toNat = B.toNat - 1 - Bj.toNat := by
    rw [UInt8.toNat_ofNat']; omega
  have hkle : UInt8.ofNat (B.toNat - 1 - Bj.toNat) ≤ B - 1 := by
    rw [UInt8.le_iff_toNat_le, hkof, UInt8.toNat_sub_of_le _ _ h1B, h1nat]; omega
  have hBjB : B - 1 - UInt8.ofNat (B.toNat - 1 - Bj.toNat) = Bj := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hkle, UInt8.toNat_sub_of_le _ _ h1B, hkof, h1nat]
    omega
  simp only [hBjB] at hg2
  have hBjreal : IsRealCard Bj := hwf.pos2card_real j _
  have hBj64 : Bj.toNat < 64 := by
    have hsn := SUIT_toNat Bj; have h1 := hBjreal.1; omega
  have hBj64u : Bj.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hBj64
  have hg2' := hg2 hBj64u
    (by rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt Bj.toNat hBj64)
  have hfree : isFreeCard g p Bj := by
    unfold isFreeCard
    simp only [dif_pos hBj64]
    have hpileEq' : g.card2pile.get ⟨Bj.toNat, hBj64⟩ = cardPile g Bj := by
      unfold cardPile; simp [hBj64]
    have hpile64 : (cardPile g Bj).toNat < 10 := hpileEq' ▸ hwf.card2pile_lt Bj.toNat hBj64
    simp only [hpileEq', dif_pos hpile64]
    have hpileEqGE : (g.card2pile[Bj.toUInt32.toNat]'hBj64u).toUInt32.toNat =
        (cardPile g Bj).toNat := by
      have : g.card2pile[Bj.toUInt32.toNat]'hBj64u = g.card2pile.get ⟨Bj.toNat, hBj64⟩ := rfl
      rw [this, hpileEq', UInt8.toNat_toUInt32]
    have hdepthEqGE : (g.card2depth[Bj.toUInt32.toNat]'hBj64u).toNat =
        (g.card2depth.get ⟨Bj.toNat, hBj64⟩).toNat := by
      have : g.card2depth[Bj.toUInt32.toNat]'hBj64u = g.card2depth.get ⟨Bj.toNat, hBj64⟩ := rfl
      rw [this]
    have keyEqV : p.pileDepth[(g.card2pile[Bj.toUInt32.toNat]'hBj64u).toUInt32.toNat]'
        (by rw [hpileEqGE]; exact hpile64) = p.pileDepth[(cardPile g Bj).toNat]'hpile64 := by
      congr 1
    have keyEq : (p.pileDepth[(g.card2pile[Bj.toUInt32.toNat]'hBj64u).toUInt32.toNat]'
        (by rw [hpileEqGE]; exact hpile64)).toInt32.toInt.toNat =
      (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toInt.toNat := by
      rw [keyEqV]
      show (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toInt32.toInt.toNat =
        (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toInt.toNat
      rw [Int8.toInt_toInt32]
    show (g.card2depth.get ⟨Bj.toNat, hBj64⟩).toNat ≥
      (p.pileDepth.get ⟨(cardPile g Bj).toNat, hpile64⟩).toInt.toNat
    rw [← hdepthEqGE, ← keyEq]
    exact hg2'
  exact free_card_ne_boundary hwf hnf j hdj Bj hfree rfl

end SolverSpec
