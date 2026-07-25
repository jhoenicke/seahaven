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
   h.hash_def, h.usedSpace_def⟩

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

/-- The base layer ignores `busyAces`, so it transfers across a `busyAces` write —
    **as long as the write only ADDS bits** (`p.busyAces ||| y`, never clears one):
    `king_frontier`'s busyAces-pending disjunct is monotone in the bitmask, so an
    already-set bit stays set. (This collapses the `busyAces` branch of
    `cleanupRunResult`, whose only busyAces write is exactly this OR-in shape.) -/
private theorem nf_setBusyAces {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (y : UInt8) :
    SolverInvBase g { p with busyAces := p.busyAces ||| y } :=
  ⟨fun i => pileBase_setBusyAces (h.pileBase i) y,
   fun s => ⟨h.aces_kings_valid s,
             h.foundation_cards_free s, h.foundation_maximal_weak s,
             ⟨(h.king_frontier s).1.imp (fun hc => ⟨hc.1, hc.2.imp id uint8_and_ne_zero_of_or_left⟩) id,
              (h.king_frontier s).2⟩⟩,
   h.hash_def, h.usedSpace_def⟩

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
  · intro k hdpos hk0 hklt hs
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
    have hval0 := congrArg (fun c => (SUIT c).toNat) hXeq
    have hs' : (SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
        by have := hb.pileDepth_bound; omega⟩)).toNat < 4 := hval0 ▸ hs
    have hEq2 : p.aces.get ⟨(SUIT ((g.pos2card.get j).get
          ⟨((preCleanupPile pile hpile B ph hs4
              (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get j).toInt.toNat - 1,
            by rw [hdeq]; have := hb.pileDepth_bound; omega⟩)).toNat, hs⟩ =
        p.aces.get ⟨(SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toInt.toNat - 1,
          by have := hb.pileDepth_bound; omega⟩)).toNat, hs'⟩ := by
      congr 1
      exact Fin.ext hval0
    rw [haeq, hEq2, hXeq]
    exact hb.flute_not_aces k hdpos' hk0 hklt' hs'

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
    flute_not_aces := fun _ hpos _ _ _ => absurd hpos (by rw [hd0]; decide)
    merge_complete := Or.inl (by rw [hd0]; decide)
    flute_maximal := Or.inl hd0
    busyAces_complete := fun hpos => absurd hpos (by rw [hd0]; decide) }

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
      intro j hdi hj0 hjlt
      have hjlt' : j.toNat < ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute[pile.toNat]'hpile).toNat :=
        hjlt
      rw [hpf, hfl8] at hjlt'
      -- Restate the whole `∀ hs, …` goal via the (still-wrapped) `preCleanupPile`
      -- terms, then reduce those wrappers uniformly — BEFORE `intro hs` — so the
      -- reduction doesn't have to fight an already-fixed dependent hypothesis
      -- (mirrors the recipe from `preCleanupPile_pileBase_ne`'s own `flute_not_aces`).
      show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
          (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
          ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toNat < 4,
        (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).aces.get
          ⟨(SUIT ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
              ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut)).toNat, hs⟩ <
          ((g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
              (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f p
              ).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut - j).toInt8
      rw [preCleanupPile_aces_eq, hcardEqOut]
      intro hs
      have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
      have hidxEq : (⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ : Fin 4) =
          ⟨(SUIT B).toNat, hs4'⟩ := Fin.ext (congrArg UInt8.toNat hSm)
      have hEq2 : p.aces.get ⟨(SUIT (B + UInt8.ofNat m)).toNat, hs⟩ =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
        rw [hidxEq]; congr 1
      rw [hEq2]
      rcases flute_offset_split B m f hBrange.2 (by omega) hf_le j hj0 (by omega)
        with ⟨k, hkm, hval⟩ | ⟨l, hl1, hlf, hval⟩
      · rw [hval]; exact haces_lt_Bk k (by omega)
      · rw [hval]; exact (hffree l hl1 hlf).2 }

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
    (hf_le_tight : f + 2 ≤ (VALUE B).toNat)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
    (hfstop : (B - 1 - UInt8.ofNat f).toInt8 ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 ∨
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
        p.aces[(SUIT boundary).toUInt32.toNat]'hs ≥ prevCard.toInt8) ∨
      ¬ isFreeCard g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) prevCard
    right
    simp only [hcardEqOut, hSm, hpf, hprevEq]
    rcases hfstop with hge | hnfree
    · left
      exact ⟨hs4, hge⟩
    · right
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
      exact preCleanupPile_not_free_of_lt_boundary g pile hpile hwf B
        (pileHashes[pile.toNat]'hpile) hs4 hBrange.2 p m f hd5 hm_le hmcards
        (B - 1 - UInt8.ofNat f) (by
          have hsn := SUIT_toNat B
          have hvn := VALUE_toNat B
          have hsn' := SUIT_toNat (B - 1 - UInt8.ofNat f)
          have hvn' := VALUE_toNat (B - 1 - UInt8.ofNat f)
          have hs1 : (SUIT B).toNat < 4 := hreal.1
          have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
          have hv2 : (VALUE B).toNat ≤ 13 := hreal.2.2
          have hBdecomp : B.toNat = 16 * (SUIT B).toNat + (VALUE B).toNat := by omega
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
    (hf_le_tight : f + 2 ≤ (VALUE B).toNat)
    (hffree : ∀ l, 1 ≤ l → l ≤ f →
      isFreeCard g p (B - UInt8.ofNat l) ∧
      p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8)
    (hfstop : (B - 1 - UInt8.ofNat f).toInt8 ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4 ∨
      ¬ isFreeCard g p (B - 1 - UInt8.ofNat f)) :
    PileClean g (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) ⟨pile.toNat, hpile⟩ := by
  have hb := preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hf_le hffree
  have hm := preCleanupPile_pileMerged_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef
    m f hm_le hmcards hmstop hf_le hf_le_tight hffree hfstop hb.pileDepth_bound
  exact { hb, hm with }

-- `cleanupPile_baseNF`'s discharge has grown large enough (12 clauses × 2
-- branches, each needing its own index/arithmetic bookkeeping) that the
-- default 200000-heartbeat budget is exceeded on unrelated later bullets
-- purely from the theorem's overall size — confirmed by reproducing the
-- timeout even with the newest clause `sorry`'d out (so it isn't a specific
-- broken `rfl`/`exact` looping forever; it's cumulative elaboration cost).
-- Same remedy already used elsewhere in this file's `rfl`-twin proofs.
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
  by_cases hd : p.pileDepth[pile.toNat]'hpile = 0
  · -- Empty pile: the run is `cleanupPile_empty_eq`; the depth write is a no-op,
    -- the flute write realizes exactly the normalization the precondition is
    -- stated about, and the base layer ignores `freePiles`.
    have hrun := cleanupPile_empty_eq pile g p hpile hd
    have hsd : p.pileDepth.set pile.toNat 0 hpile = p.pileDepth := by
      conv_lhs => rw [← hd]
      exact Vector.set_getElem_self hpile
    refine ⟨0xffff, _, hrun, ?_⟩
    simp only [hsd]
    exact nf_setFreePiles hnf _
  · -- Loop-bearing case: `pileDepth[pile] > 0`.
    -- (`fluteNorm` only changes `pileFlute`, so all depth/aces facts of `hnf`
    -- transfer to `p` definitionally.)
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
      have htiB : B.toInt8.toInt = (B.toNat : Int) := by
        have h' : B.toInt8.toInt = ((B.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
          show B.toInt8.toBitVec.toInt = _
          rw [BitVec.toInt_eq_toNat_bmod]
          rfl
        rw [UInt8.toUInt8_toInt8] at h'
        rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
      have h1 : (B.toNat : Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
        rwa [htiB] at hge
      have hgeNat : B.toNat ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
        rw [Int8.toNat_toUInt8_of_le haces0, (Int8.toNat_toInt (p.aces[(SUIT B).toUInt32.toNat]'hs4)).symm]
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
            have hbdg1 : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
            show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat <
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat
            omega)
      exact hnfB hfree
    -- Every same-suit card `aces[SUIT B]` represents lies within `SUIT B`'s
    -- own 16-wide code block (never below it) — the counterpart lower bound
    -- to `foundation_cards_free`'s implicit upper range, needed to rule out
    -- the freed loop (and, later, the lone-king branch) crossing into a
    -- different suit's card block.
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
    obtain ⟨m, f, hmg, hmx, hfg, hfx, hrun⟩ :=
      cleanupPile_nonempty_eq pile g p B (pileHashes[pile.toNat]'hpile) hpile rfl
        hd1 hd5 hidx hBdef.symm hs4 hprev64 hwf.card2pile_lt haces0
    refine ⟨_, _, hrun, ?_⟩
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
    have hmofI : (Int32.ofNat m).toInt = (m : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hdepth1I : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[pile.toNat]'hpile).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
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
    -- Tighter than `hf_le`: the freed loop never crosses into a lower suit's
    -- card block either — at step `VALUE(B)−1` the walked card would be
    -- exactly the value-0 sentinel of `SUIT B`, contradicting `haces_ge`.
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
          ((UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toNat : Int) := by
        have h' : (UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toInt8.toInt =
            (((UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toInt8.toUInt8.toNat : Int)
              ).bmod (2 ^ 8) := by
          show (UInt8.ofNat (16 * (SUIT B).toUInt32.toNat)).toInt8.toBitVec.toInt = _
          rw [BitVec.toInt_eq_toNat_bmod]
          rfl
        rw [UInt8.toUInt8_toInt8] at h'
        rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
      have hlt := Int8.lt_iff_toInt_lt.mp hg
      rw [hti, hcardnat] at hlt
      have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
        Int8.toNat_toUInt8_of_le haces0
      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
      omega
    have hf60 : f ≤ 60 := by omega
    have hfofI : (Int32.ofNat f).toInt = (f : Int) := by
      rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hfof8 : (UInt8.ofNat f).toNat = f := by
      rw [UInt8.toNat_ofNat']; omega
    have hprev2 : (B - 1 - UInt8.ofNat f).toNat = B.toNat - 1 - f := by
      have hle : UInt8.ofNat f ≤ B - 1 := by
        rw [UInt8.le_iff_toNat_le, hfof8, UInt8.toNat_sub_of_le _ _ h1B,
          show ((1 : UInt8).toNat = 1) from rfl]
        omega
      rw [UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_sub_of_le _ _ h1B, hfof8,
        show ((1 : UInt8).toNat = 1) from rfl]
    -- The final flute value `1 + m + f` is small, so all its casts are exact.
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
    -- ------------------------------------------------------------------
    -- Clause discharge over `cleanupRunResult`.  Base-NF ignores `busyAces`,
    -- so the busyAces branch collapses via `nf_setBusyAces`; the lone-king
    -- branch is a genuine case split.
    -- ------------------------------------------------------------------
    simp only [cleanupRunResult]
    by_cases hk : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1
        && VALUE (B + UInt8.ofNat m) == 13) = true
    · -- Lone-king branch.
      have key : SolverInvBase g
          { p with
            hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) -
              (pileHashes[pile.toNat]'hpile),
            usedSpace := p.usedSpace - Int8.ofNat f +
              (1 + Int32.ofNat m + Int32.ofNat f).toInt8,
            freePiles := p.freePiles + 1,
            kings := p.kings.set (SUIT B).toUInt32.toNat
              (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4,
            pileDepth := p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile,
            pileFlute := p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile,
            busyAces := p.busyAces |||
              (if (p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f).toInt8)
                then (1 : UInt8) <<< SUIT B else 0) } := by
        have hdec : ∀ i : Fin 10,
            (((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile).get i)).toInt.toNat ≤
            ((fluteNorm pile hpile p).pileDepth.get i).toInt.toNat := by
          intro i
          show ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[i.val]'i.isLt
            ).toInt.toNat ≤ (p.pileDepth[i.val]'i.isLt).toInt.toNat
          by_cases hip : pile.toNat = i.val
          · simp only [← hip, Vector.getElem_set_self]
            rw [show (((0 : Int32).toInt8).toInt.toNat = 0) from rfl]
            exact Nat.zero_le _
          · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
        have hk1 : (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m = 1 := by
          rw [Bool.and_eq_true] at hk
          exact eq_of_beq hk.1
        have hd0c : (p.pileDepth[pile.toNat]'hpile).toInt.toNat = m + 1 := by
          have hz := congrArg Int32.toInt hk1
          rw [hdepth1I, Int32.toInt_one] at hz
          show (p.pileDepth[pile.toNat]'hpile).toInt.toNat = m + 1
          omega
        -- Shared facts about `kings[SUIT B]` at entry, needed by BOTH
        -- `aces_kings_valid` (to know the value being decremented) and
        -- `king_frontier` (to know the new value stays a valid frontier):
        -- the lone-king branch fires exactly when the merged run's boundary
        -- `B+m` IS the king (`hk`'s 2nd conjunct); since `B+m` is still the
        -- pile's own (not-yet-written) boundary at this point, it isn't
        -- free, so `king_frontier`'s unconditional `∀c` clause forces
        -- `kings[SUIT B]=B+m` exactly (same suit, and value pinned to 13 by
        -- `¬isFreeCard(B+m)` ruling out `<13`, `≤13` from `aces_kings_valid`).
        have hkv13 : VALUE (B + UInt8.ofNat m) = 13 := by
          rw [Bool.and_eq_true] at hk
          exact eq_of_beq hk.2
        have hcard_pos_m : ∃ hidxm : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 1).toUInt32.toNat < 5,
            (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
              Int32.ofNat m - 1).toUInt32.toNat]'hidxm = B + UInt8.ofNat m := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0
            simp only [show Int32.ofNat 0 = 0 from rfl, Int32.sub_zero,
              show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
            exact ⟨hidx, hBdef.symm⟩
          · exact merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
              (p.pileDepth[pile.toNat]'hpile).toInt32 m p
              (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
              hmg m hmpos (le_refl m)
        obtain ⟨hidxm, heqm⟩ := hcard_pos_m
        have hidx0eq : (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 = 0 := by
          rw [hk1]; decide
        have hidxNat0 : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
            Int32.ofNat m - 1).toUInt32.toNat = 0 := by
          rw [hidx0eq]; decide
        have hcardEqK : (g.pos2card[pile.toNat]'hpile)[(0 : Nat)]'(by omega) =
            B + UInt8.ofNat m := by
          have hstep : (g.pos2card[pile.toNat]'hpile)[(0 : Nat)]'(by omega) =
              (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
            congr 1
            omega
          rw [hstep, heqm]
        have hnfreeKM : ¬ isFreeCard g (fluteNorm pile hpile p) (B + UInt8.ofNat m) := by
          rw [← hcardEqK]
          exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩ ⟨0, by omega⟩ (by
            show (0 : Nat) < (p.pileDepth[pile.toNat]'hpile).toInt.toNat
            omega)
        have hrcm := merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
          (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
          (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
          hmg m (le_refl m)
        have hSmEq : SUIT (B + UInt8.ofNat m) = SUIT B := by
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
        have hak : SUIT (p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8 =
              (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 ∧
            (VALUE (p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat ≤ 13 ∧
            SUIT (p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8 =
              (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 ∧
            (VALUE (p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat ≤ 13 ∧
            p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) ≤
              p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) :=
          hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
        -- `king_frontier`'s `∀c`-clause is unconditional (doesn't depend on
        -- which of its "case" disjuncts holds), so `¬isFreeCard(B+m)`
        -- (`hnfreeKM`) directly pins `VALUE(kings[s])=13`, hence
        -- `kings[s]=B+m` by same suit+value — no case split needed at all.
        have hall : ∀ c : UInt8,
            SUIT c = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 →
            (VALUE c).toNat > (VALUE (p.kings.get
                (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat →
            (VALUE c).toNat ≤ 13 →
            isFreeCard g (fluteNorm pile hpile p) c :=
          (hnf.king_frontier ⟨(SUIT B).toUInt32.toNat, hs4⟩).2
        have hgetEqA : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
            p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
        have hgetEqK : p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
            p.kings[(SUIT B).toUInt32.toNat]'hs4 := rfl
        have hSeqBm : SUIT (B + UInt8.ofNat m) =
            (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := by
          rw [hSmEq]; exact hsuiteq
        have hBmEq : p.kings[(SUIT B).toUInt32.toNat]'hs4 = (B + UInt8.ofNat m).toInt8 := by
          have hVKle13 : (VALUE ((p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat
              ≤ 13 := by rw [← hgetEqK]; exact hak.2.2.2.1
          have hVKge13 : (VALUE ((p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat
              ≥ 13 := by
            by_contra hlt
            push Not at hlt
            have hgt : (VALUE (B + UInt8.ofNat m)).toNat >
                (VALUE ((p.kings.get ⟨(SUIT B).toUInt32.toNat, hs4⟩).toUInt8)).toNat := by
              rw [hgetEqK, hkv13]
              have h13 : (13 : UInt8).toNat = 13 := rfl
              omega
            have hisfree := hall (B + UInt8.ofNat m) hSeqBm hgt (by rw [hkv13]; decide)
            exact hnfreeKM hisfree
          have hVKeq13 : (VALUE ((p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8)).toNat
              = 13 := by omega
          have hSKeq : SUIT ((p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
            rw [← hgetEqK, hak.2.2.1]
            exact hsuiteq.symm
          have hVBm13 : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by rw [hkv13]; rfl
          have hcardeq : (p.kings[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
              B + UInt8.ofNat m :=
            card_eq_of_suit_value _ _ (by rw [hSKeq, hSmEq]) (by rw [hVKeq13, hVBm13])
          have hlift := congrArg UInt8.toInt8 hcardeq
          rwa [Int8.toInt8_toUInt8] at hlift
        have htiBm : (B + UInt8.ofNat m).toInt8.toInt = (B.toNat + m : Int) := by
          have h' : (B + UInt8.ofNat m).toInt8.toInt =
              (((B + UInt8.ofNat m).toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
            show (B + UInt8.ofNat m).toInt8.toBitVec.toInt = _
            rw [BitVec.toInt_eq_toNat_bmod]
            rfl
          rw [UInt8.toUInt8_toInt8] at h'
          have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
          have hlt256 : B.toNat + m < 256 := by omega
          have hadd : (B + UInt8.ofNat m).toNat = B.toNat + m := by
            rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt256]
          rw [h', hadd, Int.bmod_eq_of_le (by omega) (by omega)]
          push_cast
          omega
        have htiBf : (B - 1 - UInt8.ofNat f).toInt8.toInt = (B.toNat - 1 - f : Int) := by
          have h' : (B - 1 - UInt8.ofNat f).toInt8.toInt =
              (((B - 1 - UInt8.ofNat f).toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
            show (B - 1 - UInt8.ofNat f).toInt8.toBitVec.toInt = _
            rw [BitVec.toInt_eq_toNat_bmod]
            rfl
          rw [UInt8.toUInt8_toInt8] at h'
          rw [h', hprev2, Int.bmod_eq_of_le (by omega) (by omega)]
          omega
        have hSubEq : ((B + UInt8.ofNat m).toInt8 -
            (1 + Int32.ofNat m + Int32.ofNat f).toInt8).toInt = (B.toNat - 1 - f : Int) := by
          rw [Int8.toInt_sub, Int32.toInt_toInt8, hfl32I]
          have hb : ((1 : Int) + (m : Int) + (f : Int)).bmod (2 ^ 8) = 1 + (m : Int) + f :=
            Int.bmod_eq_of_le (by omega) (by omega)
          rw [hb, htiBm, Int.bmod_eq_of_le (by omega) (by omega)]
          omega
        -- The new `kings[SUIT B]` write, evaluated exactly (`B-1-f`), and its
        -- suit preservation / relation to `aces[SUIT B]` — shared between
        -- `aces_kings_valid`'s own construction and `king_frontier`'s
        -- reasoning about the same slot.
        have hnk : p.kings[(SUIT B).toUInt32.toNat]'hs4 -
            (1 + Int32.ofNat m + Int32.ofNat f).toInt8 = (B - 1 - UInt8.ofNat f).toInt8 := by
          rw [hBmEq]
          apply Int8.toInt_inj.mp
          rw [hSubEq, htiBf]
        have hSK : SUIT (B - 1 - UInt8.ofNat f) = SUIT B := by
          apply UInt8.toNat_inj.mp
          have hb1 := SUIT_toNat (B - 1 - UInt8.ofNat f)
          have hb2 := SUIT_toNat B
          have hb3 := VALUE_toNat B
          have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
          omega
        have haces_le_new_king : p.aces[(SUIT B).toUInt32.toNat]'hs4 ≤
            (B - 1 - UInt8.ofNat f).toInt8 := by
          rcases Nat.eq_zero_or_pos f with hf0 | hfpos
          · subst hf0
            have heq0 : B - 1 - UInt8.ofNat 0 = B - 1 := by
              simp only [show UInt8.ofNat 0 = 0 from rfl, UInt8.sub_zero]
            rw [heq0]
            have htiBm1 : (B - 1).toInt8.toInt = (B.toNat - 1 : Int) := by
              have h' : (B - 1).toInt8.toInt =
                  (((B - 1).toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                show (B - 1).toInt8.toBitVec.toInt = _
                rw [BitVec.toInt_eq_toNat_bmod]
                rfl
              rw [UInt8.toUInt8_toInt8] at h'
              rw [h', UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl,
                Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            have htiB : B.toInt8.toInt = (B.toNat : Int) := by
              have h' : B.toInt8.toInt = ((B.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                show B.toInt8.toBitVec.toInt = _
                rw [BitVec.toInt_eq_toNat_bmod]
                rfl
              rw [UInt8.toUInt8_toInt8] at h'
              rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
            rw [Int8.le_iff_toInt_le, htiBm1]
            have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
            rw [htiB] at hlt
            omega
          · have hg := (hfg (f - 1) (by omega)).1 hs4
            have hlm1of : (UInt8.ofNat (f - 1)).toNat = f - 1 := by
              rw [UInt8.toNat_ofNat']; omega
            have hfof : (UInt8.ofNat f).toNat = f := by rw [UInt8.toNat_ofNat']; omega
            have hstepEq : (B - 1) - UInt8.ofNat (f - 1) = B - UInt8.ofNat f := by
              apply UInt8.toNat_inj.mp
              have hle1 : UInt8.ofNat (f - 1) ≤ B - 1 := by
                rw [UInt8.le_iff_toNat_le, hlm1of,
                  UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
                omega
              have hlel : UInt8.ofNat f ≤ B := by
                rw [UInt8.le_iff_toNat_le, hfof]; omega
              rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B,
                hlm1of, show ((1 : UInt8).toNat = 1) from rfl,
                UInt8.toNat_sub_of_le _ _ hlel, hfof]
              omega
            rw [show freedIter (f - 1) (⟨1 + Int32.ofNat m,
                { p with hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) },
                B - 1⟩ : FreedAcc) = ⟨_, _, (B - 1) - UInt8.ofNat (f - 1)⟩
                from freedIter_eq _ _] at hg
            rw [hstepEq] at hg
            have htiBmf : (B - UInt8.ofNat f).toInt8.toInt = (B.toNat - f : Int) := by
              have h' : (B - UInt8.ofNat f).toInt8.toInt =
                  (((B - UInt8.ofNat f).toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                show (B - UInt8.ofNat f).toInt8.toBitVec.toInt = _
                rw [BitVec.toInt_eq_toNat_bmod]
                rfl
              rw [UInt8.toUInt8_toInt8] at h'
              rw [h', UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hfof]; omega),
                hfof, Int.bmod_eq_of_le (by omega) (by omega)]
              omega
            have hg2 : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat f).toInt8 := hg
            have hlt := Int8.lt_iff_toInt_lt.mp hg2
            rw [htiBmf] at hlt
            rw [Int8.le_iff_toInt_le, htiBf]
            omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- pileBase (0)/(0b)/(3)/(3a)/(3c): bundle the base per-pile facts.
          -- The cleaned pile is written depth 0 / flute 1; other piles
          -- transfer unchanged from `hnf`.
          intro i
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- (0) pileDepth_bound
            show ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[i.val]'i.isLt
              ).toInt.toNat ≤ 5
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              decide
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              exact hnf.pileDepth_bound i
          · -- (0b) pileDepth_nonneg
            show (0 : Int8) ≤ (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[i.val]'i.isLt
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              decide
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              exact hnf.pileDepth_nonneg i
          · -- (3) flute_pos: the vacated pile is rewritten to flute 1.
            show 1 ≤ ((p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile
              )[i.val]'i.isLt).toNat
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              decide
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              have h := hnf.flute_pos i
              have h' : 1 ≤ ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat := h
              rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at h'
          · -- (3) flute_empty: the vacated pile has flute 1; other piles unchanged.
            intro hdep
            show ((p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile
              )[i.val]'i.isLt) = 1
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              decide
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              have hdep' : (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                  )[i.val]'i.isLt = 0 := hdep
              rw [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdep'
              have h := hnf.flute_empty i hdep'
              have h' : ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt) = 1 := h
              rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at h'
          · -- (3a) flute_cards_free: the vacated pile has depth 0, so its own
            -- instance is vacuous; other piles transfer via `isFreeCard_mono`.
            intro j hdi hj0 hjlt
            by_cases hip : pile.toNat = i.val
            · exfalso
              have hdi' : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[i.val]'i.isLt
                  ).toInt.toNat > 0 := hdi
              simp only [← hip, Vector.getElem_set_self] at hdi'
              exact absurd hdi' (by decide)
            · have h1' : ((fluteNorm pile hpile p).pileDepth[i.val]'i.isLt).toInt.toNat > 0 := by
                show (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0
                have hdi' : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat > 0 := hdi
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdi'
              have h3' : j.toNat < ((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt).toNat := by
                show j.toNat < ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                have hj' : j.toNat < ((p.pileFlute.set pile.toNat
                    (1 : Int32).toUInt32.toUInt8 hpile)[i.val]'i.isLt).toNat := hjlt
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hj'
              have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'(by
                      have h5 : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                          )[i.val]'i.isLt).toInt.toNat ≤ 5 := by
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                        exact hnf.pileDepth_bound i
                      omega)
                  = (g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    (by
                      have h5 : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 :=
                        hnf.pileDepth_bound i
                      omega) := by
                congr 1
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              show isFreeCard g _
                ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'(by
                      have h5 : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                          )[i.val]'i.isLt).toInt.toNat ≤ 5 := by
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                        exact hnf.pileDepth_bound i
                      omega) - j)
              rw [hcardEq3]
              exact isFreeCard_mono hdec (hnf.flute_cards_free i j h1' hj0 h3')
          · -- (3c) flute_not_aces: the vacated pile has depth 0, so its own
            -- instance is vacuous; other piles transfer unchanged (aces are
            -- never touched by cleanup, and `i ≠ pile`'s depth/flute/boundary
            -- are untouched by this branch).
            intro j hdi hj0 hjlt
            by_cases hip : pile.toNat = i.val
            · exfalso
              have hdi' : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[i.val]'i.isLt
                  ).toInt.toNat > 0 := hdi
              simp only [← hip, Vector.getElem_set_self] at hdi'
              exact absurd hdi' (by decide)
            · have h1' : ((fluteNorm pile hpile p).pileDepth[i.val]'i.isLt).toInt.toNat > 0 := by
                show (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0
                have hdi' : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat > 0 := hdi
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdi'
              have h3' : j.toNat < ((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt).toNat := by
                show j.toNat < ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                have hj' : j.toNat < ((p.pileFlute.set pile.toNat
                    (1 : Int32).toUInt32.toUInt8 hpile)[i.val]'i.isLt).toNat := hjlt
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hj'
              -- Shared index-bound proofs, named once and reused, so the term
              -- below doesn't re-elaborate the same `omega` proof many times.
              have hb5_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 := hnf.pileDepth_bound i
              have hb5_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat ≤ 5 := by
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]; exact hb5_old
              have hidx_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
              have hidx_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
              have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                  = (g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    hidx_old := by
                congr 1
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              show ∀ hs : (SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat < 4,
                p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat,
                  hs⟩ <
                  ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                      (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                    - j).toInt8
              intro hs
              have hval : (SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat
                  = (SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    hidx_old)).toNat :=
                congrArg (fun c => (SUIT c).toNat) hcardEq3
              have hs' : (SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt
                  ).toInt.toNat - 1]'hidx_old)).toNat < 4 := hval ▸ hs
              have hres := hnf.flute_not_aces i j h1' hj0 h3' hs'
              have hEq2 : p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat,
                  hs⟩ =
                p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt
                    ).toInt.toNat - 1]'hidx_old)).toNat, hs'⟩ := by
                congr 1
                exact Fin.ext hval
              rw [hEq2, hcardEq3]
              exact hres
        · -- suitClean
          intro s
          refine ⟨?_, ?_, ?_, ?_⟩
          · -- (1) aces_kings_valid: aces untouched (suit/value bounds transfer
            -- directly); for kings, only `SUIT B`'s slot changes, from `B+m`
            -- (`hBmEq`, shared preamble) to `B-1-f`, whose suit is `SUIT B`
            -- by `hf_le_tight` (never crosses below the suit's own value-0
            -- card).
            by_cases hip : (SUIT B).toUInt32.toNat = s.val
            · have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hip
              subst hseq
              refine ⟨hak.1, hak.2.1, ?_, ?_, ?_⟩
              · show SUIT ((p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                    )[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
                  (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8
                rw [Vector.getElem_set_self, hnk, UInt8.toUInt8_toInt8, hSK]
                exact hsuiteq
              · show (VALUE ((p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                    )[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat ≤ 13
                rw [Vector.getElem_set_self, hnk, UInt8.toUInt8_toInt8]
                have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                have hb2 := VALUE_toNat B
                have hv1 : 1 ≤ (VALUE B).toNat := hreal.2.1
                have hv13 : (VALUE B).toNat ≤ 13 := hreal.2.2
                omega
              · show p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) ≤
                  (p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                  )[(SUIT B).toUInt32.toNat]'hs4
                rw [Vector.getElem_set_self, hnk, hgetEqA]
                exact haces_le_new_king
            · refine ⟨(hnf.aces_kings_valid s).1, (hnf.aces_kings_valid s).2.1, ?_, ?_, ?_⟩ <;>
                rw [show ((p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s) =
                    p.kings.get s from Vector.getElem_set_ne hs4 s.isLt hip]
              exacts [(hnf.aces_kings_valid s).2.2.1, (hnf.aces_kings_valid s).2.2.2.1,
                (hnf.aces_kings_valid s).2.2.2.2]
          · -- (4a) foundation_cards_free: aces unchanged, freeness monotone.
            intro c h1 h2 h3
            exact isFreeCard_mono hdec (hnf.foundation_cards_free s c h1 h2 h3)
          · -- (4b-weak) foundation_maximal_weak: `aces` is untouched, so only
            -- `SUIT B`'s own witness can be disturbed by this cleanup (every
            -- card revealed by the pile's depth change is same-suit as `B`, via
            -- `hSjEq`/`hPosGen` above).  We dispose of the `VALUE=13` disjunct
            -- up front (independent of which disjunct `hnf` actually hands us),
            -- so every later step gets `VALUE(aces[s]+1) ≤ 13`, i.e. `aces[s]+1`
            -- is a genuine real card.
            -- Hoisted from the king_frontier bullet below (also needed by the
            -- foundation_maximal_weak bullet): the pile is entirely occupied
            -- by the merged same-suit run B..B+m.
            have hRCgen : ∀ j : Nat, j ≤ m →
                (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
              (merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
                (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
                (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                hmg j hjm).2
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
            have hd0cI : (p.pileDepth[pile.toNat]'hpile).toInt32.toInt = (m + 1 : Nat) := by
              rw [Int8.toInt_toInt32]
              have hbdg : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                  (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
              omega
            have hPosGen : ∀ idx : Nat, idx ≤ m → ∃ hidx5 : idx < 5,
                (g.pos2card[pile.toNat]'hpile)[idx]'hidx5 = B + UInt8.ofNat (m - idx) := by
              intro idx hidxm
              rcases Nat.eq_zero_or_pos (m - idx) with hj0 | hjpos
              · refine ⟨by omega, ?_⟩
                rw [hj0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
                have hsub1 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
                    (p.pileDepth[pile.toNat]'hpile).toInt32.toInt - 1 := by
                  rw [Int32.toInt_sub_of_le _ _ (by decide)
                    (by rw [Int32.le_iff_toInt_le, hd0cI,
                      show ((1 : Int32).toInt = 1) from by decide]; omega),
                    show ((1 : Int32).toInt = 1) from by decide]
                have hidx0m : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat = idx := by
                  rw [Int32.toNat_toUInt32_of_le (by
                    rw [Int32.le_iff_toInt_le, hsub1, hd0cI,
                      show ((0 : Int32).toInt = 0) from by decide]; omega)]
                  show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat = idx
                  rw [hsub1, hd0cI]
                  omega
                rw [show (g.pos2card[pile.toNat]'hpile)[idx]'(by omega) =
                    (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
                      ).toUInt32.toNat]'hidx from by congr 1; omega]
              · obtain ⟨hidxj, heqj⟩ := merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m p
                  (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                  hmg (m - idx) hjpos (by omega)
                have hiN : (Int32.ofNat idx).toInt = (idx : Int) := by
                  rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
                  exact Int.bmod_eq_of_le (by omega) (by omega)
                have hposEq : (p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat (m - idx) - 1 = Int32.ofNat idx := by
                  apply Int32.toInt_inj.mp
                  have hd0le5 : (p.pileDepth[pile.toNat]'hpile).toInt32.toInt ≤ 5 := by
                    rw [Int8.toInt_toInt32]; exact hd5
                  have hilt : ((m - idx : Nat) : Int) + 1 ≤
                      (p.pileDepth[pile.toNat]'hpile).toInt32.toInt := by
                    rw [hd0cI]; omega
                  have hstep : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (m - idx) - 1).toInt =
                      (p.pileDepth[pile.toNat]'hpile).toInt32.toInt - ((m - idx : Nat) : Int) - 1 :=
                    depth_sub_ofNat_sub_one_eq hd0le5 hilt
                  rw [hstep, hiN, hd0cI]
                  omega
                have hidxNat : (Int32.ofNat idx).toUInt32.toNat = idx := by
                  rw [Int32.toNat_toUInt32_of_le (by
                    rw [Int32.le_iff_toInt_le, show ((0:Int32).toInt=0) from by decide, hiN]
                    omega)]
                  show (Int32.ofNat idx).toInt.toNat = idx
                  rw [hiN]
                  omega
                have hIdxEq : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat (m - idx) - 1).toUInt32.toNat = idx := by
                  rw [hposEq]; exact hidxNat
                refine ⟨by omega, ?_⟩
                rw [show (g.pos2card[pile.toNat]'hpile)[idx]'(by omega) =
                    (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (m - idx) - 1).toUInt32.toNat]'hidxj from by
                      congr 1; exact hIdxEq.symm]
                exact heqj
            by_cases hAV13 : (VALUE (p.aces.get s).toUInt8).toNat = 13
            · exact Or.inl hAV13
            · have hvalid : SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 ∧
                  (VALUE (p.aces.get s).toUInt8).toNat ≤ 13 ∧
                  SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 ∧
                  (VALUE (p.kings.get s).toUInt8).toNat ≤ 13 ∧
                  p.aces.get s ≤ p.kings.get s := hnf.aces_kings_valid s
              have hAV12 : (VALUE (p.aces.get s).toUInt8).toNat ≤ 12 := by
                have := hvalid.2.1; omega
              have hVlt15 : (VALUE (p.aces.get s).toUInt8).toNat < 15 := by omega
              have hSA : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT (p.aces.get s).toUInt8 :=
                SUIT_succ _ hVlt15
              have hVA : (VALUE ((p.aces.get s).toUInt8 + 1)).toNat =
                  (VALUE (p.aces.get s).toUInt8).toNat + 1 := VALUE_succ _ hVlt15
              have hSAeqSval : SUIT ((p.aces.get s).toUInt8 + 1) = s.val.toUInt8 :=
                hSA.trans hvalid.1
              have hs4v : s.val < 4 := s.isLt
              have hsvalNat : s.val.toUInt8.toNat = s.val := by
                rw [UInt8.toNat_ofNat']; omega
              have hrealA : IsRealCard ((p.aces.get s).toUInt8 + 1) := by
                refine ⟨?_, by omega, by omega⟩
                have hSct := congrArg UInt8.toNat hSAeqSval
                omega
              have hc64 : ((p.aces.get s).toUInt8 + 1).toNat < 64 := by
                have hb1 := VALUE_toNat ((p.aces.get s).toUInt8 + 1)
                have hb2 := SUIT_toNat ((p.aces.get s).toUInt8 + 1)
                have hb3 := congrArg UInt8.toNat hSAeqSval
                omega
              have hp64 : (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat < 10 := by
                unfold cardPile; rw [dif_pos hc64]; exact hwf.card2pile_lt _ hc64
              by_cases hSB : (SUIT B).toUInt32.toNat = s.val
              · -- `s` is `SUIT B`'s own index: the frontier's own suit.
                have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSB
                subst hseq
                have hSAeqB : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) = SUIT B := by
                  have h' : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                      (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := hSAeqSval
                  rw [h']; exact hsuiteq.symm
                have hc64 : ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1).toNat < 64 := hc64
                have hp64 : (cardPile g ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat <
                    10 := hp64
                have hrealA : IsRealCard ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) :=
                  hrealA
                have hVA : (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat =
                    (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat + 1 := hVA
                have hAV12 : (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat ≤ 12 :=
                  hAV12
                have hSA : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                    SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 := hSA
                have hSAeqAces : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = SUIT B :=
                  hSA.symm.trans hSAeqB
                -- Shared escape hatch: once `A := aces[SUIT B]+1` is pinned to
                -- `B` exactly, the *new* king value `B-1-f` is automatically
                -- `< VALUE A = VALUE B` (disjunct 4), regardless of `f`.
                have hescape : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B →
                    p.aces[(SUIT B).toUInt32.toNat]'hs4 = (p.kings.set (SUIT B).toUInt32.toNat
                      (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                        (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4)[(SUIT B).toUInt32.toNat]'hs4 := by
                  intro hAB
                  rw [Vector.getElem_set_self, hnk]
                  sorry
                rcases hnf.foundation_maximal_weak
                    (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkltA
                · exact absurd h13 hAV13
                · -- disjunct 2 (old): pin down whether `A` sits in `pile` itself.
                  have hnfreeOld : ¬ isFreeCard g p
                      ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) := hnfreeA
                  by_cases hcp : (cardPile g ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                      ).toNat = pile.toNat
                  · have hcd5 : (cardDepth g
                        ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat < 5 := by
                      by_contra hcon
                      push Not at hcon
                      have hle5 := hwf.depth_le _ hrealA
                      have heq5 : (cardDepth g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat = 5 := by omega
                      apply hnfreeOld
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      rw [heq5]
                      exact hnf.pileDepth_bound ⟨(cardPile g
                        ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat, hp64⟩
                    have hrt := hwf.round_trip _ hrealA hcd5
                    obtain ⟨hidxg, heqg⟩ := hPosGen (cardDepth g
                        ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat (by
                      by_contra hgtm
                      push Not at hgtm
                      apply hnfreeOld
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      have heqIdx : p.pileDepth[(cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hp64 =
                          p.pileDepth[pile.toNat]'hpile := by congr 1
                      rw [heqIdx, hd0c]; omega)
                    have hcardEq : (g.pos2card[pile.toNat]'hpile)[(cardDepth g
                        ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hidxg
                        = (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 := by
                      have hbracket : (g.pos2card.get ⟨(cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat, hp64⟩).get
                          ⟨(cardDepth g
                            ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat, hcd5⟩ =
                          (g.pos2card[(cardPile g
                            ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hp64)[
                              (cardDepth g
                                ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hcd5 :=
                        rfl
                      rw [hbracket] at hrt
                      rw [show (g.pos2card[(cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hp64)[
                            (cardDepth g
                              ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hcd5 =
                          (g.pos2card[pile.toNat]'hpile)[(cardDepth g
                            ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hidxg
                          from by congr 1; congr 1] at hrt
                      exact hrt
                    rw [heqg] at hcardEq
                    set k := m - (cardDepth g
                        ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat with hkdef
                    have hVeq2 := hRCgen k (by omega)
                    have hVeqCard := congrArg (fun x : UInt8 => (VALUE x).toNat) hcardEq
                    by_cases hk0 : k = 0
                    · refine Or.inr (Or.inr (Or.inr (hescape ?_)))
                      rw [hk0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero] at hcardEq
                      exact hcardEq.symm
                    · -- `k ≥ 1`: `aces[SUIT B] ≥ B`, contradicting `haces_lt_B`.
                      exfalso
                      have hb1 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                      have hb2 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                      have hb3 := congrArg UInt8.toNat hSAeqB
                      have hb4 := SUIT_toNat B
                      have hb5 := VALUE_toNat B
                      have hb0v := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
                      have hb0s := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
                      have hb3' := congrArg UInt8.toNat hSAeqAces
                      have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
                      have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
                      have htiB : B.toInt8.toInt = (B.toNat : Int) := by
                        have h' : B.toInt8.toInt = ((B.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                          show B.toInt8.toBitVec.toInt = _
                          rw [BitVec.toInt_eq_toNat_bmod]
                          rfl
                        rw [UInt8.toUInt8_toInt8] at h'
                        rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
                      rw [htiB] at hlt
                      have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
                        Int8.toNat_toUInt8_of_le haces0
                      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
                      omega
                  · refine Or.inr (Or.inl ?_)
                    show ¬ isFreeCard g _ ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                    intro hfreeNew
                    apply hnfreeOld
                    have hge := isFree_to_cardDepth_ge g _ hwf
                      ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) hc64 hp64 hfreeNew
                    have heqD : (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                        (cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hp64 =
                        p.pileDepth[(cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat]'hp64 :=
                      Vector.getElem_set_ne hpile hp64 (Ne.symm hcp)
                    rw [heqD] at hge
                    exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
                · -- disjunct 3 (old): the flute-top witness pile `i`.
                  by_cases hip : pile.toNat = i.val
                  · -- `i = pile`: the normalized entry's own flute is `1`, so the
                    -- witness forces `A = B` exactly.
                    have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
                    subst hieq
                    have hdi' : (0 : Int8) < p.pileDepth[pile.toNat]'hpile := by
                      have h : (0 : Int8) <
                          (fluteNorm pile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩ := by
                        have hpos : (0 : Nat) <
                            ((fluteNorm pile hpile p).pileDepth.get
                              ⟨pile.toNat, hpile⟩).toInt.toNat := hdi
                        have hnn' : (0 : Int8) ≤
                            (fluteNorm pile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩ :=
                          hnf.pileDepth_nonneg ⟨pile.toNat, hpile⟩
                        rw [Int8.lt_iff_toInt_lt, show ((0 : Int8).toInt = 0) from rfl]
                        rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at hnn'
                        show (0 : Int) < ((fluteNorm pile hpile p).pileDepth.get
                          ⟨pile.toNat, hpile⟩).toInt
                        have hbdg : ((fluteNorm pile hpile p).pileDepth.get
                            ⟨pile.toNat, hpile⟩).toInt.toNat =
                          ((fluteNorm pile hpile p).pileDepth.get
                            ⟨pile.toNat, hpile⟩).toInt.toNat := rfl
                        omega
                      exact h
                    have hfluteEq : (fluteNorm pile hpile p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
                      show (p.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile = 1
                      rw [Vector.getElem_set_self]
                    have heqA' : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
                      (g.pos2card[pile.toNat]'hpile)[
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                          have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) - 1 := by
                      have h := heqA
                      rw [hfluteEq] at h
                      exact h
                    have hposB : (g.pos2card[pile.toNat]'hpile)[
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                          have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) = B := by
                      obtain ⟨hidx5, heqpm⟩ := hPosGen m (le_refl m)
                      have hmeq : (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 = m := by omega
                      rw [show (g.pos2card[pile.toNat]'hpile)[
                          (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                            have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) =
                          (g.pos2card[pile.toNat]'hpile)[m]'hidx5 from by congr 1]
                      rw [heqpm, show m - m = 0 from by omega, show UInt8.ofNat 0 = 0 from rfl,
                        UInt8.add_zero]
                    rw [hposB] at heqA'
                    --exact Or.inr (Or.inr (Or.inr (hescape heqA'.symm)))
                    sorry
                  · -- `i ≠ pile`: this witness pile is untouched by the cleanup.
                    refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
                    · show ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat > 0
                      rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                      have hdi' : (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0 := hdi
                      exact hdi'
                    · have hb5_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 :=
                        hnf.pileDepth_bound i
                      have hidx_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                      have hb5_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat ≤ 5 := by
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]; exact hb5_old
                      have hidx_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                      have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                            (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                          = (g.pos2card[i.val]'i.isLt)[
                            (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'hidx_old := by
                        congr 1
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                      have hfluteBridge2 : (fluteNorm pile hpile p).pileFlute[i.val]'i.isLt =
                          p.pileFlute[i.val]'i.isLt := by
                        show (p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt =
                          p.pileFlute[i.val]'i.isLt
                        exact Vector.getElem_set_ne hpile i.isLt (by omega)
                      --have heqAb : (g.pos2card[i.val]'i.isLt)[
                      --    (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'hidx_old -
                      --    (((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt) - 1) =
                      --    (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 := heqA
                      --rw [hfluteBridge2] at heqAb
                      sorry
                      --show (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                      --    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new -
                      --  ((p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile)[
                      --    i.val]'i.isLt - 1) =
                      --  (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1
                      --rw [hcardEq3, Vector.getElem_set_ne hpile i.isLt (by omega)]
                      --exact heqAb
                · -- disjunct 4 (old): `VALUE(kings[SUIT B]) < VALUE A` transfers via
                  -- `VALUE(new kings[SUIT B]) ≤ VALUE(old kings[SUIT B])`.
                  refine Or.inr (Or.inr (Or.inr ?_))
                  --show (VALUE ((p.kings.set (SUIT B).toUInt32.toNat
                  --    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                  --      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                  --    )[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat <
                  --  (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat
                  --rw [Vector.getElem_set_self, hnk, UInt8.toUInt8_toInt8]
                  have hVBf : (VALUE (B - 1 - UInt8.ofNat f)).toNat = (VALUE B).toNat - 1 - f := by
                    have hb5 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                    have hb6 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                    have hb7 := SUIT_toNat B
                    have hb8 := VALUE_toNat B
                    have hSKn := congrArg UInt8.toNat hSK
                    omega
                  have hVBm : (VALUE (B + UInt8.ofNat m)).toNat = (VALUE B).toNat + m :=
                    hRCgen m (le_refl m)
                  --have hkold : (VALUE (p.kings.get
                  --    (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat <
                  --    (VALUE ((p.aces.get
                  --      (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8 + 1)).toNat := hkltA
                  --rw [hgetEqK, hgetEqA, hBmEq, UInt8.toUInt8_toInt8] at hkold
                  --omega
                  sorry
              · -- `s` is a different suit: `kings`/`aces` are untouched for it.
                have hKeqOther : (p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s = p.kings.get s :=
                  Vector.getElem_set_ne hs4 s.isLt hSB
                rcases hnf.foundation_maximal_weak s with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkltA
                · exact absurd h13 hAV13
                · by_cases hcp : (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat = pile.toNat
                  · exfalso
                    have hnfreeOld : ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1) := hnfreeA
                    have hcd5 : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat < 5 := by
                      by_contra hcon
                      push Not at hcon
                      have hle5 := hwf.depth_le _ hrealA
                      have heq5 : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat = 5 := by omega
                      apply hnfreeOld
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      rw [heq5]
                      exact hnf.pileDepth_bound ⟨(cardPile g
                        ((p.aces.get s).toUInt8 + 1)).toNat, hp64⟩
                    have hrt := hwf.round_trip _ hrealA hcd5
                    obtain ⟨hidxg, heqg⟩ := hPosGen (cardDepth g
                        ((p.aces.get s).toUInt8 + 1)).toNat (by
                      by_contra hgtm
                      push Not at hgtm
                      apply hnfreeOld
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      have heqIdx : p.pileDepth[(cardPile g
                          ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 =
                          p.pileDepth[pile.toNat]'hpile := by congr 1
                      rw [heqIdx, hd0c]; omega)
                    have hcardEq : (g.pos2card[pile.toNat]'hpile)[(cardDepth g
                        ((p.aces.get s).toUInt8 + 1)).toNat]'hidxg
                        = (p.aces.get s).toUInt8 + 1 := by
                      have hbracket : (g.pos2card.get ⟨(cardPile g
                          ((p.aces.get s).toUInt8 + 1)).toNat, hp64⟩).get
                          ⟨(cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat, hcd5⟩ =
                          (g.pos2card[(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64)[
                              (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hcd5 :=
                        rfl
                      rw [hbracket] at hrt
                      rw [show (g.pos2card[(cardPile g
                          ((p.aces.get s).toUInt8 + 1)).toNat]'hp64)[
                            (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hcd5 =
                          (g.pos2card[pile.toNat]'hpile)[(cardDepth g
                            ((p.aces.get s).toUInt8 + 1)).toNat]'hidxg
                          from by congr 1; congr 1] at hrt
                      exact hrt
                    rw [heqg] at hcardEq
                    have hSeqk := hSjEq (m - (cardDepth g
                        ((p.aces.get s).toUInt8 + 1)).toNat) (by omega)
                    have hSeqCard := congrArg (fun x : UInt8 => (SUIT x).toUInt32.toNat) hcardEq
                    have hb6 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                      UInt8.toNat_toUInt32 (SUIT B)
                    have hb7 := congrArg UInt8.toNat hSeqk
                    have hb8 := congrArg UInt8.toNat hSAeqSval
                    have hb9 : (SUIT (B + UInt8.ofNat (m - (cardDepth g
                        ((p.aces.get s).toUInt8 + 1)).toNat))).toUInt32.toNat =
                        (SUIT (B + UInt8.ofNat (m - (cardDepth g
                        ((p.aces.get s).toUInt8 + 1)).toNat))).toNat :=
                      UInt8.toNat_toUInt32 _
                    have hb10 : (SUIT ((p.aces.get s).toUInt8 + 1)).toUInt32.toNat =
                        (SUIT ((p.aces.get s).toUInt8 + 1)).toNat := UInt8.toNat_toUInt32 _
                    apply hSB
                    omega
                  · refine Or.inr (Or.inl ?_)
                    show ¬ isFreeCard g _ ((p.aces.get s).toUInt8 + 1)
                    intro hfreeNew
                    apply hnfreeA
                    have hge := isFree_to_cardDepth_ge g _ hwf
                      ((p.aces.get s).toUInt8 + 1) hc64 hp64 hfreeNew
                    have heqD : (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                        (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 =
                        p.pileDepth[(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 :=
                      Vector.getElem_set_ne hpile hp64 (Ne.symm hcp)
                    rw [heqD] at hge
                    exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
                · by_cases hip : pile.toNat = i.val
                  · exfalso
                    have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
                    subst hieq
                    have hfluteEq : (fluteNorm pile hpile p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
                      show (p.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile = 1
                      rw [Vector.getElem_set_self]
                    have heqA' : (g.pos2card[pile.toNat]'hpile)[
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                          have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) -
                        ((1 : UInt8) - 1) = (p.aces.get s).toUInt8 + 1 := by
                      have h := heqA
                      rw [hfluteEq] at h
                      --exact h
                      sorry
                    rw [show ((1 : UInt8) - 1) = 0 from rfl, UInt8.sub_zero] at heqA'
                    have hposB : (g.pos2card[pile.toNat]'hpile)[
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                          have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) = B := by
                      obtain ⟨hidx5, heqpm⟩ := hPosGen m (le_refl m)
                      have hmeq : (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 = m := by omega
                      rw [show (g.pos2card[pile.toNat]'hpile)[
                          (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by
                            have := hnf.pileDepth_bound ⟨pile.toNat, hpile⟩; omega) =
                          (g.pos2card[pile.toNat]'hpile)[m]'hidx5 from by congr 1]
                      rw [heqpm, show m - m = 0 from by omega, show UInt8.ofNat 0 = 0 from rfl,
                        UInt8.add_zero]
                    rw [hposB] at heqA'
                    apply hSB
                    have hb8 := congrArg UInt8.toNat hSAeqSval
                    have hbB : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                      UInt8.toNat_toUInt32 (SUIT B)
                    have hbA : (SUIT ((p.aces.get s).toUInt8 + 1)).toUInt32.toNat =
                        (SUIT ((p.aces.get s).toUInt8 + 1)).toNat := UInt8.toNat_toUInt32 _
                    rw [← heqA'] at hb8
                    omega
                  · refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
                    · show ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat > 0
                      rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                      have hdi' : (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0 := hdi
                      exact hdi'
                    · have hb5_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 :=
                        hnf.pileDepth_bound i
                      have hidx_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                      have hb5_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat ≤ 5 := by
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]; exact hb5_old
                      have hidx_new : ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                      have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                            (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                          = (g.pos2card[i.val]'i.isLt)[
                            (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'hidx_old := by
                        congr 1
                        rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                      have hfluteBridge2 : (fluteNorm pile hpile p).pileFlute[i.val]'i.isLt =
                          p.pileFlute[i.val]'i.isLt := by
                        show (p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt =
                          p.pileFlute[i.val]'i.isLt
                        exact Vector.getElem_set_ne hpile i.isLt (by omega)
                      --have heqAb : (g.pos2card[i.val]'i.isLt)[
                      --    (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'hidx_old -
                      --    (((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt) - 1) =
                      --    (p.aces.get s).toUInt8 + 1 := heqA
                      --rw [hfluteBridge2] at heqAb
                      --show (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                      --    (0 : Int32).toInt8 hpile)[i.val]'i.isLt).toInt.toNat - 1]'hidx_new -
                      --  ((p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile)[
                      --    i.val]'i.isLt - 1) =
                      --  (p.aces.get s).toUInt8 + 1
                      --rw [hcardEq3, Vector.getElem_set_ne hpile i.isLt (by omega)]
                      --exact heqAb
                      sorry
                · refine Or.inr (Or.inr (Or.inr ?_))
                  --show (VALUE ((p.kings.set (SUIT B).toUInt32.toNat
                  --    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                  --      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s).toUInt8).toNat <
                  --  (VALUE ((p.aces.get s).toUInt8 + 1)).toNat
                  --rw [hKeqOther]
                  --exact hkltA
                  sorry
          · -- (9) king_frontier: `SUIT B`'s king slot updates from `B+m` to
            -- `B-1-f` (`hnk`).  The pile's whole live range (positions `0..m`)
            -- is exactly the same-suit run `B..B+m` (`hSjEq`/`hPosGen`), so
            -- every card of `SUIT B` strictly above `B-1-f` and `≤13` is free:
            -- either absorbed by the merge (now depth `0`) or already free via
            -- the freed-predecessor chase (`hfg`).  Other suits are untouched;
            -- the new `busyAces` write only ever ADDS a bit, so the
            -- pending-busy disjunct transfers monotonically, and a
            -- different-suit king can never be a *live* card of THIS pile (its
            -- whole live range is same-suit), so `¬isFreeCard` transfers too.
            -- Hoisted from the king_frontier bullet below (also needed by the
            -- foundation_maximal_weak bullet): the pile is entirely occupied
            -- by the merged same-suit run B..B+m.
            have hRCgen : ∀ j : Nat, j ≤ m →
                (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
              (merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
                (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
                (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                hmg j hjm).2
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
            have hd0cI : (p.pileDepth[pile.toNat]'hpile).toInt32.toInt = (m + 1 : Nat) := by
              rw [Int8.toInt_toInt32]
              have hbdg : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                  (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
              omega
            have hPosGen : ∀ idx : Nat, idx ≤ m → ∃ hidx5 : idx < 5,
                (g.pos2card[pile.toNat]'hpile)[idx]'hidx5 = B + UInt8.ofNat (m - idx) := by
              intro idx hidxm
              rcases Nat.eq_zero_or_pos (m - idx) with hj0 | hjpos
              · refine ⟨by omega, ?_⟩
                rw [hj0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
                have hsub1 : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt =
                    (p.pileDepth[pile.toNat]'hpile).toInt32.toInt - 1 := by
                  rw [Int32.toInt_sub_of_le _ _ (by decide)
                    (by rw [Int32.le_iff_toInt_le, hd0cI,
                      show ((1 : Int32).toInt = 1) from by decide]; omega),
                    show ((1 : Int32).toInt = 1) from by decide]
                have hidx0m : ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toUInt32.toNat = idx := by
                  rw [Int32.toNat_toUInt32_of_le (by
                    rw [Int32.le_iff_toInt_le, hsub1, hd0cI,
                      show ((0 : Int32).toInt = 0) from by decide]; omega)]
                  show ((p.pileDepth[pile.toNat]'hpile).toInt32 - 1).toInt.toNat = idx
                  rw [hsub1, hd0cI]
                  omega
                rw [show (g.pos2card[pile.toNat]'hpile)[idx]'(by omega) =
                    (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 - 1
                      ).toUInt32.toNat]'hidx from by congr 1; omega]
              · obtain ⟨hidxj, heqj⟩ := merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m p
                  (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                  hmg (m - idx) hjpos (by omega)
                have hiN : (Int32.ofNat idx).toInt = (idx : Int) := by
                  rw [Int32.toInt_ofNat', show Int32.size = 4294967296 from rfl]
                  exact Int.bmod_eq_of_le (by omega) (by omega)
                have hposEq : (p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat (m - idx) - 1 = Int32.ofNat idx := by
                  apply Int32.toInt_inj.mp
                  have hd0le5 : (p.pileDepth[pile.toNat]'hpile).toInt32.toInt ≤ 5 := by
                    rw [Int8.toInt_toInt32]; exact hd5
                  have hilt : ((m - idx : Nat) : Int) + 1 ≤
                      (p.pileDepth[pile.toNat]'hpile).toInt32.toInt := by
                    rw [hd0cI]; omega
                  have hstep : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (m - idx) - 1).toInt =
                      (p.pileDepth[pile.toNat]'hpile).toInt32.toInt - ((m - idx : Nat) : Int) - 1 :=
                    depth_sub_ofNat_sub_one_eq hd0le5 hilt
                  rw [hstep, hiN, hd0cI]
                  omega
                have hidxNat : (Int32.ofNat idx).toUInt32.toNat = idx := by
                  rw [Int32.toNat_toUInt32_of_le (by
                    rw [Int32.le_iff_toInt_le, show ((0:Int32).toInt=0) from by decide, hiN]
                    omega)]
                  show (Int32.ofNat idx).toInt.toNat = idx
                  rw [hiN]
                  omega
                have hIdxEq : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat (m - idx) - 1).toUInt32.toNat = idx := by
                  rw [hposEq]; exact hidxNat
                refine ⟨by omega, ?_⟩
                rw [show (g.pos2card[pile.toNat]'hpile)[idx]'(by omega) =
                    (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat (m - idx) - 1).toUInt32.toNat]'hidxj from by
                      congr 1; exact hIdxEq.symm]
                exact heqj
            by_cases hip : (SUIT B).toUInt32.toNat = s.val
            · -- Same suit: the frontier moves from `B+m` to `B-1-f`.
              have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hip
              subst hseq
              constructor
              · by_cases hba' : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                    (B - 1 - UInt8.ofNat f).toInt8) = true
                · refine Or.inl ⟨?_, Or.inr ?_⟩
                  · show (p.kings.set (SUIT B).toUInt32.toNat
                        (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                          (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                        )[(SUIT B).toUInt32.toNat]'hs4 = p.aces[(SUIT B).toUInt32.toNat]'hs4
                    rw [Vector.getElem_set_self, hnk]
                    exact (eq_of_beq hba').symm
                  · show (p.busyAces |||
                        (if (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
                          (B - 1 - UInt8.ofNat f).toInt8) then (1 : UInt8) <<< SUIT B else 0))
                        &&& ((1 : UInt8) <<<
                          (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8) ≠ 0
                    simp only [hba', reduceIte]
                    have hSBeq : (SUIT B).toUInt32.toNat.toUInt8 = SUIT B := by
                      apply UInt8.toNat_inj.mp
                      rw [UInt8.toNat_ofNat']
                      have := UInt8.toNat_toUInt32 (SUIT B)
                      omega
                    show (p.busyAces ||| ((1 : UInt8) <<< SUIT B)) &&&
                        ((1 : UInt8) <<< (SUIT B).toUInt32.toNat.toUInt8) ≠ 0
                    rw [hSBeq]
                    exact uint8_and_ne_zero_of_or_right (uint8_shift_self_ne_zero (SUIT B)
                      (by rw [← UInt8.toNat_toUInt32]; exact hs4))
                · rw [Bool.not_eq_true] at hba'
                  have hba'' : p.aces[(SUIT B).toUInt32.toNat]'hs4 ≠
                      (B - 1 - UInt8.ofNat f).toInt8 := fun he => by
                    rw [he] at hba'; simp at hba'
                  have haces_lt : p.aces[(SUIT B).toUInt32.toNat]'hs4 <
                      (B - 1 - UInt8.ofNat f).toInt8 := by
                    rw [Int8.lt_iff_toInt_lt]
                    apply lt_of_le_of_ne (Int8.le_iff_toInt_le.mp haces_le_new_king)
                    intro he
                    exact hba'' (Int8.toInt_inj.mp he)
                  have hVge1 : 1 ≤ (VALUE (B - 1 - UInt8.ofNat f)).toNat := by
                    by_contra hcon
                    push Not at hcon
                    have heq16 : (B - 1 - UInt8.ofNat f).toNat = 16 * (SUIT B).toNat := by
                      have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                      have hb2 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                      have hSKn := congrArg UInt8.toNat hSK
                      omega
                    rw [hprev2] at heq16
                    have haces0I : (0:Int) ≤ (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
                      have h := Int8.le_iff_toInt_le.mp haces0
                      rwa [show ((0:Int8).toInt = 0) from by decide] at h
                    have hage2 : 16 * (SUIT B).toNat ≤
                        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt := by
                      have hage := haces_ge
                      have hb4 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                        UInt8.toNat_toUInt32 (SUIT B)
                      have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
                        Int8.toNat_toUInt8_of_le haces0
                      omega
                    have h1 := Int8.lt_iff_toInt_lt.mp haces_lt
                    rw [htiBf] at h1
                    omega
                  -- `¬isFreeCard g p (B-1-f)`, unconditionally, via `hfx`/`hfg`.
                  have hnfreeOld : ¬ isFreeCard g p (B - 1 - UInt8.ofNat f) := by
                    intro hfreeOld
                    apply hfx
                    rw [show freedIter f (⟨1 + Int32.ofNat m,
                        { p with hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) },
                        B - 1⟩ : FreedAcc) = ⟨_, _, B - 1 - UInt8.ofNat f⟩ from freedIter_eq _ _]
                    refine ⟨fun _ => ?_, fun h64 h10 => ?_⟩
                    · show p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1 - UInt8.ofNat f).toInt8
                      exact haces_lt
                    · have hc64' : (B - 1 - UInt8.ofNat f).toNat < 64 := by
                        have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                        have hb2 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                        have hb3 := SUIT_toNat B
                        have hSKn := congrArg UInt8.toNat hSK
                        omega
                      have hraw := isFree_to_card2depth_ge g p hwf (B - 1 - UInt8.ofNat f)
                        hc64' hfreeOld
                      have e1 : (g.card2depth[(B - 1 - UInt8.ofNat f).toNat]'hc64') =
                          (g.card2depth[(B - 1 - UInt8.ofNat f).toUInt32.toNat]'h64) := by congr 1
                      have e2 : (g.card2pile[(B - 1 - UInt8.ofNat f).toNat]'hc64') =
                          (g.card2pile[(B - 1 - UInt8.ofNat f).toUInt32.toNat]'h64) := by congr 1
                      have e3 : p.pileDepth[(g.card2pile[(B - 1 - UInt8.ofNat f).toNat]'hc64'
                          ).toNat]'(hwf.card2pile_lt _ hc64') =
                          p.pileDepth[(g.card2pile[(B - 1 - UInt8.ofNat f).toUInt32.toNat]'h64
                            ).toUInt32.toNat]'h10 := by
                        congr 1
                      rw [e1, e3] at hraw
                      exact hraw
                  have hc64 : (B - 1 - UInt8.ofNat f).toNat < 64 := by
                    have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                    have hb2 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                    have hb3 := SUIT_toNat B
                    have hSKn := congrArg UInt8.toNat hSK
                    omega
                  have hp64 : (cardPile g (B - 1 - UInt8.ofNat f)).toNat < 10 := by
                    unfold cardPile
                    rw [dif_pos hc64]
                    exact hwf.card2pile_lt _ hc64
                  have hreal2 : IsRealCard (B - 1 - UInt8.ofNat f) := by
                    have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                    have hb2 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                    have hb3 := SUIT_toNat B
                    have hbV := VALUE_toNat B
                    have hSKn := congrArg UInt8.toNat hSK
                    have hrV := hreal.2.2
                    have hp2 := hprev2
                    have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
                    refine ⟨by omega, hVge1, by omega⟩
                  have hcpNe : (cardPile g (B - 1 - UInt8.ofNat f)).toNat ≠ pile.toNat := by
                    intro hcp
                    have hcd5 : (cardDepth g (B - 1 - UInt8.ofNat f)).toNat < 5 := by
                      by_contra hcon
                      push Not at hcon
                      have hle5 := hwf.depth_le (B - 1 - UInt8.ofNat f) hreal2
                      have heq5 : (cardDepth g (B - 1 - UInt8.ofNat f)).toNat = 5 := by omega
                      apply hnfreeOld
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      rw [heq5]
                      exact hnf.pileDepth_bound ⟨(cardPile g (B - 1 - UInt8.ofNat f)).toNat, hp64⟩
                    have hrt := hwf.round_trip (B - 1 - UInt8.ofNat f) hreal2 hcd5
                    obtain ⟨hidxg, heqg⟩ := hPosGen (cardDepth g (B - 1 - UInt8.ofNat f)).toNat
                      (by
                        by_contra hgtm
                        push Not at hgtm
                        apply hnfreeOld
                        apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                        have heqIdx : p.pileDepth[(cardPile g (B - 1 - UInt8.ofNat f)).toNat]'hp64 =
                            p.pileDepth[pile.toNat]'hpile := by congr 1
                        rw [heqIdx, hd0c]; omega)
                    have hcardEq : (g.pos2card[pile.toNat]'hpile)[
                        (cardDepth g (B - 1 - UInt8.ofNat f)).toNat]'hidxg
                        = (B - 1 - UInt8.ofNat f) := by
                      have hbracket : (g.pos2card.get
                          ⟨(cardPile g (B - 1 - UInt8.ofNat f)).toNat, hp64⟩).get
                          ⟨(cardDepth g (B - 1 - UInt8.ofNat f)).toNat, hcd5⟩ =
                          (g.pos2card[(cardPile g (B - 1 - UInt8.ofNat f)).toNat]'hp64)[
                            (cardDepth g (B - 1 - UInt8.ofNat f)).toNat]'hcd5 := rfl
                      rw [hbracket] at hrt
                      rw [show (g.pos2card[(cardPile g (B - 1 - UInt8.ofNat f)).toNat]'hp64)[
                          (cardDepth g (B - 1 - UInt8.ofNat f)).toNat]'hcd5 =
                          (g.pos2card[pile.toNat]'hpile)[
                            (cardDepth g (B - 1 - UInt8.ofNat f)).toNat]'hidxg
                          from by congr 1; congr 1] at hrt
                      exact hrt
                    rw [heqg] at hcardEq
                    have hVeq2 := hRCgen (m - (cardDepth g (B - 1 - UInt8.ofNat f)).toNat) (by omega)
                    have hVeqCard := congrArg (fun x : UInt8 => (VALUE x).toNat) hcardEq
                    have hb1 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                    have hb2 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                    have hb3 := SUIT_toNat B
                    have hbV := VALUE_toNat B
                    have hSKn := congrArg UInt8.toNat hSK
                    have hrV := hreal.2.2
                    have hp2 := hprev2
                    omega
                  refine Or.inr ⟨?_, ?_⟩
                  · --show p.aces[(SUIT B).toUInt32.toNat]'hs4 = ((p.kings.set (SUIT B).toUInt32.toNat
                    --    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                    --      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                    --    )[(SUIT B).toUInt32.toNat]'hs4)
                    --rw [Vector.getElem_set_self, hnk, UInt8.toUInt8_toInt8]
                    --exact hVge1
                    sorry
                  · show ¬ isFreeCard g _ ((p.kings.set (SUIT B).toUInt32.toNat
                        (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                          (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                        )[(SUIT B).toUInt32.toNat]'hs4).toUInt8
                    rw [Vector.getElem_set_self, hnk, UInt8.toUInt8_toInt8]
                    intro hfreeNew
                    apply hnfreeOld
                    have hge := isFree_to_cardDepth_ge g _ hwf
                      (B - 1 - UInt8.ofNat f) hc64 hp64 hfreeNew
                    have heqD : (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                        (cardPile g (B - 1 - UInt8.ofNat f)).toNat]'hp64 =
                        p.pileDepth[(cardPile g (B - 1 - UInt8.ofNat f)).toNat]'hp64 :=
                      Vector.getElem_set_ne hpile hp64 (Ne.symm hcpNe)
                    rw [heqD] at hge
                    exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
              · intro c hSc hgt hle
                have hgt2 : (VALUE c).toNat > (VALUE ((p.kings.set (SUIT B).toUInt32.toNat
                    (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                      (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get
                    (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat := hgt
                have hgt' : (VALUE c).toNat > (VALUE (B - 1 - UInt8.ofNat f)).toNat := by
                  have heqK : (p.kings.set (SUIT B).toUInt32.toNat
                      (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                        (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get
                      (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = (B - 1 - UInt8.ofNat f).toInt8 := by
                    show (p.kings.set (SUIT B).toUInt32.toNat
                        (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                          (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4
                        )[(SUIT B).toUInt32.toNat]'hs4 = (B - 1 - UInt8.ofNat f).toInt8
                    rw [Vector.getElem_set_self]; exact hnk
                  rw [heqK, UInt8.toUInt8_toInt8] at hgt2
                  exact hgt2
                clear hgt hgt2
                have hcSB : SUIT c = SUIT B := hSc.trans hsuiteq.symm
                have hVBf : (VALUE (B - 1 - UInt8.ofNat f)).toNat = (VALUE B).toNat - 1 - f := by
                  have hb5 := VALUE_toNat (B - 1 - UInt8.ofNat f)
                  have hb6 := SUIT_toNat (B - 1 - UInt8.ofNat f)
                  have hb7 := SUIT_toNat B
                  have hb8 := VALUE_toNat B
                  have hSKn := congrArg UInt8.toNat hSK
                  omega
                by_cases hgeB : (VALUE B).toNat ≤ (VALUE c).toNat
                · -- merged range: `c = B + k` for some `k ≤ m`.
                  have hkm : (VALUE c).toNat - (VALUE B).toNat ≤ m := by
                    have hVeq2b := hRCgen m (le_refl m)
                    have hkv13n : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by
                      rw [hkv13]; decide
                    omega
                  set k := (VALUE c).toNat - (VALUE B).toNat with hkdef
                  have hVeq : (VALUE (B + UInt8.ofNat k)).toNat = (VALUE c).toNat := by
                    rw [hRCgen k hkm]; omega
                  have hSeq : SUIT (B + UInt8.ofNat k) = SUIT c := (hSjEq k hkm).trans hcSB.symm
                  have hceq : c = B + UInt8.ofNat k := (card_eq_of_suit_value _ _ hSeq hVeq).symm
                  obtain ⟨hidx5, heqpos⟩ := hPosGen (m - k) (by omega)
                  have hmk : m - (m - k) = k := by omega
                  have hposcard : (g.pos2card[pile.toNat]'hpile)[(m - k)]'hidx5 = c := by
                    rw [heqpos, hmk, hceq]
                  have hcp : (cardPile g c).toNat = pile.toNat := by
                    have hrti := hwf.round_trip_inv ⟨pile.toNat, hpile⟩ ⟨m - k, hidx5⟩
                    rw [show (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
                        (⟨m - k, hidx5⟩ : Fin 5) =
                        (g.pos2card[pile.toNat]'hpile)[(m - k)]'hidx5 from rfl, hposcard] at hrti
                    exact hrti.1
                  have hc64 : c.toNat < 64 := by
                    have hb1 := VALUE_toNat c
                    have hb2 := SUIT_toNat c
                    have hb3 := SUIT_toNat B
                    have hScB := congrArg UInt8.toNat hcSB
                    have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
                    omega
                  have hp64 : (cardPile g c).toNat < 10 := by rw [hcp]; exact hpile
                  apply isFree_of_cardDepth_ge g _ hwf c hc64 hp64
                  show (cardDepth g c).toNat ≥
                      ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                        (cardPile g c).toNat]'hp64).toInt.toNat
                  rw [show ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                      (cardPile g c).toNat]'hp64) =
                      (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[pile.toNat]'hpile
                      from by congr 1, Vector.getElem_set_self]
                  exact Nat.zero_le _
                · -- chased range: `c = B - l` for some `1 ≤ l ≤ f`, already free via `hfg`.
                  push Not at hgeB
                  have hl1 : 1 ≤ (VALUE B).toNat - (VALUE c).toNat := by omega
                  have hlf : (VALUE B).toNat - (VALUE c).toNat ≤ f := by omega
                  set l := (VALUE B).toNat - (VALUE c).toNat with hldef
                  have hlB : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
                  have hle1 : UInt8.ofNat l ≤ B := by
                    rw [UInt8.le_iff_toNat_le, hlB]; omega
                  have hsubL : (B - UInt8.ofNat l).toNat = B.toNat - l := by
                    rw [UInt8.toNat_sub_of_le _ _ hle1, hlB]
                  have hSBl : SUIT (B - UInt8.ofNat l) = SUIT B := by
                    apply UInt8.toNat_inj.mp
                    have hb1 := SUIT_toNat (B - UInt8.ofNat l)
                    have hb2 := SUIT_toNat B
                    have hb3 := VALUE_toNat B
                    omega
                  have hVeql : (VALUE (B - UInt8.ofNat l)).toNat = (VALUE c).toNat := by
                    have hb1 := VALUE_toNat (B - UInt8.ofNat l)
                    have hb2 := SUIT_toNat (B - UInt8.ofNat l)
                    have hb3 := VALUE_toNat B
                    omega
                  have hceq : c = B - UInt8.ofNat l :=
                    (card_eq_of_suit_value _ _ (hSBl.trans hcSB.symm) hVeql).symm
                  have hg2 := (hfg (l - 1) (by omega)).2
                  rw [show freedIter (l - 1) (⟨1 + Int32.ofNat m,
                      { p with hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) },
                      B - 1⟩ : FreedAcc) = ⟨_, _, (B - 1) - UInt8.ofNat (l - 1)⟩
                      from freedIter_eq _ _] at hg2
                  have hstepEq2 : (B - 1) - UInt8.ofNat (l - 1) = B - UInt8.ofNat l := by
                    apply UInt8.toNat_inj.mp
                    have hlm1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by
                      rw [UInt8.toNat_ofNat']; omega
                    have hlof : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
                    have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
                      rw [UInt8.le_iff_toNat_le, hlm1of, UInt8.toNat_sub_of_le _ _ h1B,
                        show ((1 : UInt8).toNat = 1) from rfl]
                      omega
                    have hlel : UInt8.ofNat l ≤ B := by
                      rw [UInt8.le_iff_toNat_le, hlof]; omega
                    rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B, hlm1of,
                      show ((1 : UInt8).toNat = 1) from rfl,
                      UInt8.toNat_sub_of_le _ _ hlel, hlof]
                    omega
                  rw [hstepEq2] at hg2
                  have hc64 : (B - UInt8.ofNat l).toNat < 64 := by
                    have hb1 := VALUE_toNat (B - UInt8.ofNat l)
                    have hb2 := SUIT_toNat (B - UInt8.ofNat l)
                    have hb3 := SUIT_toNat B
                    omega
                  have hc64u : (B - UInt8.ofNat l).toUInt32.toNat < 64 := by
                    rw [UInt8.toNat_toUInt32]; exact hc64
                  have hp10 : (g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u
                      ).toUInt32.toNat < 10 := by
                    rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc64u
                  have hfreeOld : isFreeCard g p (B - UInt8.ofNat l) := by
                    apply isFree_of_card2depth_ge g p hwf _ hc64
                    have e1 : (g.card2depth[(B - UInt8.ofNat l).toNat]'hc64) =
                        (g.card2depth[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u) := by congr 1
                    have e2 : (g.card2pile[(B - UInt8.ofNat l).toNat]'hc64) =
                        (g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u) := by congr 1
                    have e3 : p.pileDepth[(g.card2pile[(B - UInt8.ofNat l).toNat]'hc64
                        ).toNat]'(hwf.card2pile_lt _ hc64) =
                        p.pileDepth[(g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u
                          ).toUInt32.toNat]'hp10 := by congr 1
                    rw [e1, e3]
                    exact hg2 hc64u hp10
                  rw [hceq]
                  exact isFreeCard_mono hdec hfreeOld
            · -- Other suit: `kings[s]`/`aces[s]` are untouched, and the new
              -- `busyAces` bit only ADDS, so `hnf.king_frontier s` transfers.
              have hKeqOther : (p.kings.set (SUIT B).toUInt32.toNat
                  (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                    (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s = p.kings.get s :=
                Vector.getElem_set_ne hs4 s.isLt hip
              constructor
              · rcases (hnf.king_frontier s).1 with ⟨hkeq, hcase⟩ | ⟨hv1, hnfree⟩
                · refine Or.inl ⟨?_, ?_⟩
                  · show (p.kings.set (SUIT B).toUInt32.toNat
                        (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                          (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s = p.aces.get s
                    rw [hKeqOther]; exact hkeq
                  · rcases hcase with h13 | hbusy
                    · exact Or.inl h13
                    · exact Or.inr (uint8_and_ne_zero_of_or_left hbusy)
                · refine Or.inr ⟨?_, ?_⟩
                  · sorry
                  show ¬ isFreeCard g _
                    ((p.kings.set (SUIT B).toUInt32.toNat
                        (p.kings[(SUIT B).toUInt32.toNat]'hs4 -
                          (1 + Int32.ofNat m + Int32.ofNat f).toInt8) hs4).get s).toUInt8
                  rw [hKeqOther]
                  have hSs : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
                    (hnf.aces_kings_valid s).2.2.1
                  have hc64 : (p.kings.get s).toUInt8.toNat < 64 := by
                    have hb1 := VALUE_toNat (p.kings.get s).toUInt8
                    have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                    have hb3 := congrArg UInt8.toNat hSs
                    have hb4 : s.val.toUInt8.toNat = s.val := by
                      rw [UInt8.toNat_ofNat']; omega
                    have hb5 := (hnf.aces_kings_valid s).2.2.2.1
                    omega
                  have hp64 : (cardPile g (p.kings.get s).toUInt8).toNat < 10 := by
                    unfold cardPile; rw [dif_pos hc64]; exact hwf.card2pile_lt _ hc64
                  have hcpNe : (cardPile g (p.kings.get s).toUInt8).toNat ≠ pile.toNat := by
                    intro hcp
                    have hnfree' : ¬ isFreeCard g p (p.kings.get s).toUInt8 := hnfree
                    have hcd5 : (cardDepth g (p.kings.get s).toUInt8).toNat < 5 := by
                      by_contra hcon
                      push Not at hcon
                      have hreal' : IsRealCard (p.kings.get s).toUInt8 := ⟨by
                        have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                        have hb3 := congrArg UInt8.toNat hSs
                        have hb4 : s.val.toUInt8.toNat = s.val := by
                          rw [UInt8.toNat_ofNat']; omega
                        omega, sorry, (hnf.aces_kings_valid s).2.2.2.1⟩
                      have hle5 := hwf.depth_le _ hreal'
                      have heq5 : (cardDepth g (p.kings.get s).toUInt8).toNat = 5 := by omega
                      apply hnfree'
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      rw [heq5]
                      exact hnf.pileDepth_bound ⟨(cardPile g (p.kings.get s).toUInt8).toNat, hp64⟩
                    have hcd_lt : (cardDepth g (p.kings.get s).toUInt8).toNat < m + 1 := by
                      by_contra hgem
                      push Not at hgem
                      apply hnfree'
                      apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                      have heqIdx : p.pileDepth[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                          p.pileDepth[pile.toNat]'hpile := by congr 1
                      rw [heqIdx, hd0c]; omega
                    have hreal' : IsRealCard (p.kings.get s).toUInt8 := ⟨by
                      have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                      have hb3 := congrArg UInt8.toNat hSs
                      have hb4 : s.val.toUInt8.toNat = s.val := by
                        rw [UInt8.toNat_ofNat']; omega
                      omega, sorry, (hnf.aces_kings_valid s).2.2.2.1⟩
                    have hrt := hwf.round_trip (p.kings.get s).toUInt8 hreal' hcd5
                    obtain ⟨hidxg, heqg⟩ := hPosGen (cardDepth g (p.kings.get s).toUInt8).toNat
                      (by omega)
                    have hcardEq : (g.pos2card[pile.toNat]'hpile)[
                        (cardDepth g (p.kings.get s).toUInt8).toNat]'hidxg
                        = (p.kings.get s).toUInt8 := by
                      have hbracket : (g.pos2card.get
                          ⟨(cardPile g (p.kings.get s).toUInt8).toNat, hp64⟩).get
                          ⟨(cardDepth g (p.kings.get s).toUInt8).toNat, hcd5⟩ =
                          (g.pos2card[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64)[
                            (cardDepth g (p.kings.get s).toUInt8).toNat]'hcd5 := rfl
                      rw [hbracket] at hrt
                      rw [show (g.pos2card[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64)[
                          (cardDepth g (p.kings.get s).toUInt8).toNat]'hcd5 =
                          (g.pos2card[pile.toNat]'hpile)[
                            (cardDepth g (p.kings.get s).toUInt8).toNat]'hidxg
                          from by congr 1; congr 1] at hrt
                      exact hrt
                    rw [heqg] at hcardEq
                    have hSeq2 := congrArg (fun x : UInt8 => (SUIT x).toUInt32.toNat) hcardEq
                    have hSjEq2 := hSjEq (m - (cardDepth g (p.kings.get s).toUInt8).toNat) (by omega)
                    have hb6 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                      UInt8.toNat_toUInt32 (SUIT B)
                    have hb7 := congrArg UInt8.toNat hSjEq2
                    have hb8 := congrArg UInt8.toNat hSs
                    have hb9 : s.val.toUInt8.toNat = s.val := by
                      rw [UInt8.toNat_ofNat']; omega
                    have hb10 : (SUIT (B + UInt8.ofNat (m -
                        (cardDepth g (p.kings.get s).toUInt8).toNat))).toUInt32.toNat =
                        (SUIT (B + UInt8.ofNat (m -
                        (cardDepth g (p.kings.get s).toUInt8).toNat))).toNat :=
                      UInt8.toNat_toUInt32 _
                    have hb11 : (SUIT (p.kings.get s).toUInt8).toUInt32.toNat =
                        (SUIT (p.kings.get s).toUInt8).toNat := UInt8.toNat_toUInt32 _
                    apply hip
                    omega
                  intro hfreeNew
                  apply hnfree
                  have hge := isFree_to_cardDepth_ge g _ hwf
                    (p.kings.get s).toUInt8 hc64 hp64 hfreeNew
                  have heqDepth : (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile)[
                      (cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                      p.pileDepth[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 :=
                    Vector.getElem_set_ne hpile hp64 (Ne.symm hcpNe)
                  rw [heqDepth] at hge
                  exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
              · intro c hSc hgt hle
                rw [hKeqOther] at hgt
                exact isFreeCard_mono hdec ((hnf.king_frontier s).2 c hSc hgt hle)
        · -- (8) hash_def: the pile went from depth m+1 to 0, and the hash lost
          -- (m+1)·ph — m from the merge loop, 1 from the lone-king branch.
          show p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) -
              (pileHashes[pile.toNat]'hpile) =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              (((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile).get i)
                ).toInt.toNat.toUInt32) 0
          have hhd : p.hash = (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              (p.pileDepth.get i).toInt.toNat.toUInt32) 0 := hnf.hash_def
          have hadd := hash_foldl_set p.pileDepth pile.toNat hpile (0 : Int32).toInt8
          rw [show (((0 : Int32).toInt8).toInt.toNat = 0) from rfl,
            show ((0 : Nat).toUInt32 = 0) from rfl, UInt32.mul_zero, UInt32.add_zero,
            hd0c, show ((m + 1 : Nat).toUInt32 = UInt32.ofNat (m + 1)) from rfl,
            UInt32.ofNat_add, UInt32.ofNat_one, UInt32.mul_add, UInt32.mul_one] at hadd
          have h2 := congrArg
            (· - ((pileHashes[pile.toNat]'hpile) * UInt32.ofNat m + (pileHashes[pile.toNat]'hpile)))
            hadd
          rw [UInt32.add_sub_cancel, uint32_sub_add] at h2
          rw [hhd, UInt32.mul_comm (UInt32.ofNat m) (pileHashes[pile.toNat]'hpile), ← h2]
        · -- (10) usedSpace_def: pile's depth `m+1` is fully freed; the
          -- flute-term at `pile` is 0 both in the normalized entry state
          -- (flute 1, depth `m+1`) and here (flute 1, depth 0), so it
          -- cancels; aces are untouched.
          show (p.usedSpace - Int8.ofNat f + (1 + Int32.ofNat m + Int32.ofNat f).toInt8).toInt =
            (52 : Int)
            - ((p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile).toList.foldl
                (fun acc d => acc + d.toInt.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
            - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                (p.pileDepth.set pile.toNat (0 : Int32).toInt8 hpile).toList
                (p.pileFlute.set pile.toNat (1 : Int32).toUInt32.toUInt8 hpile).toList
                |>.foldl (·+·) 0 : Nat))
          have hud : p.usedSpace.toInt = (52 : Int)
              - (p.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
              - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
              - (List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                  p.pileDepth.toList (p.pileFlute.set pile.toNat 1 hpile).toList
                  |>.foldl (·+·) 0 : Nat) :=
            hnf.usedSpace_def
          have hds := depth_sum_foldl_set p.pileDepth pile.toNat hpile (0 : Int32).toInt8
          have hft_norm := usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
            (p.pileDepth[pile.toNat]'hpile) (1 : UInt8)
          have hft_new := usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
            (0 : Int32).toInt8 ((1 : Int32).toUInt32.toUInt8)
          rw [Vector.set_getElem_self hpile] at hft_norm
          have hd' : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) := hd
          have ho : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
              (p.pileFlute[pile.toNat]'hpile).toNat - 1 else 0) =
              (p.pileFlute[pile.toNat]'hpile).toNat - 1 := if_pos hd'
          have hn : (if (p.pileDepth[pile.toNat]'hpile) ≠ (0 : Int8) then
              (1 : UInt8).toNat - 1 else 0) = 0 := if_pos hd'
          have hfl1 : ((1 : Int32).toUInt32.toUInt8).toNat = 1 := rfl
          have hz : (if ((0 : Int32).toInt8) ≠ (0 : Int8) then
              ((1 : Int32).toUInt32.toUInt8).toNat - 1 else 0) = 0 :=
            if_neg (show ¬((0 : Int32).toInt8 ≠ (0 : Int8)) from by decide)
          rw [ho, hn] at hft_norm
          rw [ho, hz] at hft_new
          -- The Int8 arithmetic `usedSpace − f + (1+m+f)` doesn't wrap: with
          -- `usedSpace ∈ [0,52]` (from `usedSpace_nonneg`) and `f ≤ 60`, `m ≤ 4`,
          -- every intermediate value stays within `[-60, 57] ⊂ [-128,127]`.
          have hspace_bound : 0 ≤ p.usedSpace.toInt ∧ p.usedSpace.toInt ≤ 52 := by
            have h := usedSpace_nonneg hwf hnf
            rwa [show (fluteNorm pile hpile p).usedSpace = p.usedSpace from rfl] at h
          have hfInt : (Int8.ofNat f).toInt = (f : Int) := by
            rw [Int8.toInt_ofNat', show Int8.size = 256 from rfl]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hflInt : ((1 + Int32.ofNat m + Int32.ofNat f).toInt8).toInt = 1 + (m : Int) + f := by
            rw [Int32.toInt_toInt8, hfl32I]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hsub : (p.usedSpace - Int8.ofNat f).toInt = p.usedSpace.toInt - f := by
            rw [Int8.toInt_sub, hfInt]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have huInt0 : (p.usedSpace - Int8.ofNat f + (1 + Int32.ofNat m + Int32.ofNat f).toInt8
              ).toInt = p.usedSpace.toInt - f + (1 + (m : Int) + f) := by
            rw [Int8.toInt_add, hsub, hflInt]
            exact Int.bmod_eq_of_le (by omega) (by omega)
          have hd00 : ((0 : Int32).toInt8).toInt.toNat = 0 := rfl
          omega
      by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
          (B - 1 - UInt8.ofNat f).toInt8) = true
      · simp only [hk, hba, reduceIte]
        simp only [hba, reduceIte] at key
        exact key
      · rw [Bool.not_eq_true] at hba
        simp only [hk, hba, Bool.false_eq_true, reduceIte]
        simp only [hba, Bool.false_eq_true, reduceIte, UInt8.or_zero] at key
        exact key
    · -- No lone king.
      rw [Bool.not_eq_true] at hk
      have key : SolverInvBase g
          { p with
            hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile),
            usedSpace := p.usedSpace - Int8.ofNat f,
            pileDepth := p.pileDepth.set pile.toNat
              ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile,
            pileFlute := p.pileFlute.set pile.toNat
              ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile } := by
        have hd1m : 1 ≤ (p.pileDepth[pile.toNat]'hpile).toInt - m := by omega
        have hdI8 : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt =
            (p.pileDepth[pile.toNat]'hpile).toInt - m := by
          rw [Int32.toInt_toInt8, hdepth1I]
          exact Int.bmod_eq_of_le (by omega) (by omega)
        have hdec : ∀ i : Fin 10,
            (((p.pileDepth.set pile.toNat
              ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile).get i)
              ).toInt.toNat ≤
            ((fluteNorm pile hpile p).pileDepth.get i).toInt.toNat := by
          intro i
          show ((p.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt).toInt.toNat ≤
            (p.pileDepth[i.val]'i.isLt).toInt.toNat
          by_cases hip : pile.toNat = i.val
          · simp only [← hip, Vector.getElem_set_self]
            show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
              ).toInt.toNat ≤ (p.pileDepth[pile.toNat]'hpile).toInt.toNat
            omega
          · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
        -- The pile's new boundary is `B + m` (`m = 0`: the entry boundary itself;
        -- `m > 0`: the last merge step's guard equality, reindexed).  More
        -- generally every slot `d0 - k - 1` for `k ≤ m` still holds `B + k`.
        have hcard_pos : ∀ k, k ≤ m → ∃ hidxk : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
              Int32.ofNat k - 1).toUInt32.toNat < 5,
            (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
              Int32.ofNat k - 1).toUInt32.toNat]'hidxk = B + UInt8.ofNat k := by
          intro k hkm
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            simp only [show Int32.ofNat 0 = 0 from rfl, Int32.sub_zero,
              show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
            exact ⟨hidx, hBdef.symm⟩
          · exact merge_pos_chain g pile hpile (pileHashes[pile.toNat]'hpile) B
              (p.pileDepth[pile.toNat]'hpile).toInt32 m p
              (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
              hmg k hkpos hkm
        -- Every card `B + k` for `k < m` sat in a slot now beyond the shrunk
        -- depth `d0 − m`, so it is free in the post-cleanup position.
        have hfree_interior : ∀ k, k < m → isFreeCard g
            { p with
              hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile),
              usedSpace := p.usedSpace - Int8.ofNat f,
              pileDepth := p.pileDepth.set pile.toNat
                ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile,
              pileFlute := p.pileFlute.set pile.toNat
                ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile }
            (B + UInt8.ofNat k) := by
          intro k hkm
          obtain ⟨hidxk, heqk⟩ := hcard_pos k (by omega)
          have hreal_k : IsRealCard (B + UInt8.ofNat k) := heqk ▸ hwf.pos2card_real _ _
          have hc64 : (B + UInt8.ofNat k).toNat < 64 := by
            have hsn := SUIT_toNat (B + UInt8.ofNat k); have h1 := hreal_k.1; omega
          have heqk' : (g.pos2card.get (⟨pile.toNat, hpile⟩ : Fin 10)).get
              (⟨((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat,
                hidxk⟩ : Fin 5) = B + UInt8.ofNat k := heqk
          have hrt := hwf.round_trip_inv ⟨pile.toNat, hpile⟩ ⟨((p.pileDepth[pile.toNat]'hpile
              ).toInt32 - Int32.ofNat k - 1).toUInt32.toNat, hidxk⟩
          rw [heqk'] at hrt
          have hp64 : (cardPile g (B + UInt8.ofNat k)).toNat < 10 := by
            rw [hrt.1]; exact hpile
          apply isFree_of_cardDepth_ge g _ hwf _ hc64 hp64
          have hgoal2 : (p.pileDepth.set pile.toNat
                (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8) hpile
              )[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
              = ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
            have hstep : (p.pileDepth.set pile.toNat
                  (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8) hpile
                )[(cardPile g (B + UInt8.ofNat k)).toNat]'hp64
                = (p.pileDepth.set pile.toNat
                  (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8) hpile
                )[pile.toNat]'hpile := by
              congr 1
              exact hrt.1
            rw [hstep, Vector.getElem_set_self]
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
        -- Every card `B - l` for `1 ≤ l ≤ f` was already free before cleanup ran
        -- (that's what the freed loop's guard checked), and freeness is
        -- monotone under the pile's depth decrease.
        have hfree_freed : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g
            { p with
              hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile),
              usedSpace := p.usedSpace - Int8.ofNat f,
              pileDepth := p.pileDepth.set pile.toNat
                ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile,
              pileFlute := p.pileFlute.set pile.toNat
                ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile }
            (B - UInt8.ofNat l) := by
          intro l hl1 hlf
          have hg := (hfg (l - 1) (by omega)).2
          have hlm1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by
            rw [UInt8.toNat_ofNat']; omega
          have hlof : (UInt8.ofNat l).toNat = l := by
            rw [UInt8.toNat_ofNat']; omega
          have hstepEq : (B - 1) - UInt8.ofNat (l - 1) = B - UInt8.ofNat l := by
            apply UInt8.toNat_inj.mp
            have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
              rw [UInt8.le_iff_toNat_le, hlm1of,
                UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
              omega
            have hlel : UInt8.ofNat l ≤ B := by
              rw [UInt8.le_iff_toNat_le, hlof]
              omega
            rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B,
              hlm1of, show ((1 : UInt8).toNat = 1) from rfl,
              UInt8.toNat_sub_of_le _ _ hlel, hlof]
            omega
          rw [show freedIter (l - 1) (⟨1 + Int32.ofNat m,
              { p with hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) },
              B - 1⟩ : FreedAcc) = ⟨_, _, (B - 1) - UInt8.ofNat (l - 1)⟩ from freedIter_eq _ _]
            at hg
          rw [hstepEq] at hg
          have hc64 : (B - UInt8.ofNat l).toNat < 64 := by
            have hleB : UInt8.ofNat l ≤ B := by
              rw [UInt8.le_iff_toNat_le, hlof]; omega
            have := UInt8.toNat_sub_of_le B (UInt8.ofNat l) hleB
            omega
          have h64 : ∀ (h64 : (B - UInt8.ofNat l).toUInt32.toNat < 64)
              (h10 : (g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'h64).toUInt32.toNat < 10),
              (g.card2depth[(B - UInt8.ofNat l).toUInt32.toNat]'h64).toNat ≥
              (p.pileDepth[(g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'h64
                  ).toUInt32.toNat]'h10).toInt32.toInt.toNat := hg
          have hc64u : (B - UInt8.ofNat l).toUInt32.toNat < 64 := by
            rw [UInt8.toNat_toUInt32]; exact hc64
          have hp10 : (g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u).toUInt32.toNat < 10 :=
            by rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc64u
          have hfree_p : isFreeCard g p (B - UInt8.ofNat l) := by
            apply isFree_of_card2depth_ge g p hwf _ hc64
            have e1 : (g.card2depth[(B - UInt8.ofNat l).toNat]'hc64) =
                (g.card2depth[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u) := by
              congr 1
            have e2 : (g.card2pile[(B - UInt8.ofNat l).toNat]'hc64) =
                (g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u) := by
              congr 1
            have e3 : p.pileDepth[(g.card2pile[(B - UInt8.ofNat l).toNat]'hc64
                ).toNat]'(hwf.card2pile_lt _ hc64) =
                p.pileDepth[(g.card2pile[(B - UInt8.ofNat l).toUInt32.toNat]'hc64u
                  ).toUInt32.toNat]'hp10 := by
              congr 1
            rw [e1, e3]
            exact h64 hc64u hp10
          exact isFreeCard_mono hdec hfree_p
        -- Shared "≤ 5" bound for the cleaned pile's post-cleanup depth, reused
        -- by every clause below that needs an index proof for `p'`'s boundary.
        have hb5 : ∀ i : Fin 10, ((p.pileDepth.set pile.toNat
            ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
            )[i.val]'i.isLt).toInt.toNat ≤ 5 := by
          intro i
          by_cases hip : pile.toNat = i.val
          · simp only [← hip, Vector.getElem_set_self]
            show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
              ).toInt.toNat ≤ 5
            omega
          · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
            exact hnf.pileDepth_bound i
        -- aces/kings are untouched in this branch, so clause (1) transfers.
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- pileBase (0)/(0b)/(3)/(3a)/(3c): bundle the base per-pile facts.
          intro i
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- (0) pileDepth_bound: the cleaned pile ends at depth − m ∈ [1, 5].
            show ((p.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt).toInt.toNat ≤ 5
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
                ).toInt.toNat ≤ 5
              omega
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              exact hnf.pileDepth_bound i
          · -- (0b) pileDepth_nonneg
            show (0 : Int8) ≤ (p.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl, hdI8]
              omega
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              exact hnf.pileDepth_nonneg i
          · -- (3) flute_pos: the cleaned pile ends at flute 1 + m + f ≥ 1.
            show 1 ≤ ((p.pileFlute.set pile.toNat
              ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile)[i.val]'i.isLt).toNat
            by_cases hip : pile.toNat = i.val
            · simp only [← hip, Vector.getElem_set_self]
              rw [hfl8]
              omega
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              have h := hnf.flute_pos i
              have h' : 1 ≤ ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat := h
              rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at h'
          · -- (3) flute_empty: the cleaned pile keeps depth ≥ 1, so only other
            -- piles can be empty, and they are unchanged.
            -- piles can be empty, and they are unchanged.
            intro hdep
            show ((p.pileFlute.set pile.toNat
              ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile)[i.val]'i.isLt) = 1
            by_cases hip : pile.toNat = i.val
            · exfalso
              have hdep' : (p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt = 0 := hdep
              simp only [← hip, Vector.getElem_set_self] at hdep'
              have hz := congrArg Int8.toInt hdep'
              rw [hdI8, show ((0 : Int8).toInt = 0) from rfl] at hz
              omega
            · rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              have hdep' : (p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt = 0 := hdep
              rw [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdep'
              have h := hnf.flute_empty i hdep'
              have h' : ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt) = 1 := h
              rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at h'
          · -- (3a) flute_cards_free: for `pile` itself, the flute interior
            -- `B+m-j` splits into merge-absorbed cards (`j ≤ m`, free via
            -- `hfree_interior`) and already-free predecessor cards (`j > m`, via
            -- `hfree_freed`); other piles transfer unchanged via `isFreeCard_mono`.
            intro j hdi hj0 hjlt
            by_cases hip : pile.toNat = i.val
            · have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
              subst hieq
              have hjlt' : j.toNat < ((p.pileFlute.set pile.toNat
                  ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile
                  )[pile.toNat]'hpile).toNat := hjlt
              simp only [Vector.getElem_set_self] at hjlt'
              have hjm : j.toNat < 1 + m + f := by rw [hfl8] at hjlt'; exact hjlt'
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
              obtain ⟨hidxm, heqm⟩ := hcard_pos m (le_refl m)
              have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
                  ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
                  = B + UInt8.ofNat m := by
                have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
                      ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
                    = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
                  congr 1
                rw [hstep, heqm]
              show isFreeCard g _
                ((g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[pile.toNat]'hpile).toInt.toNat - 1]'(by
                      have h5 : ((p.pileDepth.set pile.toNat
                          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                          )[pile.toNat]'hpile).toInt.toNat ≤ 5 := hb5 ⟨pile.toNat, hpile⟩
                      omega) - j)
              simp only [Vector.getElem_set_self]
              rw [hcardEq]
              by_cases hjle : j.toNat ≤ m
              · -- interior merge-absorbed card: `B + m - j = B + (m - j.toNat)`.
                have hjpos : 0 < j.toNat := hj0
                set k := m - j.toNat with hkdef
                have hkm : k < m := by omega
                have hval : B + UInt8.ofNat m - j = B + UInt8.ofNat k := by
                  apply UInt8.toNat_inj.mp
                  have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
                  have hlt : B.toNat + m < 256 := by omega
                  have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
                    rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt]
                  have hjB : j ≤ B + UInt8.ofNat m := by
                    rw [UInt8.le_iff_toNat_le, hBmB]; omega
                  rw [UInt8.toNat_sub_of_le _ _ hjB]
                  have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
                  have hltk : B.toNat + k < 256 := by omega
                  have hBkB : (B + UInt8.ofNat k).toNat = B.toNat + k := by
                    rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hltk]
                  rw [hBmB, hBkB]
                  omega
                rw [hval]
                exact hfree_interior k hkm
              · -- freed-predecessor card: `B + m - j = B - (j.toNat - m)`.
                set l := j.toNat - m with hldef
                have hl1 : 1 ≤ l := by omega
                have hlf : l ≤ f := by omega
                have hval : B + UInt8.ofNat m - j = B - UInt8.ofNat l := by
                  apply UInt8.toNat_inj.mp
                  have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
                  have hlB : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
                  have hlt : B.toNat + m < 256 := by omega
                  have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
                    rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt]
                  have hjB : j ≤ B + UInt8.ofNat m := by
                    rw [UInt8.le_iff_toNat_le, hBmB]; omega
                  have hlB' : UInt8.ofNat l ≤ B := by
                    rw [UInt8.le_iff_toNat_le, hlB]; omega
                  rw [UInt8.toNat_sub_of_le _ _ hjB, UInt8.toNat_sub_of_le _ _ hlB', hBmB, hlB]
                  omega
                rw [hval]
                exact hfree_freed l hl1 hlf
            · -- other piles: `pile`'s cleanup only shrinks depths, freeness transfers.
              have h1' : ((fluteNorm pile hpile p).pileDepth[i.val]'i.isLt).toInt.toNat > 0 := by
                show (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0
                have hdi' : ((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat > 0 := hdi
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdi'
              have h3' : j.toNat < ((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt).toNat := by
                show j.toNat < ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                have hj' : j.toNat < ((p.pileFlute.set pile.toNat
                    ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile
                    )[i.val]'i.isLt).toNat := hjlt
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hj'
              have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat - 1]'(by have := hb5 i; omega)
                  = (g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    (by
                      have h5 : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 :=
                        hnf.pileDepth_bound i
                      omega) := by
                congr 1
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              show isFreeCard g _
                ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat - 1]'(by
                      have := hb5 i; omega) - j)
              rw [hcardEq3]
              exact isFreeCard_mono hdec (hnf.flute_cards_free i j h1' hj0 h3')
          · -- (3c) flute_not_aces: for `pile` itself, aces hasn't reached any
            -- interior flute card.  Merge-absorbed cards (`j ≤ m`) inherit the
            -- boundary's own bound `haces_lt_B` (via `boundary_not_free` /
            -- `foundation_cards_free`'s contrapositive, established in the
            -- shared preamble) since aces only compares against a *larger*
            -- card as `k` grows; already-free predecessor cards (`j > m`) get
            -- their bound directly from the freed loop's own guard (`hfg`).
            -- Other piles transfer unchanged (mirrors the king branch's
            -- `i ≠ pile` case verbatim, with the shrunk depth/grown flute).
            intro j hdi hj0 hjlt
            by_cases hip : pile.toNat = i.val
            · have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
              subst hieq
              have hjlt' : j.toNat < ((p.pileFlute.set pile.toNat
                  ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile
                  )[pile.toNat]'hpile).toNat := hjlt
              simp only [Vector.getElem_set_self] at hjlt'
              have hjm : j.toNat < 1 + m + f := by rw [hfl8] at hjlt'; exact hjlt'
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
              obtain ⟨hidxm, heqm⟩ := hcard_pos m (le_refl m)
              have hcardEq : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
                    ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
                  = B + UInt8.ofNat m := by
                have hstep : (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile
                      ).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
                    = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                      Int32.ofNat m - 1).toUInt32.toNat]'hidxm := by
                  congr 1
                rw [hstep, heqm]
              have hrcm := merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
                (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
                (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                hmg m (le_refl m)
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
              have haces_lt_Bk : ∀ k, k ≤ m →
                  p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B + UInt8.ofNat k).toInt8 := by
                intro k hkm
                have htiBk : (B + UInt8.ofNat k).toInt8.toInt = (B.toNat + k : Int) := by
                  have h' : (B + UInt8.ofNat k).toInt8.toInt =
                      (((B + UInt8.ofNat k).toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                    show (B + UInt8.ofNat k).toInt8.toBitVec.toInt = _
                    rw [BitVec.toInt_eq_toNat_bmod]
                    rfl
                  rw [UInt8.toUInt8_toInt8] at h'
                  have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
                  have hlt256 : B.toNat + k < 256 := by omega
                  have hadd : (B + UInt8.ofNat k).toNat = B.toNat + k := by
                    rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hlt256]
                  rw [h', hadd, Int.bmod_eq_of_le (by omega) (by omega)]
                  push_cast
                  omega
                have htiB : B.toInt8.toInt = (B.toNat : Int) := by
                  have h' : B.toInt8.toInt = ((B.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                    show B.toInt8.toBitVec.toInt = _
                    rw [BitVec.toInt_eq_toNat_bmod]
                    rfl
                  rw [UInt8.toUInt8_toInt8] at h'
                  rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
                have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
                rw [htiB] at hlt
                rw [Int8.lt_iff_toInt_lt, htiBk]
                omega
              have haces_lt_Bl : ∀ l, 1 ≤ l → l ≤ f →
                  p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - UInt8.ofNat l).toInt8 := by
                intro l hl1 hlf
                have hg := (hfg (l - 1) (by omega)).1 hs4
                have hlm1of : (UInt8.ofNat (l - 1)).toNat = l - 1 := by
                  rw [UInt8.toNat_ofNat']; omega
                have hlof : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
                have hstepEq : (B - 1) - UInt8.ofNat (l - 1) = B - UInt8.ofNat l := by
                  apply UInt8.toNat_inj.mp
                  have hle1 : UInt8.ofNat (l - 1) ≤ B - 1 := by
                    rw [UInt8.le_iff_toNat_le, hlm1of,
                      UInt8.toNat_sub_of_le _ _ h1B, show ((1 : UInt8).toNat = 1) from rfl]
                    omega
                  have hlel : UInt8.ofNat l ≤ B := by
                    rw [UInt8.le_iff_toNat_le, hlof]
                    omega
                  rw [UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_sub_of_le _ _ h1B,
                    hlm1of, show ((1 : UInt8).toNat = 1) from rfl,
                    UInt8.toNat_sub_of_le _ _ hlel, hlof]
                  omega
                rw [show freedIter (l - 1) (⟨1 + Int32.ofNat m,
                    { p with hash := p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) },
                    B - 1⟩ : FreedAcc) = ⟨_, _, (B - 1) - UInt8.ofNat (l - 1)⟩ from freedIter_eq _ _]
                  at hg
                rwa [hstepEq] at hg
              have hidx_new' : ((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[pile.toNat]'hpile).toInt.toNat - 1 < 5 := by
                rw [Vector.getElem_set_self]
                have hbdg : (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
                    ).toNatClampNeg = (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                    Int32.ofNat m).toInt8).toInt.toNat := rfl
                omega
              show ∀ hs : (SUIT ((g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[pile.toNat]'hpile).toInt.toNat - 1]'hidx_new')).toNat < 4,
                p.aces.get ⟨(SUIT ((g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[pile.toNat]'hpile).toInt.toNat - 1]'hidx_new')).toNat, hs⟩ <
                  ((g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set pile.toNat
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                      )[pile.toNat]'hpile).toInt.toNat - 1]'hidx_new'
                    - j).toInt8
              simp only [Vector.getElem_set_self]
              intro hs
              have hval0 : (SUIT ((g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat
                  ]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'(hbidx ▸ hidxm)
                  )).toNat = (SUIT (B + UInt8.ofNat m)).toNat :=
                congrArg (fun c => (SUIT c).toNat) hcardEq
              have hs' : (SUIT (B + UInt8.ofNat m)).toNat < 4 := hval0 ▸ hs
              have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
              have hidxEq : (⟨(SUIT (B + UInt8.ofNat m)).toNat, hs'⟩ : Fin 4) =
                  ⟨(SUIT B).toNat, hs4'⟩ := Fin.ext (congrArg UInt8.toNat hSm)
              have hacesGet_eq : p.aces.get (⟨(SUIT B).toNat, hs4'⟩ : Fin 4) =
                  p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
                congr 1
              have hEq2 : p.aces.get ⟨(SUIT ((g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[
                  pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat - 1]'
                  (hbidx ▸ hidxm))).toNat, hs⟩ = p.aces[(SUIT B).toUInt32.toNat]'hs4 := by
                rw [← hacesGet_eq, ← hidxEq]
                congr 1
                exact Fin.ext hval0
              rw [hEq2, hcardEq]
              by_cases hjle : j.toNat ≤ m
              · -- merge-absorbed card: `B + m - j = B + k`, `k = m - j.toNat`.
                have hjpos : 0 < j.toNat := hj0
                set k := m - j.toNat with hkdef
                have hkm : k ≤ m := by omega
                have hval : B + UInt8.ofNat m - j = B + UInt8.ofNat k := by
                  apply UInt8.toNat_inj.mp
                  have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
                  have hlt : B.toNat + m < 256 := by omega
                  have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
                    rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt]
                  have hjB : j ≤ B + UInt8.ofNat m := by
                    rw [UInt8.le_iff_toNat_le, hBmB]; omega
                  rw [UInt8.toNat_sub_of_le _ _ hjB]
                  have hkB : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
                  have hltk : B.toNat + k < 256 := by omega
                  have hBkB : (B + UInt8.ofNat k).toNat = B.toNat + k := by
                    rw [UInt8.toNat_add, hkB, Nat.mod_eq_of_lt hltk]
                  rw [hBmB, hBkB]
                  omega
                rw [hval]
                exact haces_lt_Bk k hkm
              · -- freed-predecessor card: `B + m - j = B - l`, `l = j.toNat - m`.
                set l := j.toNat - m with hldef
                have hl1 : 1 ≤ l := by omega
                have hlf : l ≤ f := by omega
                have hval : B + UInt8.ofNat m - j = B - UInt8.ofNat l := by
                  apply UInt8.toNat_inj.mp
                  have hmB : (UInt8.ofNat m).toNat = m := by rw [UInt8.toNat_ofNat']; omega
                  have hlB : (UInt8.ofNat l).toNat = l := by rw [UInt8.toNat_ofNat']; omega
                  have hlt : B.toNat + m < 256 := by omega
                  have hBmB : (B + UInt8.ofNat m).toNat = B.toNat + m := by
                    rw [UInt8.toNat_add, hmB, Nat.mod_eq_of_lt hlt]
                  have hjB : j ≤ B + UInt8.ofNat m := by
                    rw [UInt8.le_iff_toNat_le, hBmB]; omega
                  have hlB' : UInt8.ofNat l ≤ B := by
                    rw [UInt8.le_iff_toNat_le, hlB]; omega
                  rw [UInt8.toNat_sub_of_le _ _ hjB, UInt8.toNat_sub_of_le _ _ hlB', hBmB, hlB]
                  omega
                rw [hval]
                exact haces_lt_Bl l hl1 hlf
            · -- other piles: `pile`'s cleanup only shrinks depth/extends flute,
              -- so `flute_not_aces` transfers unchanged from `hnf`.
              have h1' : ((fluteNorm pile hpile p).pileDepth[i.val]'i.isLt).toInt.toNat > 0 := by
                show (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0
                have hdi' : ((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat > 0 := hdi
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hdi'
              have h3' : j.toNat < ((fluteNorm pile hpile p).pileFlute[i.val]'i.isLt).toNat := by
                show j.toNat < ((p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt).toNat
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                have hj' : j.toNat < ((p.pileFlute.set pile.toNat
                    ((1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8) hpile
                    )[i.val]'i.isLt).toNat := hjlt
                rwa [Vector.getElem_set_ne hpile i.isLt (by omega)] at hj'
              have hidx_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1 < 5 := by
                have h5 : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 := hnf.pileDepth_bound i
                omega
              have hidx_new : ((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat - 1 < 5 := by
                have := hb5 i; omega
              have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                  = (g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    hidx_old := by
                congr 1
                rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
              show ∀ hs : (SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat < 4,
                p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                    ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                    )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat,
                  hs⟩ <
                  ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                      )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                    - j).toInt8
              intro hs
              have hval : (SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat
                  = (SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'
                    hidx_old)).toNat :=
                congrArg (fun c => (SUIT c).toNat) hcardEq3
              have hs' : (SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt
                  ).toInt.toNat - 1]'hidx_old)).toNat < 4 := hval ▸ hs
              have hres := hnf.flute_not_aces i j h1' hj0 h3' hs'
              have hEq2 : p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                  ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                  )[i.val]'i.isLt).toInt.toNat - 1]'hidx_new)).toNat, hs⟩ =
                p.aces.get ⟨(SUIT ((g.pos2card[i.val]'i.isLt)[(p.pileDepth[i.val]'i.isLt
                    ).toInt.toNat - 1]'hidx_old)).toNat, hs'⟩ := by
                congr 1
                exact Fin.ext hval
              rw [hEq2, hcardEq3]
              exact hres
        · intro s
          refine ⟨hnf.aces_kings_valid s, ?_, ?_, ?_⟩
          · -- (4a) foundation_cards_free: aces unchanged, freeness monotone.
            intro c h1 h2 h3
            exact isFreeCard_mono hdec (hnf.foundation_cards_free s c h1 h2 h3)
          · -- (4b-weak) foundation_maximal_weak: `aces` and `kings` are BOTH
            -- completely untouched by this branch, so disjuncts 1 and 4
            -- transfer for every `s` with no work at all.  Disjuncts 2/3 only
            -- need care for `SUIT B`'s own witness, via the same "in-pile ⟹
            -- pinned to the merged run `B..B+m`" analysis as the lone-king
            -- branch above (using the shared `hcard_pos` for the position
            -- formula instead of `hPosGen`).  If the witness pins `A = B`
            -- exactly, the freed-loop guard at step 0 forces `f = 0` (else it
            -- would demand the strict inequality `aces[SUIT B] < B - 1`,
            -- contradicting `aces[SUIT B] = B - 1`); with `f = 0` the new
            -- boundary/flute of `pile` itself (`B+m` / `1+m`) gives EXACTLY
            -- `A` back as the new disjunct-3 witness.
            have hAeqB_implies_f0 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B →
                f = 0 := by
              intro hAB
              by_contra hfne
              have hg := (hfg 0 (by omega)).1 hs4
              have hak1 : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
                  ((SUIT B).toUInt32.toNat).toUInt8 :=
                (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
              have hak21 : (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat ≤ 13 :=
                (hnf.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).2.1
              have hb1 := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
              have hb2 := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
              have hb3 := congrArg UInt8.toNat hak1
              have hb4 : ((SUIT B).toUInt32.toNat).toUInt8.toNat =
                  (SUIT B).toUInt32.toNat := by rw [UInt8.toNat_ofNat']; omega
              have hacesLt255 : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat < 255 := by
                omega
              have htoNatSucc : ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1).toNat =
                  (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat + 1 :=
                toNat_succ _ hacesLt255
              have hABn := congrArg UInt8.toNat hAB
              rw [htoNatSucc] at hABn
              have hBm1 : (B - 1).toNat = B.toNat - 1 := UInt8.toNat_sub_of_le _ _ h1B
              have hUeq : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = B - 1 := by
                apply UInt8.toNat_inj.mp
                rw [hBm1]; omega
              have h2 := congrArg UInt8.toInt8 hUeq
              rw [Int8.toInt8_toUInt8] at h2
              have hg2 : p.aces[(SUIT B).toUInt32.toNat]'hs4 < (B - 1).toInt8 := hg
              rw [h2] at hg2
              have hlt := Int8.lt_iff_toInt_lt.mp hg2
              omega
            -- Local copies of the merged-run suit/value facts (mirrors the
            -- `king_frontier` bullet's own copy; scoped to this bullet only).
            have hRCgen : ∀ j : Nat, j ≤ m →
                (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
              (merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
                (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
                (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                hmg j hjm).2
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
            by_cases hAV13 : (VALUE (p.aces.get s).toUInt8).toNat = 13
            · exact Or.inl hAV13
            · have hvalid : SUIT (p.aces.get s).toUInt8 = s.val.toUInt8 ∧
                  (VALUE (p.aces.get s).toUInt8).toNat ≤ 13 ∧
                  SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 ∧
                  (VALUE (p.kings.get s).toUInt8).toNat ≤ 13 ∧
                  p.aces.get s ≤ p.kings.get s := hnf.aces_kings_valid s
              have hAV12 : (VALUE (p.aces.get s).toUInt8).toNat ≤ 12 := by
                have := hvalid.2.1; omega
              have hVlt15 : (VALUE (p.aces.get s).toUInt8).toNat < 15 := by omega
              have hSA : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT (p.aces.get s).toUInt8 :=
                SUIT_succ _ hVlt15
              have hVA : (VALUE ((p.aces.get s).toUInt8 + 1)).toNat =
                  (VALUE (p.aces.get s).toUInt8).toNat + 1 := VALUE_succ _ hVlt15
              have hSAeqSval : SUIT ((p.aces.get s).toUInt8 + 1) = s.val.toUInt8 :=
                hSA.trans hvalid.1
              have hs4v : s.val < 4 := s.isLt
              have hsvalNat : s.val.toUInt8.toNat = s.val := by
                rw [UInt8.toNat_ofNat']; omega
              have hrealA : IsRealCard ((p.aces.get s).toUInt8 + 1) := by
                refine ⟨?_, by omega, by omega⟩
                have hSct := congrArg UInt8.toNat hSAeqSval
                omega
              have hc64 : ((p.aces.get s).toUInt8 + 1).toNat < 64 := by
                have hb1 := VALUE_toNat ((p.aces.get s).toUInt8 + 1)
                have hb2 := SUIT_toNat ((p.aces.get s).toUInt8 + 1)
                have hb3 := congrArg UInt8.toNat hSAeqSval
                omega
              have hp64 : (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat < 10 := by
                unfold cardPile; rw [dif_pos hc64]; exact hwf.card2pile_lt _ hc64
              rcases hnf.foundation_maximal_weak s with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkltA
              · exact absurd h13 hAV13
              · -- disjunct 2 (old): pin down whether `A` sits in `pile` itself.
                have hnfreeOld : ¬ isFreeCard g p ((p.aces.get s).toUInt8 + 1) := hnfreeA
                by_cases hcp : (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat = pile.toNat
                · have hcd5 : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat < 5 := by
                    by_contra hcon
                    push Not at hcon
                    have hle5 := hwf.depth_le _ hrealA
                    have heq5 : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat = 5 := by omega
                    apply hnfreeOld
                    apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                    rw [heq5]
                    exact hnf.pileDepth_bound ⟨(cardPile g
                      ((p.aces.get s).toUInt8 + 1)).toNat, hp64⟩
                  have hcdlt : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat <
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat := by
                    by_contra hgem
                    push Not at hgem
                    apply hnfreeOld
                    apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                    have heqIdx : p.pileDepth[(cardPile g
                        ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 =
                        p.pileDepth[pile.toNat]'hpile := by congr 1
                    rw [heqIdx]
                    have hbdg : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
                    omega
                  have hrt := hwf.round_trip _ hrealA hcd5
                  by_cases hrevealed : (p.pileDepth[pile.toNat]'hpile).toInt.toNat -
                      m ≤ (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat
                  · -- revealed range: pin down k via hcard_pos.
                    set k := (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 -
                        (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat with hkdef
                    have hkm : k ≤ m := by omega
                    obtain ⟨hidxk, heqk⟩ := hcard_pos k hkm
                    have hposEqK : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat k - 1).toUInt32.toNat =
                        (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat := by
                      have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1
                          ).toInt = (p.pileDepth[pile.toNat]'hpile).toInt - k - 1 := by
                        rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                          (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                      have hikn : (0 : Int32) ≤
                          (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1 := by
                        rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
                        omega
                      rw [Int32.toNat_toUInt32_of_le hikn]
                      show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1
                        ).toInt.toNat = (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat
                      rw [hik]; omega
                    have hidxk' : (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat < 5 :=
                      hposEqK ▸ hidxk
                    have hcardEq : (g.pos2card[pile.toNat]'hpile)[
                        (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hidxk'
                        = (p.aces.get s).toUInt8 + 1 := by
                      have hbracket : (g.pos2card.get
                          ⟨(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat, hp64⟩).get
                          ⟨(cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat, hcd5⟩ =
                          (g.pos2card[(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64)[
                            (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hcd5 := rfl
                      rw [hbracket] at hrt
                      rw [show (g.pos2card[(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64)[
                          (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hcd5 =
                          (g.pos2card[pile.toNat]'hpile)[
                            (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hidxk'
                          from by congr 1; congr 1] at hrt
                      exact hrt
                    have hstepPos : (g.pos2card[pile.toNat]'hpile)[
                        (cardDepth g ((p.aces.get s).toUInt8 + 1)).toNat]'hidxk' =
                        (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat k - 1).toUInt32.toNat]'hidxk := by
                      congr 1
                      exact hposEqK.symm
                    rw [hstepPos, heqk] at hcardEq
                    -- `A = B + UInt8.ofNat k`; split on same-suit vs different-suit.
                    by_cases hSB : (SUIT B).toUInt32.toNat = s.val
                    · have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSB
                      subst hseq
                      have hc64' : ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1).toNat < 64 :=
                        hc64
                      have hp64' : (cardPile g
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat < 10 := hp64
                      have hrealA' : IsRealCard
                          ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) := hrealA
                      have hVA' : (VALUE ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)).toNat =
                          (VALUE (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8).toNat + 1 := hVA
                      have hcardEq' : B + UInt8.ofNat k =
                          (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 := hcardEq
                      by_cases hk0 : k = 0
                      · have hAB : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B := by
                          rw [hk0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero] at hcardEq'
                          exact hcardEq'.symm
                        have hf0 := hAeqB_implies_f0 hAB
                        subst hf0
                        refine Or.inr (Or.inr (Or.inl ⟨⟨pile.toNat, hpile⟩, ?_, ?_⟩))
                        · show ((p.pileDepth.set pile.toNat
                              ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                              pile.toNat]'hpile).toInt.toNat > 0
                          rw [Vector.getElem_set_self]
                          show (0 : Nat) <
                            (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
                              ).toInt.toNat
                          rw [hdI8]; omega
                        · have hidx_tgt : (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                              Int32.ofNat m).toInt8).toInt.toNat - 1 =
                              ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m - 1).toUInt32.toNat := by
                            have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m - 1).toInt =
                                (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
                              rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                                (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                            have hikn : (0 : Int32) ≤
                                (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
                              rw [Int32.le_iff_toInt_le, hik,
                                show ((0 : Int32).toInt = 0) from by decide]
                              omega
                            rw [Int32.toNat_toUInt32_of_le hikn]
                            show (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m).toInt8).toInt.toNat - 1 =
                              ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m - 1).toInt.toNat
                            rw [hdI8, hik]; omega
                          have hbnd5m : (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                              Int32.ofNat m).toInt8).toInt.toNat ≤ 5 := by
                            show (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                              Int32.ofNat m).toInt8).toInt.toNat ≤ 5
                            rw [hdI8]; omega
                          have hcardEqSelf : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set
                                pile.toNat ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m).toInt8 hpile)[pile.toNat]'hpile).toInt.toNat - 1]'(by
                                  rw [Vector.getElem_set_self]; omega)
                              = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                                Int32.ofNat m - 1).toUInt32.toNat]'(by rw [← hidx_tgt]; omega) := by
                            congr 1
                            rw [Vector.getElem_set_self, hidx_tgt]
                          have hfluteEqSelf : (p.pileFlute.set pile.toNat
                              ((1 + Int32.ofNat m + Int32.ofNat 0).toUInt32.toUInt8) hpile
                              )[pile.toNat]'hpile =
                              ((1 + Int32.ofNat m + Int32.ofNat 0).toUInt32.toUInt8) := by
                            rw [Vector.getElem_set_self]
                          sorry
                      · -- `k ≥ 1`: `aces[SUIT B] ≥ B`, contradicting `haces_lt_B`.
                        exfalso
                        have hb1 := VALUE_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                        have hb2 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1)
                        have hSAeqB : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                            SUIT B := by
                          have h' : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                              (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4).val.toUInt8 := hSAeqSval
                          rw [h']; exact hsuiteq.symm
                        have hb3 := congrArg UInt8.toNat hSAeqB
                        have hb4 := SUIT_toNat B
                        have hb5' := VALUE_toNat B
                        have hb0v := VALUE_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
                        have hb0s := SUIT_toNat (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8
                        have hSA' : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1) =
                            SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 := hSA
                        have hSAeqAces : SUIT (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 = SUIT B :=
                          hSA'.symm.trans hSAeqB
                        have hb3' := congrArg UInt8.toNat hSAeqAces
                        have hs4' : (SUIT B).toNat < 4 := by rw [← UInt8.toNat_toUInt32]; exact hs4
                        have hlt := Int8.lt_iff_toInt_lt.mp haces_lt_B
                        have htiB : B.toInt8.toInt = (B.toNat : Int) := by
                          have h' : B.toInt8.toInt = ((B.toInt8.toUInt8.toNat : Int)).bmod (2 ^ 8) := by
                            show B.toInt8.toBitVec.toInt = _
                            rw [BitVec.toInt_eq_toNat_bmod]
                            rfl
                          rw [UInt8.toUInt8_toInt8] at h'
                          rw [h', Int.bmod_eq_of_le (by omega) (by omega)]
                        rw [htiB] at hlt
                        have hacesNat : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat =
                            (p.aces[(SUIT B).toUInt32.toNat]'hs4).toInt.toNat :=
                          Int8.toNat_toUInt8_of_le haces0
                        rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at haces0
                        have hVeqCard := congrArg (fun x : UInt8 => (VALUE x).toNat) hcardEq'
                        have hVeq2 := hRCgen k hkm
                        omega
                    · exfalso
                      apply hSB
                      have hSeq2 := congrArg (fun x : UInt8 => (SUIT x).toUInt32.toNat) hcardEq
                      have hSjEq2 := hSjEq k hkm
                      have hb6 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                        UInt8.toNat_toUInt32 (SUIT B)
                      have hb7 := congrArg UInt8.toNat hSjEq2
                      have hb8 := congrArg UInt8.toNat hSAeqSval
                      have hb9 : s.val.toUInt8.toNat = s.val := by
                        rw [UInt8.toNat_ofNat']; omega
                      have hb10 : (SUIT (B + UInt8.ofNat k)).toUInt32.toNat =
                          (SUIT (B + UInt8.ofNat k)).toNat := UInt8.toNat_toUInt32 _
                      have hb11 : (SUIT ((p.aces.get s).toUInt8 + 1)).toUInt32.toNat =
                          (SUIT ((p.aces.get s).toUInt8 + 1)).toNat := UInt8.toNat_toUInt32 _
                      omega
                  · -- not revealed: A is still (more) deeply buried in the
                    -- shrunk pile, so it stays not-free.
                    refine Or.inr (Or.inl ?_)
                    show ¬ isFreeCard g _ ((p.aces.get s).toUInt8 + 1)
                    intro hfreeNew
                    have hge := isFree_to_cardDepth_ge g _ hwf
                      ((p.aces.get s).toUInt8 + 1) hc64 hp64 hfreeNew
                    have hstep : (p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 =
                        (p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        pile.toNat]'hpile := by
                      congr 1
                    rw [hstep, Vector.getElem_set_self] at hge
                    rw [hdI8] at hge
                    omega
                · refine Or.inr (Or.inl ?_)
                  show ¬ isFreeCard g _ ((p.aces.get s).toUInt8 + 1)
                  intro hfreeNew
                  apply hnfreeOld
                  have hge := isFree_to_cardDepth_ge g _ hwf
                    ((p.aces.get s).toUInt8 + 1) hc64 hp64 hfreeNew
                  have heqD : (p.pileDepth.set pile.toNat
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                      (cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 =
                      p.pileDepth[(cardPile g ((p.aces.get s).toUInt8 + 1)).toNat]'hp64 :=
                    Vector.getElem_set_ne hpile hp64 (Ne.symm hcp)
                  rw [heqD] at hge
                  exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
              · -- disjunct 3 (old): the flute-top witness pile `i`.
                by_cases hip : pile.toNat = i.val
                · -- `i = pile`: the normalized entry's own flute is `1`, so the
                  -- witness forces `A = B` exactly (hence same suit as `B`).
                  have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
                  subst hieq
                  have hpb5 : (p.pileDepth[pile.toNat]'hpile).toInt.toNat ≤ 5 :=
                    hnf.pileDepth_bound ⟨pile.toNat, hpile⟩
                  have hfluteEq : (fluteNorm pile hpile p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
                    show (p.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile = 1
                    rw [Vector.getElem_set_self]
                  have heqA' : (g.pos2card[pile.toNat]'hpile)[
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) -
                      ((1 : UInt8) - 1) = (p.aces.get s).toUInt8 + 1 := by
                    sorry
                  rw [show ((1 : UInt8) - 1) = 0 from rfl, UInt8.sub_zero] at heqA'
                  have hposB : (g.pos2card[pile.toNat]'hpile)[
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) = B := by
                    obtain ⟨hidx0, heq0⟩ := hcard_pos 0 (by omega)
                    have hmeq : (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 =
                        (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat 0 - 1).toUInt32.toNat) := by
                      have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat 0 - 1).toInt =
                          (p.pileDepth[pile.toNat]'hpile).toInt - 0 - 1 := by
                        rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                          (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                        omega
                      have hikn : (0 : Int32) ≤
                          (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat 0 - 1 := by
                        rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
                        omega
                      rw [Int32.toNat_toUInt32_of_le hikn]
                      show (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 =
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat 0 - 1).toInt.toNat
                      rw [hik]
                      have hbdg : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                          (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
                      omega
                    rw [show (g.pos2card[pile.toNat]'hpile)[
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) =
                        (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat 0 - 1).toUInt32.toNat)]'hidx0 from by congr 1]
                    rw [heq0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
                  rw [hposB] at heqA'
                  have hAB0 : (p.aces.get s).toUInt8 + 1 = B := heqA'.symm
                  -- Same-suit forced: `SUIT A = SUIT B`.
                  have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
                    have hSAeqB0 : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT B :=
                      congrArg SUIT hAB0
                    have hb1 := congrArg UInt8.toNat hSAeqB0
                    have hb2 := congrArg UInt8.toNat hSAeqSval
                    have hb3 : s.val.toUInt8.toNat = s.val := by
                      rw [UInt8.toNat_ofNat']; omega
                    have hb4 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                      UInt8.toNat_toUInt32 (SUIT B)
                    omega
                  have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
                  subst hseq
                  have hAB : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B := hAB0
                  have hf0 := hAeqB_implies_f0 hAB
                  subst hf0
                  refine Or.inr (Or.inr (Or.inl ⟨⟨pile.toNat, hpile⟩, ?_, ?_⟩))
                  · show ((p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        pile.toNat]'hpile).toInt.toNat > 0
                    rw [Vector.getElem_set_self]
                    show (0 : Nat) <
                      (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat
                    rw [hdI8]; omega
                  · have hidx_tgt : (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat m).toInt8).toInt.toNat - 1 =
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat m - 1).toUInt32.toNat := by
                      have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat m - 1).toInt =
                          (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
                        rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                          (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                      have hikn : (0 : Int32) ≤
                          (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
                        rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
                        omega
                      rw [Int32.toNat_toUInt32_of_le hikn]
                      show (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat m).toInt8).toInt.toNat - 1 =
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat
                      rw [hdI8, hik]; omega
                    have hbnd5m : (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat m).toInt8).toInt.toNat ≤ 5 := by
                      show (((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat m).toInt8).toInt.toNat ≤ 5
                      rw [hdI8]; omega
                    have hcardEqSelf : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth.set
                          pile.toNat ((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat m).toInt8 hpile)[pile.toNat]'hpile).toInt.toNat - 1]'(by
                            rw [Vector.getElem_set_self]; omega)
                        = (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                          Int32.ofNat m - 1).toUInt32.toNat]'(by rw [← hidx_tgt]; omega) := by
                      congr 1
                      rw [Vector.getElem_set_self, hidx_tgt]
                    have hfluteEqSelf : (p.pileFlute.set pile.toNat
                        ((1 + Int32.ofNat m + Int32.ofNat 0).toUInt32.toUInt8) hpile
                        )[pile.toNat]'hpile =
                        ((1 + Int32.ofNat m + Int32.ofNat 0).toUInt32.toUInt8) := by
                      rw [Vector.getElem_set_self]
                    sorry
                · -- `i ≠ pile`: this witness pile is untouched by the cleanup.
                  refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
                  · show ((p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        i.val]'i.isLt).toInt.toNat > 0
                    rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                    have hdi' : (p.pileDepth[i.val]'i.isLt).toInt.toNat > 0 := hdi
                    exact hdi'
                  · have hb5_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat ≤ 5 :=
                      hnf.pileDepth_bound i
                    have hidx_old : (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                    have hb5_new : ((p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        i.val]'i.isLt).toInt.toNat ≤ 5 := by
                      rw [Vector.getElem_set_ne hpile i.isLt (by omega)]; exact hb5_old
                    have hidx_new : ((p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                        i.val]'i.isLt).toInt.toNat - 1 < 5 := by omega
                    have hcardEq3 : (g.pos2card[i.val]'i.isLt)[((p.pileDepth.set pile.toNat
                          ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile)[
                          i.val]'i.isLt).toInt.toNat - 1]'hidx_new
                        = (g.pos2card[i.val]'i.isLt)[
                          (p.pileDepth[i.val]'i.isLt).toInt.toNat - 1]'hidx_old := by
                      congr 1
                      rw [Vector.getElem_set_ne hpile i.isLt (by omega)]
                    have hfluteBridge2 : (fluteNorm pile hpile p).pileFlute[i.val]'i.isLt =
                        p.pileFlute[i.val]'i.isLt := by
                      show (p.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt =
                        p.pileFlute[i.val]'i.isLt
                      exact Vector.getElem_set_ne hpile i.isLt (by omega)
                    sorry
              · -- disjunct 4 (old): `kings`/`aces` are both entirely untouched.
                exact Or.inr (Or.inr (Or.inr hkltA))
          · -- (9) king_frontier: `kings`/`aces`/`busyAces` are entirely
            -- untouched in this branch, so disjunct 1 and the `∀c` part
            -- transfer verbatim/via monotonicity.  Disjunct 2 (`¬isFreeCard`)
            -- needs care since `pile`'s depth shrinks by `m`: the
            -- newly-revealed range (positions `d0-m..d0-1`) holds exactly the
            -- same-suit run `B..B+m-1` (`hcard_pos`), which is provably ALL
            -- strictly below `kings[SUIT B]` (via the entry state's own
            -- `king_frontier`, applied to the still-boundary card `B+m`), so
            -- `kings[s]` (whatever suit `s` is) can never coincide with a
            -- revealed card — ruling out the only way `¬isFreeCard` could
            -- fail to transfer.
            have hRCgen : ∀ j : Nat, j ≤ m →
                (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := fun j hjm =>
              (merge_real_chain g pile hpile hwf (pileHashes[pile.toNat]'hpile) B
                (p.pileDepth[pile.toNat]'hpile).toInt32 m p hreal
                (by rw [Int8.toInt_toInt32]; exact hd5) (by rw [Int8.toInt_toInt32]; omega)
                hmg j hjm).2
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
            obtain ⟨hidxbm, heqbm⟩ := hcard_pos m (le_refl m)
            have hnfreeBm : ¬ isFreeCard g (fluteNorm pile hpile p) (B + UInt8.ofNat m) := by
              rw [← heqbm]
              exact depth_card_not_free hwf hnf ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩ (by
                have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt =
                    (p.pileDepth[pile.toNat]'hpile).toInt - m - 1 := by
                  rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                    (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                have hikn : (0 : Int32) ≤
                    (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1 := by
                  rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
                  omega
                show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toUInt32.toNat <
                  (p.pileDepth[pile.toNat]'hpile).toInt.toNat
                rw [Int32.toNat_toUInt32_of_le hikn]
                show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m - 1).toInt.toNat <
                  (p.pileDepth[pile.toNat]'hpile).toInt.toNat
                rw [hik]
                have hbdg : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                    (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
                omega)
            -- `kings[SUIT B]` is at least as large as the still-boundary card
            -- `B+m` (its own `∀c` clause forces this, via `hnfreeBm`'s
            -- contrapositive).
            have hrealBm : IsRealCard (B + UInt8.ofNat m) := by
              rw [← heqbm]; exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ ⟨_, hidxbm⟩
            have hVKge : (VALUE (p.kings.get
                (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat ≥
                (VALUE (B + UInt8.ofNat m)).toNat := by
              by_contra hlt
              push Not at hlt
              apply hnfreeBm
              have hall := (hnf.king_frontier (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).2
              exact hall _ ((hSjEq m (le_refl m)).trans hsuiteq) hlt hrealBm.2.2
            constructor
            · rcases (hnf.king_frontier s).1 with case1 | ⟨hv1, hnfree⟩
              · exact Or.inl case1
              · refine Or.inr ⟨hv1, ?_⟩
                have hSs : SUIT (p.kings.get s).toUInt8 = s.val.toUInt8 :=
                  (hnf.aces_kings_valid s).2.2.1
                have hc64 : (p.kings.get s).toUInt8.toNat < 64 := by
                  have hb1 := VALUE_toNat (p.kings.get s).toUInt8
                  have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                  have hb3 := congrArg UInt8.toNat hSs
                  have hb4 : s.val.toUInt8.toNat = s.val := by rw [UInt8.toNat_ofNat']; omega
                  have hb5 := (hnf.aces_kings_valid s).2.2.2.1
                  omega
                have hp64 : (cardPile g (p.kings.get s).toUInt8).toNat < 10 := by
                  unfold cardPile; rw [dif_pos hc64]; exact hwf.card2pile_lt _ hc64
                intro hfree'
                apply hnfree
                by_cases hcp : (cardPile g (p.kings.get s).toUInt8).toNat = pile.toNat
                · exfalso
                  have hge := isFree_to_cardDepth_ge g _ hwf (p.kings.get s).toUInt8 hc64 hp64 hfree'
                  have heqDm : (p.pileDepth.set pile.toNat
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                      )[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 := by
                    rw [show (p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                        )[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                        (p.pileDepth.set pile.toNat
                        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                        )[pile.toNat]'hpile from by congr 1, Vector.getElem_set_self]
                  rw [heqDm] at hge
                  have hcdge : (cardDepth g (p.kings.get s).toUInt8).toNat ≥
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat - m := by
                    rw [hdI8] at hge
                    omega
                  have hcdlt : (cardDepth g (p.kings.get s).toUInt8).toNat <
                      (p.pileDepth[pile.toNat]'hpile).toInt.toNat := by
                    by_contra hgem
                    push Not at hgem
                    apply hnfree
                    apply isFree_of_cardDepth_ge g p hwf _ hc64 hp64
                    have heqIdx : p.pileDepth[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                        p.pileDepth[pile.toNat]'hpile := by congr 1
                    rw [heqIdx]
                    have hbdg2 : (p.pileDepth[pile.toNat]'hpile).toNatClampNeg =
                        (p.pileDepth[pile.toNat]'hpile).toInt.toNat := rfl
                    omega
                  have hcd5 : (cardDepth g (p.kings.get s).toUInt8).toNat < 5 := by
                    have hreal' : IsRealCard (p.kings.get s).toUInt8 := ⟨by
                      have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                      have hb3 := congrArg UInt8.toNat hSs
                      have hb4 : s.val.toUInt8.toNat = s.val := by
                        rw [UInt8.toNat_ofNat']; omega
                      omega, sorry, (hnf.aces_kings_valid s).2.2.2.1⟩
                    have := hwf.depth_le _ hreal'
                    omega
                  have hreal' : IsRealCard (p.kings.get s).toUInt8 := ⟨by
                    have hb2 := SUIT_toNat (p.kings.get s).toUInt8
                    have hb3 := congrArg UInt8.toNat hSs
                    have hb4 : s.val.toUInt8.toNat = s.val := by
                      rw [UInt8.toNat_ofNat']; omega
                    omega, sorry, (hnf.aces_kings_valid s).2.2.2.1⟩
                  have hrt := hwf.round_trip (p.kings.get s).toUInt8 hreal' hcd5
                  set k := (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1 -
                      (cardDepth g (p.kings.get s).toUInt8).toNat with hkdef
                  have hkm : k ≤ m := by omega
                  obtain ⟨hidxk, heqk⟩ := hcard_pos k hkm
                  have hposEqK : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1
                      ).toUInt32.toNat = (cardDepth g (p.kings.get s).toUInt8).toNat := by
                    have hik : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toInt =
                        (p.pileDepth[pile.toNat]'hpile).toInt - k - 1 := by
                      rw [depth_sub_ofNat_sub_one_eq (by rw [Int8.toInt_toInt32]; exact hd5)
                        (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
                    have hikn : (0 : Int32) ≤
                        (p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1 := by
                      rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]
                      omega
                    rw [Int32.toNat_toUInt32_of_le hikn]
                    show ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toInt.toNat =
                      (cardDepth g (p.kings.get s).toUInt8).toNat
                    rw [hik]
                    omega
                  have hidxk' : (cardDepth g (p.kings.get s).toUInt8).toNat < 5 := hposEqK ▸ hidxk
                  have hcardEq : (g.pos2card[pile.toNat]'hpile)[
                      (cardDepth g (p.kings.get s).toUInt8).toNat]'hidxk'
                      = (p.kings.get s).toUInt8 := by
                    have hbracket : (g.pos2card.get
                        ⟨(cardPile g (p.kings.get s).toUInt8).toNat, hp64⟩).get
                        ⟨(cardDepth g (p.kings.get s).toUInt8).toNat, hcd5⟩ =
                        (g.pos2card[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64)[
                          (cardDepth g (p.kings.get s).toUInt8).toNat]'hcd5 := rfl
                    rw [hbracket] at hrt
                    rw [show (g.pos2card[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64)[
                        (cardDepth g (p.kings.get s).toUInt8).toNat]'hcd5 =
                        (g.pos2card[pile.toNat]'hpile)[
                          (cardDepth g (p.kings.get s).toUInt8).toNat]'hidxk'
                        from by congr 1; congr 1] at hrt
                    exact hrt
                  have hstepPos : (g.pos2card[pile.toNat]'hpile)[
                      (cardDepth g (p.kings.get s).toUInt8).toNat]'hidxk' =
                      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32 -
                        Int32.ofNat k - 1).toUInt32.toNat]'hidxk := by
                    congr 1
                    exact hposEqK.symm
                  rw [hstepPos, heqk] at hcardEq
                  -- `kings[s] = B + UInt8.ofNat k`; split on whether `s` is
                  -- `SUIT B`'s own suit index (VALUE contradiction) or not
                  -- (SUIT contradiction).
                  by_cases hSB : (SUIT B).toUInt32.toNat = s.val
                  · have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSB
                    have hVeq := hRCgen k hkm
                    have hVBm := hRCgen m (le_refl m)
                    have hkingEq : (p.kings.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8 =
                        B + UInt8.ofNat k := by rw [hseq]; exact hcardEq.symm
                    have hVeqS : (VALUE (p.kings.get
                        (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4)).toUInt8).toNat =
                        (VALUE B).toNat + k := by rw [hkingEq]; exact hVeq
                    have hkltm : k < m := by omega
                    omega
                  · apply hSB
                    have hSeq2 := congrArg (fun x : UInt8 => (SUIT x).toUInt32.toNat) hcardEq
                    have hSjEq2 := hSjEq k hkm
                    have hb6 : (SUIT B).toUInt32.toNat = (SUIT B).toNat :=
                      UInt8.toNat_toUInt32 (SUIT B)
                    have hb7 := congrArg UInt8.toNat hSjEq2
                    have hb8 := congrArg UInt8.toNat hSs
                    have hb9 : s.val.toUInt8.toNat = s.val := by
                      rw [UInt8.toNat_ofNat']; omega
                    have hb10 : (SUIT (B + UInt8.ofNat k)).toUInt32.toNat =
                        (SUIT (B + UInt8.ofNat k)).toNat := UInt8.toNat_toUInt32 _
                    have hb11 : (SUIT (p.kings.get s).toUInt8).toUInt32.toNat =
                        (SUIT (p.kings.get s).toUInt8).toNat := UInt8.toNat_toUInt32 _
                    omega
                · have heqDepth : (p.pileDepth.set pile.toNat
                      ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile
                      )[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 =
                      p.pileDepth[(cardPile g (p.kings.get s).toUInt8).toNat]'hp64 :=
                    Vector.getElem_set_ne hpile hp64 (Ne.symm hcp)
                  have hge := isFree_to_cardDepth_ge g _ hwf (p.kings.get s).toUInt8 hc64 hp64 hfree'
                  rw [heqDepth] at hge
                  exact isFree_of_cardDepth_ge g p hwf _ hc64 hp64 hge
            · intro c hSc hgt hle
              exact isFreeCard_mono hdec ((hnf.king_frontier s).2 c hSc hgt hle)
        · -- (8) hash_def: the merge loop subtracted m·ph, matching the depth
          -- decrease of m at `pile` in the dot product.
          show p.hash - UInt32.ofNat m * (pileHashes[pile.toNat]'hpile) =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              (((p.pileDepth.set pile.toNat
                ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8 hpile).get i)
                ).toInt.toNat.toUInt32) 0
          have hhd : p.hash = (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              (p.pileDepth.get i).toInt.toNat.toUInt32) 0 := hnf.hash_def
          have hclamp : (p.pileDepth[pile.toNat]'hpile).toInt.toNat =
              (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
                ).toInt.toNat + m := by
            show (p.pileDepth[pile.toNat]'hpile).toInt.toNat =
              (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8).toInt.toNat + m
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
        · -- (10) usedSpace_def: depth shrinks by `m` and the flute-term at
          -- `pile` goes from 0 (normalized entry: depth `d0`>0, flute 1) to
          -- `m+f` (depth `d0-m`>0, flute `1+m+f`); combined with the `f`
          -- lost from `usedSpace` itself, the ledger balances exactly.
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
      by_cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 ==
          (B - 1 - UInt8.ofNat f).toInt8) = true
      · simp only [hk, hba, Bool.false_eq_true, reduceIte]
        exact nf_setBusyAces key ((1 : UInt8) <<< SUIT B)
      · rw [Bool.not_eq_true] at hba
        simp only [hk, hba, Bool.false_eq_true, reduceIte]
        simpa using nf_setBusyAces key 0

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
      SolverInvMerged g p' := by
  sorry

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
      SolverInvMerged g p' := by
  rw [removeFlute_eq pile g p hpile]
  exact cleanupPile_merged pile g (removeFlutePre pile hpile p) hpile hwf hready

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
  obtain ⟨hnf, hfp, hpm⟩ := hpre
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
    refine ⟨0xffff, _, hrun, ⟨?_, ?_, ?_⟩, ?_⟩
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
    · -- frame: other piles' depths untouched (set only at index k)
      intro j hj
      exact Vector.getElem_set_ne (show (UInt32.ofNat k).toNat < 10 by rw [hpkn]; exact hk)
        j.isLt (by rw [hpkn]; omega)
  · -- LOOP-BEARING CASE: pileDepth[k] > 0 — merge/freed while loops run.
    sorry

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
      SolverInvMerged g p' := by
  sorry

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

/-- **The drain loop reaches canonical form.**  From a merged state, draining
    `busyAces` (via `drainLoop`, with enough fuel) yields a fully canonical state. -/
theorem drain_canonical (g : Globals) (p : SolverPosType) (fk0 : UInt16)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) :
    ∃ fk p', EStateM.run (SolverModel.drainLoop 64 fk0) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' := by
  sorry

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
