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
      rw [haeq, hnewkingsInt8]
      rcases hkey with haceq | ⟨hacest, hCrealPrev, _⟩
      · exact Or.inr (Or.inr (Or.inr haceq))
      · rcases hsc.foundation_maximal_weak with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkeqK
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
        · -- disjunct 3: witness `i`; `i = pile` is impossible (would force
          -- `aces = prevCard` exactly, contradicting `hacest`).
          by_cases hip : i.val = pile.toNat
          · exfalso
            have hieq : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hip
            subst hieq
            have heqA' : (p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4)).toUInt8 =
                K - p.pileFlute[pile.toNat]'hpile := by
              have step := congrArg (· - p.pileFlute[pile.toNat]'hpile) hKeqBoundary
              rw [← step]; exact heqA
            have heqA'' : p.aces.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) =
                (K - p.pileFlute[pile.toNat]'hpile).toInt8 := by
              have h := congrArg (fun x : UInt8 => x.toInt8) heqA'
              rwa [Int8.toInt8_toUInt8] at h
            rw [heqA''] at hacest
            have := Int8.lt_iff_toInt_lt.mp hacest
            omega
          · refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
            · rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip]; exact hdi
            · have hdeqI := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip
              have hfeqI := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p i hip
              have hidxEqI : ((kingMove pile hpile suit hs4 ph p).pileDepth.get i).toInt.toNat - 1
                  = (p.pileDepth.get i).toInt.toNat - 1 := by rw [hdeqI]
              have hcardEq3 : (g.pos2card.get i).get ⟨((kingMove pile hpile suit hs4 ph p
                    ).pileDepth.get i).toInt.toNat - 1, by rw [hdeqI]; have := hpdb i; omega⟩
                  = (g.pos2card.get i).get ⟨(p.pileDepth.get i).toInt.toNat - 1,
                    by have := hpdb i; omega⟩ := by
                congr 1
                exact Fin.ext hidxEqI
              rw [hcardEq3, hfeqI]
              exact heqA
        · exfalso
          have hOldKingsInt8 : p.kings.get (⟨(SUIT K).toUInt32.toNat, hsK⟩ : Fin 4) = K.toInt8 := by
            have h := congrArg (fun x : UInt8 => x.toInt8) hKingsEqK
            rwa [Int8.toInt8_toUInt8] at h
          rw [hOldKingsInt8] at hkeqK
          rw [hkeqK] at hacest
          have h1 := Int8.lt_iff_toInt_lt.mp hacest
          have h2 := Int8.lt_iff_toInt_lt.mp hprevLtK
          omega
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
    · rw [haeq, hkingsEq]
      by_cases hAV13 : (VALUE (p.aces.get s).toUInt8).toNat = 13
      · exact Or.inl hAV13
      · have hAV12 : (VALUE (p.aces.get s).toUInt8).toNat ≤ 12 := by
          have := hsc.aces_kings_valid.2.1
          omega
        rcases hsc.foundation_maximal_weak with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkeqK
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
        · by_cases hip : i.val = pile.toNat
          · exfalso
            have hieq : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hip
            subst hieq
            apply hsame
            have heqA' : (p.aces.get s).toUInt8 = K - p.pileFlute[pile.toNat]'hpile := by
              have step := congrArg (· - p.pileFlute[pile.toNat]'hpile) hKeqBoundary
              rw [← step]; exact heqA
            have hSUITaces : SUIT (p.aces.get s).toUInt8 = SUIT K := by
              rw [heqA']; exact hSUITprev
            have hb1 := congrArg UInt8.toNat (hSUITaces.symm.trans hsc.aces_kings_valid.1)
            have hb2 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            have hb3 : (SUIT K).toUInt32.toNat = (SUIT K).toNat := UInt8.toNat_toUInt32 (SUIT K)
            omega
          · refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
            · rw [kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip]; exact hdi
            · have hdeqI := kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i hip
              have hfeqI := kingMove_pileFlute_eq_of_ne pile hpile suit hs4 ph p i hip
              have hidxEqI : ((kingMove pile hpile suit hs4 ph p).pileDepth.get i).toInt.toNat - 1
                  = (p.pileDepth.get i).toInt.toNat - 1 := by rw [hdeqI]
              have hcardEq3 : (g.pos2card.get i).get ⟨((kingMove pile hpile suit hs4 ph p
                    ).pileDepth.get i).toInt.toNat - 1, by rw [hdeqI]; have := hpdb i; omega⟩
                  = (g.pos2card.get i).get ⟨(p.pileDepth.get i).toInt.toNat - 1,
                    by have := hpdb i; omega⟩ := by
                congr 1
                exact Fin.ext hidxEqI
              rw [hcardEq3, hfeqI]
              exact heqA
        · exact Or.inr (Or.inr (Or.inr hkeqK))
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
  · -- (4b-weak) foundation_maximal_weak: `aces`/`kings` untouched, so only the
    -- `¬isFreeCard`/flute-top-witness disjuncts need real work, and only for
    -- `s = SUIT B` (any other suit's witness can't be a merge-absorbed card).
    rw [haeq, hkeqV]
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
      rcases (hnf.suitClean s).foundation_maximal_weak with h13 | hnfreeA | ⟨i, hdi, heqA⟩ | hkltA
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
            refine Or.inr (Or.inr (Or.inl ⟨⟨pile.toNat, hpile⟩, ?_, ?_⟩))
            · show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m 0 p).pileDepth[pile.toNat]'hpile
                  ).toInt.toNat > 0
              rw [hpd]
              show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
                ).toInt.toNat > 0
              omega
            · show (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
                (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
                    (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32
                    m 0 p).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut -
                (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                  (p.pileDepth[pile.toNat]'hpile).toInt32 m 0 p).pileFlute[pile.toNat]'hpile
              rw [hcardEqOut, hpf, hprevEq, hAeqBm1_of hAB, show UInt8.ofNat 0 = 0 from rfl,
                UInt8.sub_zero]
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
      · -- disjunct 3: a flute-top witness pile `i`.
        by_cases hip : pile.toNat = i.val
        · -- `i = pile`: the entry's own (normalized) flute is `1`, forcing
          -- `A = B` exactly.
          have hieq : i = ⟨pile.toNat, hpile⟩ := Fin.ext hip.symm
          subst hieq
          have hfluteEq : (fluteNorm pile hpile p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
            show (p.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile = 1
            rw [Vector.getElem_set_self]
          have heqA' : (p.aces.get s).toUInt8 = (g.pos2card[pile.toNat]'hpile)[
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) - 1 := by
            have h := heqA
            rw [hfluteEq] at h
            exact h
          have hposB : (g.pos2card[pile.toNat]'hpile)[
              (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) = B := by
            obtain ⟨hidx0, heq0⟩ := hmcards 0 (by omega)
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
              omega
            rw [show (g.pos2card[pile.toNat]'hpile)[
                (p.pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'(by omega) =
                (g.pos2card[pile.toNat]'hpile)[(((p.pileDepth[pile.toNat]'hpile).toInt32 -
                  Int32.ofNat 0 - 1).toUInt32.toNat)]'hidx0 from by congr 1]
            rw [heq0, show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
          rw [hposB] at heqA'
          -- `heqA' : (p.aces.get s).toUInt8 = B - 1`; convert to `A + 1 = B`.
          have hAB0 : (p.aces.get s).toUInt8 + 1 = B := by
            apply UInt8.toNat_inj.mp
            rw [UInt8.toNat_add, heqA', UInt8.toNat_sub_of_le _ _ h1B,
              show (1 : UInt8).toNat = 1 from rfl]
            have hB1 : 1 ≤ B.toNat := by
              have h := h1B
              rw [UInt8.le_iff_toNat_le, show (1 : UInt8).toNat = 1 from rfl] at h
              exact h
            omega
          have hSAeqB0 : SUIT ((p.aces.get s).toUInt8 + 1) = SUIT B := congrArg SUIT hAB0
          have hSBeqval : SUIT B = s.val.toUInt8 := hSAeqB0.symm.trans hSAeqSval
          have hSBeq : (SUIT B).toUInt32.toNat = s.val := by
            have hb1 := congrArg UInt8.toNat hSBeqval
            have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
            have hb3 : (s.val.toUInt8).toNat = s.val := by
              rw [UInt8.toNat_ofNat']; have := s.isLt; omega
            omega
          have hseq : (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) = s := Fin.ext hSBeq
          subst hseq
          have hAB0' : (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 + 1 = B := hAB0
          have hf0 := hAeqB_implies_f0 hAB0'
          subst hf0
          refine Or.inr (Or.inr (Or.inl ⟨⟨pile.toNat, hpile⟩, ?_, ?_⟩))
          · show ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m 0 p).pileDepth[pile.toNat]'hpile
                ).toInt.toNat > 0
            rw [hpd]
            show (((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toInt8
              ).toInt.toNat > 0
            omega
          · show (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8 =
              (g.pos2card[pile.toNat]'hpile)[((preCleanupPile pile hpile B
                  (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32
                  m 0 p).pileDepth[pile.toNat]'hpile).toInt.toNat - 1]'hboundOut -
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m 0 p).pileFlute[pile.toNat]'hpile
            rw [hcardEqOut, hpf, hprevEq, hAeqBm1_of hAB0', show UInt8.ofNat 0 = 0 from rfl,
              UInt8.sub_zero]
        · -- `i ≠ pile`: untouched.
          refine Or.inr (Or.inr (Or.inl ⟨i, ?_, ?_⟩))
          · rw [preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile)
              hs4 p m f i (by omega)]
            exact hdi
          · have hfluteBridge_i : (fluteNorm pile hpile p).pileFlute.get i = p.pileFlute.get i :=
              Vector.getElem_set_ne hpile i.isLt (by omega)
            rw [hfluteBridge_i] at heqA
            have hpdEqI : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i =
                p.pileDepth.get i :=
              preCleanupPile_pileDepth_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                p m f i (by omega)
            have hpfEqI : (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileFlute.get i =
                p.pileFlute.get i :=
              preCleanupPile_pileFlute_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                p m f i (by omega)
            have hpb5i : (p.pileDepth.get i).toInt.toNat ≤ 5 := hnf.pileDepth_bound i
            have hidxEqI : ((preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get i).toInt.toNat - 1 =
                (p.pileDepth.get i).toInt.toNat - 1 :=
              congrArg (fun d => d.toInt.toNat - 1) hpdEqI
            have hcardEq3 : (g.pos2card.get i).get ⟨((preCleanupPile pile hpile B
                  (pileHashes[pile.toNat]'hpile) hs4 (p.pileDepth[pile.toNat]'hpile).toInt32 m f
                  p).pileDepth.get i).toInt.toNat - 1,
                by rw [hidxEqI]; omega⟩
                = (g.pos2card.get i).get ⟨(p.pileDepth.get i).toInt.toNat - 1,
                  by omega⟩ := by
              congr 1
              exact Fin.ext hidxEqI
            rw [hcardEq3, hpfEqI]
            exact heqA
      · exact Or.inr (Or.inr (Or.inr hkltA))
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
         (g, { p with freePiles := p.freePiles + 1,
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
                |>.foldl (·+·) 0 : Nat)),
          EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok
            (0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4)
            (g, kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
                  (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                    (p.pileDepth[pile.toNat]'hpile).toInt32 m f p))))) := by
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
    -- Reconnect to the real run via `cleanupRunResult_eq`, then case-split
    -- on the lone-king condition.
    -- ------------------------------------------------------------------
    have hm_le_int : (m : Int) ≤ (p.pileDepth[pile.toNat]'hpile).toInt - 1 := by omega
    rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hmf128] at hrun
    cases hk : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1 &&
        VALUE (B + UInt8.ofNat m) == 13) with
    | false =>
      simp only [hk, Bool.false_eq_true, reduceIte] at hrun
      refine ⟨0xffff, preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p, ?_, ?_⟩
      · exact hrun
      · refine ⟨fun i => ?_, fun s => ?_, ?_, ?_⟩
        · by_cases hij : i.val = pile.toNat
          · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
            subst hii
            exact preCleanupPile_pileBase_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx
              hBdef.symm m f hm_le_int hmcards hf_le hffree
          · exact preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p
              m f hd5 (by omega) i hij (hnfp i hij)
        · exact preCleanupPile_suitClean pile g p hpile hwf hnf B hs4 hd1 hd5 hidx hBdef.symm
            m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop s
        · exact preCleanupPile_hash_def pile g p hpile hnf B hs4 hd5 m f hm_le_int
        · exact preCleanupPile_usedSpace_def pile g p hpile hwf hnf B hs4 hd hd5 m f hm_le_int
            hf_le hBrange.2
    | true =>
      simp only [hk, reduceIte] at hrun
      have hpc := preCleanupPile_pileClean_self pile g p hpile hwf hnf B hs4 hd1 hd5 hidx
        hBdef.symm m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop
      have hpdb_all := preCleanupPile_pileDepth_bound_all pile g p hpile hwf hnf B hs4 hd1 hd5
        hidx hBdef.symm m f hm_le_int hmcards hf_le hffree
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
      have hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8 :=
        fun t => (hnf.suitClean t).aces_kings_valid.1
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
      refine ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
        kingMove pile hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
          (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
            (p.pileDepth[pile.toNat]'hpile).toInt32 m f p), ?_, ?_⟩
      · exact hrun
      · refine ⟨fun i => ?_, fun s => ?_, ?_, ?_⟩
        · by_cases hij : i.val = pile.toNat
          · have hii : i = ⟨pile.toNat, hpile⟩ := Fin.ext hij
            subst hii
            exact (kingMove_pileClean_self pile g hpile (SUIT B) hs4
              (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p)).toPileBase
          · exact kingMove_pileBase_ne pile g hpile (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
              (preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
                (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) i hij
              (preCleanupPile_pileBase_ne pile g hpile B (pileHashes[pile.toNat]'hpile) hs4 p m f
                hd5 (by omega) i hij (hnfp i hij))
        · exact kingMove_suitClean pile g hpile hwf (SUIT B) hs4 (pileHashes[pile.toNat]'hpile)
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
  obtain ⟨hnf, hfp, hpm, hfluteRest⟩ := hpre
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
    -- This mirrors `cleanupPile_base`'s loop-bearing case almost verbatim
    -- (same guard-derivation preamble, same `cleanupRunResult_eq` case split
    -- into non-king/king branches), substituting `pile := UInt32.ofNat k`,
    -- `hpile := hk_` throughout, and bridging `hnf`/`hpm`/`hfluteRest` (the
    -- `MergedUpTo` witnesses) to `cleanupPile_base`'s `fluteNorm`'d
    -- precondition.  Each branch's final `refine` is extended from a bare
    -- `SolverInvBase g p'` into the full 4-conjunct `MergedUpTo g p' (k+1)`
    -- plus the frame condition, using the modular `_ne`/`_self` lemmas already
    -- proved for `preCleanupPile`/`kingMove`.
    have hk_ : (UInt32.ofNat k).toNat < 10 := by rw [hpkn]; exact hk
    -- Bridge the outer `¬(pileDepth[k] = 0)` (stated via `.get ⟨k,hk⟩`) to the
    -- `[]`-indexed form `cleanupPile_base`'s body expects.
    have hfinEq : (⟨(UInt32.ofNat k).toNat, hk_⟩ : Fin 10) = (⟨k, hk⟩ : Fin 10) := Fin.ext hpkn
    have hd : p.pileDepth[(UInt32.ofNat k).toNat]'hk_ ≠ 0 := by
      show p.pileDepth.get (⟨(UInt32.ofNat k).toNat, hk_⟩ : Fin 10) ≠ 0
      rw [hfinEq]
      exact hdk
    -- Pile `k` hasn't been reached by the loop yet, so `hfluteRest` says its
    -- flute is already the default `1`, making `fluteNorm` a no-op here — this
    -- is exactly what bridges `MergedUpTo`'s raw base layer to
    -- `cleanupPile_base`'s `fluteNorm`'d precondition.
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
    -- (`fluteNorm` only changes `pileFlute`, so all depth/aces facts of `hnf_`
    -- transfer to `p` definitionally.)
    have hnn : (0 : Int8) ≤ p.pileDepth[(UInt32.ofNat k).toNat]'hk_ :=
      hnf_.pileDepth_nonneg ⟨(UInt32.ofNat k).toNat, hk_⟩
    have hd1 : 0 < (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt := by
      rw [Int8.le_iff_toInt_le, show ((0 : Int8).toInt = 0) from rfl] at hnn
      have hne : (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt ≠ 0 :=
        fun h => hd (Int8.toInt_inj.mp h)
      omega
    have hd5 : (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt ≤ 5 := by
      have hb := hnf_.pileDepth_bound ⟨(UInt32.ofNat k).toNat, hk_⟩
      have : (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat ≤ 5 := hb
      omega
    have h1le : (1 : Int32) ≤ (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 := by
      rw [Int32.le_iff_toInt_le, Int32.toInt_one, Int8.toInt_toInt32]; omega
    have hsubd : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toInt =
        (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - 1 := by
      rw [Int32.toInt_sub_of_le _ _ (by decide) h1le, Int32.toInt_one, Int8.toInt_toInt32]
    have hidx : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat < 5 := by
      rw [Int32.toNat_toUInt32_of_le (by
        rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]; omega)]
      show ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toInt.toNat < 5
      omega
    -- The boundary card is a real card (WellFormedLayout).
    have hreal : IsRealCard ((g.pos2card[(UInt32.ofNat k).toNat]'hk_)[
        ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat]'hidx) :=
      hwf.pos2card_real ⟨(UInt32.ofNat k).toNat, hk_⟩
        ⟨((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat, hidx⟩
    set B := (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[
      ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat]'hidx with hBdef
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
        (hnf_.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩).1
    -- The boundary card is still physically in the (UInt32.ofNat k) (`boundary_not_free`,
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
      have hacesEq : (fluteNorm (UInt32.ofNat k) hk_ p).aces = p.aces := rfl
      have hak := hacesEq ▸ hnf_.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
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
      have hfree : isFreeCard g (fluteNorm (UInt32.ofNat k) hk_ p) B :=
        hnf_.foundation_cards_free ⟨(SUIT B).toUInt32.toNat, hs4⟩ B hsuiteq hreal.2.1 hVBS
      have hnfB : ¬ isFreeCard g (fluteNorm (UInt32.ofNat k) hk_ p) B := by
        rw [hBdef]
        exact depth_card_not_free hwf hnf_ ⟨(UInt32.ofNat k).toNat, hk_⟩
          ⟨((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat, hidx⟩ (by
            show ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toUInt32.toNat <
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat
            rw [Int32.toNat_toUInt32_of_le (by
              rw [Int32.le_iff_toInt_le, hsubd, show ((0 : Int32).toInt = 0) from by decide]
              omega)]
            show ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - 1).toInt.toNat <
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat
            omega)
      exact hnfB hfree
    -- Every same-suit card `aces[SUIT B]` represents lies within `SUIT B`'s
    -- own 16-wide code block (never below it) — the counterpart lower bound
    -- to `foundation_cards_free`'s implicit upper range, needed to rule out
    -- the freed loop crossing into a different suit's card block.
    have haces_ge : (16 : Nat) * (SUIT B).toUInt32.toNat ≤
        (p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8.toNat := by
      have hacesEq : (fluteNorm (UInt32.ofNat k) hk_ p).aces = p.aces := rfl
      have hak := hacesEq ▸ hnf_.aces_kings_valid ⟨(SUIT B).toUInt32.toNat, hs4⟩
      have hgetEq : p.aces.get (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) =
          p.aces[(SUIT B).toUInt32.toNat]'hs4 := rfl
      have hSuitAces : SUIT ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8) = SUIT B := by
        rw [← hgetEq, hak.1, ← hsuiteq]
      have hb1 := SUIT_toNat ((p.aces[(SUIT B).toUInt32.toNat]'hs4).toUInt8)
      have hsEq := congrArg UInt8.toNat hSuitAces
      have hb2 : (SUIT B).toUInt32.toNat = (SUIT B).toNat := UInt8.toNat_toUInt32 (SUIT B)
      omega
    -- `fluteNorm` only ever changes `pileFlute[(UInt32.ofNat k)]`, so `hnf_`'s `PileBase`
    -- facts about any OTHER (UInt32.ofNat k) transfer to `p` (not `fluteNorm (UInt32.ofNat k) hk_ p`)
    -- verbatim — needed since `preCleanupPile_pileBase_ne`/`kingMove_pileBase_ne`
    -- are stated about `p` directly (they don't take the full `SolverInvBase`
    -- and re-derive the bridge themselves).
    have hnfp : ∀ i : Fin 10, i.val ≠ (UInt32.ofNat k).toNat → PileBase g p i := by
      intro i hij
      have hfeq : (fluteNorm (UInt32.ofNat k) hk_ p).pileFlute.get i = p.pileFlute.get i := by
        show (fluteNorm (UInt32.ofNat k) hk_ p).pileFlute[i.val]'i.isLt = p.pileFlute[i.val]'i.isLt
        simp only [fluteNorm]
        exact Vector.getElem_set_ne hk_ i.isLt (Ne.symm hij)
      have hb := hnf_.pileBase i
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
      cleanupPile_nonempty_eq (UInt32.ofNat k) g p B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hk_ rfl
        hd1 hd5 hidx hBdef.symm hs4 hprev64 hwf.card2pile_lt haces0
    -- ------------------------------------------------------------------
    -- Guard-derived arithmetic: bounds on the iteration counts (no wraps).
    -- ------------------------------------------------------------------
    -- The merge loop runs at most depth−1 times: the guard at step
    -- `depth.toNat − 1` would need `1 < depth − (depth−1) = 1`.
    have hm_le : m ≤ (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat - 1 := by
      by_contra hgt
      push Not at hgt
      have hg := (hmg ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat - 1) (by omega)).1
      simp only [mergeIter_eq] at hg
      rw [Int32.lt_iff_toInt_lt, Int32.toInt_one] at hg
      have hofk : (Int32.ofNat ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat - 1)).toInt =
          (((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt.toNat - 1 : Nat) : Int) := by
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
    have hdepth1I : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m).toInt =
        (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m := by
      rw [Int32.toInt_sub_of_le _ _
        (by rw [Int32.le_iff_toInt_le, hmofI, show ((0 : Int32).toInt = 0) from by decide]; omega)
        (by rw [Int32.le_iff_toInt_le, hmofI, Int8.toInt_toInt32]; omega),
        hmofI, Int8.toInt_toInt32]
    have hmcards : ∀ kk, kk ≤ m → ∃ h5 : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 -
          Int32.ofNat kk - 1).toUInt32.toNat < 5,
        (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 -
          Int32.ofNat kk - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat kk := by
      intro kk hkm
      rcases Nat.eq_zero_or_pos kk with hk0 | hkpos
      · subst hk0
        refine ⟨by simpa using hidx, ?_⟩
        simp only [show Int32.ofNat 0 = 0 from rfl, Int32.sub_zero,
          show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero]
        exact hBdef.symm
      · have hd0 : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32).toInt ≤ 5 := by
          rw [Int8.toInt_toInt32]; exact hd5
        have hmlt : (m : Int) < ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32).toInt := by
          rw [Int8.toInt_toInt32]; omega
        exact merge_pos_chain g (UInt32.ofNat k) hk_ (pileHashes[(UInt32.ofNat k).toNat]'hk_) B
          (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m p hd0 hmlt hmg kk hkpos hkm
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
    have hmstop : (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m ≤ 1 ∨
        (1 < (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m ∧
          ∃ h5 : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2
            ).toUInt32.toNat < 5,
            (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 -
              Int32.ofNat m - 2).toUInt32.toNat]'h5 ≠ B + UInt8.ofNat (m + 1)) := by
      by_cases hle1 : (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m ≤ 1
      · exact Or.inl hle1
      · push_neg at hle1
        right
        have h1lt : (1 : Int32) < (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m := by
          rw [Int32.lt_iff_toInt_lt, Int32.toInt_one, hdepth1I]; omega
        have hidx2 : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2
            ).toUInt32.toNat < 5 := by
          have hik : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2).toInt =
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - m - 2 := by
            rw [depth_sub_ofNat_sub_two_eq (by rw [Int8.toInt_toInt32]; exact hd5)
              (by rw [Int8.toInt_toInt32]; omega), Int8.toInt_toInt32]
          have hikn : (0 : Int32) ≤
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2 := by
            rw [Int32.le_iff_toInt_le, hik, show ((0 : Int32).toInt = 0) from by decide]; omega
          rw [Int32.toNat_toUInt32_of_le hikn]
          show ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2).toInt.toNat < 5
          rw [hik]; omega
        refine ⟨hle1, hidx2, ?_⟩
        intro heq
        apply hmx
        rw [mergeIter_eq]
        refine ⟨h1lt, fun h10 h5 => ?_⟩
        have hSame : (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[
            ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2).toUInt32.toNat]'h5 =
            (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[
            ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 2).toUInt32.toNat]'hidx2 := by
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
    -- Reconnect to the real run via `cleanupRunResult_eq`, then case-split
    -- on the lone-king condition.
    -- ------------------------------------------------------------------
    have hm_le_int : (m : Int) ≤ (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt - 1 := by omega
    rw [cleanupRunResult_eq (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
      (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p hmf128] at hrun
    cases hkc : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m == 1 &&
        VALUE (B + UInt8.ofNat m) == 13) with
    | false =>
      simp only [hkc, Bool.false_eq_true, reduceIte] at hrun
      have hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8 :=
        fun t => (hnf_.suitClean t).aces_kings_valid.1
      have hframeNK : ∀ j : Fin 10, j.val ≠ k →
          (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
            (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth.get j =
          p.pileDepth.get j :=
        fun j hj => preCleanupPile_pileDepth_eq_of_ne (UInt32.ofNat k) hk_ B
          (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f j (by rw [hpkn]; exact hj)
      refine ⟨0xffff, preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
          (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p, hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · refine ⟨fun i => ?_, fun s => ?_, ?_, ?_⟩
        · by_cases hij : i.val = (UInt32.ofNat k).toNat
          · have hii : i = ⟨(UInt32.ofNat k).toNat, hk_⟩ := Fin.ext hij
            subst hii
            exact preCleanupPile_pileBase_self (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5 hidx
              hBdef.symm m f hm_le_int hmcards hf_le hffree
          · exact preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p
              m f hd5 (by omega) i hij (hnfp i hij)
        · exact preCleanupPile_suitClean (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5 hidx hBdef.symm
            m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop s
        · exact preCleanupPile_hash_def (UInt32.ofNat k) g p hk_ hnf_ B hs4 hd5 m f hm_le_int
        · exact preCleanupPile_usedSpace_def (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd hd5 m f hm_le_int
            hf_le hBrange.2
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
          rw [Int32.toInt_toInt8, hdepth1I, Int.bmod_eq_of_le (by omega) (by omega),
            show ((0 : Int8).toInt = 0) from rfl] at h'
          omega
        have hstepEq := hfreePilesStep0 _ hframeNK hpdNeNK
        rw [hpfEq2, hstepEq]
        exact hfp
      · -- (3) `PileMerged` for the first `k+1` piles: piles `< k` transfer
        -- from `hpm` via `preCleanupPile_pileMerged_ne`; pile `k` itself is
        -- freshly `PileClean` via `preCleanupPile_pileClean_self`.
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
        · exact preCleanupPile_pileMerged_ne (UInt32.ofNat k) g hk_ hwf B
            (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 hm_le_int hmcards hak i
            (by rw [hpkn]; omega) (hnf.pileBase i) (hpm i hik)
        · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
          have hpc := preCleanupPile_pileClean_self (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5 hidx
            hBdef.symm m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop
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
    | true =>
      simp only [hkc, reduceIte] at hrun
      have hpc := preCleanupPile_pileClean_self (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5 hidx
        hBdef.symm m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop
      have hpdb_all := preCleanupPile_pileDepth_bound_all (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5
        hidx hBdef.symm m f hm_le_int hmcards hf_le hffree
      rw [Bool.and_eq_true] at hkc
      have hk1 := hkc.1
      have hk2 := hkc.2
      have hpdEq : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
          (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ =
          ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m).toInt8 := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hpfEq : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
          (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileFlute[(UInt32.ofNat k).toNat]'hk_ =
          (1 + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8 := by
        simp only [preCleanupPile]
        rw [Vector.getElem_set_self]
      have hd1' : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
          (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth[(UInt32.ofNat k).toNat]'hk_ = 1 := by
        rw [hpdEq, eq_of_beq hk1]; decide
      have hVK13 : (VALUE (B + UInt8.ofNat m)).toNat = 13 := by
        rw [eq_of_beq hk2]; decide
      have hak : ∀ t : Fin 4, SUIT (p.aces.get t).toUInt8 = t.val.toUInt8 :=
        fun t => (hnf_.suitClean t).aces_kings_valid.1
      have hrcm := merge_real_chain' g (UInt32.ofNat k) hk_ hwf B (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m
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
      have hidx0 : ((p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 - Int32.ofNat m - 1
          ).toUInt32.toNat = 0 := by
        have he1 := eq_of_beq hk1
        rw [he1]
        decide
      obtain ⟨hidxm, heqm⟩ := hmcards m (le_refl m)
      have hKeq : B + UInt8.ofNat m = (g.pos2card[(UInt32.ofNat k).toNat]'hk_)[0]'(by omega) := by
        rw [← heqm]
        congr 1
      have hframeK : ∀ j : Fin 10, j.val ≠ k →
          (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.get j =
          p.pileDepth.get j := by
        intro j hj
        have hj' : j.val ≠ (UInt32.ofNat k).toNat := by rw [hpkn]; exact hj
        rw [kingMove_pileDepth_eq_of_ne (UInt32.ofNat k) hk_ (SUIT B) hs4
          (pileHashes[(UInt32.ofNat k).toNat]'hk_)
          (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
            (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p) j hj',
          preCleanupPile_pileDepth_eq_of_ne (UInt32.ofNat k) hk_ B
            (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f j hj']
      refine ⟨0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
        kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
          (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
            (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p), hrun, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · refine ⟨fun i => ?_, fun s => ?_, ?_, ?_⟩
        · by_cases hij : i.val = (UInt32.ofNat k).toNat
          · have hii : i = ⟨(UInt32.ofNat k).toNat, hk_⟩ := Fin.ext hij
            subst hii
            exact (kingMove_pileClean_self (UInt32.ofNat k) g hk_ (SUIT B) hs4
              (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).toPileBase
          · exact kingMove_pileBase_ne (UInt32.ofNat k) g hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p) i hij
              (preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f
                hd5 (by omega) i hij (hnfp i hij))
        · exact kingMove_suitClean (UInt32.ofNat k) g hk_ hwf (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)
            hpdb_all hd1' (B + UInt8.ofNat m) hKeq hVK13 hSm.symm hak hpc s
            (preCleanupPile_suitClean (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd1 hd5 hidx hBdef.symm
              m f hm_le_int hmcards hmstop hf_le hf_le_tight hffree hfstop s)
        · -- hash_def for the king branch: compose `preCleanupPile_hash_def` with
          -- `kingMove`'s own simple `hash -= ph` write, isolating `(UInt32.ofNat k)`'s own
          -- term (now `0`) via `hash_foldl_set`.
          have hqhash := preCleanupPile_hash_def (UInt32.ofNat k) g p hk_ hnf_ B hs4 hd5 m f hm_le_int
          show (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).hash -
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) =
            (List.finRange 10).foldl (fun acc i => acc + pileHashes.get i *
              ((kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                  (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.get i
                ).toInt.toNat.toUInt32) 0
          have hpdeq : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                  (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth =
              (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth.set
                (UInt32.ofNat k).toNat (0 : Int8) hk_ := by
            simp only [kingMove]
            congr 1
          rw [hpdeq, hqhash]
          have hadd := hash_foldl_set (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            hs4 (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth (UInt32.ofNat k).toNat hk_ (0 : Int8)
          rw [hd1'] at hadd
          simp only [show ((1 : Int8).toInt.toNat = 1) from rfl,
            show ((0 : Int8).toInt.toNat = 0) from rfl,
            show (Nat.toUInt32 0 = 0) from rfl, show (Nat.toUInt32 1 = 1) from rfl,
            UInt32.mul_one, UInt32.mul_zero, UInt32.add_zero] at hadd
          rw [← hadd, UInt32.add_sub_cancel]
        · -- usedSpace_def for the king branch: compose `preCleanupPile_usedSpace_def`
          -- with `kingMove`'s own `usedSpace += pileFlute[(UInt32.ofNat k)]` write, isolating
          -- `(UInt32.ofNat k)`'s own depth/flute terms (now `0`/`1`) the same way.
          have hqused := preCleanupPile_usedSpace_def (UInt32.ofNat k) g p hk_ hwf hnf_ B hs4 hd hd5 m f
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
          have hds := depth_sum_foldl_set (preCleanupPile (UInt32.ofNat k) hk_ B
            (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p
            ).pileDepth (UInt32.ofNat k).toNat hk_ (0 : Int8)
          rw [hd1'] at hds
          simp only [show ((1 : Int8).toInt.toNat = 1) from rfl,
            show ((0 : Int8).toInt.toNat = 0) from rfl] at hds
          have hft := usedSpace_term_foldl_set (preCleanupPile (UInt32.ofNat k) hk_ B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p
              ).pileDepth
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileFlute
            (UInt32.ofNat k).toNat hk_ (0 : Int8) (1 : UInt8)
          rw [hd1', hpfEq] at hft
          simp only [show ((0 : Int8) ≠ (0 : Int8)) = False from by simp,
            show ((1 : Int8) ≠ (0 : Int8)) = True from by simp, reduceIte] at hft
          rw [hfl8] at hft
          show ((preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).usedSpace +
              ((preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileFlute[(UInt32.ofNat k).toNat]'hk_
                ).toInt8).toInt =
            (52 : Int)
            - ((kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                  (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)
                ).pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
            - (p.aces.toList.foldl (fun acc a => acc + (VALUE a.toUInt8).toNat) 0 : Nat)
            - ((List.zipWith (fun d f => if d ≠ (0 : Int8) then f.toNat - 1 else 0)
                (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                  (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                    (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.toList
                (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                  (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                    (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileFlute.toList
                |>.foldl (·+·) 0 : Nat))
          have hpdeqL : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                  (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileDepth.toList =
              ((preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileDepth.set
                (UInt32.ofNat k).toNat (0 : Int8) hk_).toList := by
            simp only [kingMove]
            congr 1
          have hpfeqL : (kingMove (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
                (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                  (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).pileFlute.toList =
              ((preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
                (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileFlute.set
                (UInt32.ofNat k).toNat (1 : UInt8) hk_).toList := by
            simp only [kingMove]
            congr 1
          rw [hpdeqL, hpfeqL]
          have hfl8Int : ((preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).pileFlute[(UInt32.ofNat k).toNat]'hk_
              ).toInt8.toInt = (1 + (m : Int) + f) := by
            rw [hpfEq]
            have hb128 : (((1 : Int32) + Int32.ofNat m + Int32.ofNat f).toUInt32.toUInt8
                ).toNat < 128 := by rw [hfl8]; omega
            rw [uint8_toInt8_toInt_of_lt128 hb128, hfl8]
            push_cast
            ring
          have hqb_le : (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).usedSpace.toInt ≤ 127 := by
            have h := (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).usedSpace.toInt_le
            rw [Int8.toInt_maxValue] at h
            omega
          have hqb_ge : (-128 : Int) ≤ (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_)
              hs4 (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).usedSpace.toInt := by
            have h := (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p).usedSpace.le_toInt
            omega
          rw [Int8.toInt_add, hfl8Int, Int.bmod_eq_of_le (by omega) (by omega)]
          omega
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
          exact kingMove_pileDepth_self (UInt32.ofNat k) hk_ (SUIT B) hs4 (pileHashes[(UInt32.ofNat k).toNat]'hk_)
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
        -- via `kingMove_pileClean_self`.
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
        · have hijk : i.val ≠ (UInt32.ofNat k).toNat := by rw [hpkn]; omega
          exact kingMove_pileMerged_ne (UInt32.ofNat k) g hk_ hwf (SUIT B) hs4
            (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)
            hd1' (B + UInt8.ofNat m) hKeq hVK13 hak i hijk
            (preCleanupPile_pileBase_ne (UInt32.ofNat k) g hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f
              hd5 (by omega) i hijk (hnfp i hijk))
            (preCleanupPile_pileMerged_ne (UInt32.ofNat k) g hk_ hwf B
              (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4 p m f hd5 hm_le_int hmcards hak i hijk
              (hnf.pileBase i) (hpm i hik))
        · obtain rfl : i = ⟨k, hk⟩ := Fin.ext hik
          rw [← hfinEq]
          exact (kingMove_pileClean_self (UInt32.ofNat k) g hk_ (SUIT B) hs4
            (pileHashes[(UInt32.ofNat k).toNat]'hk_)
            (preCleanupPile (UInt32.ofNat k) hk_ B (pileHashes[(UInt32.ofNat k).toNat]'hk_) hs4
              (p.pileDepth[(UInt32.ofNat k).toNat]'hk_).toInt32 m f p)).toPileMerged
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
