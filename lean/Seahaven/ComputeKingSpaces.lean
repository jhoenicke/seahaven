import Seahaven.GetDestination
import Seahaven.SoundnessSkeleton

/-!
# `computeKingSpaces`: model, loop invariants, and its specification

`computeKingSpaces` has three nested loops:

* `for i in List.range numBits` — one local king configuration per iteration,
  accumulating into `possibleKings`;
* `for suit in List.range 4` — the refund fold, computing the *effective*
  `usedSpace` of that configuration;
* `while usedSpace ≤ 4` — the bit setter: it ORs bit `i` into `possibleKings[c]`
  for every `c ≤ 4 - usedSpace`.

The middle loop is a 4-step fold over a literal list and the inner one is a real
`Loop.forIn`, so the file follows the established recipe (`SolverRealSpec`):
explicit bodies, a `rfl` twin, then exact-run lemmas by induction.

The invariant is carried **bit by bit**: iteration `i` only ever ORs `1 <<< i`, so
what iteration `i` writes is invisible to bit `i' ≠ i`.  That is what gives the
"only if" half of `KingSpacesSpec`'s iff.
-/

open Lean Lean.Order

/-! ## The loop bodies -/

/-- Body of the refund fold: subtract suit `suit`'s freed king stack when the
configuration puts that suit on a pile (bit clear). -/
def spaceBody (game : SolverPosType) (kb : UInt8) :
    Nat → Int32 → EStateM Error Globals (ForInStep Int32) :=
  fun suit u => do
    if kb &&& ((1 : UInt8) <<< UInt8.ofNat suit) == 0 then
      let k ← game.kings.getE (UInt32.ofNat suit)
      return .yield (u - Int32.ofNat (13 - (VALUE k).toNat))
    else
      return .yield u

/-- Accumulator of the bit-setting `while` loop: `(kingInfo, usedSpace)`. -/
abbrev BitAcc := MProd KingInfo Int32

/-- Body of the bit-setting `while` loop. -/
def bitBody (bit : UInt8) : Unit → BitAcc → EStateM Error Globals (ForInStep BitAcc) :=
  fun _ r => do
    if r.snd ≤ 4 then
      let idx := ((4 : Int32) - r.snd).toUInt32
      let old ← r.fst.possibleKings.getE idx
      let newPK ← r.fst.possibleKings.setE idx (old ||| bit)
      return .yield ⟨{ r.fst with possibleKings := newPK }, r.snd + 1⟩
    else
      return .done r

/-- Body of the outer per-configuration loop. -/
def blockBody (shiftValue : UInt8) (game : SolverPosType) :
    Nat → KingInfo → EStateM Error Globals (ForInStep KingInfo) :=
  fun i ki => do
    let kingBitmap ← grlex2bits.getE (shiftValue + UInt8.ofNat i).toUInt32
    let u ← forIn (List.range 4) game.usedSpace.toInt32 (spaceBody game kingBitmap)
    let bit : UInt8 := (1 : UInt8) <<< UInt8.ofNat i
    let r ← Loop.forIn Loop.mk (⟨ki, u⟩ : BitAcc) (bitBody bit)
    return .yield r.fst

/-- Explicit-loop twin of `computeKingSpaces`. -/
def kingSpacesExplicit (shiftValue numBits : UInt8) (game : SolverPosType) :
    EStateM Error Globals KingInfo := do
  let ki : KingInfo := { possibleKings := mkVector 6 0 }
  let ki ← forIn (List.range numBits.toNat) ki (blockBody shiftValue game)
  return ki

/-- The explicit-loop twin is definitionally the real function. -/
theorem kingSpaces_eq_explicit : computeKingSpaces = kingSpacesExplicit := rfl

/-! ## The refund fold

Four steps over a literal list, so its exact run is a matter of unrolling.  The
result is the position's `usedSpace` minus the refund the configuration claims. -/

/-- One step of the refund fold. -/
def effStep (game : SolverPosType) (kb : UInt8) (suit : Fin 4) (u : Int32) : Int32 :=
  if kb &&& ((1 : UInt8) <<< UInt8.ofNat suit.val) == 0 then
    u - Int32.ofNat (13 - (VALUE (game.kings.get suit)).toNat)
  else u

/-- The effective `usedSpace` of configuration `kb`: what the middle loop leaves
in the mutable `usedSpace`. -/
def effSpace (game : SolverPosType) (kb : UInt8) : Int32 :=
  effStep game kb 3 (effStep game kb 2 (effStep game kb 1
    (effStep game kb 0 game.usedSpace.toInt32)))

theorem spaceLoop_run (game : SolverPosType) (kb : UInt8) (s : Globals) :
    forIn (List.range 4) game.usedSpace.toInt32 (spaceBody game kb) s
      = .ok (effSpace game kb) s := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have k0 : game.kings[0]? = some (game.kings.get 0) := rfl
  have k1 : game.kings[1]? = some (game.kings.get 1) := rfl
  have k2 : game.kings[2]? = some (game.kings.get 2) := rfl
  have k3 : game.kings[3]? = some (game.kings.get 3) := rfl
  rw [h4]
  by_cases h0 : (kb &&& ((1 : UInt8) <<< UInt8.ofNat 0) == 0) = true <;>
    by_cases h1 : (kb &&& ((1 : UInt8) <<< UInt8.ofNat 1) == 0) = true <;>
      by_cases h2 : (kb &&& ((1 : UInt8) <<< UInt8.ofNat 2) == 0) = true <;>
        by_cases h3 : (kb &&& ((1 : UInt8) <<< UInt8.ofNat 3) == 0) = true <;>
          simp only [List.forIn_cons, List.forIn_nil, spaceBody, effSpace, effStep,
            bind, EStateM.bind, pure, EStateM.pure, Vector.getE,
            show ((0 : Fin 4)).val = 0 from rfl, show ((1 : Fin 4)).val = 1 from rfl,
            show ((2 : Fin 4)).val = 2 from rfl, show ((3 : Fin 4)).val = 3 from rfl,
            show ((UInt32.ofNat 0).toNat = 0) from rfl,
            show ((UInt32.ofNat 1).toNat = 1) from rfl,
            show ((UInt32.ofNat 2).toNat = 2) from rfl,
            show ((UInt32.ofNat 3).toNat = 3) from rfl,
            k0, k1, k2, k3,
            h0, h1, h2, h3, Bool.false_eq_true, reduceIte]

/-! ## The bit-setting loop

Starting from effective space `u`, the loop ORs `bit` into `possibleKings[c]` for
exactly the entries `c ≤ 4 - u`, one per iteration, counting `u` up to `5`.  It
indexes `possibleKings[4 - u]`, so `u ≤ -2` runs off the end and throws — which is
why `KingSpacesSpec` may assume the run succeeded. -/

/-- `Int32` addition without wraparound (companion of `int32_toInt_sub`). -/
private theorem int32_toInt_add (a b : Int32) (h1 : -2147483648 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2147483648) : (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem int32_four_toInt : ((4 : Int32)).toInt = 4 := by decide
private theorem int32_one_toInt : ((1 : Int32)).toInt = 1 := by decide

/-- The guard, as an arithmetic statement. -/
theorem bit_guard_iff (u : Int32) : (u ≤ (4 : Int32)) ↔ u.toInt ≤ 4 := by
  rw [Int32.le_iff_toInt_le, int32_four_toInt]

/-- The entry the loop writes at effective space `u`. -/
def bitIdx (u : Int32) : Nat := (((4 : Int32) - u).toUInt32).toNat

/-- OR `bit` into one entry. -/
def orAt (v : Vector UInt8 6) (i : Nat) (hi : i < 6) (bit : UInt8) : Vector UInt8 6 :=
  v.set i (v.get ⟨i, hi⟩ ||| bit) hi

private theorem bitIdx_eq (u : Int32) (h1 : -60 ≤ u.toInt) (h2 : u.toInt ≤ 4) :
    bitIdx u = (4 - u.toInt).toNat := by
  have hsub : ((4 : Int32) - u).toInt = 4 - u.toInt := by
    rw [int32_toInt_sub _ _ (by rw [int32_four_toInt]; omega)
      (by rw [int32_four_toInt]; omega), int32_four_toInt]
  rw [bitIdx, Int32.toUInt32_toNat_of_nonneg _ (by rw [hsub]; omega), hsub]

/-- One iteration of the bit loop, when the write index is in range. -/
private theorem bitBody_yield (bit : UInt8) (s : Globals) (ki : KingInfo) (u : Int32)
    (hg : u ≤ (4 : Int32)) (hidx : bitIdx u < 6) :
    bitBody bit () ⟨ki, u⟩ s
      = .ok (.yield ⟨⟨orAt ki.possibleKings (bitIdx u) hidx bit⟩, u + 1⟩) s := by
  have hidx' : (((4 : Int32) - u).toUInt32).toNat < 6 := hidx
  have hsome : ki.possibleKings[(((4 : Int32) - u).toUInt32).toNat]?
      = some (ki.possibleKings.get ⟨(((4 : Int32) - u).toUInt32).toNat, hidx'⟩) :=
    getElem?_pos ki.possibleKings (((4 : Int32) - u).toUInt32).toNat hidx'
  show bitBody bit () ⟨ki, u⟩ s
      = .ok (.yield ⟨⟨ki.possibleKings.set (((4 : Int32) - u).toUInt32).toNat
        (ki.possibleKings.get ⟨(((4 : Int32) - u).toUInt32).toNat, hidx'⟩ ||| bit) hidx'⟩,
      u + 1⟩) s
  simp only [bitBody, hg, reduceIte, bind, EStateM.bind, pure, EStateM.pure, Vector.getE,
    Vector.setE, hsome, dif_pos hidx']

/-- One iteration of the bit loop, when the guard already fails. -/
private theorem bitBody_done (bit : UInt8) (s : Globals) (ki : KingInfo) (u : Int32)
    (hg : ¬ (u ≤ (4 : Int32))) :
    bitBody bit () ⟨ki, u⟩ s = .ok (.done ⟨ki, u⟩) s := by
  simp only [bitBody, hg, reduceIte, pure, EStateM.pure]

/-- Reading back one `orAt` write. -/
private theorem orAt_get (v : Vector UInt8 6) (i : Nat) (hi : i < 6) (bit : UInt8) (c : Fin 6) :
    (orAt v i hi bit).get c = if i = c.val then v.get ⟨i, hi⟩ ||| bit else v.get c := by
  show (v.set i _ hi)[c.val] = _
  rw [Vector.getElem_set hi c.isLt]
  rfl

/-- **Exact run of the bit-setting loop.** -/
theorem bitLoop_ok (bit : UInt8) (s : Globals) :
    ∀ (n : Nat) (ki : KingInfo) (u : Int32), 5 - u.toInt ≤ (n : Int) → -1 ≤ u.toInt →
      ∃ res : BitAcc,
        Loop.forIn Loop.mk (⟨ki, u⟩ : BitAcc) (bitBody bit) s = .ok res s ∧
        ∀ c : Fin 6, res.fst.possibleKings.get c
          = if (c.val : Int) ≤ 4 - u.toInt then ki.possibleKings.get c ||| bit
            else ki.possibleKings.get c := by
  intro n
  induction n with
  | zero =>
    intro ki u h1 _
    have hng : ¬ (u ≤ (4 : Int32)) := by rw [bit_guard_iff]; omega
    refine ⟨⟨ki, u⟩, ?_, fun c => ?_⟩
    · rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals)]
      simp only [bind, EStateM.bind, bitBody_done bit s ki u hng, pure, EStateM.pure]
    · rw [if_neg (by have := c.isLt; omega)]
  | succ n ih =>
    intro ki u h1 h2
    by_cases hg : u ≤ (4 : Int32)
    · have hgi : u.toInt ≤ 4 := (bit_guard_iff u).1 hg
      have hidxNat := bitIdx_eq u (by omega) hgi
      have hidx : bitIdx u < 6 := by rw [hidxNat]; omega
      have hadd : (u + 1).toInt = u.toInt + 1 := by
        rw [int32_toInt_add _ _ (by rw [int32_one_toInt]; omega)
          (by rw [int32_one_toInt]; omega), int32_one_toInt]
      obtain ⟨res, hres, hchar⟩ := ih ⟨orAt ki.possibleKings (bitIdx u) hidx bit⟩ (u + 1)
        (by rw [hadd]; omega) (by rw [hadd]; omega)
      refine ⟨res, ?_, fun c => ?_⟩
      · rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals)]
        simp only [bind, EStateM.bind, bitBody_yield bit s ki u hg hidx]
        exact hres
      · rw [hchar c, hadd, orAt_get]
        by_cases hc : (c.val : Int) ≤ 4 - (u.toInt + 1)
        · have hne : bitIdx u ≠ c.val := by rw [hidxNat]; omega
          rw [if_pos hc, if_neg hne, if_pos (by omega)]
        · by_cases hc2 : (c.val : Int) ≤ 4 - u.toInt
          · have heq : bitIdx u = c.val := by rw [hidxNat]; omega
            have hgetc : ki.possibleKings.get ⟨bitIdx u, hidx⟩ = ki.possibleKings.get c :=
              congrArg _ (Fin.ext heq)
            rw [if_neg hc, if_pos heq, if_pos hc2, hgetc]
          · have hne : bitIdx u ≠ c.val := by rw [hidxNat]; omega
            rw [if_neg hc, if_neg hne, if_neg hc2]
    · have hng : ¬ u.toInt ≤ 4 := fun h => hg ((bit_guard_iff u).2 h)
      refine ⟨⟨ki, u⟩, ?_, fun c => ?_⟩
      · rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals)]
        simp only [bind, EStateM.bind, bitBody_done bit s ki u hg, pure, EStateM.pure]
      · rw [if_neg (by have := c.isLt; omega)]

/-- **The loop throws when the effective space is `≤ -2`**: the very first write
index is `4 - u ≥ 6`, past the end of `possibleKings`. -/
theorem bitLoop_err (bit : UInt8) (s : Globals) (ki : KingInfo) (u : Int32)
    (hlo : -60 ≤ u.toInt) (hhi : u.toInt ≤ -2) :
    Loop.forIn Loop.mk (⟨ki, u⟩ : BitAcc) (bitBody bit) s
      = .error Error.ArrayOutOfBounds s := by
  have hg : u ≤ (4 : Int32) := (bit_guard_iff u).2 (by omega)
  have hidx : ¬ bitIdx u < 6 := by rw [bitIdx_eq u hlo (by omega)]; omega
  have hidx' : ¬ (((4 : Int32) - u).toUInt32).toNat < 6 := hidx
  have hnone : ki.possibleKings[(((4 : Int32) - u).toUInt32).toNat]? = none :=
    getElem?_neg ki.possibleKings (((4 : Int32) - u).toUInt32).toNat hidx'
  rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals)]
  simp only [bitBody, hg, reduceIte, bind, EStateM.bind, pure, Vector.getE,
    hnone, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-! ## Per-configuration bookkeeping

The outer loop's `i`-th iteration reads configuration `grlex2bits[shiftValue + i]`
and computes its effective space.  Both are packaged as total functions of `i`. -/

/-- The `grlex2bits` index local index `i` reads. -/
def cfgIdx (shiftValue : UInt8) (i : Nat) : Nat := (shiftValue + UInt8.ofNat i).toUInt32.toNat

/-- The configuration byte of local index `i` (`0` outside the table). -/
def blockBitmap (shiftValue : UInt8) (i : Nat) : UInt8 :=
  if h : cfgIdx shiftValue i < 16 then grlex2bits.get ⟨cfgIdx shiftValue i, h⟩ else 0

/-- The effective space of local index `i`. -/
def blockSpace (shiftValue : UInt8) (game : SolverPosType) (i : Nat) : Int32 :=
  effSpace game (blockBitmap shiftValue i)

/-- One suit's refund as an `Int`, with the **`Nat` truncation the solver uses**:
`13 - VALUE kings[su]` never goes negative here.  Under `SolverInvBase` (where
`VALUE kings[su] ≤ 13`) this agrees with `kingRefund`'s `Int` subtraction. -/
def refundInt (game : SolverPosType) (kb : UInt8) (suit : Fin 4) : Int :=
  if kb &&& ((1 : UInt8) <<< UInt8.ofNat suit.val) == 0 then
    ((13 - (VALUE (game.kings.get suit)).toNat : Nat) : Int) else 0

private theorem refundInt_bounds (game : SolverPosType) (kb : UInt8) (suit : Fin 4) :
    0 ≤ refundInt game kb suit ∧ refundInt game kb suit ≤ 13 := by
  unfold refundInt
  split
  · omega
  · omega

private theorem int32_ofNat_toInt (n : Nat) (h : n ≤ 13) : (Int32.ofNat n).toInt = (n : Int) := by
  interval_cases n <;> decide

private theorem effStep_toInt (game : SolverPosType) (kb : UInt8) (suit : Fin 4) (u : Int32)
    (h1 : -100 ≤ u.toInt) (h2 : u.toInt ≤ 300) :
    (effStep game kb suit u).toInt = u.toInt - refundInt game kb suit := by
  have hv : (VALUE (game.kings.get suit)).toNat ≤ 15 := by
    have := VALUE_toNat (game.kings.get suit); omega
  by_cases hc : (kb &&& ((1 : UInt8) <<< UInt8.ofNat suit.val) == 0) = true
  · have hof : (Int32.ofNat (13 - (VALUE (game.kings.get suit)).toNat)).toInt
        = ((13 - (VALUE (game.kings.get suit)).toNat : Nat) : Int) :=
      int32_ofNat_toInt _ (by omega)
    simp only [effStep, refundInt, hc, reduceIte]
    rw [int32_toInt_sub _ _ (by rw [hof]; omega) (by rw [hof]; omega), hof]
  · simp only [effStep, refundInt, hc, Bool.false_eq_true, reduceIte]
    omega

/-- **The effective space, in `Int`.** -/
theorem effSpace_toInt (game : SolverPosType) (kb : UInt8) :
    (effSpace game kb).toInt = (game.usedSpace.toNat : Int)
      - refundInt game kb 0 - refundInt game kb 1 - refundInt game kb 2
      - refundInt game kb 3 := by
  have hu : (game.usedSpace.toInt32).toInt = (game.usedSpace.toNat : Int) :=
    uint8_toInt32_toInt _
  have h255 : game.usedSpace.toNat < 256 := game.usedSpace.toNat_lt_size
  have b0 := refundInt_bounds game kb 0
  have b1 := refundInt_bounds game kb 1
  have b2 := refundInt_bounds game kb 2
  have b3 := refundInt_bounds game kb 3
  have e0 : (effStep game kb 0 game.usedSpace.toInt32).toInt
      = (game.usedSpace.toNat : Int) - refundInt game kb 0 := by
    rw [effStep_toInt _ _ _ _ (by rw [hu]; omega) (by rw [hu]; omega), hu]
  have e1 : (effStep game kb 1 (effStep game kb 0 game.usedSpace.toInt32)).toInt
      = (game.usedSpace.toNat : Int) - refundInt game kb 0 - refundInt game kb 1 := by
    rw [effStep_toInt _ _ _ _ (by rw [e0]; omega) (by rw [e0]; omega), e0]
  have e2 : (effStep game kb 2 (effStep game kb 1
        (effStep game kb 0 game.usedSpace.toInt32))).toInt
      = (game.usedSpace.toNat : Int) - refundInt game kb 0 - refundInt game kb 1
        - refundInt game kb 2 := by
    rw [effStep_toInt _ _ _ _ (by rw [e1]; omega) (by rw [e1]; omega), e1]
  show (effStep game kb 3 (effStep game kb 2 (effStep game kb 1
    (effStep game kb 0 game.usedSpace.toInt32)))).toInt = _
  rw [effStep_toInt _ _ _ _ (by rw [e2]; omega) (by rw [e2]; omega), e2]

theorem blockSpace_bounds (shiftValue : UInt8) (game : SolverPosType) (i : Nat) :
    -52 ≤ (blockSpace shiftValue game i).toInt
      ∧ (blockSpace shiftValue game i).toInt ≤ 255 := by
  have h := effSpace_toInt game (blockBitmap shiftValue i)
  have h255 : game.usedSpace.toNat < 256 := game.usedSpace.toNat_lt_size
  have b0 := refundInt_bounds game (blockBitmap shiftValue i) 0
  have b1 := refundInt_bounds game (blockBitmap shiftValue i) 1
  have b2 := refundInt_bounds game (blockBitmap shiftValue i) 2
  have b3 := refundInt_bounds game (blockBitmap shiftValue i) 3
  rw [blockSpace]
  omega

/-! ## One outer iteration -/

private theorem estateM_pure_apply {α : Type} (a : α) (t : Globals) :
    (EStateM.pure a : EStateM Error Globals α) t = .ok a t := rfl

theorem blockBody_run (shiftValue : UInt8) (game : SolverPosType) (s : Globals) (i : Nat)
    (ki : KingInfo) (hcfg : cfgIdx shiftValue i < 16)
    (hu : -1 ≤ (blockSpace shiftValue game i).toInt) :
    ∃ res : KingInfo, blockBody shiftValue game i ki s = .ok (.yield res) s ∧
      ∀ c : Fin 6, res.possibleKings.get c
        = if (c.val : Int) ≤ 4 - (blockSpace shiftValue game i).toInt
          then ki.possibleKings.get c ||| ((1 : UInt8) <<< UInt8.ofNat i)
          else ki.possibleKings.get c := by
  have hgrl : grlex2bits[cfgIdx shiftValue i]? = some (blockBitmap shiftValue i) := by
    rw [blockBitmap, dif_pos hcfg]
    exact getElem?_pos grlex2bits (cfgIdx shiftValue i) hcfg
  obtain ⟨res, hres, hchar⟩ := bitLoop_ok ((1 : UInt8) <<< UInt8.ofNat i) s
    (5 - (blockSpace shiftValue game i).toInt).toNat ki (blockSpace shiftValue game i)
    (by omega) hu
  refine ⟨res.fst, ?_, hchar⟩
  simp only [blockBody, bind, EStateM.bind, pure, EStateM.pure, Vector.getE, cfgIdx] at hgrl ⊢
  simp only [hgrl, estateM_pure_apply, spaceLoop_run, blockSpace] at hres ⊢
  rw [hres]

theorem blockBody_err (shiftValue : UInt8) (game : SolverPosType) (s : Globals) (i : Nat)
    (ki : KingInfo) (hcfg : cfgIdx shiftValue i < 16)
    (hu : (blockSpace shiftValue game i).toInt ≤ -2) :
    blockBody shiftValue game i ki s = .error Error.ArrayOutOfBounds s := by
  have hgrl : grlex2bits[cfgIdx shiftValue i]? = some (blockBitmap shiftValue i) := by
    rw [blockBitmap, dif_pos hcfg]
    exact getElem?_pos grlex2bits (cfgIdx shiftValue i) hcfg
  have herr := bitLoop_err ((1 : UInt8) <<< UInt8.ofNat i) s ki
    (blockSpace shiftValue game i) (by have := blockSpace_bounds shiftValue game i; omega) hu
  simp only [blockBody, bind, EStateM.bind, pure, EStateM.pure, Vector.getE, cfgIdx] at hgrl ⊢
  simp only [hgrl, estateM_pure_apply, spaceLoop_run, blockSpace] at herr ⊢
  rw [herr]

/-! ## The outer loop

The invariant is carried per *bit*: after processing the index list `l`, bit `b` of
entry `c` is set exactly when `b ∈ l` and `c ≤ 4 - space b`.  Iteration `i` ORs only
`1 <<< i`, so it cannot disturb any other bit — that is what makes the invariant
compositional (and gives the "only if" half of the spec). -/

private theorem or_shift_testBit_iff (x : UInt8) (i b : Nat) (hi : i < 8) (hb : b < 8) :
    (x ||| ((1 : UInt8) <<< UInt8.ofNat i)).toNat.testBit b = true
      ↔ (x.toNat.testBit b = true ∨ i = b) := by
  have hkey : ∀ i b : Fin 8,
      ((1 : UInt8) <<< UInt8.ofNat i.val).toNat.testBit b.val = decide (i.val = b.val) := by
    decide
  rw [UInt8.toNat_or, Nat.testBit_or, Bool.or_eq_true, hkey ⟨i, hi⟩ ⟨b, hb⟩]
  simp

theorem outerLoop_ok (shiftValue : UInt8) (game : SolverPosType) (s : Globals) :
    ∀ (l : List Nat) (ki : KingInfo),
      (∀ i ∈ l, cfgIdx shiftValue i < 16) →
      (∀ i ∈ l, i < 8) →
      (∀ i ∈ l, -1 ≤ (blockSpace shiftValue game i).toInt) →
      ∃ res : KingInfo, forIn l ki (blockBody shiftValue game) s = .ok res s ∧
        ∀ (c : Fin 6) (b : Nat), b < 8 →
          ((res.possibleKings.get c).toNat.testBit b = true ↔
            ((ki.possibleKings.get c).toNat.testBit b = true ∨
              (b ∈ l ∧ (c.val : Int) ≤ 4 - (blockSpace shiftValue game b).toInt))) := by
  intro l
  induction l with
  | nil =>
    intro ki _ _ _
    refine ⟨ki, rfl, fun c b _ => ?_⟩
    simp
  | cons i l ih =>
    intro ki hcfg h8 hu
    obtain ⟨ki1, hrun1, hchar1⟩ := blockBody_run shiftValue game s i ki
      (hcfg i (by simp)) (hu i (by simp))
    obtain ⟨res, hres, hchar⟩ := ih ki1 (fun j hj => hcfg j (by simp [hj]))
      (fun j hj => h8 j (by simp [hj])) (fun j hj => hu j (by simp [hj]))
    refine ⟨res, ?_, fun c b hb => ?_⟩
    · rw [List.forIn_cons]
      simp only [bind, EStateM.bind, hrun1]
      exact hres
    · rw [hchar c b hb, hchar1 c, List.mem_cons]
      by_cases hci : (c.val : Int) ≤ 4 - (blockSpace shiftValue game i).toInt
      · rw [if_pos hci, or_shift_testBit_iff _ _ _ (h8 i (by simp)) hb]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl h.symm, by rw [← h]; exact hci⟩
          · exact Or.inr ⟨Or.inr h.1, h.2⟩
        · rintro (h | ⟨hb', hc'⟩)
          · exact Or.inl (Or.inl h)
          · rcases hb' with rfl | hb'
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨hb', hc'⟩
      · rw [if_neg hci]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h.1, h.2⟩
        · rintro (h | ⟨hb', hc'⟩)
          · exact Or.inl h
          · rcases hb' with rfl | hb'
            · exact absurd hc' hci
            · exact Or.inr ⟨hb', hc'⟩

theorem outerLoop_err (shiftValue : UInt8) (game : SolverPosType) (s : Globals) :
    ∀ (l : List Nat) (ki : KingInfo),
      (∀ i ∈ l, cfgIdx shiftValue i < 16) →
      (∃ i ∈ l, (blockSpace shiftValue game i).toInt ≤ -2) →
      ∃ e, forIn l ki (blockBody shiftValue game) s = .error e s := by
  intro l
  induction l with
  | nil =>
    intro _ _ hex
    obtain ⟨i, hi, _⟩ := hex
    simp at hi
  | cons i l ih =>
    intro ki hcfg hex
    obtain ⟨j, hj, hjs⟩ := hex
    by_cases hi2 : (blockSpace shiftValue game i).toInt ≤ -2
    · refine ⟨Error.ArrayOutOfBounds, ?_⟩
      rw [List.forIn_cons]
      simp only [bind, EStateM.bind,
        blockBody_err shiftValue game s i ki (hcfg i (by simp)) hi2]
    · obtain ⟨ki1, hrun1, _⟩ := blockBody_run shiftValue game s i ki
        (hcfg i (by simp)) (by omega)
      rcases List.mem_cons.1 hj with rfl | hj'
      · exact absurd hjs hi2
      · obtain ⟨e, he⟩ := ih ki1 (fun k hk => hcfg k (by simp [hk])) ⟨j, hj', hjs⟩
        refine ⟨e, ?_⟩
        rw [List.forIn_cons]
        simp only [bind, EStateM.bind, hrun1]
        exact he

/-! ## From the loop invariant to `KingSpacesSpec`

Three encoding bridges remain: the bit test versus `kingRefund`'s arithmetic form,
the block index versus `globalCfg`, and `BitSet` versus `Nat.testBit`. -/

theorem cfgIdx_eq (sv : UInt8) (i : Nat) (h : sv.toNat + i < 256) :
    cfgIdx sv i = sv.toNat + i := by
  rw [cfgIdx, UInt8.toNat_toUInt32, UInt8.toNat_add, UInt8.toNat_ofNat']
  omega

-- (`closureInfo_shift_add_numBits` — every block fits inside the 16-entry
-- `grlex2bits` table — now comes from `SoundnessSkeleton`.)

/-- The configuration byte local index `i` reads is `globalCfg`'s. -/
theorem blockBitmap_eq_grlex (sv : UInt8) (i : Nat) (h : sv.toNat + i ≤ 15) :
    blockBitmap sv i = grlex2bits.get ⟨min (sv.toNat + i) 15, by omega⟩ := by
  have hc : cfgIdx sv i = sv.toNat + i := cfgIdx_eq sv i (by omega)
  rw [blockBitmap, dif_pos (by rw [hc]; omega)]
  congr 1
  apply Fin.ext
  simp only [hc]
  omega

/-- The solver's bit test is `kingRefund`'s "bit clear" condition. -/
private theorem bit_clear_iff (kb : UInt8) (i : Nat) (hi : i < 8) :
    (kb &&& ((1 : UInt8) <<< UInt8.ofNat i) == 0) = true ↔ kb.toNat / 2 ^ i % 2 = 0 := by
  have h8 : ∀ j : Fin 8, ((1 : UInt8) <<< UInt8.ofNat j.val).toNat = 2 ^ j.val := by decide
  have hshift : ((1 : UInt8) <<< UInt8.ofNat i).toNat = 2 ^ i := h8 ⟨i, hi⟩
  have hnat : (kb &&& ((1 : UInt8) <<< UInt8.ofNat i)).toNat = kb.toNat &&& (1 <<< i) := by
    rw [UInt8.toNat_and, hshift, Nat.shiftLeft_eq, one_mul]
  have hzero : ((kb &&& ((1 : UInt8) <<< UInt8.ofNat i) == 0) = true)
      ↔ kb.toNat &&& (1 <<< i) = 0 := by
    rw [beq_iff_eq]
    exact ⟨fun h => by rw [← hnat, h]; rfl,
      fun h => UInt8.toNat_inj.mp (by rw [hnat, h]; rfl)⟩
  have hbit := nat_and_shiftLeft_ne_zero kb.toNat i
  rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
  simp only [decide_eq_true_eq] at hbit
  rw [hzero]
  have hmod : kb.toNat / 2 ^ i % 2 = 0 ∨ kb.toNat / 2 ^ i % 2 = 1 := by omega
  refine ⟨fun hx => ?_, fun hd => ?_⟩
  · by_contra hd
    exact (hbit.2 (by omega)) hx
  · by_contra hx
    exact absurd (hbit.1 hx) (by omega)

/-- `kingRefund`, unfolded to its four summands. -/
private theorem kingRefund_four (p : SolverPosType) (k : Fin 16) :
    kingRefund p k
      = (if (grlex2bits.get k).toNat / 2 ^ (0 : Fin 4).val % 2 = 0
          then ((13 : Int) - (VALUE (p.kings.get 0)).toNat) else 0)
        + (if (grlex2bits.get k).toNat / 2 ^ (1 : Fin 4).val % 2 = 0
          then ((13 : Int) - (VALUE (p.kings.get 1)).toNat) else 0)
        + (if (grlex2bits.get k).toNat / 2 ^ (2 : Fin 4).val % 2 = 0
          then ((13 : Int) - (VALUE (p.kings.get 2)).toNat) else 0)
        + (if (grlex2bits.get k).toNat / 2 ^ (3 : Fin 4).val % 2 = 0
          then ((13 : Int) - (VALUE (p.kings.get 3)).toNat) else 0) := by
  have hfr : List.finRange 4 = [0, 1, 2, 3] := by decide
  rw [kingRefund, hfr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **The loop's effective space is `usedSpace - kingRefund`.**  This is where
`SolverInvBase` is needed: the loop truncates `13 - VALUE kings[su]` in `Nat`. -/
theorem blockSpace_toInt_eq {g : Globals} (p : SolverPosType) (hb : SolverInvBase g p)
    (sv : UInt8) (i : Nat) (h : sv.toNat + i ≤ 15) :
    (blockSpace sv p i).toInt
      = p.usedSpace.toInt - kingRefund p ⟨min (sv.toNat + i) 15, by omega⟩ := by
  have hval : ∀ su : Fin 4, (VALUE (p.kings.get su)).toNat ≤ 13 :=
    fun su => (hb.aces_kings_valid su).2.2.2.1
  have hbm := blockBitmap_eq_grlex sv i h
  have hterm : ∀ su : Fin 4,
      refundInt p (blockBitmap sv i) su
        = if (grlex2bits.get (⟨min (sv.toNat + i) 15, by omega⟩ : Fin 16)).toNat
              / 2 ^ su.val % 2 = 0
          then ((13 : Int) - (VALUE (p.kings.get su)).toNat) else 0 := by
    intro su
    have hsu8 : su.val < 8 := by omega
    rw [refundInt, hbm]
    by_cases hc : (grlex2bits.get (⟨min (sv.toNat + i) 15, by omega⟩ : Fin 16)).toNat
        / 2 ^ su.val % 2 = 0
    · rw [if_pos ((bit_clear_iff _ _ hsu8).2 hc), if_pos hc]
      have := hval su
      omega
    · rw [if_neg (fun hh => hc ((bit_clear_iff _ _ hsu8).1 hh)), if_neg hc]
  rw [blockSpace, effSpace_toInt, hterm 0, hterm 1, hterm 2, hterm 3, kingRefund_four]
  show (p.usedSpace.toNat : Int) - _ - _ - _ - _ = _
  ring

/-- `BitSet` on a `UInt8`-valued entry is `Nat.testBit`. -/
theorem bitSet_iff_testBit (x : UInt8) (i : Nat) (hi : i < 6) :
    BitSet x.toUInt16 ⟨min i 15, by omega⟩ ↔ x.toNat.testBit i = true := by
  rw [BitSet_toNat, UInt8.toNat_toUInt16]
  show x.toNat.testBit (min i 15) = true ↔ _
  rw [show min i 15 = i from by omega]

private theorem uint8_eq_zero_of_testBit (x : UInt8)
    (h : ∀ b, b < 8 → x.toNat.testBit b = false) : x = 0 := by
  apply UInt8.toNat_inj.mp
  show x.toNat = (0 : UInt8).toNat
  rw [show ((0 : UInt8).toNat = 0) from rfl]
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [Nat.zero_testBit]
  by_cases hb : b < 8
  · exact h b hb
  · have h256 : (256 : Nat) ≤ 2 ^ b := by
      calc (256 : Nat) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    have h256x : x.toNat < 256 := x.toNat_lt_size
    exact Nat.testBit_lt_two_pow (by omega)

/-! ## The specification -/

private theorem closureInfoOf_numBits_le (p : SolverPosType) :
    (closureInfoOf p).numBits.toNat ≤ 6 := by
  have h : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
  exact h _

private theorem closureInfoOf_fits (p : SolverPosType) :
    (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
  closureInfo_shift_add_numBits _

private theorem mkVector6_get (c : Fin 6) : (mkVector 6 (0 : UInt8)).get c = 0 := by
  fin_cases c <;> rfl

/-- **`computeKingSpaces` meets its specification.**  Bit `i` of `possibleKings[c]`
says configuration `i` of the block leaves at least `c` cells free, and entry `5` is
zero whenever no configuration leaves five. -/
theorem kingSpaces_spec : KingSpacesSpec := by
  intro g p ki hb hrun
  have hfits := closureInfoOf_fits p
  have hnb6 := closureInfoOf_numBits_le p
  have hcfg : ∀ i ∈ List.range (closureInfoOf p).numBits.toNat,
      cfgIdx (closureInfoOf p).shiftValue i < 16 := by
    intro i hi
    rw [List.mem_range] at hi
    rw [cfgIdx_eq _ _ (by omega)]
    omega
  have h8 : ∀ i ∈ List.range (closureInfoOf p).numBits.toNat, i < 8 := by
    intro i hi
    rw [List.mem_range] at hi
    omega
  -- the function is exactly the outer loop, with its result passed through
  have hok : ∀ (res : KingInfo) (t : Globals),
      forIn (List.range (closureInfoOf p).numBits.toNat)
          ({ possibleKings := mkVector 6 0 } : KingInfo)
          (blockBody (closureInfoOf p).shiftValue p) g = .ok res t →
      (computeKingSpaces (closureInfoOf p).shiftValue (closureInfoOf p).numBits p).run g
        = .ok res t := by
    intro res t h
    rw [kingSpaces_eq_explicit]
    simp only [kingSpacesExplicit, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, h]
  have herr : ∀ (e : Error) (t : Globals),
      forIn (List.range (closureInfoOf p).numBits.toNat)
          ({ possibleKings := mkVector 6 0 } : KingInfo)
          (blockBody (closureInfoOf p).shiftValue p) g = .error e t →
      (computeKingSpaces (closureInfoOf p).shiftValue (closureInfoOf p).numBits p).run g
        = .error e t := by
    intro e t h
    rw [kingSpaces_eq_explicit]
    simp only [kingSpacesExplicit, EStateM.run, bind, EStateM.bind, pure, h]
  -- the run succeeded, so no configuration overflows `possibleKings`
  have hu : ∀ i ∈ List.range (closureInfoOf p).numBits.toNat,
      -1 ≤ (blockSpace (closureInfoOf p).shiftValue p i).toInt := by
    intro i hi
    by_contra hcon
    obtain ⟨e, he⟩ := outerLoop_err (closureInfoOf p).shiftValue p g
      (List.range (closureInfoOf p).numBits.toNat) { possibleKings := mkVector 6 0 } hcfg
      ⟨i, hi, by omega⟩
    rw [herr e g he] at hrun
    simp at hrun
  obtain ⟨res, hres, hchar⟩ := outerLoop_ok (closureInfoOf p).shiftValue p g
    (List.range (closureInfoOf p).numBits.toNat) { possibleKings := mkVector 6 0 } hcfg h8 hu
  rw [hok res g hres] at hrun
  have hkieq : ki = res := ((EStateM.Result.ok.inj hrun).1).symm
  subst hkieq
  -- the free-cell reading of the effective space
  have hfree : ∀ i, i < (closureInfoOf p).numBits.toNat →
      (4 : Int) - (blockSpace (closureInfoOf p).shiftValue p i).toInt
        = freeCellsOf p (globalCfg (closureInfoOf p) i) := by
    intro i hi
    rw [blockSpace_toInt_eq p hb _ i (by omega), freeCellsOf, globalCfg]
  refine ⟨fun c hc i hi => ?_, fun hall => ?_⟩
  · rw [bitSet_iff_testBit _ i (by omega), hchar ⟨c, hc⟩ i (by omega), mkVector6_get,
      ← hfree i hi]
    simp only [show ((0 : UInt8).toNat = 0) from rfl, Nat.zero_testBit, Bool.false_eq_true,
      false_or, List.mem_range, hi, true_and]
  · refine uint8_eq_zero_of_testBit _ (fun b hbb => ?_)
    have hiff := hchar 5 b hbb
    rw [mkVector6_get, show ((0 : UInt8).toNat = 0) from rfl, Nat.zero_testBit] at hiff
    by_cases hbit : ((ki.possibleKings.get 5).toNat.testBit b) = true
    · exfalso
      obtain ⟨hmem, hle⟩ := (hiff.1 hbit).resolve_left (by simp)
      rw [List.mem_range] at hmem
      have h4 := hall b hmem
      rw [← hfree b hmem] at h4
      simp only [Fin.isValue, show ((5 : Fin 6)).val = 5 from rfl] at hle
      omega
    · exact Bool.not_eq_true _ ▸ hbit
