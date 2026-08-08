import Seahaven.SolverSpecDrain
import Seahaven.SolverSpecSolverCleanupPile

/-!
# The prologue of `SolverConvertFromPilesKings`, mirrored

`SolverConvertFromPilesKings` is four loops:

1. `for i in List.range 10` — install the pile depths from the input vector and
   recompute `pileFlute`/`usedSpace`/`hash` from scratch;
2. `for suit in List.range 4` — the per-suit foundation (`aces`) and king-frontier
   (`kings`) walks, each a `while` over the freed cards;
3. `for i in List.range 10` — `SolverCleanupPile` on every pile;
4. `while busyAces ≠ 0` — the foundation drain (`drainBody`, shared with
   `SolverMove`).

Loops 1 and 2 never touch the monadic state: they thread the position through the
`forIn` accumulator and `set` it only afterwards.  So the whole *prologue* (loops 1
and 2) is a pure function of the globals and the input depth vector — `convertPre`
below — and this file is the `rfl`-twin plus the exact-run lemmas that identify it.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-! ## The loop bodies, mirrored -/

/-- Body of the depth-installation loop (loop 1). -/
def cvDepthBody (pilesking : Vector UInt8 11) (i : Nat) (r : SolverPosType) :
    EStateM Error (Globals × SolverPosType) (ForInStep SolverPosType) :=
  have game := r
  have iU32 := UInt32.ofNat i
  do
    let d : UInt8 ← pilesking.getE iU32
    let __do_lift ← game.pileDepth.setE iU32 d
    have game : SolverPosType := { game with pileDepth := __do_lift }
    let __do_lift ← game.pileFlute.setE iU32 1
    have game : SolverPosType := { game with pileFlute := __do_lift }
    have game : SolverPosType := { game with usedSpace := game.usedSpace - d }
    let __do_lift ← pileHashes.getE iU32
    have game : SolverPosType := { game with hash := game.hash + __do_lift * d.toUInt32 }
    pure PUnit.unit
    pure (ForInStep.yield game)

/-- Body of the foundation walk (loop 2, first `while`). -/
def cvAceBody (globals : Globals) (game : SolverPosType) (card : UInt8) :
    Unit → UInt8 → EStateM Error (Globals × SolverPosType) (ForInStep UInt8) :=
  fun _ r =>
    have ace := r
    do
      let __do_lift ← (pure (decide (ace ≤ card)) <&&> do
        let __do_lift ← globals.card2depth.getE ace.toUInt32
        let __do_lift_1 ← globals.card2pile.getE ace.toUInt32
        let __do_lift_2 ← game.pileDepth.getE __do_lift_1.toUInt32
        pure (decide (__do_lift.toNat ≥ __do_lift_2.toNat)))
      if __do_lift = true then
        have ace := ace + 1
        do
          pure PUnit.unit
          pure (ForInStep.yield ace)
      else pure (ForInStep.done ace)

/-- Body of the king-frontier walk (loop 2, second `while`). -/
def cvKingBody (globals : Globals) (game : SolverPosType) :
    Unit → UInt8 → EStateM Error (Globals × SolverPosType) (ForInStep UInt8) :=
  fun _ r =>
    have card := r
    do
      let __do_lift ← globals.card2depth.getE card.toUInt32
      let __do_lift_1 ← globals.card2pile.getE card.toUInt32
      let __do_lift_2 ← game.pileDepth.getE __do_lift_1.toUInt32
      if __do_lift.toNat ≥ __do_lift_2.toNat then
        have card := card - 1
        do
          pure PUnit.unit
          pure (ForInStep.yield card)
      else pure (ForInStep.done card)

/-- Body of the per-suit loop (loop 2). -/
def cvSuitBody (globals : Globals) (suit : Nat) (r : SolverPosType) :
    EStateM Error (Globals × SolverPosType) (ForInStep SolverPosType) :=
  have game := r
  have suitU32 := UInt32.ofNat suit
  have card := CARD (UInt8.ofNat suit) (UInt8.ofNat 13)
  have ace := CARD (UInt8.ofNat suit) (UInt8.ofNat 1)
  do
    let r ← Loop.forIn Loop.mk ace (cvAceBody globals game card)
    have ace : UInt8 := r
    have ace : UInt8 := ace - 1
    let __do_lift ← game.aces.setE suitU32 ace
    have game : SolverPosType := { game with aces := __do_lift }
    have game : SolverPosType := { game with usedSpace := game.usedSpace - VALUE ace }
    have __do_jp : UInt8 → SolverPosType → PUnit →
        EStateM Error (Globals × SolverPosType) (ForInStep SolverPosType) :=
      fun card game _y => do
        let __do_lift ← game.kings.setE suitU32 card
        have game : SolverPosType := { game with kings := __do_lift }
        pure PUnit.unit
        pure (ForInStep.yield game)
    if ace < card then do
        let r ← Loop.forIn Loop.mk card (cvKingBody globals game)
        have card : UInt8 := r
        let y ← pure PUnit.unit
        __do_jp card game y
      else do
        let y ← pure PUnit.unit
        __do_jp card game y

/-- Body of the cleanup loop (loop 3). -/
def cvCleanupBody (i : Nat) (r : UInt16) :
    EStateM Error (Globals × SolverPosType) (ForInStep UInt16) :=
  have forcedKings := r
  do
    let __do_lift ← _root_.SolverCleanupPile (UInt32.ofNat i)
    have forcedKings : UInt16 := forcedKings &&& __do_lift
    pure PUnit.unit
    pure (ForInStep.yield forcedKings)

set_option maxHeartbeats 1000000 in
/-- The `rfl`-twin: `SolverConvertFromPilesKings` with all four loops presented
    through the mirrored bodies above. -/
theorem convert_eq_explicit (pk : Vector UInt8 11) :
    _root_.SolverConvertFromPilesKings pk = (do
      let s ← get
      have globals := s.1
      have game := s.2
      have game : SolverPosType :=
        { game with busyAces := 0, usedSpace := 52, freePiles := 0, hash := 0 }
      let r ← forIn (List.range 10) game (cvDepthBody pk)
      have game : SolverPosType := r
      let r ← forIn (List.range 4) game (cvSuitBody globals)
      have game : SolverPosType := r
      set ((globals, game) : Globals × SolverPosType)
      let r ← forIn (List.range 10) (0xffff : UInt16) cvCleanupBody
      have forcedKings : UInt16 := r
      let r ← Loop.forIn Loop.mk forcedKings drainBody
      pure r) :=
  rfl

/-! ## Loop 1: installing the pile depths -/

/-- One iteration of the depth loop, as a pure state transformer. -/
def cvDepthStep (pk : Vector UInt8 11) (i : Nat) (hi : i < 10) (game : SolverPosType) :
    SolverPosType :=
  { game with
    pileDepth := game.pileDepth.set i (pk[i]'(by omega)) hi
    pileFlute := game.pileFlute.set i 1 hi
    usedSpace := game.usedSpace - pk[i]'(by omega)
    hash := game.hash + (pileHashes[i]'hi) * (pk[i]'(by omega)).toUInt32 }

set_option linter.unusedSimpArgs false in
/-- The depth-loop body never touches the state and never fails. -/
theorem cvDepthBody_run (pk : Vector UInt8 11) (i : Nat) (hi : i < 10)
    (game : SolverPosType) (s : Globals × SolverPosType) :
    cvDepthBody pk i game s = .ok (.yield (cvDepthStep pk i hi game)) s := by
  have hidx : (UInt32.ofNat i).toNat = i := by
    rw [UInt32.toNat_ofNat']; omega
  have h11 : i < 11 := by omega
  simp only [cvDepthBody, cvDepthStep, bind, EStateM.bind, pure, EStateM.pure,
    Vector.getE, Vector.setE, hidx, getElem?_pos, hi, h11, dif_pos]

/-! ## Loop 1: the exact run

The loop is a fold of `cvDepthStep`; `cvDepthUpTo` names the partial folds so the
induction over `List.range' k n` composes. -/

/-- The position after the first `k` iterations of the depth loop. -/
def cvDepthUpTo (pk : Vector UInt8 11) (p0 : SolverPosType) : Nat → SolverPosType
  | 0 => p0
  | k + 1 => if h : k < 10 then cvDepthStep pk k h (cvDepthUpTo pk p0 k) else cvDepthUpTo pk p0 k

theorem cvDepthUpTo_succ (pk : Vector UInt8 11) (p0 : SolverPosType) {k : Nat} (hk : k < 10) :
    cvDepthUpTo pk p0 (k + 1) = cvDepthStep pk k hk (cvDepthUpTo pk p0 k) := by
  simp only [cvDepthUpTo, dif_pos hk]

theorem cvDepthLoop_run (pk : Vector UInt8 11) (p0 : SolverPosType)
    (s : Globals × SolverPosType) :
    ∀ (n k : Nat), k + n = 10 →
      forIn (List.range' k n) (cvDepthUpTo pk p0 k) (cvDepthBody pk) s
        = .ok (cvDepthUpTo pk p0 10) s := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 10 := by omega
    rfl
  | succ n ih =>
    intro k hk
    have hklt : k < 10 := by omega
    rw [List.range'_succ, List.forIn_cons]
    show (cvDepthBody pk k (cvDepthUpTo pk p0 k) >>= _) s = _
    simp only [bind, EStateM.bind, cvDepthBody_run pk k hklt, ← cvDepthUpTo_succ pk p0 hklt]
    exact ih (k + 1) (by omega)

/-! ### What loop 1 computes -/

/-- The pile depths installed by loop 1. -/
def cvDepths (pk : Vector UInt8 11) : Vector UInt8 10 :=
  Vector.ofFn (fun i : Fin 10 => pk[i.val]'(by omega))

@[simp] theorem cvDepths_get (pk : Vector UInt8 11) (i : Fin 10) :
    (cvDepths pk).get i = pk[i.val]'(by omega) := by
  show (Vector.ofFn (fun i : Fin 10 => pk[i.val]'(by omega)))[i.val]'i.isLt = _
  rw [Vector.getElem_ofFn]

theorem cvDepthUpTo_pileDepth (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ (k : Nat), k ≤ 10 → ∀ i : Fin 10,
      (cvDepthUpTo pk p0 k).pileDepth.get i =
        if i.val < k then (cvDepths pk).get i else p0.pileDepth.get i := by
  intro k
  induction k with
  | zero => intro _ i; simp [cvDepthUpTo]
  | succ k ih =>
    intro hk i
    rw [cvDepthUpTo_succ pk p0 (by omega)]
    show ((cvDepthUpTo pk p0 k).pileDepth.set k (pk[k]'(by omega)) (by omega))[i.val]'i.isLt = _
    rw [Vector.getElem_set]
    by_cases hik : i.val = k
    · rw [if_pos hik.symm, if_pos (by omega), cvDepths_get]
      congr 1
      exact hik.symm
    · rw [if_neg (fun h => hik h.symm)]
      show (cvDepthUpTo pk p0 k).pileDepth.get i = _
      rw [ih (by omega) i]
      by_cases h2 : i.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem cvDepthUpTo_pileFlute (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ (k : Nat), k ≤ 10 → ∀ i : Fin 10,
      (cvDepthUpTo pk p0 k).pileFlute.get i =
        if i.val < k then 1 else p0.pileFlute.get i := by
  intro k
  induction k with
  | zero => intro _ i; simp [cvDepthUpTo]
  | succ k ih =>
    intro hk i
    rw [cvDepthUpTo_succ pk p0 (by omega)]
    show ((cvDepthUpTo pk p0 k).pileFlute.set k 1 (by omega))[i.val]'i.isLt = _
    rw [Vector.getElem_set]
    by_cases hik : i.val = k
    · rw [if_pos hik.symm, if_pos (by omega)]
    · rw [if_neg (fun h => hik h.symm)]
      show (cvDepthUpTo pk p0 k).pileFlute.get i = _
      rw [ih (by omega) i]
      by_cases h2 : i.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem cvDepthUpTo_aces (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ k : Nat, (cvDepthUpTo pk p0 k).aces = p0.aces := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvDepthUpTo]; split <;> [skip; skip] <;> simp only [cvDepthStep, ih]

theorem cvDepthUpTo_kings (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ k : Nat, (cvDepthUpTo pk p0 k).kings = p0.kings := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvDepthUpTo]; split <;> [skip; skip] <;> simp only [cvDepthStep, ih]

theorem cvDepthUpTo_freePiles (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ k : Nat, (cvDepthUpTo pk p0 k).freePiles = p0.freePiles := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvDepthUpTo]; split <;> [skip; skip] <;> simp only [cvDepthStep, ih]

theorem cvDepthUpTo_busyAces (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ k : Nat, (cvDepthUpTo pk p0 k).busyAces = p0.busyAces := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvDepthUpTo]; split <;> [skip; skip] <;> simp only [cvDepthStep, ih]

/-- `UInt8.toUInt32` agrees with going through `Nat` (needed because the loop
    writes `d.toUInt32` while `hash_def` is phrased with `d.toNat.toUInt32`). -/
theorem uint8_toUInt32_eq (d : UInt8) : d.toUInt32 = d.toNat.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt8.toNat_toUInt32, UInt32.toNat_ofNat']
  have := d.toNat_lt
  omega

/-- Splitting the last element off a `take (k+1)` of `List.finRange`. -/
theorem finRange_take_succ {n k : Nat} (hk : k < n) :
    (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [(⟨k, hk⟩ : Fin n)] := by
  have hlen : k < (List.finRange n).length := by rw [List.length_finRange]; exact hk
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp only [Option.toList_some]
  congr 2
  exact Fin.ext (by simp)

theorem cvDepthUpTo_hash (pk : Vector UInt8 11) (p0 : SolverPosType) :
    ∀ (k : Nat), k ≤ 10 →
      (cvDepthUpTo pk p0 k).hash =
        ((List.finRange 10).take k).foldl
          (fun acc i => acc + pileHashes.get i * ((cvDepths pk).get i).toNat.toUInt32) p0.hash := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hklt : k < 10 := by omega
    rw [cvDepthUpTo_succ pk p0 hklt, finRange_take_succ hklt, List.foldl_append,
      ← ih (by omega)]
    show (cvDepthUpTo pk p0 k).hash + (pileHashes[k]'hklt) * (pk[k]'(by omega)).toUInt32 = _
    simp only [List.foldl_cons, List.foldl_nil, cvDepths_get, uint8_toUInt32_eq]
    rfl

/-- The prefix sum of the installed depths. -/
def cvDepthPrefix (pk : Vector UInt8 11) (k : Nat) : Nat :=
  ((List.finRange 10).take k).foldl (fun acc i => acc + ((cvDepths pk).get i).toNat) 0

theorem cvDepthPrefix_succ (pk : Vector UInt8 11) {k : Nat} (hk : k < 10) :
    cvDepthPrefix pk (k + 1) = cvDepthPrefix pk k + ((cvDepths pk).get ⟨k, hk⟩).toNat := by
  unfold cvDepthPrefix
  rw [finRange_take_succ hk, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

theorem cvDepthPrefix_le (pk : Vector UInt8 11) (hpk : ValidDepths pk) :
    ∀ (k : Nat), k ≤ 10 → cvDepthPrefix pk k ≤ 5 * k := by
  intro k
  induction k with
  | zero => intro _; simp [cvDepthPrefix]
  | succ k ih =>
    intro hk
    have hklt : k < 10 := by omega
    have hd : ((cvDepths pk).get ⟨k, hklt⟩).toNat ≤ 5 := by
      rw [cvDepths_get]; exact hpk ⟨k, hklt⟩
    rw [cvDepthPrefix_succ pk hklt]
    have := ih (by omega)
    omega

theorem cvDepthUpTo_usedSpace (pk : Vector UInt8 11) (p0 : SolverPosType)
    (hpk : ValidDepths pk) (hu : 50 ≤ p0.usedSpace.toNat) :
    ∀ (k : Nat), k ≤ 10 →
      (cvDepthUpTo pk p0 k).usedSpace.toNat = p0.usedSpace.toNat - cvDepthPrefix pk k := by
  intro k
  induction k with
  | zero => intro _; simp [cvDepthUpTo, cvDepthPrefix]
  | succ k ih =>
    intro hk
    have hklt : k < 10 := by omega
    have hprev := ih (by omega)
    have hple : cvDepthPrefix pk k ≤ 5 * k := cvDepthPrefix_le pk hpk k (by omega)
    have hd : ((cvDepths pk).get ⟨k, hklt⟩).toNat ≤ 5 := by
      rw [cvDepths_get]; exact hpk ⟨k, hklt⟩
    have hdd : (pk[k]'(by omega : k < 11)) = (cvDepths pk).get ⟨k, hklt⟩ :=
      (cvDepths_get pk ⟨k, hklt⟩).symm
    rw [cvDepthUpTo_succ pk p0 hklt, cvDepthPrefix_succ pk hklt]
    show ((cvDepthUpTo pk p0 k).usedSpace - (pk[k]'(by omega : k < 11))).toNat = _
    rw [hdd, UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hprev]; omega), hprev]
    omega

/-! ## Loop 2: the per-suit walks

Both walks scan a suit's cards for freeness; `runLen` is the length of the
initial run of a decidable predicate, and both walk results are read off it. -/

instance decIsFreeCard (g : Globals) (p : SolverPosType) (c : UInt8) :
    Decidable (isFreeCard g p c) := by
  unfold isFreeCard; exact Nat.decLe _ _

/-- Length of the initial run of `P` over `0, 1, …, n-1`. -/
def runLen (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => if runLen P n = n ∧ P n then n + 1 else runLen P n

theorem runLen_le (P : Nat → Prop) [DecidablePred P] : ∀ n, runLen P n ≤ n
  | 0 => le_refl 0
  | n + 1 => by
      rw [runLen]
      split
      · exact le_refl _
      · exact le_trans (runLen_le P n) (by omega)

theorem runLen_holds (P : Nat → Prop) [DecidablePred P] : ∀ n, ∀ j < runLen P n, P j := by
  intro n
  induction n with
  | zero => intro j hj; simp [runLen] at hj
  | succ n ih =>
    intro j hj
    rw [runLen] at hj
    split at hj
    · rename_i hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact ih j (by omega)
      · subst h; exact hc.2
    · exact ih j hj

theorem runLen_stop (P : Nat → Prop) [DecidablePred P] : ∀ n, runLen P n < n → ¬ P (runLen P n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hlt
    rw [runLen] at hlt ⊢
    split at hlt
    · omega
    · rename_i hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · rw [if_neg hc]; exact ih h
      · rw [if_neg hc, h]
        intro hP
        exact hc ⟨h, hP⟩

/-- **Freeness, as a function of the pile depths alone.**  `isFreeCard` reads no
    other field of the position, and the walks run while `aces`/`kings`/`usedSpace`
    are being rewritten around them — so the values they compute are stated over the
    depth vector, which stays fixed through the whole of loop 2. -/
def freeAt (g : Globals) (d : Vector UInt8 10) (c : UInt8) : Prop :=
  let pile : UInt8 := if h : c.toNat < 64 then g.card2pile.get ⟨c.toNat, h⟩ else 0
  let origDepth : UInt8 := if h : c.toNat < 64 then g.card2depth.get ⟨c.toNat, h⟩ else 0
  let pileDepth : UInt8 := if h : pile.toNat < 10 then d.get ⟨pile.toNat, h⟩ else 0
  origDepth.toNat ≥ pileDepth.toNat

theorem isFreeCard_eq_freeAt (g : Globals) (p : SolverPosType) (c : UInt8) :
    isFreeCard g p c = freeAt g p.pileDepth c := rfl

instance decFreeAt (g : Globals) (d : Vector UInt8 10) (c : UInt8) :
    Decidable (freeAt g d c) := by unfold freeAt; exact Nat.decLe _ _

/-- The predicate the foundation walk tests: card `su`-`(v+1)` is free. -/
def aceFree (g : Globals) (d : Vector UInt8 10) (su : Nat) (v : Nat) : Prop :=
  freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (v + 1)))

instance (g : Globals) (d : Vector UInt8 10) (su : Nat) : DecidablePred (aceFree g d su) :=
  fun _ => decFreeAt _ _ _

/-- The predicate the king-frontier walk tests: card `su`-`(13-t)` is free. -/
def kingFree (g : Globals) (d : Vector UInt8 10) (su : Nat) (t : Nat) : Prop :=
  freeAt g d (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t)))

instance (g : Globals) (d : Vector UInt8 10) (su : Nat) : DecidablePred (kingFree g d su) :=
  fun _ => decFreeAt _ _ _

/-- The foundation top the walk computes for suit `su`: the number of cards
    freed consecutively from the ace up. -/
def cvAceVal (g : Globals) (d : Vector UInt8 10) (su : Nat) : Nat := runLen (aceFree g d su) 13

/-- The number of cards freed consecutively from the king down. -/
def cvKingRun (g : Globals) (d : Vector UInt8 10) (su : Nat) : Nat := runLen (kingFree g d su) 13

/-- The king frontier the walk computes: `13` when the whole suit is free (then
    the walk does not run at all), otherwise the first un-freed card from the top. -/
def cvKingVal (g : Globals) (d : Vector UInt8 10) (su : Nat) : Nat :=
  if cvAceVal g d su = 13 then 13 else 13 - cvKingRun g d su

/-! ### Card arithmetic for the walks -/

theorem cv_card_toNat {su v : Nat} (hsu : su < 4) (hv : v < 16) :
    (CARD (UInt8.ofNat su) (UInt8.ofNat v)).toNat = su * 16 + v :=
  CARD_toNat (by omega) hv

theorem cv_card_lt64 {su v : Nat} (hsu : su < 4) (hv : v ≤ 14) :
    (CARD (UInt8.ofNat su) (UInt8.ofNat v)).toNat < 64 := by
  rw [cv_card_toNat hsu (by omega)]; omega

theorem cv_card_succ {su v : Nat} (hsu : su < 4) (hv : v + 1 < 16) :
    CARD (UInt8.ofNat su) (UInt8.ofNat v) + 1 = CARD (UInt8.ofNat su) (UInt8.ofNat (v + 1)) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, cv_card_toNat hsu (by omega), cv_card_toNat hsu hv,
    show ((1 : UInt8).toNat = 1) from rfl]
  omega

theorem cv_card_le {su v w : Nat} (hsu : su < 4) (hv : v < 16) (hw : w < 16) :
    (CARD (UInt8.ofNat su) (UInt8.ofNat v) ≤ CARD (UInt8.ofNat su) (UInt8.ofNat w)) ↔ v ≤ w := by
  rw [UInt8.le_iff_toNat_le, cv_card_toNat hsu hv, cv_card_toNat hsu hw]
  omega

/-! ### The foundation walk, one step at a time -/

set_option linter.unusedSimpArgs false in
theorem cvAceBody_yield (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (card ace : UInt8) (s : Globals × SolverPosType) (hc64 : ace.toNat < 64)
    (hle : ace ≤ card) (hfree : isFreeCard g q ace) :
    cvAceBody g q card () ace s = .ok (.yield (ace + 1)) s := by
  have hc32 : ace.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hc64
  have hp10 : (g.card2pile[ace.toUInt32.toNat]'hc32).toUInt32.toNat < 10 := by
    rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc32
  have hcmp : (decide ((g.card2depth[ace.toUInt32.toNat]'hc32).toNat ≥
      (q.pileDepth[(g.card2pile[ace.toUInt32.toNat]'hc32).toUInt32.toNat]'hp10).toNat) = true) := by
    rw [decide_eq_true_eq]
    exact isFree_to_card2depth_ge g q hwf ace hc64 hfree
  have hleT : (ace ≤ card) = True := eq_true hle
  simp only [cvAceBody, bind, EStateM.bind, pure, EStateM.pure, andM, Vector.getE,
    getElem?_pos, hc32, hp10, hleT, decide_true, toBool, hcmp, reduceIte]

set_option linter.unusedSimpArgs false in
theorem cvAceBody_done_notFree (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (card ace : UInt8) (s : Globals × SolverPosType) (hc64 : ace.toNat < 64)
    (hle : ace ≤ card) (hfree : ¬ isFreeCard g q ace) :
    cvAceBody g q card () ace s = .ok (.done ace) s := by
  have hc32 : ace.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hc64
  have hp10 : (g.card2pile[ace.toUInt32.toNat]'hc32).toUInt32.toNat < 10 := by
    rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc32
  have hcmp : (decide ((g.card2depth[ace.toUInt32.toNat]'hc32).toNat ≥
      (q.pileDepth[(g.card2pile[ace.toUInt32.toNat]'hc32).toUInt32.toNat]'hp10).toNat) = false) := by
    rw [decide_eq_false_iff_not]
    intro h
    exact hfree (isFree_of_card2depth_ge g q hwf ace hc64 h)
  have hleT : (ace ≤ card) = True := eq_true hle
  simp only [cvAceBody, bind, EStateM.bind, pure, EStateM.pure, andM, Vector.getE,
    getElem?_pos, hc32, hp10, hleT, decide_true, toBool, hcmp, Bool.false_eq_true, reduceIte]

set_option linter.unusedSimpArgs false in
theorem cvAceBody_done_gt (g : Globals) (q : SolverPosType)
    (card ace : UInt8) (s : Globals × SolverPosType) (hle : ¬ (ace ≤ card)) :
    cvAceBody g q card () ace s = .ok (.done ace) s := by
  have hleT : (ace ≤ card) = False := eq_false hle
  simp only [cvAceBody, bind, EStateM.bind, pure, EStateM.pure, andM, Vector.getE,
    hleT, decide_false, toBool, Bool.false_eq_true, reduceIte]

/-- **The foundation walk stops exactly at the first un-freed card.**  Stated for
    an abstract stopping value `V` (instantiated at `cvAceVal` below) and from an
    arbitrary already-walked prefix `w`, so the induction composes; the solver
    enters it at `w = 0`. -/
theorem cvAceWalk_run_gen (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (su : Nat) (hsu : su < 4) (s : Globals × SolverPosType)
    (V : Nat) (hV13 : V ≤ 13)
    (hholds : ∀ j, j < V → isFreeCard g q (CARD (UInt8.ofNat su) (UInt8.ofNat (j + 1))))
    (hstop : V < 13 → ¬ isFreeCard g q (CARD (UInt8.ofNat su) (UInt8.ofNat (V + 1)))) :
    ∀ (m w : Nat), w + m = 13 → w ≤ V →
      Loop.forIn Loop.mk (CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1)))
          (cvAceBody g q (CARD (UInt8.ofNat su) (UInt8.ofNat 13))) s
        = .ok (CARD (UInt8.ofNat su) (UInt8.ofNat (V + 1))) s := by
  intro m
  induction m with
  | zero =>
    intro w hw hle
    obtain rfl : w = 13 := by omega
    obtain rfl : V = 13 := by omega
    rw [Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := CARD (UInt8.ofNat su) (UInt8.ofNat (13 + 1)))
      (f := cvAceBody g q (CARD (UInt8.ofNat su) (UInt8.ofNat 13)))]
    have hgt : ¬ (CARD (UInt8.ofNat su) (UInt8.ofNat (13 + 1))
        ≤ CARD (UInt8.ofNat su) (UInt8.ofNat 13)) := by
      rw [cv_card_le hsu (by omega) (by omega)]; omega
    simp only [bind, EStateM.bind,
      cvAceBody_done_gt g q (CARD (UInt8.ofNat su) (UInt8.ofNat 13))
        (CARD (UInt8.ofNat su) (UInt8.ofNat (13 + 1))) s hgt, pure, EStateM.pure]
  | succ m ih =>
    intro w hw hle
    have hw12 : w ≤ 12 := by omega
    have hc64 : (CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1))).toNat < 64 :=
      cv_card_lt64 hsu (by omega)
    have hleC : CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1))
        ≤ CARD (UInt8.ofNat su) (UInt8.ofNat 13) :=
      (cv_card_le hsu (by omega) (by omega)).mpr (by omega)
    rw [Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1)))
      (f := cvAceBody g q (CARD (UInt8.ofNat su) (UInt8.ofNat 13)))]
    by_cases hlt : w < V
    · simp only [bind, EStateM.bind,
        cvAceBody_yield g q hwf (CARD (UInt8.ofNat su) (UInt8.ofNat 13))
          (CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1))) s hc64 hleC (hholds w hlt)]
      rw [cv_card_succ hsu (by omega)]
      exact ih (w + 1) (by omega) (by omega)
    · obtain rfl : w = V := by omega
      simp only [bind, EStateM.bind,
        cvAceBody_done_notFree g q hwf (CARD (UInt8.ofNat su) (UInt8.ofNat 13))
          (CARD (UInt8.ofNat su) (UInt8.ofNat (w + 1))) s hc64 hleC (hstop (by omega)),
        pure, EStateM.pure]

/-- The walk, instantiated at the value it actually computes. -/
theorem cvAceWalk_run (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (su : Nat) (hsu : su < 4) (s : Globals × SolverPosType) :
    Loop.forIn Loop.mk (CARD (UInt8.ofNat su) (UInt8.ofNat 1))
        (cvAceBody g q (CARD (UInt8.ofNat su) (UInt8.ofNat 13))) s
      = .ok (CARD (UInt8.ofNat su) (UInt8.ofNat (cvAceVal g q.pileDepth su + 1))) s :=
  cvAceWalk_run_gen g q hwf su hsu s (cvAceVal g q.pileDepth su) (runLen_le _ _)
    (fun j hj => runLen_holds (aceFree g q.pileDepth su) 13 j hj)
    (fun h => runLen_stop (aceFree g q.pileDepth su) 13 h) 13 0 rfl (Nat.zero_le _)

/-! ### The king-frontier walk -/

theorem cv_card_pred {su v : Nat} (hsu : su < 4) (hv : v < 16) (hv1 : 1 ≤ v) :
    CARD (UInt8.ofNat su) (UInt8.ofNat v) - 1 = CARD (UInt8.ofNat su) (UInt8.ofNat (v - 1)) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_sub_of_le _ _ (by
      rw [UInt8.le_iff_toNat_le, cv_card_toNat hsu hv, show ((1 : UInt8).toNat = 1) from rfl]
      omega),
    cv_card_toNat hsu hv, cv_card_toNat hsu (by omega), show ((1 : UInt8).toNat = 1) from rfl]
  omega

set_option linter.unusedSimpArgs false in
theorem cvKingBody_yield (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (card : UInt8) (s : Globals × SolverPosType) (hc64 : card.toNat < 64)
    (hfree : isFreeCard g q card) :
    cvKingBody g q () card s = .ok (.yield (card - 1)) s := by
  have hc32 : card.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hc64
  have hp10 : (g.card2pile[card.toUInt32.toNat]'hc32).toUInt32.toNat < 10 := by
    rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc32
  simp only [cvKingBody, bind, EStateM.bind, pure, EStateM.pure, Vector.getE,
    getElem?_pos, hc32, hp10]
  have hge : (g.card2depth[card.toUInt32.toNat]'hc32).toNat ≥
      (q.pileDepth[(g.card2pile[card.toUInt32.toNat]'hc32).toUInt32.toNat]'hp10).toNat :=
    isFree_to_card2depth_ge g q hwf card hc64 hfree
  rw [if_pos hge]
  rfl

set_option linter.unusedSimpArgs false in
theorem cvKingBody_done (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (card : UInt8) (s : Globals × SolverPosType) (hc64 : card.toNat < 64)
    (hfree : ¬ isFreeCard g q card) :
    cvKingBody g q () card s = .ok (.done card) s := by
  have hc32 : card.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact hc64
  have hp10 : (g.card2pile[card.toUInt32.toNat]'hc32).toUInt32.toNat < 10 := by
    rw [UInt8.toNat_toUInt32]; exact hwf.card2pile_lt _ hc32
  simp only [cvKingBody, bind, EStateM.bind, pure, EStateM.pure, Vector.getE,
    getElem?_pos, hc32, hp10]
  have hnge : ¬ ((g.card2depth[card.toUInt32.toNat]'hc32).toNat ≥
      (q.pileDepth[(g.card2pile[card.toUInt32.toNat]'hc32).toUInt32.toNat]'hp10).toNat) := by
    intro h
    exact hfree (isFree_of_card2depth_ge g q hwf card hc64 h)
  rw [if_neg hnge]
  rfl

/-- **The king-frontier walk stops at the first un-freed card from the top.** -/
theorem cvKingWalk_run_gen (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (su : Nat) (hsu : su < 4) (s : Globals × SolverPosType)
    (T : Nat) (hT : T ≤ 12)
    (hholds : ∀ j, j < T → isFreeCard g q (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - j))))
    (hstop : ¬ isFreeCard g q (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - T)))) :
    ∀ (m t : Nat), t + m = 13 → t ≤ T →
      Loop.forIn Loop.mk (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t))) (cvKingBody g q) s
        = .ok (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - T))) s := by
  intro m
  induction m with
  | zero => intro t hw hle; omega
  | succ m ih =>
    intro t hw hle
    have hc64 : (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t))).toNat < 64 :=
      cv_card_lt64 hsu (by omega)
    rw [Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t)))
      (f := cvKingBody g q)]
    by_cases hlt : t < T
    · simp only [bind, EStateM.bind,
        cvKingBody_yield g q hwf (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t))) s hc64
          (hholds t hlt)]
      rw [cv_card_pred hsu (by omega) (by omega),
        show 13 - t - 1 = 13 - (t + 1) from by omega]
      exact ih (t + 1) (by omega) (by omega)
    · obtain rfl : t = T := by omega
      simp only [bind, EStateM.bind,
        cvKingBody_done g q hwf (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - t))) s hc64 hstop,
        pure, EStateM.pure]

/-- The king run never reaches the ace: the first un-freed card from the ace up
    blocks it, so at least one card of the suit is not free. -/
theorem cvKingRun_le (g : Globals) (d : Vector UInt8 10) (su : Nat)
    (hA : cvAceVal g d su < 13) : cvKingRun g d su ≤ 12 := by
  by_contra hc
  have h13 : runLen (kingFree g d su) 13 = 13 :=
    le_antisymm (runLen_le _ _) (by have : cvKingRun g d su = runLen (kingFree g d su) 13 := rfl
                                    omega)
  have hAA : runLen (aceFree g d su) 13 = cvAceVal g d su := rfl
  have h2 : freeAt g d
      (CARD (UInt8.ofNat su) (UInt8.ofNat (13 - (12 - cvAceVal g d su)))) :=
    runLen_holds (kingFree g d su) 13 (12 - cvAceVal g d su) (by omega)
  rw [show 13 - (12 - cvAceVal g d su) = cvAceVal g d su + 1 from by omega] at h2
  exact runLen_stop (aceFree g d su) 13 (by omega) h2

/-- The king-frontier walk, instantiated at the value it computes.  Entered only
    when `aces < kings`, i.e. when the suit is not entirely freed. -/
theorem cvKingWalk_run (g : Globals) (q : SolverPosType) (hwf : WellFormedLayout g)
    (su : Nat) (hsu : su < 4) (s : Globals × SolverPosType)
    (hA : cvAceVal g q.pileDepth su < 13) :
    Loop.forIn Loop.mk (CARD (UInt8.ofNat su) (UInt8.ofNat 13)) (cvKingBody g q) s
      = .ok (CARD (UInt8.ofNat su) (UInt8.ofNat (cvKingVal g q.pileDepth su))) s := by
  have hT : cvKingRun g q.pileDepth su ≤ 12 := cvKingRun_le g q.pileDepth su hA
  have hTdef : runLen (kingFree g q.pileDepth su) 13 = cvKingRun g q.pileDepth su := rfl
  have hKV : cvKingVal g q.pileDepth su = 13 - cvKingRun g q.pileDepth su := by
    unfold cvKingVal; rw [if_neg (by omega)]
  rw [hKV,
    show CARD (UInt8.ofNat su) (UInt8.ofNat 13)
      = CARD (UInt8.ofNat su) (UInt8.ofNat (13 - 0)) from rfl]
  exact cvKingWalk_run_gen g q hwf su hsu s (cvKingRun g q.pileDepth su) hT
    (fun j hj => runLen_holds (kingFree g q.pileDepth su) 13 j (by omega))
    (runLen_stop (kingFree g q.pileDepth su) 13 (by omega)) 13 0 rfl (Nat.zero_le _)

/-! ### One iteration of the per-suit loop -/

theorem cv_card_value {su v : Nat} (hsu : su < 4) (hv : v < 16) :
    VALUE (CARD (UInt8.ofNat su) (UInt8.ofNat v)) = UInt8.ofNat v := by
  apply UInt8.toNat_inj.mp
  rw [VALUE_toNat, cv_card_toNat hsu hv, UInt8.toNat_ofNat']
  omega

theorem cv_card_suit {su v : Nat} (hsu : su < 4) (hv : v < 16) :
    SUIT (CARD (UInt8.ofNat su) (UInt8.ofNat v)) = UInt8.ofNat su := by
  apply UInt8.toNat_inj.mp
  rw [SUIT_toNat, cv_card_toNat hsu hv, UInt8.toNat_ofNat']
  omega

theorem cv_card_lt {su v w : Nat} (hsu : su < 4) (hv : v < 16) (hw : w < 16) :
    (CARD (UInt8.ofNat su) (UInt8.ofNat v) < CARD (UInt8.ofNat su) (UInt8.ofNat w)) ↔ v < w := by
  rw [UInt8.lt_iff_toNat_lt, cv_card_toNat hsu hv, cv_card_toNat hsu hw]
  omega

/-- One iteration of the per-suit loop, as a pure state transformer. -/
def cvSuitStep (g : Globals) (su : Nat) (hsu : su < 4) (game : SolverPosType) : SolverPosType :=
  { game with
    aces := game.aces.set su
      (CARD (UInt8.ofNat su) (UInt8.ofNat (cvAceVal g game.pileDepth su))) hsu
    usedSpace := game.usedSpace - UInt8.ofNat (cvAceVal g game.pileDepth su)
    kings := game.kings.set su
      (CARD (UInt8.ofNat su) (UInt8.ofNat (cvKingVal g game.pileDepth su))) hsu }

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem cvSuitBody_run (g : Globals) (hwf : WellFormedLayout g) (su : Nat) (hsu : su < 4)
    (game : SolverPosType) (s : Globals × SolverPosType) :
    cvSuitBody g su game s = .ok (.yield (cvSuitStep g su hsu game)) s := by
  obtain ⟨A, hA⟩ : ∃ A, cvAceVal g game.pileDepth su = A := ⟨_, rfl⟩
  have hA13 : A ≤ 13 := by rw [← hA]; exact runLen_le _ _
  have hwalk := cvAceWalk_run g game hwf su hsu s
  rw [hA] at hwalk
  have hsuU : (UInt32.ofNat su).toNat = su := by rw [UInt32.toNat_ofNat']; omega
  have hpred : CARD (UInt8.ofNat su) (UInt8.ofNat (A + 1)) - 1
      = CARD (UInt8.ofNat su) (UInt8.ofNat A) := by
    rw [cv_card_pred hsu (by omega) (by omega)]
    congr 1
  unfold cvSuitStep
  rw [hA]
  simp only [cvSuitBody, bind, EStateM.bind, pure, EStateM.pure, hwalk, hpred,
    Vector.setE, hsuU, dif_pos hsu, cv_card_value hsu (show A < 16 by omega)]
  -- the king walk runs on a position that differs from `game` only in fields it
  -- does not read
  have hkw : ∀ (av : Vector UInt8 4) (us : UInt8), A < 13 →
      Loop.forIn Loop.mk (CARD (UInt8.ofNat su) (UInt8.ofNat 13))
          (cvKingBody g { game with aces := av, usedSpace := us }) s
        = .ok (CARD (UInt8.ofNat su) (UInt8.ofNat (cvKingVal g game.pileDepth su))) s := by
    intro av us hlt
    exact cvKingWalk_run g { game with aces := av, usedSpace := us } hwf su hsu s
      (by rw [show ({ game with aces := av, usedSpace := us } : SolverPosType).pileDepth
                = game.pileDepth from rfl, hA]; omega)
  by_cases hlt : A < 13
  · rw [if_pos ((cv_card_lt hsu (by omega) (by omega)).mpr hlt)]
    simp only [EStateM.bind, hkw _ _ hlt, EStateM.pure]
  · obtain rfl : A = 13 := by omega
    have hKV : cvKingVal g game.pileDepth su = 13 := by
      unfold cvKingVal; rw [if_pos (by rw [hA])]
    rw [if_neg (by rw [cv_card_lt hsu (by omega) (by omega)]; omega), hKV]
    simp only [EStateM.bind, EStateM.pure]

/-! ## Loop 2: the exact run -/

/-- The position after the first `k` iterations of the per-suit loop. -/
def cvSuitUpTo (g : Globals) (p : SolverPosType) : Nat → SolverPosType
  | 0 => p
  | k + 1 => if h : k < 4 then cvSuitStep g k h (cvSuitUpTo g p k) else cvSuitUpTo g p k

theorem cvSuitUpTo_succ (g : Globals) (p : SolverPosType) {k : Nat} (hk : k < 4) :
    cvSuitUpTo g p (k + 1) = cvSuitStep g k hk (cvSuitUpTo g p k) := by
  simp only [cvSuitUpTo, dif_pos hk]

theorem cvSuitLoop_run (g : Globals) (hwf : WellFormedLayout g) (p : SolverPosType)
    (s : Globals × SolverPosType) :
    ∀ (n k : Nat), k + n = 4 →
      forIn (List.range' k n) (cvSuitUpTo g p k) (cvSuitBody g) s
        = .ok (cvSuitUpTo g p 4) s := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 4 := by omega
    rfl
  | succ n ih =>
    intro k hk
    have hklt : k < 4 := by omega
    rw [List.range'_succ, List.forIn_cons]
    show (cvSuitBody g k (cvSuitUpTo g p k) >>= _) s = _
    simp only [bind, EStateM.bind, cvSuitBody_run g hwf k hklt (cvSuitUpTo g p k) s,
      ← cvSuitUpTo_succ g p hklt]
    exact ih (k + 1) (by omega)

/-! ### What loop 2 computes -/

theorem cvSuitUpTo_pileDepth (g : Globals) (p : SolverPosType) :
    ∀ k : Nat, (cvSuitUpTo g p k).pileDepth = p.pileDepth := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvSuitUpTo]; split <;> simp only [cvSuitStep, ih]

theorem cvSuitUpTo_pileFlute (g : Globals) (p : SolverPosType) :
    ∀ k : Nat, (cvSuitUpTo g p k).pileFlute = p.pileFlute := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvSuitUpTo]; split <;> simp only [cvSuitStep, ih]

theorem cvSuitUpTo_hash (g : Globals) (p : SolverPosType) :
    ∀ k : Nat, (cvSuitUpTo g p k).hash = p.hash := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvSuitUpTo]; split <;> simp only [cvSuitStep, ih]

theorem cvSuitUpTo_freePiles (g : Globals) (p : SolverPosType) :
    ∀ k : Nat, (cvSuitUpTo g p k).freePiles = p.freePiles := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvSuitUpTo]; split <;> simp only [cvSuitStep, ih]

theorem cvSuitUpTo_busyAces (g : Globals) (p : SolverPosType) :
    ∀ k : Nat, (cvSuitUpTo g p k).busyAces = p.busyAces := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [cvSuitUpTo]; split <;> simp only [cvSuitStep, ih]

theorem cvSuitUpTo_aces_succ (g : Globals) (p : SolverPosType) {k : Nat} (hk : k < 4) :
    (cvSuitUpTo g p (k + 1)).aces = (cvSuitUpTo g p k).aces.set k
      (CARD (UInt8.ofNat k) (UInt8.ofNat (cvAceVal g p.pileDepth k))) hk := by
  rw [cvSuitUpTo_succ g p hk]
  show (cvSuitUpTo g p k).aces.set k
    (CARD (UInt8.ofNat k) (UInt8.ofNat (cvAceVal g (cvSuitUpTo g p k).pileDepth k))) hk = _
  rw [cvSuitUpTo_pileDepth g p k]

theorem cvSuitUpTo_kings_succ (g : Globals) (p : SolverPosType) {k : Nat} (hk : k < 4) :
    (cvSuitUpTo g p (k + 1)).kings = (cvSuitUpTo g p k).kings.set k
      (CARD (UInt8.ofNat k) (UInt8.ofNat (cvKingVal g p.pileDepth k))) hk := by
  rw [cvSuitUpTo_succ g p hk]
  show (cvSuitUpTo g p k).kings.set k
    (CARD (UInt8.ofNat k) (UInt8.ofNat (cvKingVal g (cvSuitUpTo g p k).pileDepth k))) hk = _
  rw [cvSuitUpTo_pileDepth g p k]

theorem cvSuitUpTo_usedSpace_succ (g : Globals) (p : SolverPosType) {k : Nat} (hk : k < 4) :
    (cvSuitUpTo g p (k + 1)).usedSpace =
      (cvSuitUpTo g p k).usedSpace - UInt8.ofNat (cvAceVal g p.pileDepth k) := by
  rw [cvSuitUpTo_succ g p hk]
  show (cvSuitUpTo g p k).usedSpace - UInt8.ofNat (cvAceVal g (cvSuitUpTo g p k).pileDepth k) = _
  rw [cvSuitUpTo_pileDepth g p k]

theorem cvSuitUpTo_aces (g : Globals) (p : SolverPosType) :
    ∀ (k : Nat), k ≤ 4 → ∀ i : Fin 4,
      (cvSuitUpTo g p k).aces.get i =
        if i.val < k then CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvAceVal g p.pileDepth i.val))
        else p.aces.get i := by
  intro k
  induction k with
  | zero => intro _ i; simp [cvSuitUpTo]
  | succ k ih =>
    intro hk i
    rw [cvSuitUpTo_aces_succ g p (show k < 4 by omega)]
    show ((cvSuitUpTo g p k).aces.set k
      (CARD (UInt8.ofNat k) (UInt8.ofNat (cvAceVal g p.pileDepth k))) (by omega))[i.val]'i.isLt = _
    rw [Vector.getElem_set]
    by_cases hik : i.val = k
    · rw [if_pos hik.symm, if_pos (by omega), hik]
    · rw [if_neg (fun h => hik h.symm)]
      show (cvSuitUpTo g p k).aces.get i = _
      rw [ih (by omega) i]
      by_cases h2 : i.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem cvSuitUpTo_kings (g : Globals) (p : SolverPosType) :
    ∀ (k : Nat), k ≤ 4 → ∀ i : Fin 4,
      (cvSuitUpTo g p k).kings.get i =
        if i.val < k then CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvKingVal g p.pileDepth i.val))
        else p.kings.get i := by
  intro k
  induction k with
  | zero => intro _ i; simp [cvSuitUpTo]
  | succ k ih =>
    intro hk i
    rw [cvSuitUpTo_kings_succ g p (show k < 4 by omega)]
    show ((cvSuitUpTo g p k).kings.set k
      (CARD (UInt8.ofNat k) (UInt8.ofNat (cvKingVal g p.pileDepth k))) (by omega))[i.val]'i.isLt = _
    rw [Vector.getElem_set]
    by_cases hik : i.val = k
    · rw [if_pos hik.symm, if_pos (by omega), hik]
    · rw [if_neg (fun h => hik h.symm)]
      show (cvSuitUpTo g p k).kings.get i = _
      rw [ih (by omega) i]
      by_cases h2 : i.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-- The prefix sum of the foundation tops the walks compute. -/
def cvAcePrefix (g : Globals) (d : Vector UInt8 10) (k : Nat) : Nat :=
  ((List.finRange 4).take k).foldl (fun acc s => acc + cvAceVal g d s.val) 0

theorem cvAcePrefix_succ (g : Globals) (d : Vector UInt8 10) {k : Nat} (hk : k < 4) :
    cvAcePrefix g d (k + 1) = cvAcePrefix g d k + cvAceVal g d k := by
  unfold cvAcePrefix
  rw [finRange_take_succ hk, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

theorem cvAcePrefix_le (g : Globals) (d : Vector UInt8 10) :
    ∀ (k : Nat), k ≤ 4 → cvAcePrefix g d k ≤ 13 * k := by
  intro k
  induction k with
  | zero => intro _; simp [cvAcePrefix]
  | succ k ih =>
    intro hk
    have hklt : k < 4 := by omega
    have hv : cvAceVal g d k ≤ 13 := runLen_le _ _
    rw [cvAcePrefix_succ g d hklt]
    have := ih (by omega)
    omega

theorem cvAcePrefix_mono (g : Globals) (d : Vector UInt8 10) :
    ∀ (n k : Nat), k + n = 4 → cvAcePrefix g d k ≤ cvAcePrefix g d 4 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 4 := by omega
    exact le_refl _
  | succ n ih =>
    intro k hk
    have hklt : k < 4 := by omega
    exact le_trans (by rw [cvAcePrefix_succ g d hklt]; omega) (ih (k + 1) (by omega))

theorem cvSuitUpTo_usedSpace (g : Globals) (p : SolverPosType)
    (hbound : cvAcePrefix g p.pileDepth 4 ≤ p.usedSpace.toNat) :
    ∀ (k : Nat), k ≤ 4 →
      (cvSuitUpTo g p k).usedSpace.toNat = p.usedSpace.toNat - cvAcePrefix g p.pileDepth k := by
  intro k
  induction k with
  | zero => intro _; simp [cvSuitUpTo, cvAcePrefix]
  | succ k ih =>
    intro hk
    have hklt : k < 4 := by omega
    have hprev := ih (by omega)
    have hA13 : cvAceVal g p.pileDepth k ≤ 13 := runLen_le _ _
    have hstep := cvAcePrefix_succ g p.pileDepth hklt
    have hmk := cvAcePrefix_mono g p.pileDepth (4 - (k + 1)) (k + 1) (by omega)
    have hofN : (UInt8.ofNat (cvAceVal g p.pileDepth k)).toNat = cvAceVal g p.pileDepth k := by
      rw [UInt8.toNat_ofNat']; omega
    rw [cvSuitUpTo_usedSpace_succ g p hklt]
    rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hprev, hofN]; omega),
      hprev, hofN, hstep]
    omega

/-! ## The prologue's result, in closed form -/

theorem solverPos_ext {p q : SolverPosType} (h1 : p.hash = q.hash) (h2 : p.pileDepth = q.pileDepth)
    (h3 : p.pileFlute = q.pileFlute) (h4 : p.aces = q.aces) (h5 : p.kings = q.kings)
    (h6 : p.usedSpace = q.usedSpace) (h7 : p.freePiles = q.freePiles)
    (h8 : p.busyAces = q.busyAces) : p = q := by
  cases p; cases q; simp_all

/-- The position loop 1 starts from: the input position with the bookkeeping
    fields reset. -/
def cvInit (p0 : SolverPosType) : SolverPosType :=
  { p0 with busyAces := 0, usedSpace := 52, freePiles := 0, hash := 0 }

/-- The position after loop 1. -/
def cvAfterDepths (pk : Vector UInt8 11) (p0 : SolverPosType) : SolverPosType :=
  cvDepthUpTo pk (cvInit p0) 10

theorem cvAfterDepths_pileDepth (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).pileDepth = cvDepths pk := by
  refine vector_ext_get _ _ (fun i => ?_)
  rw [cvAfterDepths, cvDepthUpTo_pileDepth pk (cvInit p0) 10 (le_refl _) i, if_pos i.isLt]

theorem cvAfterDepths_pileFlute (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).pileFlute = Vector.ofFn (fun _ : Fin 10 => (1 : UInt8)) := by
  refine vector_ext_get _ _ (fun i => ?_)
  rw [cvAfterDepths, cvDepthUpTo_pileFlute pk (cvInit p0) 10 (le_refl _) i, if_pos i.isLt]
  show (1 : UInt8) = (Vector.ofFn (fun _ : Fin 10 => (1 : UInt8)))[i.val]'i.isLt
  rw [Vector.getElem_ofFn]

/-- The value the prologue leaves in `hash`: exactly `SolverInvBase.hash_def`'s
    right-hand side for the installed depths. -/
def cvHash (pk : Vector UInt8 11) : UInt32 :=
  (List.finRange 10).foldl
    (fun acc i => acc + pileHashes.get i * ((cvDepths pk).get i).toNat.toUInt32) 0

theorem cvAfterDepths_hash (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).hash = cvHash pk := by
  rw [cvAfterDepths, cvDepthUpTo_hash pk (cvInit p0) 10 (le_refl _)]
  simp only [cvHash, List.take_of_length_le (by simp : (List.finRange 10).length ≤ 10)]
  rfl

theorem cvAfterDepths_aces (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).aces = p0.aces := cvDepthUpTo_aces pk (cvInit p0) 10

theorem cvAfterDepths_kings (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).kings = p0.kings := cvDepthUpTo_kings pk (cvInit p0) 10

theorem cvAfterDepths_freePiles (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).freePiles = 0 := cvDepthUpTo_freePiles pk (cvInit p0) 10

theorem cvAfterDepths_busyAces (pk : Vector UInt8 11) (p0 : SolverPosType) :
    (cvAfterDepths pk p0).busyAces = 0 := cvDepthUpTo_busyAces pk (cvInit p0) 10

theorem cvAfterDepths_usedSpace (pk : Vector UInt8 11) (p0 : SolverPosType)
    (hpk : ValidDepths pk) :
    (cvAfterDepths pk p0).usedSpace.toNat = 52 - cvDepthPrefix pk 10 :=
  cvDepthUpTo_usedSpace pk (cvInit p0) hpk
    (show 50 ≤ (cvInit p0).usedSpace.toNat from by
      show 50 ≤ (52 : UInt8).toNat
      decide) 10 (le_refl _)

/-- **The counting bound.**  The cards still on piles and the cards the walks put
    on the foundations are disjoint families inside the 52-card deck, so `usedSpace`
    never underflows.  (Proved in `ConvertCount`.) -/
def CvCountBound (g : Globals) (pk : Vector UInt8 11) : Prop :=
  cvDepthPrefix pk 10 + cvAcePrefix g (cvDepths pk) 4 ≤ 52

/-- **The position `SolverConvertFromPilesKings`'s prologue produces.**  Every
    field is determined by the globals and the input depth vector. -/
def convertPre (g : Globals) (pk : Vector UInt8 11) : SolverPosType :=
  { hash := cvHash pk
    pileDepth := cvDepths pk
    pileFlute := Vector.ofFn (fun _ : Fin 10 => (1 : UInt8))
    aces := Vector.ofFn (fun i : Fin 4 =>
      CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvAceVal g (cvDepths pk) i.val)))
    kings := Vector.ofFn (fun i : Fin 4 =>
      CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvKingVal g (cvDepths pk) i.val)))
    usedSpace := UInt8.ofNat (52 - cvDepthPrefix pk 10 - cvAcePrefix g (cvDepths pk) 4)
    freePiles := 0
    busyAces := 0 }

theorem cvPrologue_eq (g : Globals) (pk : Vector UInt8 11) (p0 : SolverPosType)
    (hpk : ValidDepths pk) (hcount : CvCountBound g pk) :
    cvSuitUpTo g (cvAfterDepths pk p0) 4 = convertPre g pk := by
  have hdep : (cvAfterDepths pk p0).pileDepth = cvDepths pk := cvAfterDepths_pileDepth pk p0
  have hdp10 : cvDepthPrefix pk 10 ≤ 50 := cvDepthPrefix_le pk hpk 10 (le_refl _)
  have hus : (cvAfterDepths pk p0).usedSpace.toNat = 52 - cvDepthPrefix pk 10 :=
    cvAfterDepths_usedSpace pk p0 hpk
  refine solverPos_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cvSuitUpTo_hash, cvAfterDepths_hash]; rfl
  · rw [cvSuitUpTo_pileDepth, hdep]; rfl
  · rw [cvSuitUpTo_pileFlute, cvAfterDepths_pileFlute]; rfl
  · refine vector_ext_get _ _ (fun i => ?_)
    rw [cvSuitUpTo_aces g (cvAfterDepths pk p0) 4 (le_refl _) i, if_pos i.isLt, hdep]
    show _ = (Vector.ofFn (fun i : Fin 4 =>
      CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvAceVal g (cvDepths pk) i.val))))[i.val]'i.isLt
    rw [Vector.getElem_ofFn]
  · refine vector_ext_get _ _ (fun i => ?_)
    rw [cvSuitUpTo_kings g (cvAfterDepths pk p0) 4 (le_refl _) i, if_pos i.isLt, hdep]
    show _ = (Vector.ofFn (fun i : Fin 4 =>
      CARD (UInt8.ofNat i.val) (UInt8.ofNat (cvKingVal g (cvDepths pk) i.val))))[i.val]'i.isLt
    rw [Vector.getElem_ofFn]
  · apply UInt8.toNat_inj.mp
    rw [cvSuitUpTo_usedSpace g (cvAfterDepths pk p0) (by rw [hdep, hus]; exact (by
        unfold CvCountBound at hcount; omega)) 4 (le_refl _), hdep, hus]
    show _ = (UInt8.ofNat (52 - cvDepthPrefix pk 10 - cvAcePrefix g (cvDepths pk) 4)).toNat
    rw [UInt8.toNat_ofNat']
    unfold CvCountBound at hcount
    omega
  · rw [cvSuitUpTo_freePiles, cvAfterDepths_freePiles]; rfl
  · rw [cvSuitUpTo_busyAces, cvAfterDepths_busyAces]; rfl

/-- **The prologue, run.**  Loops 1 and 2 leave the state alone and hand the
    cleanup loop exactly `convertPre g pk`. -/
theorem convert_run_eq (g : Globals) (hwf : WellFormedLayout g) (pk : Vector UInt8 11)
    (p0 : SolverPosType) (hpk : ValidDepths pk) (hcount : CvCountBound g pk) :
    _root_.SolverConvertFromPilesKings pk (g, p0)
      = (forIn (List.range 10) (0xffff : UInt16) cvCleanupBody >>= fun fk =>
          Loop.forIn Loop.mk fk drainBody >>= fun r => pure r) (g, convertPre g pk) := by
  have hl1 : forIn (List.range' 0 10)
      ({ hash := 0, pileDepth := p0.pileDepth, pileFlute := p0.pileFlute, aces := p0.aces,
         kings := p0.kings, usedSpace := 52, freePiles := 0, busyAces := 0 } : SolverPosType)
      (cvDepthBody pk) (g, p0) = .ok (cvAfterDepths pk p0) (g, p0) :=
    cvDepthLoop_run pk (cvInit p0) (g, p0) 10 0 rfl
  have hl2 : forIn (List.range' 0 4) (cvAfterDepths pk p0) (cvSuitBody g) (g, p0)
      = .ok (convertPre g pk) (g, p0) := by
    rw [← cvPrologue_eq g pk p0 hpk hcount]
    exact cvSuitLoop_run g hwf (cvAfterDepths pk p0) (g, p0) 4 0 rfl
  rw [convert_eq_explicit pk]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.set, pure, EStateM.pure,
    show List.range 10 = List.range' 0 10 from by rw [List.range_eq_range'],
    show List.range 4 = List.range' 0 4 from by rw [List.range_eq_range'],
    hl1, hl2]

end SolverSpec

