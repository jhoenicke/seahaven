import Seahaven.Solver
import Seahaven.EStateMTail

/-!
# Specs proved directly against the real solver (no fuel model)

On Lean 4.31 the real solver's `while` loops are no longer opaque (see
`Seahaven.EStateMTail`), so we can state and prove specifications directly about
`_root_.SolverCleanupPile` etc., instead of going through the `SolverModel` fuel
twin and a (fragile, fuel-dependent) `model = real` equality.

This file seeds that approach.  `cleanupPile_empty` is a *complete* proof (only
the standard `propext/Classical.choice/Quot.sound` axioms — no `sorry`) about the
real function: it is the base case of the convert cleanup loop.
-/

-- **Base case of `SolverCleanupPile`.**  Cleaning an already-empty pile
-- (`pileDepth[pile] = 0`) succeeds without running either `while` loop: it leaves
-- `globals` unchanged, bumps `freePiles`, rewrites the (unchanged) depth/flute of
-- `pile`, and returns `0xffff`.
set_option linter.unusedSimpArgs false in
theorem cleanupPile_empty_eq (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hd : p.pileDepth[pile.toNat]'(by omega) = 0) :
    EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff
      (g, { p with
        freePiles := p.freePiles + 1,
        pileDepth := p.pileDepth.set pile.toNat 0 (by omega),
        pileFlute := p.pileFlute.set pile.toNat 1 (by omega) }) := by
  unfold SolverCleanupPile
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.set, EStateM.pure, Vector.getE, Vector.setE, getElem?_pos, hpile, hd, dif_pos]
  rfl

theorem cleanupPile_empty (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10)
    (hd : p.pileDepth[pile.toNat]'(by omega) = 0) :
    ∃ p', EStateM.run (_root_.SolverCleanupPile pile) (g, p) = .ok 0xffff (g, p') :=
  ⟨_, cleanupPile_empty_eq pile g p hpile hd⟩

/-!
## Loop-bearing cases

The merge/freed `while` loops of `SolverCleanupPile` are reasoned about by induction
on their decreasing measures.  `mergeBody`/`freedBody` mirror the loops (`Solver.lean`);
`mergeLoop_ok`/`freedLoop_ok` prove they terminate state-purely (complete, no `sorry`).
Each case unfolds one loop step via `Lean.Loop.forIn_eq_of_monadTail`; the `getE`s
reduce by `getElem?_pos` once the index bounds are derived, and the wrap-free
subtraction lemmas (`Int32.toInt_sub_of_le`, `UInt8.toNat_sub_of_le`) turn the
measure decrease (`depth` resp. `prevCard`) into the `Nat` decrease feeding the IH.
For the freed loop the guard itself supplies the lower bound: `aces[suit] ≥ 0` and
`aces[suit] < prevCard` force `prevCard.toNat ∈ [1, 63]` on every iteration.
-/

open Lean Lean.Order

/-- Accumulator of the merge loop: `(card, depth, flute, game)`. -/
abbrev MergeAcc := MProd UInt8 (MProd UInt8 (MProd UInt8 SolverPosType))

/-- Body of the corrected merge `while` loop (state-pure; reads only `globals`). -/
def mergeBody (g : Globals) (pile pilehash : UInt32) :
    Unit → MergeAcc → EStateM Error (Globals × SolverPosType) (ForInStep MergeAcc) :=
  fun _ r => do
    if (← (do return decide (r.snd.fst > 1)) <&&>
      (do return (← (← g.pos2card.getE pile).getE (r.snd.fst - 2).toUInt32)
         == r.fst + 1)) then
        return .yield ⟨r.fst + 1, r.snd.fst - 1, r.snd.snd.fst + 1, { r.snd.snd.snd with hash := r.snd.snd.snd.hash - pilehash }⟩
    else return .done r

/-- The merge loop terminates without touching the state, by induction on a `Nat`
    bounding `depth` (which strictly decreases each iteration; `depth ≤ 5`). -/
theorem mergeLoop_ok (g : Globals) (pile pilehash : UInt32) (hpile : pile.toNat < 10) :
    ∀ (n : Nat) (r : MergeAcc) (s : Globals × SolverPosType),
      r.snd.fst.toNat < n → r.snd.fst.toNat ≤ 5 →
      ∃ res, Loop.forIn Loop.mk r (mergeBody g pile pilehash) s = .ok res s := by
  intro n
  induction n with
  | zero => intro r s h1 _; exact absurd h1 (Nat.not_lt_zero _)
  | succ n ih =>
    intro r s h1 h2
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := r) (f := mergeBody g pile pilehash)
    by_cases hgt : r.snd.fst > 1
    · -- depth > 1: evaluate the two `getE`s (bounds from `pile < 10` and
      -- `2 ≤ depth ≤ 5` ⇒ `depth-2 ∈ [0,3] < 5`), reducing the body to `done r`
      -- (card mismatch) or `yield (card+1, depth-1, flute+1, game{hash-=pilehash})`.
      -- The `yield` case recurses; `(depth-1).toNat = depth.toNat - 1 < n` (from
      -- `h1 : depth.toNat < n+1`) and `≤ 5`, so `ih` closes it.
      have hgt' : 1 < r.snd.fst.toNat := UInt8.lt_iff_toNat_lt.mp hgt
      have hsub2 : (r.snd.fst - 2).toNat = r.snd.fst.toNat - 2 :=
        UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact hgt')
      have hidx : (r.snd.fst - 2).toUInt32.toNat < 5 := by
        rw [UInt8.toNat_toUInt32, hsub2]; omega
      by_cases hcard :
          ((g.pos2card[pile.toNat]'hpile)[(r.snd.fst - 2).toUInt32.toNat]'hidx == r.fst + 1) = true
      · -- card matches: the body yields; the IH closes the recursive call.
        have hsub1 : (r.snd.fst - 1).toNat = r.snd.fst.toNat - 1 :=
          UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)
        obtain ⟨res, hres⟩ := ih
          ⟨r.fst + 1, r.snd.fst - 1, r.snd.snd.fst + 1, { r.snd.snd.snd with hash := r.snd.snd.snd.hash - pilehash }⟩
          s (by rw [hsub1]; omega) (by rw [hsub1]; omega)
        refine ⟨res, ?_⟩
        rw [hunf]
        simp only [mergeBody, hgt, decide_true, bind, EStateM.bind, andM, toBool, pure,
          EStateM.pure, Vector.getE, getElem?_pos, hpile, hidx, hcard, reduceIte]
        exact hres
      · -- card mismatch: the body is done, returning `r` with the state untouched.
        rw [Bool.not_eq_true] at hcard
        refine ⟨r, ?_⟩
        rw [hunf]
        simp only [mergeBody, hgt, decide_true, bind, EStateM.bind, andM, toBool, pure,
          EStateM.pure, Vector.getE, getElem?_pos, hpile, hidx, hcard, Bool.false_eq_true,
          reduceIte]
    · refine ⟨r, ?_⟩
      rw [hunf]
      simp only [mergeBody, hgt]
      rfl

/-!
### Exact run characterization of the merge loop

`mergeLoop_ok` only proves termination.  For invariant-preservation proofs we
need to know *what* the loop computes: the result is `mergeIter pilehash m r`
for some `m`, the guard held before each of the `m` iterations, and fails after.
`mergeIter` recurses on the *front* (`iter (m+1) r = iter m (step r)`), so the
induction composes definitionally — no cast arithmetic in this file; closed
forms are derived downstream where Mathlib is available.
-/

/-- One iteration of the merge loop on the accumulator. -/
def mergeStep (pilehash : UInt32) (r : MergeAcc) : MergeAcc :=
  ⟨r.fst + 1, r.snd.fst - 1, r.snd.snd.fst + 1, { r.snd.snd.snd with hash := r.snd.snd.snd.hash - pilehash }⟩

/-- `m` iterations of the merge loop (front-recursion). -/
def mergeIter (pilehash : UInt32) : Nat → MergeAcc → MergeAcc
  | 0, r => r
  | m + 1, r => mergeIter pilehash m (mergeStep pilehash r)

/-- The merge-loop guard as a `Prop` (index bounds quantified so the statement
    is total; callers instantiate them with in-scope proofs). -/
def mergeGuard (g : Globals) (pile : UInt32) (r : MergeAcc) : Prop :=
  1 < r.snd.fst ∧
  ∀ (h10 : pile.toNat < 10) (h5 : (r.snd.fst - 2).toUInt32.toNat < 5),
    (g.pos2card[pile.toNat]'h10)[(r.snd.fst - 2).toUInt32.toNat]'h5 = r.fst + 1

/-- **Exact run of the merge loop**: it performs some number `m` of `mergeStep`s
    (state untouched), with the guard true before each step and false at exit. -/
theorem mergeLoop_run (g : Globals) (pile pilehash : UInt32) (hpile : pile.toNat < 10) :
    ∀ (n : Nat) (r : MergeAcc) (s : Globals × SolverPosType),
      r.snd.fst.toNat < n → r.snd.fst.toNat ≤ 5 →
      ∃ m : Nat,
        Loop.forIn Loop.mk r (mergeBody g pile pilehash) s
          = .ok (mergeIter pilehash m r) s ∧
        (∀ i, i < m → mergeGuard g pile (mergeIter pilehash i r)) ∧
        ¬ mergeGuard g pile (mergeIter pilehash m r) := by
  intro n
  induction n with
  | zero => intro r s h1 _; exact absurd h1 (Nat.not_lt_zero _)
  | succ n ih =>
    intro r s h1 h2
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := r) (f := mergeBody g pile pilehash)
    by_cases hgt : r.snd.fst > 1
    · have hgt' : 1 < r.snd.fst.toNat := UInt8.lt_iff_toNat_lt.mp hgt
      have hsub2 : (r.snd.fst - 2).toNat = r.snd.fst.toNat - 2 :=
        UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact hgt')
      have hidx : (r.snd.fst - 2).toUInt32.toNat < 5 := by
        rw [UInt8.toNat_toUInt32, hsub2]; omega
      by_cases hcard :
          ((g.pos2card[pile.toNat]'hpile)[(r.snd.fst - 2).toUInt32.toNat]'hidx == r.fst + 1) = true
      · -- guard true: one `mergeStep`, then the IH characterizes the rest.
        have hsub1 : (r.snd.fst - 1).toNat = r.snd.fst.toNat - 1 :=
          UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)
        obtain ⟨m, heq, hguards, hexit⟩ := ih (mergeStep pilehash r) s
          (by show (r.snd.fst - 1).toNat < _; rw [hsub1]; omega)
          (by show (r.snd.fst - 1).toNat ≤ 5; rw [hsub1]; omega)
        refine ⟨m + 1, ?_, ?_, hexit⟩
        · rw [hunf]
          simp only [mergeBody, hgt, decide_true, bind, EStateM.bind, andM, toBool, pure,
            EStateM.pure, Vector.getE, getElem?_pos, hpile, hidx, hcard, reduceIte]
          exact heq
        · intro i hi
          match i with
          | 0 => exact ⟨hgt, fun h10 h5 => eq_of_beq hcard⟩
          | j + 1 => exact hguards j (by omega)
      · -- guard's card test false: zero iterations.
        rw [Bool.not_eq_true] at hcard
        refine ⟨0, ?_, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
        · rw [hunf]
          simp only [mergeBody, hgt, decide_true, bind, EStateM.bind, andM, toBool, pure,
            EStateM.pure, Vector.getE, getElem?_pos, hpile, hidx, hcard, Bool.false_eq_true,
            reduceIte, mergeIter]
        · intro hg
          exact absurd (hcard ▸ beq_of_eq (hg.2 hpile hidx)) (by simp)
    · -- guard's depth test false: zero iterations.
      refine ⟨0, ?_, fun i hi => absurd hi (Nat.not_lt_zero _), fun hg => hgt hg.1⟩
      rw [hunf]
      simp only [mergeBody, hgt, mergeIter]
      rfl

/-- `a - b - c = a - (b + c)` for `UInt32` (missing from core, unlike `Int32.sub_sub`). -/
private theorem uint32_sub_sub (a b c : UInt32) : a - b - c = a - (b + c) := by
  simp only [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.add_assoc]

/-- Closed form of `mergeIter`: after `m` merge steps, `card`/`flute` grew by `m`,
    `depth` shrank by `m`, and the hash lost `m · pilehash`. -/
theorem mergeIter_eq (ph : UInt32) (m : Nat) (r : MergeAcc) :
    mergeIter ph m r =
      ⟨r.fst + UInt8.ofNat m, r.snd.fst - UInt8.ofNat m, r.snd.snd.fst + UInt8.ofNat m,
       { r.snd.snd.snd with hash := r.snd.snd.snd.hash - UInt32.ofNat m * ph }⟩ := by
  induction m generalizing r with
  | zero =>
    show r = _
    simp only [show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero, UInt8.sub_zero,
      show UInt32.ofNat 0 = 0 from rfl, UInt32.zero_mul, UInt32.sub_zero]
  | succ m ih =>
    show mergeIter ph m (mergeStep ph r) = _
    rw [ih]
    simp only [mergeStep, UInt8.ofNat_add, UInt8.ofNat_one,
      UInt32.ofNat_add, UInt32.ofNat_one,
      UInt32.add_mul, UInt32.one_mul, MProd.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [UInt8.add_assoc, UInt8.add_comm 1]
    · rw [UInt8.sub_sub, UInt8.add_comm 1]
    · rw [UInt8.add_assoc, UInt8.add_comm 1]
    · rw [uint32_sub_sub, UInt32.add_comm ph]

/-- Accumulator of the freed-predecessor loop: `(flute, game, prevCard)`. -/
abbrev FreedAcc := MProd UInt8 (MProd SolverPosType UInt8)

/-- Body of the freed-predecessor `while` loop of `SolverCleanupPile` (state-pure;
    reads only `globals` and the accumulator's game). -/
def freedBody (g : Globals) (suit : UInt8) :
    Unit → FreedAcc → EStateM Error (Globals × SolverPosType) (ForInStep FreedAcc) :=
  fun _ r => do
    if (← ((do return decide ((← r.snd.fst.aces.getE suit.toUInt32) < r.snd.snd)) <&&>
      (do return ((← g.card2depth.getE r.snd.snd.toUInt32).toNat >=
          (← r.snd.fst.pileDepth.getE
            (← g.card2pile.getE r.snd.snd.toUInt32).toUInt32).toNat)))) then
      return .yield ⟨r.fst + 1, { r.snd.fst with usedSpace := r.snd.fst.usedSpace - 1 }, r.snd.snd - 1⟩
    else return .done r

/-- The freed-predecessor loop terminates without touching the state, by induction
    on a `Nat` bounding `prevCard`.  Preconditions: `suit` indexes `aces`; every
    `card2pile` entry is a valid pile index (`< 10`, its value indexes `pileDepth`);
    `prevCard < 64` (indexes `card2depth`/`card2pile`); and the foundation top
    `aces[suit]` is nonnegative — together with the loop guard this keeps
    `prevCard.toNat` in `[1, 63]` while the loop runs, so `prevCard - 1` never
    wraps and the index bounds are maintained. -/
theorem freedLoop_ok (g : Globals) (suit : UInt8) (hsuit : suit.toUInt32.toNat < 4)
    (hpiles : ∀ (i : Nat) (h : i < 64), (g.card2pile[i]'h).toNat < 10) :
    ∀ (n : Nat) (r : FreedAcc) (s : Globals × SolverPosType),
      r.snd.snd.toNat < n → r.snd.snd.toNat < 64 →
      (0 : UInt8) ≤ r.snd.fst.aces[suit.toUInt32.toNat]'hsuit →
      ∃ res, Loop.forIn Loop.mk r (freedBody g suit) s = .ok res s := by
  intro n
  induction n with
  | zero => intro r s h1 _ _; exact absurd h1 (Nat.not_lt_zero _)
  | succ n ih =>
    intro r s h1 h64 haces
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := r) (f := freedBody g suit)
    have hc64 : r.snd.snd.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact h64
    by_cases hg1 : r.snd.fst.aces[suit.toUInt32.toNat]'hsuit < r.snd.snd
    · have hp10 : (g.card2pile[r.snd.snd.toUInt32.toNat]'hc64).toUInt32.toNat < 10 := by
        rw [UInt8.toNat_toUInt32]; exact hpiles _ hc64
      by_cases hg2 : (g.card2depth[r.snd.snd.toUInt32.toNat]'hc64).toNat ≥
          (r.snd.fst.pileDepth[(g.card2pile[r.snd.snd.toUInt32.toNat]'hc64).toUInt32.toNat]'hp10
            ).toNat
      · -- both conjuncts true: the body yields; `prevCard` strictly decreases.
        have hposN : 0 < r.snd.snd.toNat := by
          have hb := UInt8.lt_iff_toNat_lt.mp hg1
          omega
        have h1le : (1 : UInt8) ≤ r.snd.snd := by
          rw [UInt8.le_iff_toNat_le]; show 1 ≤ r.snd.snd.toNat; omega
        have hsub : (r.snd.snd - 1).toNat = r.snd.snd.toNat - 1 :=
          UInt8.toNat_sub_of_le _ _ h1le
        obtain ⟨res, hres⟩ := ih
          ⟨r.fst + 1, { r.snd.fst with usedSpace := r.snd.fst.usedSpace - 1 }, r.snd.snd - 1⟩ s
          (by rw [hsub]; omega) (by rw [hsub]; omega) haces
        refine ⟨res, ?_⟩
        rw [hunf]
        simp only [freedBody, hg1, hg2, decide_true, bind, EStateM.bind, andM, toBool, pure,
          EStateM.pure, Vector.getE, getElem?_pos, hsuit, hc64, hp10, reduceIte]
        exact hres
      · -- freed-condition false: the body is done, the state untouched.
        refine ⟨r, ?_⟩
        rw [hunf]
        simp only [freedBody, hg1, hg2, decide_true, decide_false, bind, EStateM.bind, andM,
          toBool, pure, EStateM.pure, Vector.getE, getElem?_pos, hsuit, hc64, hp10,
          Bool.false_eq_true, reduceIte]
    · -- foundation already at `prevCard`: `<&&>` short-circuits, the body is done.
      refine ⟨r, ?_⟩
      rw [hunf]
      simp only [freedBody, hg1, decide_false, bind, EStateM.bind, andM, toBool, pure,
        EStateM.pure, Vector.getE, getElem?_pos, hsuit, Bool.false_eq_true, reduceIte]

/-!
### Explicit-loop twin of `SolverCleanupPile`

`cleanupPileExplicit` is `SolverCleanupPile` with the two `while` loops written as
explicit `Loop.forIn Loop.mk … mergeBody/freedBody` calls and the join points
inlined.  All differences from the real elaboration (mut-var threading, join
lambdas, `pure`-`bind` sequencing) are definitional, so the equality is `rfl` —
this gives spec proofs a syntactic handle on the loops without matching against
the `while` elaboration.
-/
def cleanupPileExplicit (pile : UInt32) : EStateM Error (Globals × SolverPosType) UInt16 := do
  let ⟨globals, game⟩ ← get
  let forcedKings : UInt16 := 0xffff
  let pilehash ← pileHashes.getE pile
  let depth := ← game.pileDepth.getE pile
  let flute : UInt8 := 1
  -- final writes, shared by all paths (the elaborator's outer join point)
  let finish : UInt8 → UInt8 → UInt16 → SolverPosType →
      EStateM Error (Globals × SolverPosType) UInt16 :=
    fun depth flute forcedKings game => do
      let newDepth ← game.pileDepth.setE pile depth
      let newFlute ← game.pileFlute.setE pile flute
      set (⟨globals, { game with pileDepth := newDepth, pileFlute := newFlute }⟩ :
        Globals × SolverPosType)
      pure forcedKings
  if depth == 0 then
    finish depth flute forcedKings { game with freePiles := game.freePiles + 1 }
  else
    let card ← (← globals.pos2card.getE pile).getE (depth - 1).toUInt32
    let suit := SUIT card
    let prevCard := card - 1
    let r1 ← Loop.forIn Loop.mk ⟨card, depth, flute, game⟩ (mergeBody globals pile pilehash)
    let ⟨card, depth, flute, game⟩ := r1
    let r2 ← Loop.forIn Loop.mk ⟨flute, game, prevCard⟩ (freedBody globals suit)
    let ⟨flute, game, prevCard⟩ := r2
    let acesS ← game.aces.getE suit.toUInt32
    -- lone-king branch, shared by both `busyAces` outcomes (the inner join point)
    let kingCheck : SolverPosType → EStateM Error (Globals × SolverPosType) UInt16 :=
      fun game =>
        if depth == 1 && VALUE card == 13 then do
          let game := { game with freePiles := game.freePiles + 1 }
          let game := { game with usedSpace := game.usedSpace + flute }
          let kOld ← game.kings.getE suit.toUInt32
          let newKings ← game.kings.setE suit.toUInt32 (kOld - flute)
          let game := { game with kings := newKings }
          let game := { game with hash := game.hash - pilehash }
          let fk ← kingOnPileMap.getE suit.toUInt32
          finish 0 1 (forcedKings &&& fk) game
        else finish depth flute forcedKings game
    if acesS == prevCard then
      kingCheck { game with busyAces := game.busyAces ||| (1 : UInt8) <<< suit }
    else
      kingCheck game

/-- The explicit-loop twin is definitionally the real function. -/
theorem cleanupPile_eq_explicit : _root_.SolverCleanupPile = cleanupPileExplicit := rfl

/-!
### Exact run characterization of the freed loop (mirrors `mergeLoop_run`)
-/

/-- One iteration of the freed-predecessor loop on the accumulator. -/
def freedStep (r : FreedAcc) : FreedAcc :=
  ⟨r.fst + 1, { r.snd.fst with usedSpace := r.snd.fst.usedSpace - 1 }, r.snd.snd - 1⟩

/-- `f` iterations of the freed loop (front-recursion). -/
def freedIter : Nat → FreedAcc → FreedAcc
  | 0, r => r
  | f + 1, r => freedIter f (freedStep r)

/-- The freed-loop guard as a `Prop` (index bounds quantified). -/
def freedGuard (g : Globals) (suit : UInt8) (r : FreedAcc) : Prop :=
  (∀ (h4 : suit.toUInt32.toNat < 4),
    r.snd.fst.aces[suit.toUInt32.toNat]'h4 < r.snd.snd) ∧
  ∀ (h64 : r.snd.snd.toUInt32.toNat < 64)
    (h10 : (g.card2pile[r.snd.snd.toUInt32.toNat]'h64).toUInt32.toNat < 10),
    (g.card2depth[r.snd.snd.toUInt32.toNat]'h64).toNat ≥
    (r.snd.fst.pileDepth[(g.card2pile[r.snd.snd.toUInt32.toNat]'h64).toUInt32.toNat]'h10
      ).toNat

/-- `a - b - c = a - (b + c)` for `UInt8` (missing from core, unlike `UInt8.sub_sub`). -/
private theorem uint8_sub_sub (a b c : UInt8) : a - b - c = a - (b + c) := by
  simp only [UInt8.sub_eq_add_neg, UInt8.neg_add, UInt8.add_assoc]

/-- Closed form of `freedIter`: after `f` freed steps, `flute` grew by `f`,
    `usedSpace` shrank by `f`, and `prevCard` walked down by `f`. -/
theorem freedIter_eq (f : Nat) (r : FreedAcc) :
    freedIter f r =
      ⟨r.fst + UInt8.ofNat f,
       { r.snd.fst with usedSpace := r.snd.fst.usedSpace - (UInt8.ofNat f) },
       r.snd.snd - UInt8.ofNat f⟩ := by
  induction f generalizing r with
  | zero =>
    show r = _
    simp only [show UInt8.ofNat 0 = 0 from rfl, UInt8.add_zero, UInt8.sub_zero]
  | succ f ih =>
    show freedIter f (freedStep r) = _
    rw [ih]
    simp only [freedStep, UInt8.ofNat_add, show UInt8.ofNat 1 = 1 from rfl,
      UInt8.ofNat_add, UInt8.ofNat_one, MProd.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [UInt8.add_assoc, UInt8.add_comm 1]
    · rw [UInt8.sub_sub, UInt8.add_comm 1]
    · rw [uint8_sub_sub, UInt8.add_comm 1]

/-- The `(forcedKings, game)` result of a non-empty `SolverCleanupPile` run, given
    the boundary card `B`, the pile hash `ph`, the entry depth `d32`, and the two
    loops' iteration counts `m` (merge) and `f` (freed).  Mirrors the tail of the
    function after both loops: the `busyAces` check, the lone-king branch, and the
    final depth/flute writes. -/
def cleanupRunResult (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d : UInt8) (m f : Nat) (p : SolverPosType) : UInt16 × SolverPosType :=
  let card1 := B + UInt8.ofNat m
  let depth1 := d - UInt8.ofNat m
  let flute2 := 1 + UInt8.ofNat m + UInt8.ofNat f
  let prev2 := B - 1 - UInt8.ofNat f
  let game2 : SolverPosType :=
    { p with hash := p.hash - UInt32.ofNat m * ph, usedSpace := p.usedSpace - (UInt8.ofNat f) }
  let game3 :=
    if p.aces[(SUIT B).toUInt32.toNat]'hs4 == prev2 then
      { game2 with busyAces := game2.busyAces ||| (1 : UInt8) <<< SUIT B }
    else game2
  if depth1 == 1 && VALUE card1 == 13 then
    let game4 :=
      { game3 with
        freePiles := game3.freePiles + 1,
        usedSpace := game3.usedSpace + flute2,
        kings := game3.kings.set (SUIT B).toUInt32.toNat
          (game3.kings[(SUIT B).toUInt32.toNat]'hs4 - flute2) hs4,
        hash := game3.hash - ph }
    (0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
     { game4 with
       pileDepth := game4.pileDepth.set pile.toNat (0 : UInt8) hpile,
       pileFlute := game4.pileFlute.set pile.toNat (1 : UInt8) hpile })
  else
    (0xffff,
     { game3 with
       pileDepth := game3.pileDepth.set pile.toNat depth1 hpile,
       pileFlute := game3.pileFlute.set pile.toNat flute2 hpile })

/-- **`SolverCleanupPile`'s non-empty tail, always taking the "ordinary" (no
    lone-king) branch** — i.e. `cleanupRunResult`'s `else` branch, unconditionally,
    returning just the position (the `UInt16` result is only meaningful in the
    lone-king branch, where it reports the merge-forced kings).

    Splitting this out lets "merge/free the pile" and "drain a finished
    lone-king pile into `kings`" (`kingMove`) be reasoned about independently:
    the pile ends up `PileClean` after `preCleanupPile` regardless of whether
    its new boundary happens to be a king, and `kingMove` is a *generic* "drain
    a clean, depth-1, king-boundary pile" operation that doesn't need to know
    about `m`/`f`/the loops at all — see `cleanupRunResult_eq`. -/
def preCleanupPile (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d : UInt8) (m f : Nat) (p : SolverPosType) : SolverPosType :=
  let depth1 := d - UInt8.ofNat m
  let flute2 := 1 + UInt8.ofNat m + UInt8.ofNat f
  let prev2 := B - 1 - UInt8.ofNat f
  { p with
    hash := p.hash - UInt32.ofNat m * ph,
    usedSpace := p.usedSpace - UInt8.ofNat f
    busyAces := if p.aces[(SUIT B).toUInt32.toNat]'hs4 == prev2 then p.busyAces ||| (1 : UInt8) <<< SUIT B else p.busyAces
    pileDepth := p.pileDepth.set pile.toNat depth1 hpile,
    pileFlute := p.pileFlute.set pile.toNat flute2 hpile }

/-- **Drain a depth-1, king-boundary pile into `kings`.**  Given any position
    where pile `pile` currently holds nothing but a `pileFlute[pile]`-long run
    ending in the king of `suit` (so `pileDepth[pile] = 1`), replay
    `cleanupRunResult`'s lone-king tail: empty the pile (`pileDepth := 0`,
    `pileFlute := 1`), bump `freePiles`/`usedSpace`, and move the flute's worth
    of cards out of `kings[suit]` (which sits just above the drained run) down
    past them.  Reads the amount to drain directly off `pileFlute[pile]`
    rather than threading `m`/`f` through, so it applies to any clean position,
    not just a fresh `preCleanupPile` result. -/
def kingMove (pile : UInt32) (hpile : pile.toNat < 10) (suit : UInt8)
    (hs4 : suit.toUInt32.toNat < 4) (ph : UInt32) (p : SolverPosType) : SolverPosType :=
  { p with
    freePiles := p.freePiles + 1,
    usedSpace := p.usedSpace + (p.pileFlute[pile.toNat]'hpile),
    kings := p.kings.set suit.toUInt32.toNat
      (p.kings[suit.toUInt32.toNat]'hs4 - (p.pileFlute[pile.toNat]'hpile)) hs4,
    hash := p.hash - ph,
    pileDepth := p.pileDepth.set pile.toNat (0 : UInt8) hpile,
    pileFlute := p.pileFlute.set pile.toNat (1 : UInt8) hpile }

/-- **`cleanupRunResult` factors as `preCleanupPile`, followed — in the
    lone-king case only — by `kingMove`.**  `kingMove` re-derives the drained
    amount from the flute `preCleanupPile` just wrote, which is exactly `1+m+f`
    (now a plain `UInt8` computation, so the equality is `rfl` per branch). -/
theorem cleanupRunResult_eq (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d : UInt8) (m f : Nat) (p : SolverPosType) :
    cleanupRunResult pile hpile B ph hs4 d m f p =
      if d - UInt8.ofNat m == 1 && VALUE (B + UInt8.ofNat m) == 13 then
        (0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4,
          kingMove pile hpile (SUIT B) hs4 ph (preCleanupPile pile hpile B ph hs4 d m f p))
      else
        (0xffff, preCleanupPile pile hpile B ph hs4 d m f p) := by
  cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f)) <;>
    cases hk : (d - UInt8.ofNat m == 1 && VALUE (B + UInt8.ofNat m) == 13) <;>
    simp only [cleanupRunResult, preCleanupPile, kingMove, hba, hk, Bool.false_eq_true,
      reduceIte, Vector.set_set, Vector.getElem_set_self] <;>
    first
      | rfl
      | (rw [Prod.mk.injEq]; exact ⟨rfl, rfl⟩)

/-- **Exact run of the freed loop**: some number `f` of `freedStep`s, guard true
    before each and false after, state untouched. -/
theorem freedLoop_run (g : Globals) (suit : UInt8) (hsuit : suit.toUInt32.toNat < 4)
    (hpiles : ∀ (i : Nat) (h : i < 64), (g.card2pile[i]'h).toNat < 10) :
    ∀ (n : Nat) (r : FreedAcc) (s : Globals × SolverPosType),
      r.snd.snd.toNat < n → r.snd.snd.toNat < 64 →
      (0 : UInt8) ≤ r.snd.fst.aces[suit.toUInt32.toNat]'hsuit →
      ∃ f : Nat,
        Loop.forIn Loop.mk r (freedBody g suit) s = .ok (freedIter f r) s ∧
        (∀ i, i < f → freedGuard g suit (freedIter i r)) ∧
        ¬ freedGuard g suit (freedIter f r) := by
  intro n
  induction n with
  | zero => intro r s h1 _ _; exact absurd h1 (Nat.not_lt_zero _)
  | succ n ih =>
    intro r s h1 h64 haces
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := r) (f := freedBody g suit)
    have hc64 : r.snd.snd.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact h64
    by_cases hg1 : r.snd.fst.aces[suit.toUInt32.toNat]'hsuit < r.snd.snd
    · have hp10 : (g.card2pile[r.snd.snd.toUInt32.toNat]'hc64).toUInt32.toNat < 10 := by
        rw [UInt8.toNat_toUInt32]; exact hpiles _ hc64
      by_cases hg2 : (g.card2depth[r.snd.snd.toUInt32.toNat]'hc64).toNat ≥
          (r.snd.fst.pileDepth[(g.card2pile[r.snd.snd.toUInt32.toNat]'hc64).toUInt32.toNat]'hp10
            ).toNat
      · -- guard true: one `freedStep`, then the IH characterizes the rest.
        have hposN : 0 < r.snd.snd.toNat := by
          have hb := UInt8.lt_iff_toNat_lt.mp hg1
          omega
        have h1le : (1 : UInt8) ≤ r.snd.snd := by
          rw [UInt8.le_iff_toNat_le]; show 1 ≤ r.snd.snd.toNat; omega
        have hsub : (r.snd.snd - 1).toNat = r.snd.snd.toNat - 1 :=
          UInt8.toNat_sub_of_le _ _ h1le
        obtain ⟨f, heq, hguards, hexit⟩ := ih (freedStep r) s
          (by show (r.snd.snd - 1).toNat < n; rw [hsub]; omega)
          (by show (r.snd.snd - 1).toNat < 64; rw [hsub]; omega) haces
        refine ⟨f + 1, ?_, ?_, hexit⟩
        · rw [hunf]
          simp only [freedBody, hg1, hg2, decide_true, bind, EStateM.bind, andM, toBool, pure,
            EStateM.pure, Vector.getE, getElem?_pos, hsuit, hc64, hp10, reduceIte]
          exact heq
        · intro i hi
          match i with
          | 0 => exact ⟨fun h4 => hg1, fun h64' h10' => hg2⟩
          | j + 1 => exact hguards j (by omega)
      · -- freed test false: zero iterations.
        refine ⟨0, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
          fun hg => hg2 (hg.2 hc64 hp10)⟩
        rw [hunf]
        simp only [freedBody, hg1, hg2, decide_true, decide_false, bind, EStateM.bind, andM,
          toBool, pure, EStateM.pure, Vector.getE, getElem?_pos, hsuit, hc64, hp10,
          Bool.false_eq_true, reduceIte, freedIter]
    · -- aces test false: zero iterations.
      refine ⟨0, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun hg => hg1 (hg.1 hsuit)⟩
      rw [hunf]
      simp only [freedBody, hg1, decide_false, bind, EStateM.bind, andM, toBool, pure,
        EStateM.pure, Vector.getE, getElem?_pos, hsuit, Bool.false_eq_true, reduceIte,
        freedIter]

/-- **Exact run of a non-empty `SolverCleanupPile`.**  There are iteration counts
    `m` (merge loop) and `f` (freed loop) such that both loops' guards held
    before every iteration and fail at exit, and the run returns exactly
    `cleanupRunResult … m f p` with `globals` untouched.  Preconditions supply
    the index bounds: `0 < depth ≤ 5`, the boundary card `B` (with `SUIT B < 4`
    and `B - 1 < 64` for the freed loop's reads), every `card2pile` entry a valid
    pile index, and a nonnegative foundation top for `SUIT B`. -/
theorem cleanupPile_nonempty_eq (pile : UInt32) (g : Globals) (p : SolverPosType)
    (B : UInt8) (ph : UInt32)
    (hpile : pile.toNat < 10)
    (hph : pileHashes[pile.toNat]'hpile = ph)
    (hd1 : 0 < (p.pileDepth[pile.toNat]'hpile).toNat)
    (hd5 : (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5)
    (hidx : ((p.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat < 5)
    (hB : (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile) - 1
      ).toUInt32.toNat]'hidx = B)
    (hs4 : (SUIT B).toUInt32.toNat < 4)
    (hprev64 : (B - 1).toNat < 64)
    (hpiles : ∀ (i : Nat) (h : i < 64), (g.card2pile[i]'h).toNat < 10)
    (haces0 : (0 : UInt8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4) :
    ∃ m f : Nat,
      (∀ i, i < m → mergeGuard g pile
        (mergeIter ph i ⟨B, p.pileDepth[pile.toNat]'hpile, 1, p⟩)) ∧
      ¬ mergeGuard g pile
        (mergeIter ph m ⟨B, p.pileDepth[pile.toNat]'hpile, 1, p⟩) ∧
      (∀ i, i < f → freedGuard g (SUIT B) (freedIter i
        ⟨1 + UInt8.ofNat m, { p with hash := p.hash - UInt32.ofNat m * ph }, B - 1⟩)) ∧
      ¬ freedGuard g (SUIT B) (freedIter f
        ⟨1 + UInt8.ofNat m, { p with hash := p.hash - UInt32.ofNat m * ph }, B - 1⟩) ∧
      EStateM.run (_root_.SolverCleanupPile pile) (g, p) =
        .ok (cleanupRunResult pile hpile B ph hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).1
          (g, (cleanupRunResult pile hpile B ph hs4
              (p.pileDepth[pile.toNat]'hpile) m f p).2) := by
  obtain ⟨m, hmeq, hmg, hmx⟩ := mergeLoop_run g pile ph hpile 6
    ⟨B, p.pileDepth[pile.toNat]'hpile, 1, p⟩ (g, p)
    (by show (p.pileDepth[pile.toNat]'hpile).toNat < 6; omega)
    (by show (p.pileDepth[pile.toNat]'hpile).toNat ≤ 5; omega)
  rw [mergeIter_eq] at hmeq
  obtain ⟨f, hfeq, hfg, hfx⟩ := freedLoop_run g (SUIT B) hs4 hpiles 64
    ⟨1 + UInt8.ofNat m, { p with hash := p.hash - UInt32.ofNat m * ph }, B - 1⟩ (g, p)
    (by show (B - 1).toNat < 64; exact hprev64)
    (by show (B - 1).toNat < 64; exact hprev64)
    (by show (0 : UInt8) ≤ p.aces[(SUIT B).toUInt32.toNat]'hs4; exact haces0)
  rw [freedIter_eq] at hfeq
  refine ⟨m, f, hmg, hmx, hfg, hfx, ?_⟩
  have hd0 : ((p.pileDepth[pile.toNat]'hpile) == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h' := congrArg UInt8.toNat h
    rw [show ((0 : UInt8).toNat = 0) from rfl] at h'
    omega
  rw [cleanupPile_eq_explicit]
  unfold cleanupPileExplicit
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.pure, pure, Vector.getE, Vector.setE, getElem?_pos, dif_pos,
    hpile, hidx, hd0, Bool.false_eq_true, reduceIte, hph, hB]
  rw [hmeq]
  simp only []
  rw [hfeq]
  simp only [cleanupRunResult, EStateM.pure, getElem?_pos, dif_pos, hs4]
  cases hba : (p.aces[(SUIT B).toUInt32.toNat]'hs4 == (B - 1 - UInt8.ofNat f)) <;>
    cases hk : ((p.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1
        && VALUE (B + UInt8.ofNat m) == 13) <;>
    simp only [Bool.false_eq_true, reduceIte] <;> rfl

/-!
### `SolverRemoveFlute` — exact reduction to `SolverCleanupPile`

`SolverRemoveFlute` has no loops of its own: it decrements the pile's depth,
subtracts the pile hash, and tail-calls `SolverCleanupPile`.  Its exact run is
therefore the cleanup run at the modified position, which composes with
`cleanupPile_empty_eq` / `cleanupPile_nonempty_eq`.
-/

/-- The entry-state modification `SolverRemoveFlute` performs before calling
    `SolverCleanupPile`: `pileDepth[pile] -= 1`, `hash -= pileHashes[pile]`. -/
def removeFlutePre (pile : UInt32) (hpile : pile.toNat < 10) (p : SolverPosType) :
    SolverPosType :=
  { p with
    pileDepth := p.pileDepth.set pile.toNat (p.pileDepth[pile.toNat]'hpile - 1) hpile,
    hash := p.hash - pileHashes[pile.toNat]'hpile }

/-- **Exact run of `SolverRemoveFlute`**: the cleanup run at the pre-modified
    position. -/
theorem removeFlute_eq (pile : UInt32) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10) :
    EStateM.run (_root_.SolverRemoveFlute pile) (g, p) =
    EStateM.run (_root_.SolverCleanupPile pile) (g, removeFlutePre pile hpile p) := by
  unfold SolverRemoveFlute removeFlutePre
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.set, Vector.getE, Vector.setE, getElem?_pos, dif_pos, hpile]
  rfl

/-!
### Explicit-loop twin of `SolverMoveAces`

Same technique as `cleanupPileExplicit`.  The foundation-walk loop is
*state-effectful* (the `cardDepth = 0` branch writes `aces`, calls
`SolverRemoveFlute`, and re-reads the state), so its exact-run characterization
will need an invariant-carrying loop rule rather than the state-pure
`mergeLoop_run` pattern — but the `rfl` twin already gives spec proofs the
syntactic `Loop.forIn`/`moveAcesBody` handle.
-/

/-- Accumulator of the `SolverMoveAces` foundation walk:
    `(card, forcedKings, found, game, globals)`. -/
abbrev MoveAcesAcc := MProd UInt8 (MProd UInt16 (MProd UInt8 (MProd SolverPosType Globals)))

/-- Body of the `SolverMoveAces` `while` loop. -/
def moveAcesBody (suitU32 : UInt32) :
    Unit → MoveAcesAcc → EStateM Error (Globals × SolverPosType) (ForInStep MoveAcesAcc) :=
  fun _ r => do
    let card := r.fst
    let forcedKings := r.snd.fst
    let found := r.snd.snd.fst
    let game := r.snd.snd.snd.fst
    let globals := r.snd.snd.snd.snd
    if VALUE card ≤ 13 then
      let pile ← globals.card2pile.getE card.toUInt32
      let cd1 ← globals.card2depth.getE card.toUInt32
      let cd2 ← game.pileDepth.getE pile.toUInt32
      let cardDepth : Int32 := cd1.toInt32 + 1 - cd2.toInt32
      if cardDepth > 0 then
        return .yield ⟨card + 1, forcedKings, found + 1, game, globals⟩
      else if cardDepth == 0 then
        let newAces ← game.aces.setE suitU32 card
        let game := { game with aces := newAces }
        set (⟨globals, game⟩ : Globals × SolverPosType)
        let fk ← SolverRemoveFlute pile.toUInt32
        let s ← get
        return .yield ⟨card + 1, forcedKings &&& fk, 0, s.snd, s.fst⟩
      else
        return .done ⟨card, forcedKings, found, game, globals⟩
    else
      return .done ⟨card, forcedKings, found, game, globals⟩

def moveAcesExplicit : EStateM Error (Globals × SolverPosType) UInt16 := do
  let forcedKings : UInt16 := 0xffff
  let ⟨globals, game⟩ ← get
  let suit := ctz game.busyAces
  let suitU32 := UInt32.ofNat suit
  let card : UInt8 := (← game.aces.getE suitU32) + 1
  let found : UInt8 := 0
  let r ← Loop.forIn Loop.mk ⟨card, forcedKings, found, game, globals⟩ (moveAcesBody suitU32)
  let ⟨card, forcedKings, found, game, globals⟩ := r
  let card := card - 1
  let game := { game with usedSpace := game.usedSpace - found }
  let newAces ← game.aces.setE suitU32 card
  let game := { game with aces := newAces }
  -- busyAces clear + final write, shared by both branches (the join point)
  let finish : SolverPosType → EStateM Error (Globals × SolverPosType) UInt16 :=
    fun game => do
      set (⟨globals,
        { game with busyAces := game.busyAces - (1 : UInt8) <<< UInt8.ofNat suit }⟩ :
        Globals × SolverPosType)
      pure forcedKings
  if VALUE card == 13 then
    let newKings ← game.kings.setE suitU32 card
    finish { game with kings := newKings }
  else
    finish game

/-- The explicit-loop twin is definitionally the real function. -/
theorem moveAces_eq_explicit : _root_.SolverMoveAces = moveAcesExplicit := rfl

/-!
### Explicit-loop twin of `SolverMove`

`SolverMove` = destination bookkeeping (three-way branch) + `SolverRemoveFlute`
+ the `while busyAces ≠ 0` drain.  `drainBody` (accumulator: bare `forcedKings`)
is shared with `SolverConvertFromPilesKings`'s final drain.
-/

/-- Body of the `while busyAces ≠ 0 do SolverMoveAces` drain loop. -/
def drainBody : Unit → UInt16 → EStateM Error (Globals × SolverPosType) (ForInStep UInt16) :=
  fun _ r => do
    let s ← get
    if s.snd.busyAces != 0 then
      let fk ← SolverMoveAces
      return .yield (r &&& fk)
    else
      return .done r

def moveExplicit (pile : UInt32) (toPile : UInt8) :
    EStateM Error (Globals × SolverPosType) UInt16 := do
  let ⟨globals, game⟩ ← get
  let fluteLen ← game.pileFlute.getE pile
  -- set + RemoveFlute + drain, shared by all branches (the outer join point)
  let finish : SolverPosType → EStateM Error (Globals × SolverPosType) UInt16 :=
    fun game => do
      set (⟨globals, game⟩ : Globals × SolverPosType)
      let forcedKings ← SolverRemoveFlute pile
      let r ← Loop.forIn Loop.mk forcedKings drainBody
      pure r
  if toPile < 10 then
    let old ← game.pileFlute.getE toPile.toUInt32
    let newFlute ← game.pileFlute.setE toPile.toUInt32 (old + fluteLen)
    finish { game with pileFlute := newFlute }
  else
    -- usedSpace bump, shared by the two sub-branches (the inner join point)
    let finish2 : SolverPosType → EStateM Error (Globals × SolverPosType) UInt16 :=
      fun game => finish { game with usedSpace := game.usedSpace + fluteLen }
    if toPile < 14 then
      let kingIdx := (toPile - 10).toUInt32
      let old ← game.kings.getE kingIdx
      let newKings ← game.kings.setE kingIdx (old - fluteLen)
      finish2 { game with kings := newKings }
    else
      finish2 game

/-- The explicit-loop twin is definitionally the real function. -/
theorem move_eq_explicit : _root_.SolverMove = moveExplicit := rfl
