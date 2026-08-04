import Seahaven.EStateMTail
import Seahaven.SolverInvariant

/-!
# `solverGetDestination`: explicit-loop twin and fuel model

`solverGetDestination` is the last loop-bearing solver function without a spec.

Its loop *used* to contain an early `return` (a king-frontier test) as well as a
`break`.  That test turned out to be dead — see "Where the walk stops" below —
and has been removed from both this model and `solver/solver.c`, so the loop is
now `break`-only and the twin below uses the simple accumulator.  The notes on
the early-`return` desugaring are kept because they are the general recipe, and
because the other direction was what made the dead code visible in the first
place.

## How `repeat` with `break` and `return` is translated

A `repeat` whose body only `break`s becomes `forIn Loop.mk acc body` with the
accumulator being just the tuple of mutable variables; `break` is
`ForInStep.done`, falling off the end is `ForInStep.yield`.

Adding an early `return` changes two things:

* the accumulator gains a leading `Option α` (α = the function's return type),
  giving `MProd (Option α) «mutables»`.  `return v` becomes
  `ForInStep.done ⟨some v, «mutables»⟩`; every other exit carries `none`;
* after the loop the function matches on that component —
  `match r.fst with | none => «code after the loop» | some a => pure a`.

Inside the body, an `if` *without* an `else` followed by more code becomes a
**join point**: `have jp := fun «mutables» (y : PUnit) => «continuation»`, and
the `if` reads
`if c then pure (.done ⟨some v, …⟩) else do let y ← pure PUnit.unit; jp «mutables» y`.

The practical consequences for writing a `rfl`-equal twin — all three were
needed to make `getDest_eq_explicit` go through:

1. destructure the accumulator with `have`, not `let`;
2. write the branch as an explicit `if … then … else …` with the continuation
   *inside* the `else`, rather than `if … then return …` followed by the
   continuation;
3. rebind updated mutables with `have` too.
-/

open Lean

/-- Accumulator of the `solverGetDestination` walk: `⟨card, posFromTop, toPile⟩`.

Now that the in-loop king test is gone (see below) the loop has no early
`return`, so the accumulator is just the mutables — no leading `Option`. -/
abbrev DestAcc := MProd CardType (MProd Int32 UInt8)

/-- Body of the `solverGetDestination` `repeat` loop. -/
def destBody (game : SolverPosType) (globals : Globals) :
    Unit → DestAcc → EStateM Error Globals (ForInStep DestAcc) :=
  fun _ r =>
    have card := r.fst
    have posFromTop := r.snd.fst
    have toPile := r.snd.snd
    do
      have card := card + 1
      let toPile ← globals.card2pile.getE card.toUInt32
      let pd ← game.pileDepth.getE toPile.toUInt32
      let cd ← globals.card2depth.getE card.toUInt32
      have posFromTop : Int32 := pd.toInt32 - cd.toUInt32.toInt32
      if posFromTop > 0 then pure (.done ⟨card, posFromTop, toPile⟩)
      else pure (.yield ⟨card, posFromTop, toPile⟩)

def getDestExplicit (game : SolverPosType) (pile : UInt32) : EStateM Error Globals UInt8 := do
  let globals ← get
  let depth ← game.pileDepth.getE pile
  let card ← (← globals.pos2card.getE pile).getE (depth.toInt32 - 1).toUInt32
  have suit : UInt8 := SUIT card
  let k ← game.kings.getE suit.toUInt32
  if (card == k) = true then pure (10 + suit)
  else do
    let r ← Loop.forIn Loop.mk (⟨card, 0, 0⟩ : DestAcc) (destBody game globals)
    pure (if (r.snd.fst == 1) = true then r.snd.snd else 14)

/-- The explicit-loop twin is definitionally the real function. -/
theorem getDest_eq_explicit : solverGetDestination = getDestExplicit := rfl

/-! ## Fuel model

The walk increments `card` every iteration and stops no later than
`kings[suit] ≤ CARD suit 13`, so `13 - VALUE card` iterations bound it. -/

/-- Run the loop for at most `fuel` iterations; `none` means fuel ran out. -/
def destFuel (game : SolverPosType) (globals : Globals) :
    Nat → DestAcc → EStateM Error Globals (Option DestAcc)
  | 0, _ => pure none
  | fuel + 1, acc => do
      match ← destBody game globals () acc with
      | .done a => pure (some a)
      | .yield a => destFuel game globals fuel a

/-- **Exact run.**  Whenever the fuel model finishes, the real loop agrees. -/
theorem destLoop_eq_of_fuel (game : SolverPosType) (globals : Globals) :
    ∀ (fuel : Nat) (acc res : DestAcc) (g g' : Globals),
      EStateM.run (destFuel game globals fuel acc) g = .ok (some res) g' →
      EStateM.run (Loop.forIn Loop.mk acc (destBody game globals)) g = .ok res g' := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc res g g' h
    simp [destFuel, EStateM.run, pure, EStateM.pure] at h
  | succ n ih =>
    intro acc res g g' h
    rw [Loop.forIn_eq_of_monadTail (m := EStateM Error Globals) (l := Loop.mk) (b := acc)
      (f := destBody game globals)]
    rw [destFuel] at h
    cases hb : destBody game globals () acc g with
    | error e s => simp [EStateM.run, bind, EStateM.bind, hb] at h
    | ok st gm =>
      cases st with
      | done a =>
        simp only [EStateM.run, bind, EStateM.bind, hb, pure, EStateM.pure,
          EStateM.Result.ok.injEq, Option.some.injEq] at h ⊢
        exact h
      | yield a =>
        simp only [EStateM.run, bind, EStateM.bind, hb] at h ⊢
        exact ih a res gm g' h

/-! ## Where the walk stops

`SuitClean.king_frontier` (`SolverInvariant.lean:180`) pins this down, and it
makes the in-loop king test **dead code** under `IsCanonicalPos`.  Its two
disjuncts:

* `aces[s] < kings[s] ∧ ¬ isFreeCard kings[s]` — the normal case.  The walk
  advances to `B+k` only after finding `B+k` *free*, so it can never arrive at
  `kings[s]`; it breaks there (or earlier) via `posFromTop > 0` instead.
* `kings[s] = aces[s] ∧ (VALUE aces[s] = 13 ∨ busyAces bit set)`.  In a canonical
  position `busyAces = 0`, so `VALUE aces[s] = 13`: the whole suit is on the
  foundation, hence every card of `s` is free (`foundation_cards_free`) — so no
  pile boundary has suit `s` (`boundary_not_free`), and the walk never starts.

So the in-loop `card == kings[suit]` test can only fire at `k = 0`, where it
duplicates the pre-loop test.  Every other exit is the `break`, at the first
un-freed card above the boundary, which by `king_frontier`'s second conjunct is
at or below `kings[suit]` — giving both the destination and the `13 - VALUE B`
fuel bound. -/

/-- `posFromTop` of a card, as the loop computes it (clamped to stay total). -/
def posFromTopOf (g : Globals) (game : SolverPosType) (c : UInt8) : Int :=
  (game.pileDepth.get ⟨(cardPile g c).toNat % 10, Nat.mod_lt _ (by omega)⟩).toInt
    - (cardDepth g c).toNat

/-! ## Bridging the loop's test to `isFreeCard` -/

theorem pileDepth_mod (game : SolverPosType) (a : Nat) (h : a < 10) {h' : a % 10 < 10} :
    game.pileDepth.get ⟨a % 10, h'⟩ = game.pileDepth.get ⟨a, h⟩ := by
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt h)

theorem isFreeCard_iff (g : Globals) (game : SolverPosType) (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10) :
    isFreeCard g game c ↔
      (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt.toNat ≤ (cardDepth g c).toNat := by
  show ((cardDepth g c).toNat ≥
      (if h : (cardPile g c).toNat < 10 then game.pileDepth.get ⟨(cardPile g c).toNat, h⟩
       else 0).toInt.toNat) ↔ _
  rw [dif_pos hp10]

/-- **The loop's `posFromTop > 0` test is exactly "not free".**  Needs pile
depths to be non-negative, which `SolverInvBase.pileDepth_nonneg` supplies. -/
theorem posFromTopOf_pos_iff (g : Globals) (game : SolverPosType) (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10)
    (hnn : (0 : Int) ≤ (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt) :
    0 < posFromTopOf g game c ↔ ¬ isFreeCard g game c := by
  rw [isFreeCard_iff g game c hp10]
  unfold posFromTopOf
  rw [pileDepth_mod game _ hp10]
  omega

/-! ### `Int32` conversion bridges

The loop computes `posFromTop` as `pileDepth.toInt32 - card2depth.toUInt32.toInt32`.
Relating that to `posFromTopOf`'s `Int` needs three no-wrap facts.  `Int32.toInt_sub`
only exists in the `bmod` form and `Int32.toInt_sub_of_le` needs `b ≤ a`, which
fails exactly when the card *is* free — so the general version is proved here. -/

theorem int8_toInt_lb (x : UInt8) : 0 ≤ x.toInt := UInt8.toInt_nonneg x

theorem int8_toInt_ub (x : UInt8) : x.toInt < 256 := by
  have h : x.toNat < 256 := x.toNat_lt_size
  simp only [UInt8.toInt]; omega

theorem uint8_toNat_lt (x : UInt8) : x.toNat < 256 := x.toNat_lt_size

theorem uint8_toInt32_toInt (c : UInt8) : (c.toUInt32.toInt32).toInt = (c.toNat : Int) := by
  have hc := uint8_toNat_lt c
  have hbmod : (c.toUInt32.toInt32).toInt = ((c.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
    show (c.toUInt32.toInt32).toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_bmod]; rfl
  rw [hbmod, UInt8.toNat_toUInt32]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- General `Int32` subtraction bridge: no `b ≤ a` needed, just no wraparound.
(`Int32.toInt_sub_of_le` needs `b ≤ a`, which fails exactly when the card *is*
free, and `Int32.toInt_sub` only exists in `bmod` form.) -/
theorem int32_toInt_sub (a b : Int32) (h1 : -2147483648 ≤ a.toInt - b.toInt)
    (h2 : a.toInt - b.toInt < 2147483648) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem int32_toUInt32_toNat (x : Int32) (h0 : 0 ≤ x.toInt) : x.toUInt32.toNat = x.toInt.toNat := by
  have hb : x.toInt = ((x.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
    show x.toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_bmod]; rfl
  have hlt : x.toUInt32.toNat < 2 ^ 32 := x.toUInt32.toNat_lt_size
  rw [hb] at h0 ⊢
  rw [Int.bmod] at h0 ⊢
  norm_num at h0 ⊢
  omega

/-- The boundary index the code computes, in `Nat` terms: for `1 ≤ depth ≤ 5`,
`(depth.toInt32 - 1).toUInt32.toNat = depth - 1`. -/
theorem depth_index (d : UInt8) (h1 : 0 < d.toInt.toNat) (h5 : d.toInt.toNat ≤ 5) :
    (d.toInt32 - 1).toUInt32.toNat = d.toInt.toNat - 1 := by
  have hlb := int8_toInt_lb d
  have hub := int8_toInt_ub d
  have hone : (1 : Int32).toInt = 1 := by decide
  have ha : (d.toInt32).toInt = d.toInt := UInt8.toInt_toInt32 d
  have hsub : (d.toInt32 - 1).toInt = d.toInt - 1 := by
    rw [int32_toInt_sub _ _ (by rw [ha, hone]; omega) (by rw [ha, hone]; omega), ha, hone]
  rw [int32_toUInt32_toNat _ (by rw [hsub]; omega), hsub]
  omega

/-- **The loop's `posFromTop`, as an `Int`.** -/
theorem pft_toInt (pd : UInt8) (cd : UInt8) :
    (pd.toInt32 - cd.toUInt32.toInt32).toInt = pd.toInt - (cd.toNat : Int) := by
  have hb : (cd.toUInt32.toInt32).toInt = (cd.toNat : Int) := uint8_toInt32_toInt cd
  have ha : (pd.toInt32).toInt = pd.toInt := UInt8.toInt_toInt32 pd
  have h1 := int8_toInt_lb pd
  have h2 := int8_toInt_ub pd
  have h3 := uint8_toNat_lt cd
  rw [int32_toInt_sub _ _ (by rw [ha, hb]; omega) (by rw [ha, hb]; omega), ha, hb]

/-- **The loop's sign test is exactly `¬ isFreeCard`,** stated on the `Int32`
value the code actually computes. -/
theorem loop_test_iff (g : Globals) (game : SolverPosType) (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10)
    (hnn : (0 : Int) ≤ (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt) :
    0 < (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt32
          - (cardDepth g c).toUInt32.toInt32
      ↔ ¬ isFreeCard g game c := by
  rw [Int32.lt_iff_toInt_lt, pft_toInt, isFreeCard_iff g game c hp10]
  simp only [Int32.toInt_zero]
  omega

/-! ### One step of the loop

With the conversion bridges above in place, this is pure unfolding: the three
`Vector.getE` reads are discharged from the index bounds. -/

/-- **Exact run of one loop iteration.** -/
theorem destBody_run (g : Globals) (game : SolverPosType) (acc : DestAcc) (c : UInt8)
    (hc : c = acc.fst + 1) (h64 : c.toNat < 64)
    (hp10 : (cardPile g c).toNat < 10) :
    destBody game g () acc g =
      .ok (let pft := (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt32
                        - (cardDepth g c).toUInt32.toInt32
           if pft > 0 then .done ⟨c, pft, cardPile g c⟩ else .yield ⟨c, pft, cardPile g c⟩) g := by
  subst hc
  have h64' : (acc.fst + 1).toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; exact h64
  have hpEq : g.card2pile[(acc.fst + 1).toUInt32.toNat]'h64' = cardPile g (acc.fst + 1) := by
    unfold cardPile; rw [dif_pos h64]; congr 1
  have hdEq : g.card2depth[(acc.fst + 1).toUInt32.toNat]'h64' = cardDepth g (acc.fst + 1) := by
    unfold cardDepth; rw [dif_pos h64]; congr 1
  have hp10' : (cardPile g (acc.fst + 1)).toUInt32.toNat < 10 := by
    rw [UInt8.toNat_toUInt32]; exact hp10
  simp only [destBody, bind, EStateM.bind, pure, EStateM.pure, Vector.getE,
    getElem?_pos, h64', hp10', hpEq, hdEq]
  simp only [UInt8.toNat_toUInt32]
  rw [show (game.pileDepth[(cardPile g (acc.fst + 1)).toNat]'hp10)
        = game.pileDepth.get ⟨(cardPile g (acc.fst + 1)).toNat, hp10⟩ from rfl]
  split_ifs <;> rfl

/-! ### The walk -/

theorem uint8_shift (B : UInt8) (j : Nat) : B + 1 + UInt8.ofNat j = B + UInt8.ofNat (j + 1) := by
  have h : UInt8.ofNat (j + 1) = UInt8.ofNat j + 1 := by simp [UInt8.ofNat_add]
  rw [h, UInt8.add_assoc, UInt8.add_comm 1 (UInt8.ofNat j)]

/-- The `Int32` `posFromTop` the loop computes for card `c` (index clamped, so total). -/
def pftVal (g : Globals) (game : SolverPosType) (c : UInt8) : Int32 :=
  (game.pileDepth.get ⟨(cardPile g c).toNat % 10, Nat.mod_lt _ (by omega)⟩).toInt32
    - (cardDepth g c).toUInt32.toInt32

theorem pftVal_eq (g : Globals) (game : SolverPosType) (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10) :
    pftVal g game c
      = (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt32
          - (cardDepth g c).toUInt32.toInt32 := by
  unfold pftVal; rw [pileDepth_mod game _ hp10]

theorem pftVal_pos_iff (g : Globals) (game : SolverPosType) (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10)
    (hnn : (0 : Int) ≤ (game.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt) :
    0 < pftVal g game c ↔ ¬ isFreeCard g game c := by
  rw [pftVal_eq g game c hp10]; exact loop_test_iff g game c hp10 hnn

theorem destBody_run' (g : Globals) (game : SolverPosType) (acc : DestAcc) (c : UInt8)
    (hc : c = acc.fst + 1) (h64 : c.toNat < 64) (hp10 : (cardPile g c).toNat < 10) :
    destBody game g () acc g =
      .ok (if pftVal g game c > 0 then .done ⟨c, pftVal g game c, cardPile g c⟩
           else .yield ⟨c, pftVal g game c, cardPile g c⟩) g := by
  rw [pftVal_eq g game c hp10]; exact destBody_run g game acc c hc h64 hp10

theorem cardPile_lt10 (g : Globals) (hwf : WellFormedLayout g) (c : UInt8) (h64 : c.toNat < 64) :
    (cardPile g c).toNat < 10 := by
  have := hwf.card2pile_lt c.toNat h64
  unfold cardPile; rw [dif_pos h64]; exact this

/-- **The walk.**  If `B+1 … B+m` are free and `B+(m+1)` is not, the loop stops
there and reports that card's pile data. -/
theorem destFuel_walk (g : Globals) (game : SolverPosType) (hwf : WellFormedLayout g)
    (hnn : ∀ i : Fin 10, (0:Int) ≤ (game.pileDepth.get i).toInt) :
    ∀ (m : Nat) (B : UInt8) (k : Nat) (pft0 : Int32) (tp0 : UInt8),
      m + 1 ≤ k →
      (∀ j, 1 ≤ j → j ≤ m + 1 → (B + UInt8.ofNat j).toNat < 64) →
      (∀ j, 1 ≤ j → j ≤ m → isFreeCard g game (B + UInt8.ofNat j)) →
      ¬ isFreeCard g game (B + UInt8.ofNat (m + 1)) →
      EStateM.run (destFuel game g k ⟨B, pft0, tp0⟩) g
        = .ok (some ⟨B + UInt8.ofNat (m + 1), pftVal g game (B + UInt8.ofNat (m + 1)),
                     cardPile g (B + UInt8.ofNat (m + 1))⟩) g := by
  intro m
  induction m with
  | zero =>
    intro B k pft0 tp0 hk hb _ hnf
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hc1 : B + UInt8.ofNat 1 = B + 1 := by norm_num
    have h1 : (B + 1).toNat < 64 := by rw [← hc1]; exact hb 1 (by omega) (by omega)
    rw [hc1] at hnf ⊢
    have hp10 := cardPile_lt10 g hwf (B + 1) h1
    have hpos : 0 < pftVal g game (B + 1) := (pftVal_pos_iff g game (B+1) hp10 (hnn _)).2 hnf
    rw [destFuel]
    simp only [EStateM.run, bind, EStateM.bind,
      destBody_run' g game ⟨B, pft0, tp0⟩ (B+1) rfl h1 hp10, if_pos hpos, pure, EStateM.pure]
  | succ m ih =>
    intro B k pft0 tp0 hk hb hfree hnf
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hc1 : B + UInt8.ofNat 1 = B + 1 := by norm_num
    have h1 : (B + 1).toNat < 64 := by rw [← hc1]; exact hb 1 (by omega) (by omega)
    have hp10 := cardPile_lt10 g hwf (B + 1) h1
    have hfree1 : isFreeCard g game (B + 1) := by
      have := hfree 1 (by omega) (by omega); rwa [hc1] at this
    have hnpos : ¬ (0 < pftVal g game (B + 1)) := fun h =>
      ((pftVal_pos_iff g game (B+1) hp10 (hnn _)).1 h) hfree1
    have hIH := ih (B + 1) k' (pftVal g game (B+1)) (cardPile g (B+1)) (by omega)
      (fun j hj1 hj2 => by rw [uint8_shift]; exact hb (j+1) (by omega) (by omega))
      (fun j hj1 hj2 => by rw [uint8_shift]; exact hfree (j+1) (by omega) (by omega))
      (by rw [uint8_shift]; exact hnf)
    rw [uint8_shift] at hIH
    rw [destFuel]
    simp only [EStateM.run, bind, EStateM.bind,
      destBody_run' g game ⟨B, pft0, tp0⟩ (B+1) rfl h1 hp10, if_neg hnpos]
    exact hIH

/-! ### Suit arithmetic along the walk, and where it stops -/

theorem uint8_shift' (B : UInt8) (j : Nat) : B + UInt8.ofNat j + 1 = B + UInt8.ofNat (j + 1) := by
  have h : UInt8.ofNat (j + 1) = UInt8.ofNat j + 1 := by simp [UInt8.ofNat_add]
  rw [h, UInt8.add_assoc]

theorem card_walk_suit_value (B : UInt8) :
    ∀ j : Nat, (VALUE B).toNat + j ≤ 13 →
      SUIT (B + UInt8.ofNat j) = SUIT B ∧
        (VALUE (B + UInt8.ofNat j)).toNat = (VALUE B).toNat + j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show (UInt8.ofNat 0 : UInt8) = 0 from rfl, UInt8.add_zero]
    exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro h
    obtain ⟨hs, hv⟩ := ih (by omega)
    have hlt15 : (VALUE (B + UInt8.ofNat j)).toNat < 15 := by omega
    refine ⟨?_, ?_⟩
    · rw [← uint8_shift' B j, SUIT_succ _ hlt15, hs]
    · rw [← uint8_shift' B j, VALUE_succ _ hlt15, hv]; omega

theorem card_walk_lt64 (B : UInt8) (hs : (SUIT B).toNat < 4) (j : Nat)
    (h : (VALUE B).toNat + j ≤ 13) : (B + UInt8.ofNat j).toNat < 64 := by
  obtain ⟨hsj, hvj⟩ := card_walk_suit_value B j h
  have h1 := SUIT_toNat (B + UInt8.ofNat j)
  have h2 := VALUE_toNat (B + UInt8.ofNat j)
  rw [hsj] at h1
  omega

/-- **The walk stops.**  Since `kings[s]` is un-freed and sits above `B` in the
suit, there is a least un-freed card strictly above `B`, at or below `kings[s]`. -/
theorem exists_stop (g : Globals) (game : SolverPosType) (s : Fin 4) (B : UInt8)
    (hK : ¬ isFreeCard g game (game.kings.get s))
    (hsK : SUIT (game.kings.get s) = s.val.toUInt8)
    (hsB : SUIT B = s.val.toUInt8)
    (hlt : (VALUE B).toNat < (VALUE (game.kings.get s)).toNat)
    (hKle : (VALUE (game.kings.get s)).toNat ≤ 13) :
    ∃ n : Nat, 1 ≤ n ∧
      (VALUE B).toNat + n ≤ (VALUE (game.kings.get s)).toNat ∧
      (∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j)) ∧
      ¬ isFreeCard g game (B + UInt8.ofNat n) := by
  classical
  set N := (VALUE (game.kings.get s)).toNat - (VALUE B).toNat with hN
  have hNpos : 1 ≤ N := by omega
  have hBN : B + UInt8.ofNat N = (game.kings.get s) := by
    obtain ⟨hsN, hvN⟩ := card_walk_suit_value B N (by omega)
    exact card_eq_of_suit_value _ _ (by rw [hsN, hsB, hsK]) (by rw [hvN]; omega)
  have hNnf : ¬ isFreeCard g game (B + UInt8.ofNat N) := by rw [hBN]; exact hK
  have hex : ∃ j, 1 ≤ j ∧ ¬ isFreeCard g game (B + UInt8.ofNat j) := ⟨N, hNpos, hNnf⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_, (Nat.find_spec hex).2⟩
  · have hle : Nat.find hex ≤ N := Nat.find_le ⟨hNpos, hNnf⟩
    omega
  · intro j hj1 hj2
    by_contra hc
    exact Nat.find_min hex hj2 ⟨hj1, hc⟩

/-- **The loop does the walk.**  Combines `destFuel_walk` with `destLoop_eq_of_fuel`. -/
theorem destLoop_result (g : Globals) (game : SolverPosType) (hwf : WellFormedLayout g)
    (hnn : ∀ i : Fin 10, (0:Int) ≤ (game.pileDepth.get i).toInt)
    (B : UInt8) (n : Nat) (hn1 : 1 ≤ n)
    (hbound : ∀ j, 1 ≤ j → j ≤ n → (B + UInt8.ofNat j).toNat < 64)
    (hfree : ∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j))
    (hnf : ¬ isFreeCard g game (B + UInt8.ofNat n)) :
    (Loop.forIn Loop.mk (⟨B, 0, 0⟩ : DestAcc) (destBody game g)) g
      = .ok ⟨B + UInt8.ofNat n, pftVal g game (B + UInt8.ofNat n),
             cardPile g (B + UInt8.ofNat n)⟩ g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine destLoop_eq_of_fuel game g (m + 1) ⟨B, 0, 0⟩ _ g g ?_
  exact destFuel_walk g game hwf hnn m B (m + 1) 0 0 (by omega) hbound
    (fun j h1 h2 => hfree j h1 (by omega)) hnf

/-! ### Evaluating the function -/

/-- **Unfolding `solverGetDestination`**, given the reads are in bounds and the
loop's result.  This is the step `simp` cannot do on its own: `Vector.getE`'s
`getElem?` only reduces once the index bounds are supplied, and the bounds have
to be stated in `getElem` (`a[i]'h`) form to match what the earlier reads leave
behind. -/
theorem getDest_apply (game : SolverPosType) (pile : UInt32) (g g' : Globals) (B : UInt8)
    (hp : pile.toNat < 10)
    (hidx : ((game.pileDepth[pile.toNat]'hp).toInt32 - 1).toUInt32.toNat < 5)
    (hcard : (g.pos2card[pile.toNat]'hp)[((game.pileDepth[pile.toNat]'hp).toInt32
               - 1).toUInt32.toNat]'hidx = B)
    (hs32 : (SUIT B).toUInt32.toNat < 4)
    (res : DestAcc)
    (hloop : (Loop.forIn Loop.mk (⟨B, 0, 0⟩ : DestAcc) (destBody game g)) g = .ok res g') :
    solverGetDestination game pile g =
      (if (B == game.kings[(SUIT B).toUInt32.toNat]'hs32) = true then
         .ok (10 + SUIT B) g
       else .ok (if (res.snd.fst == 1) = true then res.snd.snd else 14) g') := by
  rw [getDest_eq_explicit]
  simp only [getDestExplicit, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    Vector.getE, getElem?_pos, hp, hidx, hcard, hs32, apply_ite (fun f : EStateM Error Globals UInt8 => f g),
    pure, EStateM.pure, hloop]

/-- **`solverGetDestination`, fully evaluated.**  Given where the walk stops, the
function returns the king pile if the boundary is the king frontier, and
otherwise the stopping card's pile when it is exposed, `EXTRA` when it is
buried. -/
theorem getDest_result (game : SolverPosType) (pile : UInt32) (g : Globals) (B : UInt8)
    (hwf : WellFormedLayout g)
    (hnn : ∀ i : Fin 10, (0:Int) ≤ (game.pileDepth.get i).toInt)
    (hp : pile.toNat < 10)
    (hidx : ((game.pileDepth[pile.toNat]'hp).toInt32 - 1).toUInt32.toNat < 5)
    (hcard : (g.pos2card[pile.toNat]'hp)[((game.pileDepth[pile.toNat]'hp).toInt32
               - 1).toUInt32.toNat]'hidx = B)
    (hs32 : (SUIT B).toUInt32.toNat < 4)
    (n : Nat) (hn1 : 1 ≤ n)
    (hbound : ∀ j, 1 ≤ j → j ≤ n → (B + UInt8.ofNat j).toNat < 64)
    (hfree : ∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j))
    (hnf : ¬ isFreeCard g game (B + UInt8.ofNat n)) :
    solverGetDestination game pile g =
      (if (B == game.kings[(SUIT B).toUInt32.toNat]'hs32) = true then
         .ok (10 + SUIT B) g
       else .ok (if (pftVal g game (B + UInt8.ofNat n) == 1) = true
                 then cardPile g (B + UInt8.ofNat n) else 14) g) :=
  getDest_apply game pile g g B hp hidx hcard hs32 _
    (destLoop_result g game hwf hnn B n hn1 hbound hfree hnf)

/-- **The walk stops, from the invariant alone.**  The `kings[s] = aces[s]`
disjunct of `king_frontier` cannot fire: `busyAces = 0` in a canonical position
forces `VALUE aces[s] = 13`, which makes *every* card of the suit free —
including `B`, contradicting that `B` is a pile boundary. -/
theorem exists_stop_canonical (g : Globals) (game : SolverPosType)
    (hcan : IsCanonicalPos g game) (B : UInt8) (hreal : IsRealCard B)
    (hBnf : ¬ isFreeCard g game B)
    (hne : B ≠ (game.kings.get ⟨(SUIT B).toNat, hreal.1⟩)) :
    ∃ n : Nat, 1 ≤ n ∧ (VALUE B).toNat + n ≤ 13 ∧
      (∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j)) ∧
      ¬ isFreeCard g game (B + UInt8.ofNat n) := by
  have hbase := hcan.toSolverInvMerged.toSolverInvBase
  obtain ⟨hs4, hv1, hv13⟩ := id hreal
  set s : Fin 4 := ⟨(SUIT B).toNat, hreal.1⟩ with hs
  obtain ⟨_, haV, hkS, hkV, _⟩ := hbase.aces_kings_valid s
  obtain ⟨hfront, habove⟩ := hbase.king_frontier s
  have hsB : SUIT B = (s : Nat).toUInt8 := by rw [hs]; simp
  rcases hfront with ⟨_, hcase⟩ | ⟨_, hknf⟩
  · exfalso
    rcases hcase with h13 | hbusy
    · exact hBnf (hbase.foundation_cards_free s B hsB hv1 (by omega))
    · rw [hcan.busyAces_zero] at hbusy; simp at hbusy
  · have hBle : (VALUE B).toNat ≤ (VALUE (game.kings.get s)).toNat := by
      by_contra hgt
      exact hBnf (habove B hsB (by omega) hv13)
    have hBlt : (VALUE B).toNat < (VALUE (game.kings.get s)).toNat := by
      rcases lt_or_eq_of_le hBle with h | h
      · exact h
      · exact absurd (card_eq_of_suit_value _ _ (by rw [hsB, hkS]) h) hne
    obtain ⟨n, hn1, hnle, hfree, hnf⟩ := exists_stop g game s B hknf hkS hsB hBlt hkV
    exact ⟨n, hn1, by omega, hfree, hnf⟩

/-- Boundary card *is* the king frontier: the pre-loop test fires, and the loop
is never entered — so no `n` is needed. -/
theorem getDest_king (game : SolverPosType) (pile : UInt32) (g : Globals) (B : UInt8)
    (hp : pile.toNat < 10)
    (hidx : ((game.pileDepth[pile.toNat]'hp).toInt32 - 1).toUInt32.toNat < 5)
    (hcard : (g.pos2card[pile.toNat]'hp)[((game.pileDepth[pile.toNat]'hp).toInt32
               - 1).toUInt32.toNat]'hidx = B)
    (hs32 : (SUIT B).toUInt32.toNat < 4)
    (hkeq : (B == game.kings[(SUIT B).toUInt32.toNat]'hs32) = true) :
    solverGetDestination game pile g = .ok (10 + SUIT B) g := by
  rw [getDest_eq_explicit]
  simp only [getDestExplicit, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    Vector.getE, getElem?_pos, hp, hidx, hcard, hs32,
    apply_ite (fun f : EStateM Error Globals UInt8 => f g), pure, EStateM.pure, hkeq, if_true]

/-- Boundary card is *not* the king frontier: the loop runs and stops at `B + n`. -/
theorem getDest_walk (game : SolverPosType) (pile : UInt32) (g : Globals) (B : UInt8)
    (hwf : WellFormedLayout g)
    (hnn : ∀ i : Fin 10, (0:Int) ≤ (game.pileDepth.get i).toInt)
    (hp : pile.toNat < 10)
    (hidx : ((game.pileDepth[pile.toNat]'hp).toInt32 - 1).toUInt32.toNat < 5)
    (hcard : (g.pos2card[pile.toNat]'hp)[((game.pileDepth[pile.toNat]'hp).toInt32
               - 1).toUInt32.toNat]'hidx = B)
    (hs32 : (SUIT B).toUInt32.toNat < 4)
    (hkne : (B == game.kings[(SUIT B).toUInt32.toNat]'hs32) = false)
    (n : Nat) (hn1 : 1 ≤ n)
    (hbound : ∀ j, 1 ≤ j → j ≤ n → (B + UInt8.ofNat j).toNat < 64)
    (hfree : ∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j))
    (hnf : ¬ isFreeCard g game (B + UInt8.ofNat n)) :
    solverGetDestination game pile g
      = .ok (if (pftVal g game (B + UInt8.ofNat n) == 1) = true
             then cardPile g (B + UInt8.ofNat n) else 14) g := by
  rw [getDest_result game pile g B hwf hnn hp hidx hcard hs32 n hn1 hbound hfree hnf,
    if_neg (by rw [hkne]; simp)]

/-- **`solverGetDestination`, from the invariant alone.**  `B` is let-bound, the
depth bound and card validity come from `IsCanonicalPos`/`WellFormedLayout`, and
the stopping index is *derived*, not assumed. -/
theorem getDest_spec (g : Globals) (game : SolverPosType) (pile : UInt32)
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g game)
    (hp : pile.toNat < 10)
    (hd : 0 < (game.pileDepth.get ⟨pile.toNat, hp⟩).toInt.toNat) :
    let hb5 : (game.pileDepth.get ⟨pile.toNat, hp⟩).toInt.toNat - 1 < 5 := by
      have := hcan.toSolverInvMerged.toSolverInvBase.pileDepth_bound ⟨pile.toNat, hp⟩
      simp only [UInt8.toInt_eq] at *; omega
    let B := (g.pos2card.get ⟨pile.toNat, hp⟩).get
               ⟨(game.pileDepth.get ⟨pile.toNat, hp⟩).toInt.toNat - 1, hb5⟩
    (B = (game.kings.get ⟨(SUIT B).toNat,
            (hwf.pos2card_real ⟨pile.toNat, hp⟩ ⟨_, hb5⟩).1⟩) ∧
       solverGetDestination game pile g = .ok (10 + SUIT B) g)
    ∨ (∃ n : Nat, 1 ≤ n ∧ (VALUE B).toNat + n ≤ 13 ∧
        (∀ j, 1 ≤ j → j < n → isFreeCard g game (B + UInt8.ofNat j)) ∧
        ¬ isFreeCard g game (B + UInt8.ofNat n) ∧
        solverGetDestination game pile g
          = .ok (if (pftVal g game (B + UInt8.ofNat n) == 1) = true
                 then cardPile g (B + UInt8.ofNat n) else 14) g) := by
  intro hb5 B
  have hbase := hcan.toSolverInvMerged.toSolverInvBase
  have hreal : IsRealCard B := hwf.pos2card_real ⟨pile.toNat, hp⟩ ⟨_, hb5⟩
  have hs32 : (SUIT B).toUInt32.toNat < 4 := by rw [UInt8.toNat_toUInt32]; exact hreal.1
  have hnn : ∀ i : Fin 10, (0:Int) ≤ (game.pileDepth.get i).toInt := fun i => by
    have := hbase.pileDepth_nonneg i
    rw [UInt8.le_iff_toInt_le] at this; simpa using this
  have hdi := depth_index (game.pileDepth.get ⟨pile.toNat, hp⟩) hd
                (hbase.pileDepth_bound ⟨pile.toNat, hp⟩)
  have hidx : ((game.pileDepth[pile.toNat]'hp).toInt32 - 1).toUInt32.toNat < 5 := by
    show ((game.pileDepth.get ⟨pile.toNat, hp⟩).toInt32 - 1).toUInt32.toNat < 5
    rw [hdi]; exact hb5
  have hcard : (g.pos2card[pile.toNat]'hp)[((game.pileDepth[pile.toNat]'hp).toInt32
                 - 1).toUInt32.toNat]'hidx = B := by congr 1
  have hBnf : ¬ isFreeCard g game B := boundary_not_free hwf hbase ⟨pile.toNat, hp⟩ hd
  have hkidx : game.kings[(SUIT B).toUInt32.toNat]'hs32
             = game.kings.get ⟨(SUIT B).toNat, hreal.1⟩ := by congr 1
  by_cases hkeq : B = (game.kings.get ⟨(SUIT B).toNat, hreal.1⟩)
  · refine Or.inl ⟨hkeq, getDest_king game pile g B hp hidx hcard hs32 ?_⟩
    rw [hkidx]; exact beq_iff_eq.mpr hkeq
  · obtain ⟨n, hn1, hnle, hfree, hnf⟩ := exists_stop_canonical g game hcan B hreal hBnf hkeq
    refine Or.inr ⟨n, hn1, hnle, hfree, hnf,
      getDest_walk game pile g B hwf hnn hp hidx hcard hs32 ?_ n hn1
        (fun j hj1 hj2 => card_walk_lt64 B hreal.1 j (by omega)) hfree hnf⟩
    rw [hkidx]
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact hkeq
