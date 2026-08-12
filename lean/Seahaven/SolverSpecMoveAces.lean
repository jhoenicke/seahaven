import Seahaven.SolverSpecCleanupPile
import Seahaven.SolverSpecRemoveFlute

/-!
# Spec for `moveAcesLoop` / `SolverMoveAces`

Bit-twiddling helpers (`ctz`, low-nibble facts) feeding `MoveAcesInv`, the
per-iteration invariant for the ace-advancing loop, culminating in the exact
symbolic run `moveAcesLoop_run` and the top-level `moveAces_merged` theorem
(the `SolverMoveAces` step preserves/advances `SolverInvMerged`).
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

-- ---------------------------------------------------------------------------
-- `SolverMoveAces` — the foundation-walk loop invariant and its machinery
-- ---------------------------------------------------------------------------

/-! ### `ctz`, specified

`ctz` is a `termination_by` recursion, so the kernel cannot evaluate it and a
`decide` over the 256 `UInt8` values is not available — which is why these facts
used to be `native_decide`d.  Three inductions on a bound `k` for the argument
replace that: the counter factors out of `ctz.go`, a nonzero value below `2 ^ k`
has its lowest set bit below `k`, and that bit really is set. -/

/-- `ctz.go` counts up from its first argument, so the start value factors out. -/
private theorem ctz_go_shift : ∀ k v n : Nat, v ≠ 0 → v < 2 ^ k →
    ctz.go n v = n + ctz.go 0 v := by
  intro k
  induction k with
  | zero => intro v n hv hlt; simp at hlt; omega
  | succ k ih =>
    intro v n hv hlt
    rw [ctz.go.eq_def n v, ctz.go.eq_def 0 v]
    by_cases h1 : v % 2 == 1
    · simp [h1]
    · have hmod : v % 2 = 0 := by simp at h1; omega
      have hv2 : v / 2 ≠ 0 := by omega
      have hlt2 : v / 2 < 2 ^ k := by rw [Nat.pow_succ] at hlt; omega
      have hvne0 : (v == 0) = false := by simp; omega
      simp only [h1, Bool.false_eq_true, if_false, hvne0, Nat.zero_add]
      rw [ih (v / 2) (n + 1) hv2 hlt2, ih (v / 2) 1 hv2 hlt2]
      omega

/-- A nonzero value below `2 ^ k` has its lowest set bit below `k`. -/
private theorem ctz_go_lt : ∀ k v : Nat, v ≠ 0 → v < 2 ^ k → ctz.go 0 v < k := by
  intro k
  induction k with
  | zero => intro v hv hlt; simp at hlt; omega
  | succ k ih =>
    intro v hv hlt
    rw [ctz.go.eq_def 0 v]
    by_cases h1 : v % 2 == 1
    · simp [h1]
    · have hmod : v % 2 = 0 := by simp at h1; omega
      have hv2 : v / 2 ≠ 0 := by omega
      have hlt2 : v / 2 < 2 ^ k := by rw [Nat.pow_succ] at hlt; omega
      have hvne0 : (v == 0) = false := by simp; omega
      simp only [h1, Bool.false_eq_true, if_false, hvne0, Nat.zero_add]
      have := ih (v / 2) hv2 hlt2
      rw [ctz_go_shift (k + 1) (v / 2) 1 hv2 (by rw [Nat.pow_succ]; omega)]
      omega

/-- And that bit really is set. -/
private theorem ctz_go_testBit : ∀ k v : Nat, v ≠ 0 → v < 2 ^ k →
    v.testBit (ctz.go 0 v) = true := by
  intro k
  induction k with
  | zero => intro v hv hlt; simp at hlt; omega
  | succ k ih =>
    intro v hv hlt
    rw [ctz.go.eq_def 0 v]
    by_cases h1 : v % 2 == 1
    · simp only [h1, if_true, Nat.testBit_zero, decide_eq_true_eq]
      simpa using h1
    · have hmod : v % 2 = 0 := by simp at h1; omega
      have hv2 : v / 2 ≠ 0 := by omega
      have hlt2 : v / 2 < 2 ^ k := by rw [Nat.pow_succ] at hlt; omega
      have hvne0 : (v == 0) = false := by simp; omega
      simp only [h1, Bool.false_eq_true, if_false, hvne0, Nat.zero_add]
      rw [ctz_go_shift (k + 1) (v / 2) 1 hv2 (by rw [Nat.pow_succ]; omega),
        Nat.add_comm 1 (ctz.go 0 (v / 2)), Nat.testBit_succ]
      exact ih (v / 2) hv2 hlt2

private theorem toNat_ne_zero {x : UInt8} (hx : x ≠ 0) : x.toNat ≠ 0 :=
  fun h => hx (UInt8.toNat_inj.mp (show x.toNat = (0 : UInt8).toNat from h))

/-- `ctz x < k` for a nonzero `x` bounded by `2 ^ k`. -/
theorem ctz_lt_of_lt_two_pow {x : UInt8} {k : Nat} (hne : x ≠ 0) (hlt : x.toNat < 2 ^ k) :
    ctz x < k := ctz_go_lt k x.toNat (toNat_ne_zero hne) hlt

/-- **The shape the callers want.**  `busyAces` is a nonzero *4-bit* mask
    (`SolverInvBase.busyAces_lt16`, plus "some bit is set"), so its lowest set bit
    is a suit index.  Stated on `x < 16` and `x ≠ 0` directly: those are the two
    facts every caller has, and the low-nibble mask they used to route through
    (`_ &&& 0x0F ≠ 0`) was pure detour. -/
theorem ctz_lt_four {x : UInt8} (hlt16 : x < 16) (hne : x ≠ 0) : ctz x < 4 := by
  refine ctz_lt_of_lt_two_pow hne ?_
  rw [UInt8.lt_iff_toNat_lt, show (16 : UInt8).toNat = 16 from by decide] at hlt16
  omega

private theorem nat_and_two_pow_ne_zero {n k : Nat} (h : n.testBit k = true) :
    n &&& 2 ^ k ≠ 0 := by
  intro hzero
  have hb := congrArg (fun m => Nat.testBit m k) hzero
  simp only [Nat.testBit_and, h, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at hb
  exact Bool.noConfusion hb

/-- `x`'s own `ctz`-th bit is set in `x`, whenever `x ≠ 0`. -/
theorem ctz_bit_self (x : UInt8) (hx : x ≠ 0) :
    x &&& ((1 : UInt8) <<< UInt8.ofNat (ctz x)) ≠ 0 := by
  have h256 : x.toNat < 256 := x.toNat_lt
  have h8 : ctz x < 8 := ctz_lt_of_lt_two_pow hx (by omega)
  have hbit : x.toNat.testBit (ctz x) = true :=
    ctz_go_testBit 8 x.toNat (toNat_ne_zero hx) (by omega)
  -- the mask is exactly `2 ^ ctz x`: neither `%` of `UInt8.toNat_shiftLeft` fires
  have hmask : ((1 : UInt8) <<< UInt8.ofNat (ctz x)).toNat = 2 ^ ctz x := by
    have hpow : (2 : Nat) ^ ctz x < 2 ^ 8 := Nat.pow_lt_pow_right (by omega) h8
    rw [UInt8.toNat_shiftLeft, show ((1 : UInt8).toNat = 1) from rfl, UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (show ctz x < 2 ^ 8 by omega), Nat.mod_eq_of_lt h8,
      Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hpow]
  intro hzero
  refine nat_and_two_pow_ne_zero hbit ?_
  rw [← hmask, ← UInt8.toNat_and, hzero]
  rfl

/-- **Loop invariant for `SolverMoveAces`'s foundation walk**, carried through
    every iteration of `moveAcesBody suitU32` on the accumulator
    `(card, forcedKings, found, game)` for the fixed suit `suit`:

    * `SolverInvMerged` holds *literally* for `game` (no ghost/adjustment);
    * `card` sits exactly `found` past `A + 1`, where `A := game.aces.get suit`
      is the *current* foundation top for `suit` (an `Int`-valued equation,
      to avoid `UInt8`/`UInt8` wraparound bookkeeping at every step);
    * every card strictly between `A` and `card` (the `found`-many already
      walked, already-free candidates) is free;
    * `suit`'s `busyAces` bit stays set throughout (nothing clears it until
      the walk returns, see `moveAcesExplicit`'s `finish`). -/
def MoveAcesInv (g : Globals) (suit : Fin 4) (card : UInt8) (found : UInt8)
    (game : SolverPosType) : Prop :=
  SolverInvMerged g game ∧
  found.toInt ≤ 13 ∧
  SUIT card = suit.val.toUInt8 ∧
  1 ≤ (VALUE card).toNat ∧ (VALUE card).toNat ≤ 14 ∧
  (card.toNat : Int) = (game.aces.get suit).toNat + 1 + found.toInt ∧
  (∀ l : Nat, 1 ≤ l → (l : Int) ≤ found.toInt →
    isFreeCard g game ((game.aces.get suit) + UInt8.ofNat l)) ∧
  game.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0

/-- **Key arithmetic fact for the walk invariant.**  Any card `X` of the same
    suit as the walk, not equal to the current position `card`, and not free,
    must sit strictly ABOVE `card` in value: it can't be at or below the
    foundation top `A` (`foundation_cards_free` would make it free), and it
    can't be one of the `found`-many already-walked candidates either (the
    invariant's own freeness fact would make it free). -/
theorem moveAces_lt_of_not_free (g : Globals) (suit : Fin 4) (card : UInt8)
    (found : UInt8) (game : SolverPosType) (hinv : MoveAcesInv g suit card found game)
    (X : UInt8) (hSuitX : SUIT X = suit.val.toUInt8) (hXreal : 1 ≤ (VALUE X).toNat)
    (hXnotfree : ¬ isFreeCard g game X) (hXne : X ≠ card) :
    card.toNat < X.toNat := by
  obtain ⟨hmerged, _hfound13, hsuitcard, _hval1, _hval14, hcardeq, hfoundfree, _hbit⟩ :=
    hinv
  set A := (game.aces.get suit) with hAdef
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

theorem finVal_toUInt8_toNat (s : Fin 4) : (s.val.toUInt8).toNat = s.val := by
  have h : (s.val.toUInt8).toNat = s.val % 2 ^ 8 := UInt8.toNat_ofNat'
  have := s.isLt
  omega

/-- If a single suit-bit is set in `busyAces` (`x &&& (1 <<< s) ≠ 0`), that bit's
    own value is `≤ x` — needed to show `busyAces - (1 <<< s)` doesn't wrap
    (subtracting a bit that's actually set never borrows).  Finite check over
    `Fin 16 × Fin 4` (64 cases) — plain `decide`, since no `ctz` is involved and
    the kernel evaluates `UInt8` bit operations fine. -/
private theorem uint8_bit_le_of_and_ne_zero {x : UInt8} (hx : x.toNat < 16) (s : Fin 4)
    (h : x &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0) :
    ((1 : UInt8) <<< s.val.toUInt8) ≤ x := by
  have hall : ∀ n : Fin 16, ∀ t : Fin 4,
      n.val.toUInt8 &&& ((1 : UInt8) <<< t.val.toUInt8) ≠ 0 →
      ((1 : UInt8) <<< t.val.toUInt8) ≤ n.val.toUInt8 := by decide
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
    decide
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
    (j : Fin 10) (hdj : (p.pileDepth.get j).toNat > 0)
    (C : UInt8) (hCnotfree : ¬ isFreeCard g p C)
    (hClt : C.toNat < ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hbase.pileDepth_bound j; omega⟩ : UInt8).toNat) :
    C.toNat + (p.pileFlute.get j).toNat ≤
      ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
        by have := hbase.pileDepth_bound j; omega⟩ : UInt8).toNat := by
  set Bj := (g.pos2card.get j).get (⟨(p.pileDepth.get j).toNat - 1,
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
  have hkey : C.toNat < (Bj - UInt8.ofNat off).toNat :=
    flute_stays_above hwf hbase j hdj C hCnotfree hClt (UInt8.ofNat off) hoffLt
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
    (p.aces.get t).toNat < X.toNat := by
  by_contra hle
  push Not at hle
  apply hXnf
  apply h.foundation_cards_free t X hSX hVX
  have hSA : SUIT (p.aces.get t) = t.val.toUInt8 := (h.aces_kings_valid t).1
  have hblockEq : (SUIT X).toNat = (SUIT (p.aces.get t)).toNat := by rw [hSX, hSA]
  have hsx := SUIT_toNat X; have hvx := VALUE_toNat X
  have hsa := SUIT_toNat (p.aces.get t); have hva := VALUE_toNat (p.aces.get t)
  omega

/-- **The only step of the walk that changes the position**, packaged so that a
    predicate carried through `moveAcesLoop_run` (the drain's `Simulates`, say)
    only has to survive *this* one step.

    At a sync point (`cardDepth = 0`) `card` is exactly `pile`'s current boundary;
    the solver writes `aces[suit] := card` (giving `gameA`) and calls
    `SolverRemoveFlute pile`, which runs `SolverCleanupPile` from `q`, the
    composed `fluteNorm ∘ removeFlutePre` point.  Everything the loop proof
    establishes about that step on the way is handed over: the walk invariant,
    the boundary identification, the pile's flute (`= found + 1`, the walked run
    plus the boundary), `q`'s fields, `CleanupReady` at `q`, and the run itself.
    The counting steps need no clause — they leave the position untouched. -/
def MoveAcesSyncStep (g : Globals) (suit : Fin 4) (P : UInt16 → SolverPosType → Prop) : Prop :=
  ∀ (card found : UInt8) (forcedKings fk : UInt16) (game gameA q p' : SolverPosType)
    (pile : UInt32) (hpile : pile.toNat < 10),
    MoveAcesInv g suit card found game →
    0 < (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat →
    (∀ hidx : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5,
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get
        ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx⟩ = card) →
    (game.pileFlute.get ⟨pile.toNat, hpile⟩).toNat = found.toNat + 1 →
    q = fluteNorm pile hpile (removeFlutePre pile hpile gameA) →
    (q.pileDepth.get ⟨pile.toNat, hpile⟩) = (game.pileDepth.get ⟨pile.toNat, hpile⟩) - 1 →
    (∀ i : Fin 10, i.val ≠ pile.toNat → q.pileDepth.get i = game.pileDepth.get i) →
    (q.pileFlute.get ⟨pile.toNat, hpile⟩) = 1 →
    (∀ i : Fin 10, i.val ≠ pile.toNat → q.pileFlute.get i = game.pileFlute.get i) →
    q.kings = game.kings →
    q.aces.get suit = card →
    (∀ t : Fin 4, t ≠ suit → q.aces.get t = game.aces.get t) →
    CleanupReady g q pile →
    _root_.SolverRemoveFlute pile (g, gameA) = .ok fk (g, p') →
    P forcedKings game → P (forcedKings &&& fk) p'

set_option maxHeartbeats 4000000 in
/-- **Exact run of the `SolverMoveAces` foundation walk, with its invariant.**
    By induction on a `Nat` bounding `14 - VALUE(card)` (which strictly
    decreases on every continuing iteration, since `card` only ever
    increments and the loop stops once `VALUE card > 13`).

    The `cardDepth > 0` ("already free, skip") case is a pure accumulator
    step (`card += 1, found += 1`, `game` untouched) — the *easy* half of this
    proof.  The `cardDepth == 0` case (`card` is exactly its pile's current
    boundary) is the genuinely novel half. -/
theorem moveAcesLoop_run (g : Globals) (hwf : WellFormedLayout g) (suit : Fin 4)
    (suitU32 : UInt32) (hsuitU32 : suitU32.toNat = suit.val)
    (P : UInt16 → SolverPosType → Prop) (hsync : MoveAcesSyncStep g suit P) :
    ∀ (n : Nat) (card : UInt8) (forcedKings : UInt16) (found : UInt8) (game : SolverPosType),
      14 - (VALUE card).toNat < n →
      MoveAcesInv g suit card found game →
      P forcedKings game →
      ∃ (card' : UInt8) (forcedKings' : UInt16) (found' : UInt8) (game' : SolverPosType),
        Loop.forIn Loop.mk
            (⟨card, forcedKings, found, game, g⟩ : MoveAcesAcc) (moveAcesBody suitU32)
            (g, game) =
          .ok (⟨card', forcedKings', found', game', g⟩ : MoveAcesAcc) (g, game') ∧
        MoveAcesInv g suit card' found' game' ∧
        ((VALUE card').toNat = 14 ∨
          (¬ isFreeCard g game' card' ∧
            ∃ hp64 : (cardPile g card').toNat < 10,
              (cardDepth g card').toNat + 1 <
                (game'.pileDepth[(cardPile g card').toNat]'hp64).toNat)) ∧
        (∀ t : Fin 4, t ≠ suit → game'.aces.get t = game.aces.get t) ∧
        ((card' = card ∧ forcedKings' = forcedKings ∧ found' = found ∧ game' = game) ∨
          card.toNat < card'.toNat) ∧
        P forcedKings' game' := by
  intro n
  induction n with
  | zero => intro card _ _ _ hmeas _ _; omega
  | succ n ih =>
    intro card forcedKings found game hmeas hinv hP
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := (⟨card, forcedKings, found, game, g⟩ : MoveAcesAcc))
      (f := moveAcesBody suitU32)
    obtain ⟨hmerged, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
    -- `found` is a `uint8_t`, so its `Int` view is nonnegative (needed by the
    -- wrap-freedom arithmetic below; `omega` treats `UInt8.toInt` as an atom).
    have hf0 : (0 : Int) ≤ found.toInt := UInt8.toInt_nonneg found
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
      simp only [moveAcesBody, hgProp, bind, EStateM.bind, pure,
        EStateM.pure, Vector.getE, getElem?_pos, hc64, hp10, reduceIte, ← hpiledef, ← hcd1def,
        ← hcd2def]
      -- Bridge the `Int32` sign test on `cd1.toUInt32.toInt32 + 1 - cd2.toInt32`
      -- down to a plain `Int` equation relating `cd1`/`cd2`, wrap-free (both
      -- are tiny: `cd1 ≤ 5`, `0 ≤ cd2 ≤ 5`).
      have hcd1le5 : cd1.toNat ≤ 5 := by rw [hcd1EqCD]; exact hwf.depth_le card hcardReal
      have hcd2le5 : cd2.toInt ≤ 5 := by
        have hb := hmerged.pileDepth_bound ⟨(cardPile g card).toNat, hp64⟩
        have hshow : game.pileDepth[(cardPile g card).toNat]'hp64 =
            game.pileDepth.get ⟨(cardPile g card).toNat, hp64⟩ := by congr 1
        rw [hcd2EqPD, hshow]
        have hcast : (game.pileDepth.get ⟨(cardPile g card).toNat, hp64⟩).toInt =
            ((game.pileDepth.get ⟨(cardPile g card).toNat, hp64⟩).toNat : Int) := rfl
        omega
      have hcd2nonneg : (0 : Int) ≤ cd2.toInt := UInt8.toInt_nonneg cd2
      have hcd1small : (cd1.toUInt32.toInt32).toInt = (cd1.toNat : Int) := by
        have hbmod : (cd1.toUInt32.toInt32).toInt = ((cd1.toUInt32.toNat : Int)).bmod (2 ^ 32) := by
          show (cd1.toUInt32.toInt32).toBitVec.toInt = _
          rw [BitVec.toInt_eq_toNat_bmod]; rfl
        rw [hbmod, UInt8.toNat_toUInt32]
        exact Int.bmod_eq_of_le (by omega) (by omega)
      have hcd2Int32 : (cd2.toInt32).toInt = cd2.toInt := UInt8.toInt_toInt32 cd2
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
          have hcast : cd2.toInt = (cd2.toNat : Int) := rfl
          omega
        simp only [hcdpos, reduceIte, EStateM.pure]
        have hfound1 : (found + 1).toInt = found.toInt + 1 := by
          rw [UInt8.toInt_add, UInt8.toInt_one]
          omega
        have hnewcardeq : ((card + 1).toNat : Int) =
            ((game.aces.get suit).toNat : Int) + 1 + (found + 1).toInt := by
          have hci : ((card.toNat : Int)) = (game.aces.get suit).toNat + 1 + found.toInt :=
            hcardeq
          rw [hcard1nat, hfound1]
          push_cast
          omega
        have hfound1le13 : (found + 1).toInt ≤ 13 := by
          have hsx1 := SUIT_toNat (card + 1); have hvx1 := VALUE_toNat (card + 1)
          have hSuitA : SUIT (game.aces.get suit) = suit.val.toUInt8 :=
            (hmerged.aces_kings_valid suit).1
          have hsa := SUIT_toNat (game.aces.get suit)
          have hva := VALUE_toNat (game.aces.get suit)
          have hblockEq : (SUIT (card + 1)).toNat = (SUIT (game.aces.get suit)).toNat := by
            rw [hsuitcard1, hSuitA]
          have hnc : ((card + 1).toNat : Int) =
              ((game.aces.get suit).toNat : Int) + 1 + (found + 1).toInt := hnewcardeq
          omega
        have hnewfoundfree : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ (found + 1).toInt →
            isFreeCard g game ((game.aces.get suit) + UInt8.ofNat l) := by
          intro l hl1 hlle
          by_cases hlold : (l : Int) ≤ found.toInt
          · exact hfoundfree l hl1 hlold
          · have hleq : (l : Int) = found.toInt + 1 := by omega
            have hAl256 : (game.aces.get suit).toNat + l < 256 := by
              have := card.toNat_lt; omega
            have hcardEqA : card = (game.aces.get suit) + UInt8.ofNat l :=
              uint8_eq_add_ofNat_of_toNat_eq hAl256 (by
                have hci : (card.toNat : Int) =
                    (game.aces.get suit).toNat + 1 + found.toInt := hcardeq
                omega)
            rw [← hcardEqA]
            exact hcardFree
        have hnewinv : MoveAcesInv g suit (card + 1) (found + 1) game :=
          ⟨hmerged, hfound1le13, hsuitcard1, hval1_1, hval14_1, hnewcardeq,
            hnewfoundfree, hbit⟩
        have hnewmeas : 14 - (VALUE (card + 1)).toNat < n := by
          have := VALUE_succ card hcardVal15; omega
        obtain ⟨card', fk', found', game', heq, hinv', hexit', hframe', hdich', hP'⟩ :=
          ih (card + 1) forcedKings (found + 1) game hnewmeas hnewinv hP
        have hdich : card.toNat < card'.toNat := by
          rcases hdich' with ⟨hce, _, _, _⟩ | hgt
          · have h2 := congrArg UInt8.toNat hce
            omega
          · omega
        exact ⟨card', fk', found', game', heq, hinv', hexit', hframe', Or.inr hdich, hP'⟩
      · -- NOT `> 0`: either `card` is exactly its pile's boundary (`== 0`, the
        -- genuinely novel case, below) or genuinely buried (`< 0`, `.done`,
        -- unchanged accumulator).
        by_cases hcd0 : (cd1.toUInt32.toInt32 + 1 - cd2.toInt32 == 0) = true
        · -- THE KEY STEP (design's "why `SolverInvMerged` needs no ghost").
          -- `card` is exactly `pile`'s current boundary.  Writing
          -- `aces[suit] := card` then calling `SolverRemoveFlute pile`
          -- restores `MoveAcesInv` at `(card + 1, 0, gameF)` for the
          -- resulting `gameF`, via:
          --  1. `hmerged.pileMerged pile` gives `flute_maximal` at this
          --     boundary; `PileBase.flute_not_aces` gives
          --     `A.toNat + pileFlute[pile].toNat ≤ card.toNat`, i.e.
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
          have hpdEqNat : (game.pileDepth.get pileFin).toNat = cd1.toNat + 1 := by
            rw [hpdEq]
            have hcast : cd2.toInt = (cd2.toNat : Int) := rfl
            omega
          have hcd1lt5 : cd1.toNat < 5 := by omega
          have hcd1lt5CD : (cardDepth g card).toNat < 5 := by rw [← hcd1EqCD]; exact hcd1lt5
          have hdepthPos : 0 < (game.pileDepth.get pileFin).toNat := by omega
          have hpm := hmerged.pileMerged pileFin
          have hpb := hmerged.pileBase pileFin
          -- `card` is exactly `pileFin`'s current boundary: the `pileDepth-1`
          -- index matches `cardDepth g card` (`= cd1`) exactly.
          have hidxeq : (game.pileDepth.get pileFin).toNat - 1 = cd1.toNat := by omega
          have hcd1EqCDnat : cd1.toNat = (cardDepth g card).toNat := congrArg UInt8.toNat hcd1EqCD
          have hboundaryEq : (g.pos2card.get pileFin).get
              ⟨(game.pileDepth.get pileFin).toNat - 1, by omega⟩ = card := by
            have hr := hwf.round_trip card hcardReal hcd1lt5CD
            have hfineq : (⟨(game.pileDepth.get pileFin).toNat - 1, by omega⟩ : Fin 5) =
                ⟨(cardDepth g card).toNat, hcd1lt5CD⟩ := by
              apply Fin.ext
              show (game.pileDepth.get pileFin).toNat - 1 = (cardDepth g card).toNat
              omega
            rw [hfineq]
            exact hr
          rcases hpm.flute_maximal with hd0 | hbig
          · exact absurd hd0 (by
              intro hz
              rw [hz] at hpdEqNat
              have : ((0 : UInt8).toNat) = 0 := rfl
              omega)
          · rw [hboundaryEq] at hbig
            set pileFlute := game.pileFlute.get pileFin with hpileFlutedef
            set prevCard := card - pileFlute with hprevCarddef
            have hfluteposUInt : 1 ≤ pileFlute.toNat := hpb.flute_pos
            have hSuitCard : SUIT card = suit.val.toUInt8 := hsuitcard
            -- `prevCard = A` exactly (`A := (game.aces.get suit)`).
            set Araw := game.aces.get suit with hArawdef
            set A := Araw with hAdef
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
                have hh := congrArg (fun x : UInt8 => x) heq
                exact hh.symm
              · -- Rule out `prevCard ≠ A`: `flute_not_aces` gives
                -- `A.toNat + pileFlute.toNat ≤ card.toNat`, i.e.
                -- `prevCard.toNat ≥ A.toNat`; if strictly `>`, `prevCard` is
                -- one of the `found`-many already-free candidates (by
                -- `card`'s own invariant fact), contradicting `hnf`.
                have hnotaces := hpb.flute_not_aces
                  (show (game.pileDepth.get pileFin).toNat > 0 by omega)
                simp only [hboundaryEq] at hnotaces
                have hnotaces' := hnotaces hs4card
                rw [hSuitEqFin2] at hnotaces'
                have hnotaces'' : A.toNat + pileFlute.toNat ≤ card.toNat := by
                  exact hnotaces'
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
                have hci : (card.toNat : Int) = (Araw.toNat : Int) + 1 + found.toInt :=
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
                (show (game.pileDepth.get pileFin).toNat > 0 by omega)
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
            -- hp10 { game with aces := game.aces.set suit.val card
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
              EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get,
              set, EStateM.set]
            set gameA : SolverPosType :=
              { game with aces := game.aces.set suitU32.toNat card hsuitU32lt4 } with
              hgameAdef
            have hinvBundle : MoveAcesInv g suit card found game :=
              ⟨hmerged, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩
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
            have hp1AcesSuit : p1.aces.get suit = card := by
              rw [hp1_aces, hgameAdef]
              show (game.aces.set suitU32.toNat card hsuitU32lt4)[suit.val]'suit.isLt =
                card
              have hfin : (⟨suit.val, suit.isLt⟩ : Fin 4) = (⟨suitU32.toNat, hsuitU32lt4⟩ : Fin 4) :=
                Fin.ext hsuitValEq
              have hget : (game.aces.set suitU32.toNat card hsuitU32lt4)[suit.val]'suit.isLt =
                  (game.aces.set suitU32.toNat card hsuitU32lt4).get
                    (⟨suit.val, suit.isLt⟩ : Fin 4) := rfl
              rw [hget, hfin]
              exact Vector.getElem_set_self hsuitU32lt4
            have hp1AcesNe : ∀ t : Fin 4, t ≠ suit → p1.aces.get t = game.aces.get t := by
              intro t ht
              rw [hp1_aces, hgameAdef]
              show (game.aces.set suitU32.toNat card hsuitU32lt4)[t.val]'t.isLt =
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
                (p1.pileDepth.get k).toNat ≤ (game.pileDepth.get k).toNat := by
              intro k
              by_cases hkP : k.val = pile.toUInt32.toNat
              · have hkeq : k = (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := Fin.ext hkP
                rw [hkeq, hp1_pileDepth_self]
                have hpos : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat
                    > 0 := by
                  have : (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = pileFin := hpileFinEqP32.symm
                  rw [this]; exact hdepthPos
                have h1 : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                    (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt - 1 := by
                  rw [UInt8.toInt_sub_of_le
                    (by rw [UInt8.le_iff_toInt_le, UInt8.toInt_one]
                        have : (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = pileFin := hpileFinEqP32.symm
                        rw [this]
                        have hcast : (game.pileDepth.get pileFin).toInt =
                            ((game.pileDepth.get pileFin).toNat : Int) := rfl
                        omega),
                    UInt8.toInt_one]
                have hcast2 : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt =
                    ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat : Int) := rfl
                have hcast3 : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                    (((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toNat : Int) := rfl
                omega
              · rw [hp1_pileDepth_ne k hkP]
            -- Shared subtraction fact: `pileFin`'s depth decrement by exactly `1`,
            -- wrap-free (since its depth is `> 0`, established by `hdepthPos`).
            have hDepthSubEq : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                ).toInt = (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt - 1 := by
              rw [UInt8.toInt_sub_of_le
                (by rw [UInt8.le_iff_toInt_le, UInt8.toInt_one]
                    have : (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) = pileFin := hpileFinEqP32.symm
                    rw [this]
                    have hcast : (game.pileDepth.get pileFin).toInt =
                        ((game.pileDepth.get pileFin).toNat : Int) := rfl
                    omega),
                UInt8.toInt_one]
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
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · -- pileDepth_bound
                  rw [hp1_pileDepth_self]
                  have hcast : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                      (((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toNat : Int) := rfl
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
                    show (g.pos2card.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).get
                        ⟨(p1.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1,
                          by have := hp1DepthEq
                             have hcast : (p1.pileDepth.get
                                 (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat =
                                 (p1.pileDepth.get
                                   (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat := rfl
                             omega⟩ =
                      (g.pos2card.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).get
                        ⟨cd1.toNat - 1, hidxlt5⟩
                    congr 1
                  have hboundaryEq2 : boundary = (g.pos2card.get pileFin).get ⟨cd1.toNat - 1, hidxlt5⟩ := by
                    rw [hboundaryEqIdx, hpileFinEqP32]
                  have hNBreal : IsRealCard boundary := by
                    rw [hboundaryEq2]; exact hwf.pos2card_real pileFin _
                  have hNBnotfree : ¬ isFreeCard g game boundary := by
                    rw [hboundaryEq2]
                    have hidx4lt : (cd1.toNat - 1 : Nat) < (game.pileDepth.get pileFin).toNat := by
                      have h9 := hpdEqNat
                      omega
                    exact depth_card_not_free hwf hmerged.toSolverInvBase pileFin
                      ⟨cd1.toNat - 1, hidxlt5⟩ hidx4lt
                  have hcardIdxEq : (⟨cd1.toNat, hcd1lt5⟩ : Fin 5) =
                      ⟨(game.pileDepth.get pileFin).toNat - 1, by
                        have := hmerged.pileDepth_bound pileFin; omega⟩ := by
                    apply Fin.ext
                    show cd1.toNat = (game.pileDepth.get pileFin).toNat - 1
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
                    have hcast : (p1.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat =
                        (p1.pileDepth.get
                          (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat := rfl
                    omega
                  by_cases hSNB : SUIT boundary = suit.val.toUInt8
                  · have hlt := hAboveCard boundary hSNB hNBreal.2.1 hNBnotfree hNBnecard
                    have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
                      apply Fin.ext
                      show (SUIT boundary).toNat = suit.val
                      rw [hSNB, finVal_toUInt8_toNat]
                    rw [hEqFin, hp1AcesSuit, hp1_pileFlute_self]
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
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · rw [hdeq]; exact hbOld.pileDepth_bound
                · rw [hfeq]; exact hbOld.flute_pos
                · intro h; rw [hfeq]; exact hbOld.flute_empty (hdeq ▸ h)
                · intro j hdj hj0 hjlt
                  rw [hdeq] at hdj
                  rw [hfeq] at hjlt
                  apply isFreeCard_mono hp1_depth_mono
                  have hfc := hbOld.flute_cards_free j hdj hj0 hjlt
                  have hboundaryEqNe : (g.pos2card.get i).get
                      ⟨(p1.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ =
                      (g.pos2card.get i).get
                      ⟨(game.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                    have hfin : (⟨(p1.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ : Fin 5) =
                        ⟨(game.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                      apply Fin.ext
                      show (p1.pileDepth.get i).toNat - 1 =
                        (game.pileDepth.get i).toNat - 1
                      rw [hdeq]
                    rw [hfin]
                  rw [hboundaryEqNe]
                  exact hfc
                · -- flute_not_aces: frame if `SUIT boundary ≠ suit`, else the
                  -- cross-pile `hAboveCard`/`flute_le_of_lt_and_notfree` argument.
                  intro hdj boundary hs
                  have hboundaryEqNe2 : boundary = (g.pos2card.get i).get
                      ⟨(game.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩ := by
                    show (g.pos2card.get i).get ⟨(p1.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; rw [hdeq]; omega⟩ =
                      (g.pos2card.get i).get ⟨(game.pileDepth.get i).toNat - 1, by
                        have := hbOld.pileDepth_bound; omega⟩
                    congr 1
                    apply Fin.ext
                    show (p1.pileDepth.get i).toNat - 1 =
                      (game.pileDepth.get i).toNat - 1
                    rw [hdeq]
                  have hgameHdj : (game.pileDepth.get i).toNat > 0 := by rw [← hdeq]; exact hdj
                  have hs' : (SUIT ((g.pos2card.get i).get ⟨(game.pileDepth.get i).toNat - 1,
                      by have := hbOld.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ : UInt8)).toNat < 4 := by
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
                        (by have := hbOld.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega)
                    have hboundaryReal : IsRealCard boundary := by
                      rw [hboundaryEqNe2]; exact hwf.pos2card_real i _
                    have hboundaryNeCard : boundary ≠ card := by
                      intro hcon
                      rw [hboundaryEqNe2] at hcon
                      have hcon2 : (g.pos2card.get i).get ⟨(game.pileDepth.get i).toNat - 1,
                          by have := hbOld.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ =
                        (g.pos2card.get pileFin).get ⟨(game.pileDepth.get pileFin).toNat - 1,
                          by have := hmerged.pileDepth_bound pileFin; simp only [UInt8.toInt_eq] at *; omega⟩ :=
                        hcon.trans hboundaryEq.symm
                      have hinj := hwf.pos2card_inj i pileFin
                        ⟨(game.pileDepth.get i).toNat - 1, by
                          have := hbOld.pileDepth_bound; omega⟩
                        ⟨(game.pileDepth.get pileFin).toNat - 1, by
                          have := hmerged.pileDepth_bound pileFin; omega⟩ hcon2
                      exact hine hinj.1
                    have hclt := hAboveCard boundary hSB hboundaryReal.2.1 hboundaryNotFree
                      hboundaryNeCard
                    have hle := flute_le_of_lt_and_notfree hwf hmerged.toSolverInvBase i
                      (by have := hbOld.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega) card hcardNotFree
                      (by rw [← hboundaryEqNe2]; exact hclt)
                    have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
                      apply Fin.ext
                      show (SUIT boundary).toNat = suit.val
                      rw [hSB, finVal_toUInt8_toNat]
                    rw [hEqFin, hp1AcesSuit, hfeq]
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
              have hfin : (⟨(game.pileDepth.get pileFin).toNat - 1, by
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
                  have hcast1 : (game.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat =
                      (game.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat := rfl
                  have hcast2 : ((game.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                      (((game.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toNat : Int) := rfl
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
                  have hgePD : (game.pileDepth[(cardPile g X).toNat]'hXp64).toNat =
                      (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat := by
                    have heq2 : game.pileDepth[(cardPile g X).toNat]'hXp64 =
                        game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := by congr 1
                    rw [heq2]
                    rfl
                  rw [hgePD]
                  have h3 := hgameDepthLit
                  omega
              · have hne : (⟨(cardPile g X).toNat, hXp64⟩ : Fin 10).val ≠ pile.toUInt32.toNat :=
                  hXP
                have heq := hp1_pileDepth_ne ⟨(cardPile g X).toNat, hXp64⟩ hne
                have hge := isFree_to_cardDepth_ge g p1 hwf X hX64 hXp64 hf
                apply isFree_of_cardDepth_ge g game hwf X hX64 hXp64
                have hgePD : (game.pileDepth[(cardPile g X).toNat]'hXp64).toNat =
                    (p1.pileDepth[(cardPile g X).toNat]'hXp64).toNat := by
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
                have hKSuit : SUIT K = s.val.toUInt8 := hbOldS.aces_kings_valid.2.2.1
                have hKVal13 : (VALUE K).toNat ≤ 13 := hbOldS.aces_kings_valid.2.2.2.1
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
                  have hcd1EqCDnat : (cardDepth g card).toNat = cd1.toNat :=
                    (congrArg UInt8.toNat hcd1EqCD).symm
                  have hcast1 : (game.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toInt.toNat =
                      (game.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat := rfl
                  have hcast2 : ((game.pileDepth.get
                      (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toNat =
                      (game.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1 := by
                    have h := hDepthSubEq
                    have hc : ((game.pileDepth.get
                        (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toInt =
                        (((game.pileDepth.get
                          (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1).toNat : Int) := rfl
                    omega
                  omega
                -- `card ≤ kings[s]` (byte-wise): otherwise `card` would be
                -- free in `game` by `king_frontier`'s `∀c` clause, contradicting
                -- `hcardNotFree`.
                have hcardLeK : card.toNat ≤ K.toNat := by
                  by_contra hgt
                  push Not at hgt
                  have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
                  have hsk := SUIT_toNat K; have hvk := VALUE_toNat K
                  have hVgt : (VALUE K).toNat < (VALUE card).toNat := by
                    rw [hsuitcard] at hsc; rw [hKSuit] at hsk; omega
                  exact hcardNotFree (hbOldS.king_frontier.2 card hsuitcard hVgt hg)
                refine ⟨?_, ?_, ?_, ?_⟩
                · -- aces_kings_valid
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · rw [hacesEq]; exact hsuitcard
                  · rw [hacesEq]; exact hg
                  · rw [hp1_kings]; exact hKSuit
                  · rw [hp1_kings]; exact hKVal13
                  · rw [hacesEq, hp1_kings]
                    apply UInt8.le_iff_toInt_le.mpr
                    simp only [UInt8.toInt_eq]
                    exact_mod_cast hcardLeK
                · -- foundation_cards_free
                  intro c hSc hVc1 hVc2
                  rw [hacesEq] at hVc2
                  by_cases hcOld : (VALUE c).toNat ≤ (VALUE (game.aces.get s)).toNat
                  · exact isFreeCard_mono hp1_depth_mono
                      (hbOldS.foundation_cards_free c hSc hVc1 hcOld)
                  · by_cases hcCard : c = card
                    · rw [hcCard]; exact hcardFreeP1
                    · push Not at hcOld
                      have hSuitA : SUIT (game.aces.get s) = s.val.toUInt8 :=
                        hbOldS.aces_kings_valid.1
                      have hsc := SUIT_toNat c; have hvc := VALUE_toNat c
                      have hsa := SUIT_toNat (game.aces.get s)
                      have hva := VALUE_toNat (game.aces.get s)
                      have hSameSuit :
                          (SUIT c).toNat = (SUIT (game.aces.get s)).toNat := by
                        rw [hSc, hSuitA]
                      set l := c.toNat - (game.aces.get s).toNat with hldef
                      have hl1 : 1 ≤ l := by omega
                      have hlfound : (l : Int) ≤ found.toInt := by
                        have hci : (card.toNat : Int) =
                            (game.aces.get s).toNat + 1 + found.toInt := hcardeq
                        have hcne : c.toNat ≠ card.toNat := fun h => hcCard (UInt8.toNat_inj.mp h)
                        have hscard := SUIT_toNat card; have hvcard := VALUE_toNat card
                        have hSuitCardEq : (SUIT card).toNat = (SUIT (game.aces.get s)).toNat := by
                          rw [hsuitcard, hSuitA]
                        omega
                      have hAl256 : (game.aces.get s).toNat + l < 256 := by
                        have := c.toNat_lt; omega
                      have hceq : c = (game.aces.get s) + UInt8.ofNat l :=
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
                        apply UInt8.lt_iff_toInt_lt.mpr
                        simp only [UInt8.toInt_eq]
                        exact_mod_cast hlt
                      · have hKreal : IsRealCard K := by
                          refine ⟨?_, ?_, hKVal13⟩
                          · rw [hKSuit]
                            have := s.isLt; have := finVal_toUInt8_toNat s; omega
                          · have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
                            have hsk := SUIT_toNat K; have hvk := VALUE_toNat K
                            rw [hsuitcard] at hsc; rw [hKSuit] at hsk; omega
                        have hKneCard : K ≠ card := fun hEq => by
                          rw [hEq] at hlt; omega
                        rcases hbOldS.king_frontier.1 with ⟨hKeqA, _⟩ | ⟨_, hKnf⟩
                        · -- Case (A) `kings[s] = aces[s]` is impossible:
                          -- `card > aces[s] = kings[s]` would make
                          -- `card` free via the `∀c` clause, contradicting
                          -- `hcardNotFree`.
                          exfalso
                          have hAeqK : K.toNat = (game.aces.get s).toNat :=
                            congrArg (fun x => x.toNat) hKeqA
                          have hci : (card.toNat : Int) =
                              (game.aces.get s).toNat + 1 + found.toInt := hcardeq
                          omega
                        · exact hfreeTransfer K hKreal hKneCard hKnf
                    · -- `card = kings[s]` (byte-wise): the busy bit alone
                      -- justifies disjunct (A).
                      have hEq : K = card := by
                        apply UInt8.toNat_inj.mp; omega
                      refine Or.inl ⟨?_, Or.inr (by rw [hp1_busyAces]; exact hbit)⟩
                      rw [hacesEq, ← hEq]
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
                  by_cases hVal13 : (VALUE (game.aces.get s)).toNat = 13
                  · exact Or.inl hVal13
                  · rcases hbOldS.foundation_maximal_weak with h13 | hnf | hbusy
                    · exact absurd h13 hVal13
                    · refine Or.inr (Or.inl ?_)
                      have hSAs : SUIT (game.aces.get s) = s.val.toUInt8 :=
                        (hbOldS.aces_kings_valid).1
                      have hVAs13 : (VALUE (game.aces.get s)).toNat ≤ 13 :=
                        (hbOldS.aces_kings_valid).2.1
                      have hVAslt15 : (VALUE (game.aces.get s)).toNat < 15 := by omega
                      have hSAs1 : SUIT ((game.aces.get s) + 1) = s.val.toUInt8 := by
                        rw [SUIT_succ _ hVAslt15]; exact hSAs
                      have hVAs1 : (VALUE ((game.aces.get s) + 1)).toNat ≤ 13 := by
                        rw [VALUE_succ _ hVAslt15]; omega
                      have hVAs1pos : 1 ≤ (VALUE ((game.aces.get s) + 1)).toNat := by
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
                      have hSK : SUIT (game.kings.get s) = s.val.toUInt8 :=
                        (hbOldS.aces_kings_valid).2.2.1
                      have hVK13 : (VALUE (game.kings.get s)).toNat ≤ 13 :=
                        (hbOldS.aces_kings_valid).2.2.2.1
                      have hVKpos : 1 ≤ (VALUE (game.kings.get s)).toNat := by
                        have hsa := SUIT_toNat (game.aces.get s)
                        have hva := VALUE_toNat (game.aces.get s)
                        have hsk := SUIT_toNat (game.kings.get s)
                        have hvk := VALUE_toNat (game.kings.get s)
                        have hsuitEq : (SUIT (game.aces.get s)).toNat =
                            (SUIT (game.kings.get s)).toNat := by
                          rw [(hbOldS.aces_kings_valid).1, hSK]
                        have hlt' : (game.aces.get s).toNat <
                            (game.kings.get s).toNat := UInt8.lt_iff_toNat_lt.mp hlt
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
            have hp1_aces_eq : p1.aces = game.aces.set suit.val card suit.isLt := by
              apply vector_ext_get
              intro t
              by_cases htS : t = suit
              · rw [htS, hp1AcesSuit]
                show card = (game.aces.set suit.val card suit.isLt)[suit.val]'suit.isLt
                rw [Vector.getElem_set_self]
              · rw [hp1AcesNe t htS]
                show game.aces[t.val]'t.isLt =
                  (game.aces.set suit.val card suit.isLt)[t.val]'t.isLt
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
            have hpdOldNat' : (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                ).toNat = cd1.toNat + 1 := hpdOldNat
            have hpdNewNat : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                ).toInt.toNat = cd1.toNat := by
              have h1 := hDepthSubEq
              omega
            have hpdNewNat' : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                ).toNat = cd1.toNat := hpdNewNat
            have hash_def_p1 : p1.hash = (List.finRange 10).foldl
                (fun acc i => acc + pileHashes.get i * (p1.pileDepth.get i).toNat.toUInt32)
                0 := by
              have hadd := hash_foldl_set game.pileDepth pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1)
              rw [← hp1_pileDepth_eq] at hadd
              have hnewCast : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                  ).toNat.toUInt32 = cd1.toNat.toUInt32 := by rw [hpdNewNat']
              have holdCast : (game.pileDepth[pile.toUInt32.toNat]'hp10).toNat.toUInt32
                  = (cd1.toNat + 1).toUInt32 := by
                have : (game.pileDepth[pile.toUInt32.toNat]'hp10) =
                    game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [this, hpdOldNat']
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
                - (p1.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
                - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
                    p1.pileDepth.toList p1.pileFlute.toList |>.foldl (· + ·) 0 : Nat) := by
              have hds := depth_sum_foldl_set game.pileDepth pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1)
              rw [← hp1_pileDepth_eq] at hds
              have has_ := aces_sum_foldl_set game.aces suit.val suit.isLt card
              rw [← hp1_aces_eq] at has_
              have hft := usedSpace_term_foldl_set game.pileDepth game.pileFlute
                pile.toUInt32.toNat hp10
                ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) 1
              rw [← hp1_pileDepth_eq, ← hp1_pileFlute_eq] at hft
              have holdD : (game.pileDepth[pile.toUInt32.toNat]'hp10) ≠ (0 : UInt8) := by
                intro hz
                have : (game.pileDepth[pile.toUInt32.toNat]'hp10).toNat = 0 := by
                  rw [hz]; decide
                have hlit : (game.pileDepth[pile.toUInt32.toNat]'hp10) =
                    game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [hlit, hpdOldNat'] at this
                omega
              have hnewD : ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1
                  ) ≠ (0 : UInt8) ∨
                  ((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) = 0 :=
                (em (((game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) = 0)).symm
              have hgameOldFluteVal : (game.pileFlute[pile.toUInt32.toNat]'hp10).toNat =
                  found.toInt.toNat + 1 := by
                have hlit : (game.pileFlute[pile.toUInt32.toNat]'hp10) =
                    game.pileFlute.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10) := rfl
                rw [hlit, ← hpileFinEqP32]; exact hpileFluteVal
              have hOldTerm : (if (game.pileDepth[pile.toUInt32.toNat]'hp10) ≠ (0 : UInt8)
                  then (game.pileFlute[pile.toUInt32.toNat]'hp10).toNat - 1 else 0) =
                  found.toInt.toNat := by
                rw [if_pos holdD, hgameOldFluteVal]; omega
              have hNewTerm : (if ((game.pileDepth.get
                  (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)) - 1) ≠ (0 : UInt8)
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
              rw [hOldLit, hpdOldNat', hpdNewNat'] at hds
              have hAcesIdxEq : (game.aces[suit.val]'suit.isLt) = game.aces.get suit := rfl
              rw [hAcesIdxEq] at has_
              have hVAeq : (VALUE (game.aces.get suit)).toNat + 1 + found.toInt.toNat =
                  (VALUE card).toNat := by
                have hsa := SUIT_toNat (game.aces.get suit)
                have hva := VALUE_toNat (game.aces.get suit)
                have hsc := SUIT_toNat card
                have hvc := VALUE_toNat card
                have hSuitEq : (SUIT (game.aces.get suit)).toNat = (SUIT card).toNat := by
                  rw [hsuitcard, (hmerged.aces_kings_valid suit).1]
                have hci : (card.toNat : Int) =
                    (game.aces.get suit).toNat + 1 + found.toInt := hcardeq
                omega
              have hfoldEq : (game.pileDepth.toList.foldl
                  (fun acc x => acc + x.toInt.toNat) 0 : Nat) =
                  (game.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat) := rfl
              have hfoldEqP1 : (p1.pileDepth.toList.foldl
                  (fun acc d => acc + d.toInt.toNat) 0 : Nat) =
                  (p1.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat) := rfl
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
                  have hb1 : (⟨(p1.pileDepth.get j).toNat - 2, by
                      have := hnf.pileDepth_bound j; omega⟩ : Fin 5) =
                      ⟨(game.pileDepth.get j).toNat - 2, by
                      have := hbOldBase.pileDepth_bound; omega⟩ := by
                    apply Fin.ext
                    show (p1.pileDepth.get j).toNat - 2 =
                      (game.pileDepth.get j).toNat - 2
                    rw [hdeq]
                  have hb2 : (⟨(p1.pileDepth.get j).toNat - 1, by
                      have := hnf.pileDepth_bound j; omega⟩ : Fin 5) =
                      ⟨(game.pileDepth.get j).toNat - 1, by
                      have := hbOldBase.pileDepth_bound; omega⟩ := by
                    apply Fin.ext
                    show (p1.pileDepth.get j).toNat - 1 =
                      (game.pileDepth.get j).toNat - 1
                    rw [hdeq]
                  rw [hb1, hb2]
                  exact hne
              · -- flute_maximal
                by_cases hd0 : p1.pileDepth.get j = 0
                · left; exact hd0
                · have hgd0 : game.pileDepth.get j ≠ 0 := by rw [hdeq] at hd0; exact hd0
                  have hgdj : (game.pileDepth.get j).toNat > 0 :=
                    Nat.pos_of_ne_zero (fun h => hgd0 (UInt8.toNat_inj.mp h))
                  right
                  have hidxEqB : (p1.pileDepth.get j).toNat - 1 =
                      (game.pileDepth.get j).toNat - 1 := by rw [hdeq]
                  have hboundaryB : (g.pos2card.get j).get ⟨(p1.pileDepth.get j).toNat - 1,
                      by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩ =
                      (g.pos2card.get j).get ⟨(game.pileDepth.get j).toNat - 1,
                      by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ := by
                    congr 1; exact Fin.ext hidxEqB
                  show (∃ hs : (SUIT ((g.pos2card.get j).get
                      ⟨(p1.pileDepth.get j).toNat - 1,
                      by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩)).toNat < 4,
                      p1.aces.get ⟨(SUIT ((g.pos2card.get j).get
                        ⟨(p1.pileDepth.get j).toNat - 1,
                        by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩)).toNat, hs⟩ =
                      (((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toNat - 1,
                        by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩) - p1.pileFlute.get j)) ∨
                    ¬ isFreeCard g p1 (((g.pos2card.get j).get
                      ⟨(p1.pileDepth.get j).toNat - 1,
                      by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩) - p1.pileFlute.get j)
                  rw [hboundaryB, hfeq]
                  set boundary := (g.pos2card.get j).get ⟨(game.pileDepth.get j).toNat - 1,
                    by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ with hboundaryDef
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
                      exact hpc.symm
                    · right
                      have hboundaryNotFree : ¬ isFreeCard g game boundary :=
                        boundary_not_free hwf hmerged.toSolverInvBase j
                          (by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega)
                      have hboundaryNeCard : boundary ≠ card := by
                        intro hcon
                        have hcon2 : (g.pos2card.get j).get ⟨(game.pileDepth.get j).toNat - 1,
                            by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ =
                          (g.pos2card.get pileFin).get ⟨(game.pileDepth.get pileFin
                            ).toNat - 1, by have := hmerged.pileDepth_bound pileFin; simp only [UInt8.toInt_eq] at *; omega⟩ :=
                          (hboundaryDef ▸ hcon).trans hboundaryEq.symm
                        have hinj := hwf.pos2card_inj j pileFin
                          ⟨(game.pileDepth.get j).toNat - 1, by
                            have := hbOldBase.pileDepth_bound; omega⟩
                          ⟨(game.pileDepth.get pileFin).toNat - 1, by
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
                          have hAeqUInt8 : (game.aces.get suit) = prevCard := heqOld
                          have hAeqNat : (game.aces.get suit).toNat = prevCard.toNat := by
                            rw [hAeqUInt8]
                          have hci : (card.toNat : Int) =
                              (game.aces.get suit).toNat + 1 + found.toInt := hcardeq
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
                      have hak : ∀ t : Fin 4, SUIT (game.aces.get t) = t.val.toUInt8 :=
                        fun t => (hmerged.aces_kings_valid t).1
                      have hna : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat +
                          (game.pileFlute.get j).toNat ≤ boundary.toNat :=
                        hbOldBase.flute_not_aces hgdj hs4'
                      have hSuitAcesEq : SUIT ((game.aces.get
                          ⟨(SUIT boundary).toNat, hs4'⟩)) = SUIT boundary := by
                        rw [hak ⟨(SUIT boundary).toNat, hs4'⟩]
                        apply UInt8.toNat_inj.mp
                        rw [finVal_toUInt8_toNat]
                      have hVBnat := VALUE_toNat
                        ((game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
                      have hSBnat := SUIT_toNat
                        ((game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
                      have hSeq := congrArg UInt8.toNat hSuitAcesEq
                      have hprevNat0 : prevCard.toNat = 16 * (SUIT boundary).toNat := by omega
                      have hacesGeNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toNat ≥ prevCard.toNat := by rw [hprevNat0]; omega
                      have hacesLeNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toNat ≤ prevCard.toNat := by rw [hprevNat]; omega
                      have hacesEqNat : (game.aces.get ⟨(SUIT boundary).toNat, hs4'⟩
                          ).toNat = prevCard.toNat := le_antisymm hacesLeNat hacesGeNat
                      exact UInt8.toNat_inj.mp hacesEqNat
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
                have hgdj : (game.pileDepth.get j).toNat > 0 := by rw [← hdeq]; exact hdj0
                have hidxEqB : (p1.pileDepth.get j).toNat - 1 =
                    (game.pileDepth.get j).toNat - 1 := by rw [hdeq]
                have hboundaryB : (g.pos2card.get j).get ⟨(p1.pileDepth.get j).toNat - 1,
                    by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩ =
                    (g.pos2card.get j).get ⟨(game.pileDepth.get j).toNat - 1,
                    by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ := by
                  congr 1; exact Fin.ext hidxEqB
                show ∀ hs : (SUIT ((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toNat - 1,
                    by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩)).toNat < 4,
                  (p1.aces.get ⟨(SUIT ((g.pos2card.get j).get
                    ⟨(p1.pileDepth.get j).toNat - 1,
                    by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩)).toNat, hs⟩) =
                    ((g.pos2card.get j).get ⟨(p1.pileDepth.get j).toNat - 1,
                      by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩) - p1.pileFlute.get j →
                  p1.busyAces &&& ((1 : UInt8) <<< (SUIT ((g.pos2card.get j).get
                    ⟨(p1.pileDepth.get j).toNat - 1,
                    by have := hnf.pileDepth_bound j; simp only [UInt8.toInt_eq] at *; omega⟩))) ≠ 0
                rw [hboundaryB]
                set boundary := (g.pos2card.get j).get ⟨(game.pileDepth.get j).toNat - 1,
                  by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ with hboundaryDef
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
              rw [hp1_freePiles, cleanupReady_freePiles_frame_eq pile.toUInt32 game p1 hp1_pileDepth_ne]
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
                  (0 : UInt8) then (1 : Nat) else 0) = 0 := by
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
            have hp'AcesSuit : p'.aces.get suit = card := by
              rw [hacesEq', ← hp1_aces]; exact hp1AcesSuit
            have hp'AcesSuitUInt8 : (p'.aces.get suit) = card := by
              rw [hp'AcesSuit]
            have hgameAbusy : gameA.busyAces = game.busyAces := by rw [hgameAdef]
            have hp'busybit : p'.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0 :=
              hbusyMonoP _ (by rw [hgameAbusy]; exact hbit)
            have hnewcard1eq : ((card + 1).toNat : Int) =
                (p'.aces.get suit).toNat + 1 + (0 : UInt8).toInt := by
              rw [hp'AcesSuitUInt8, hcard1nat]
              have h0 : (0 : UInt8).toInt = 0 := rfl
              rw [h0]
              push_cast
              ring
            have hnewfoundfree0 : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ (0 : UInt8).toInt →
                isFreeCard g p' ((p'.aces.get suit) + UInt8.ofNat l) := by
              intro l hl1 hlle
              exfalso
              have h0 : (0 : UInt8).toInt = 0 := rfl
              omega
            have hnewinv2 : MoveAcesInv g suit (card + 1) 0 p' :=
              ⟨hinvP', by decide, hsuitcard1, hval1_1, hval14_1,
                hnewcard1eq, hnewfoundfree0, hp'busybit⟩
            have hnewmeas : 14 - (VALUE (card + 1)).toNat < n := by
              have := VALUE_succ card hcardVal15; omega
            -- the carried predicate crosses the one position-changing step
            have hdepthPos32 :
                0 < (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat := by
              rw [← hpileFinEqP32]; omega
            have hfluteEq32 :
                (game.pileFlute.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat
                  = found.toNat + 1 := by
              rw [← hpileFinEqP32, ← hpileFlutedef]
              have hb : found.toInt.toNat = found.toNat := rfl
              omega
            have hboundary32 : ∀ hidx :
                (game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1 < 5,
                (g.pos2card.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).get
                  ⟨(game.pileDepth.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1,
                    hidx⟩ = card := by
              intro hidx
              have hvec : g.pos2card.get (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)
                  = g.pos2card.get pileFin := by rw [hpileFinEqP32]
              have hidxP : (game.pileDepth.get pileFin).toNat - 1 < 5 := by
                rw [hpileFinEqP32]; exact hidx
              have hfin : (⟨(game.pileDepth.get
                    (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1, hidx⟩ : Fin 5)
                  = ⟨(game.pileDepth.get pileFin).toNat - 1, hidxP⟩ :=
                Fin.ext (show (game.pileDepth.get
                    (⟨pile.toUInt32.toNat, hp10⟩ : Fin 10)).toNat - 1
                  = (game.pileDepth.get pileFin).toNat - 1 from by rw [hpileFinEqP32])
              rw [hvec, hfin]
              exact hboundaryEq
            have hPnew : P (forcedKings &&& fk) p' :=
              hsync card found forcedKings fk game gameA p1 p' pile.toUInt32 hp10
                hinvBundle hdepthPos32 hboundary32 hfluteEq32 hp1def hp1_pileDepth_self
                hp1_pileDepth_ne hp1_pileFlute_self hp1_pileFlute_ne hp1_kings hp1AcesSuit
                hp1AcesNe hready hrunEq' hP
            obtain ⟨card', fk', found', game', heq, hinv', hexit', hframe'', hdich'', hP'⟩ :=
              ih (card + 1) (forcedKings &&& fk) 0 p' hnewmeas hnewinv2 hPnew
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
            exact ⟨card', fk', found', game', heq, hinv', hexit', hframe, Or.inr hdich, hP'⟩
        · -- BURIED (`< 0`): `.done`, unchanged accumulator; `card` not free.
          have hcd0' : cd1.toUInt32.toInt32 + 1 - cd2.toInt32 ≠ 0 := by
            intro heq; exact hcd0 (by rw [heq]; decide)
          have hle0' : (cd1.toNat : Int) + 1 - cd2.toInt ≤ 0 := by
            by_contra hcon
            push Not at hcon
            apply hcdpos
            rw [gt_iff_lt, Int32.lt_iff_toInt_lt, hcardDepthI, show ((0 : Int32).toInt = 0) from by decide]
            omega
          have hne0' : (cd1.toNat : Int) + 1 - cd2.toInt ≠ 0 := by
            intro heq
            apply hcd0'
            apply Int32.toInt_inj.mp
            rw [hcardDepthI, show ((0 : Int32).toInt = 0) from by decide]
            exact heq
          refine ⟨card, forcedKings, found, game, ?_,
            ⟨hmerged, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩,
            Or.inr ⟨?_, hp64, ?_⟩, fun _ _ => rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩, hP⟩
          · simp only [hcdpos, hcd0, reduceIte, EStateM.pure, Bool.false_eq_true]
          · intro hfree
            have hge := isFree_to_cardDepth_ge g game hwf card hc64' hp64 hfree
            rw [← hcd1EqCD, ← hcd2EqPD] at hge
            have hcast : cd2.toInt = (cd2.toNat : Int) := rfl
            omega
          · rw [← hcd1EqCD, ← hcd2EqPD]
            have hcast : cd2.toInt = (cd2.toNat : Int) := rfl
            omega
    · -- guard false: `.done`, unchanged accumulator; `VALUE card = 14`.
      have hgProp' : ¬ (VALUE card ≤ (13 : UInt8)) := fun h => hg (hgIff.mp h)
      refine ⟨card, forcedKings, found, game, ?_,
        ⟨hmerged, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩,
        Or.inl (by omega), fun _ _ => rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩, hP⟩
      rw [hunf]
      simp only [moveAcesBody, hgProp', bind, EStateM.bind, pure, EStateM.pure, reduceIte]

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
        (VALUE (p'.aces.get s)).toNat > (VALUE (p.aces.get s)).toNat ∨
        (p'.aces = p.aces ∧ p'.busyAces.toNat < p.busyAces.toNat)) ∧
      DepthLe p p' := by
  -- `suit := ctz p.busyAces` must be `< 4` for the real function to even
  -- typecheck through (`aces`/`kings` have only 4 entries) — now immediate
  -- from `SolverInvBase.busyAces_lt16` (bits `4..7` are always clear) plus
  -- `hbusy` (some bit IS set, so it must be among `0..3`).
  have hsuit4 : ctz p.busyAces < 4 := ctz_lt_four hmerged.busyAces_lt16 hbusy
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
  set card0 : UInt8 := A + 1 with hcard0def
  set found0 : UInt8 := 0 with hfound0def
  -- Establish `MoveAcesInv` at the walk's starting point.
  have hAsuit : SUIT A = suit.val.toUInt8 := (hmerged.aces_kings_valid suit).1
  have hAval13 : (VALUE A).toNat ≤ 13 := (hmerged.aces_kings_valid suit).2.1
  have hcard0eq : card0 = A + 1 := hcard0def
  have hAval15 : (VALUE A).toNat < 15 := by omega
  have hsuitcard0 : SUIT card0 = suit.val.toUInt8 := by
    rw [hcard0eq, SUIT_succ A hAval15]; exact hAsuit
  have hval1_0 : 1 ≤ (VALUE card0).toNat := by
    rw [hcard0eq, VALUE_succ A hAval15]; omega
  have hval14_0 : (VALUE card0).toNat ≤ 14 := by
    rw [hcard0eq, VALUE_succ A hAval15]; omega
  have hAtoNat255 : A.toNat < 255 := by
    have hsn := SUIT_toNat A; have hs4 : (SUIT A).toNat < 4 := by
      rw [hAsuit]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
    omega
  have hcard0nat : card0.toNat = A.toNat + 1 := by
    rw [hcard0eq]; exact toNat_succ A hAtoNat255
  have hcard0eqInv : (card0.toNat : Int) = (p.aces.get suit).toNat + 1 + found0.toInt := by
    rw [hcard0nat, hfound0def, hAdef, show ((0 : UInt8).toInt = 0) from rfl]
    push_cast
    ring
  have hfoundfree0 : ∀ l : Nat, 1 ≤ l → (l : Int) ≤ found0.toInt →
      isFreeCard g p ((p.aces.get suit) + UInt8.ofNat l) := by
    intro l hl1 hlle
    exfalso
    have hf0 : found0.toInt = 0 := by rw [hfound0def]; decide
    omega
  have hbusybit : p.busyAces &&& ((1 : UInt8) <<< suit.val.toUInt8) ≠ 0 := by
    rw [hsuitval]
    exact ctz_bit_self p.busyAces hbusy
  have hinv0 : MoveAcesInv g suit card0 found0 p :=
    ⟨hmerged, by rw [hfound0def]; decide, hsuitcard0, hval1_0,
      hval14_0, hcard0eqInv, hfoundfree0, hbusybit⟩
  obtain ⟨cardF, forcedKingsF, foundF, gameF, hloopeq, hloopinv, hloopexit, hloopframe,
      hloopdich, hloopDepth⟩ :=
    moveAcesLoop_run g hwf suit suitU32 hsuitU32 (fun _ game => DepthLe p game)
      (by
        -- the walk's one position-changing step is a `SolverRemoveFlute` call, and those
        -- only ever shrink depths (`removeFlute_depth_le`)
        intro card found _fkAcc fk game gameA q p'' pile' hpile' _hinv hdpos _hbnd _hflute
          hq hqds hqdne _hqfs _hqfne _hqk _hqas _hqane hready hrunRF hP
        obtain ⟨hnfq, -, -⟩ := hready
        subst hq
        obtain ⟨fk2, p2, hrun2, hle2⟩ :=
          cleanupPile_depth_le pile' g (removeFlutePre pile' hpile' gameA) hpile' hwf hnfq
        have hrunRF' : EStateM.run (_root_.SolverRemoveFlute pile') (g, gameA)
            = .ok fk (g, p'') := hrunRF
        rw [removeFlute_eq pile' g gameA hpile'] at hrunRF'
        injection hrun2.symm.trans hrunRF' with h1 h2
        injection h2 with _hg hp2
        subst hp2
        refine hP.trans' (DepthLe.trans' ?_ hle2)
        -- the cleanup's entry point is one card shallower at `pile'`, unchanged elsewhere
        intro i
        by_cases hi : i.val = pile'.toNat
        · have hii : i = (⟨pile'.toNat, hpile'⟩ : Fin 10) := Fin.ext hi
          subst hii
          show ((fluteNorm pile' hpile'
            (removeFlutePre pile' hpile' gameA)).pileDepth.get _).toNat ≤ _
          rw [hqds]
          have hsub : (game.pileDepth.get (⟨pile'.toNat, hpile'⟩ : Fin 10) - 1).toNat
              = (game.pileDepth.get (⟨pile'.toNat, hpile'⟩ : Fin 10)).toNat - 1 := by
            refine UInt8.toNat_sub_of_le _ _ ?_
            rw [UInt8.le_iff_toNat_le]
            simp only [show ((1 : UInt8).toNat = 1) from rfl]
            omega
          omega
        · show ((fluteNorm pile' hpile'
            (removeFlutePre pile' hpile' gameA)).pileDepth.get i).toNat ≤ _
          rw [hqdne i hi])
      15 card0 0xffff found0 p (by have := hval14_0; omega) hinv0 (DepthLe.rfl' p)
  obtain ⟨hmergedF, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩ :=
    hloopinv
  have hf0F : (0 : Int) ≤ foundF.toInt := UInt8.toInt_nonneg foundF
  have hloopinv' : MoveAcesInv g suit cardF foundF gameF :=
    ⟨hmergedF, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩
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
  have hcard2eqA : (card2.toNat : Int) = (gameF.aces.get suit).toNat + foundF.toInt := by
    have h := hcardeqF; omega
  have hAFsuit : SUIT (gameF.aces.get suit) = suit.val.toUInt8 :=
    (hmergedF.aces_kings_valid suit).1
  have hAFval13 : (VALUE (gameF.aces.get suit)).toNat ≤ 13 :=
    (hmergedF.aces_kings_valid suit).2.1
  have hVcard2eq13From : (VALUE cardF).toNat = 14 → (VALUE card2).toNat = 13 := by
    intro h14
    have hs1 := SUIT_toNat card2; have hv1 := VALUE_toNat card2
    have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
    have hSeq : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
    omega
  -- **Key cross-pile fact**: for any pile `i` whose CURRENT boundary shares
  -- `suit`, `card2.toNat + pileFlute[i].toNat < boundary.toNat` (strict).
  have hAboveCard2 : ∀ i : Fin 10, (gameF.pileDepth.get i).toNat > 0 →
      SUIT ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
        by have := hmergedF.pileDepth_bound i; simp only [UInt8.toInt_eq] at *; omega⟩) = suit.val.toUInt8 →
      card2.toNat + (gameF.pileFlute.get i).toNat <
        ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
          by have := hmergedF.pileDepth_bound i; simp only [UInt8.toInt_eq] at *; omega⟩ : UInt8).toNat := by
    intro i hdi hSB
    set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
      by have := hmergedF.pileDepth_bound i; simp only [UInt8.toInt_eq] at *; omega⟩ with hboundaryDef
    have hboundaryReal : IsRealCard boundary := hwf.pos2card_real i _
    have hboundaryNotFree : ¬ isFreeCard g gameF boundary :=
      boundary_not_free hwf hmergedF.toSolverInvBase i hdi
    have hvacuous : (VALUE card2).toNat = 13 → False := by
      intro hVcard2eq13
      apply hboundaryNotFree
      by_cases hle : (VALUE boundary).toNat ≤ (VALUE (gameF.aces.get suit)).toNat
      · exact hmergedF.foundation_cards_free suit boundary hSB hboundaryReal.2.1 hle
      · push Not at hle
        set l := (VALUE boundary).toNat - (VALUE (gameF.aces.get suit)).toNat with hldef
        have hl1 : 1 ≤ l := by omega
        have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
        have hsa0 := SUIT_toNat (gameF.aces.get suit)
        have hva0 := VALUE_toNat (gameF.aces.get suit)
        have hsb := SUIT_toNat boundary; have hvb := VALUE_toNat boundary
        have hVB13 := hboundaryReal.2.2
        have hSeqAFc2 : (SUIT card2).toNat = (SUIT (gameF.aces.get suit)).toNat := by
          rw [hSuitCard2, hAFsuit]
        have hSeq2 : (SUIT boundary).toNat = (SUIT (gameF.aces.get suit)).toNat := by
          rw [hSB, hAFsuit]
        have hlfound : (l : Int) ≤ foundF.toInt := by
          have h := hcard2eqA
          omega
        have hSA4 : (SUIT (gameF.aces.get suit)).toNat < 4 := by
          rw [hAFsuit]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
        have hAl256 : (gameF.aces.get suit).toNat + l < 256 := by
          have := boundary.toNat_lt; omega
        have hXeq : boundary = (gameF.aces.get suit) + UInt8.ofNat l :=
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
          have hcon2 : (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
              by have := hmergedF.pileDepth_bound i; simp only [UInt8.toInt_eq] at *; omega⟩ =
            (g.pos2card.get ⟨(cardPile g cardF).toNat, hp64F'⟩).get
              ⟨(cardDepth g cardF).toNat, hcdF5⟩ := (hboundaryDef ▸ hcon).trans hrt.symm
          have hinj := hwf.pos2card_inj i ⟨(cardPile g cardF).toNat, hp64F'⟩
            ⟨(gameF.pileDepth.get i).toNat - 1, by
              have := hmergedF.pileDepth_bound i; omega⟩
            ⟨(cardDepth g cardF).toNat, hcdF5⟩ hcon2
          have hii : i = (⟨(cardPile g cardF).toNat, hp64F'⟩ : Fin 10) := hinj.1
          have hdval : (gameF.pileDepth.get i).toNat - 1 = (cardDepth g cardF).toNat :=
            congrArg Fin.val hinj.2
          have hstrict' : (cardDepth g cardF).toNat + 1 <
              (gameF.pileDepth.get i).toNat := by
            rw [hii]
            show (cardDepth g cardF).toNat + 1 <
              (gameF.pileDepth[(cardPile g cardF).toNat]'hp64F').toNat
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
  simp only [Vector.setE, dif_pos hidx4, pure, EStateM.pure, set]
  set acesFinal : Vector UInt8 4 := gameF.aces.set suit.val card2 suit.isLt with
    hacesFinalDef
  -- The REAL reduced code indexes `aces`/`kings` via `suitU32.toNat` (matching
  -- `moveAcesBody`'s own `suitU32`-based writes), not `suit.val` — even though
  -- `hsuitU32 : suitU32.toNat = suit.val` holds propositionally, the two
  -- `.set` calls are not syntactically/definitionally interchangeable, so the
  -- final `SolverInvMerged.of_base` application needs an explicit bridge
  -- (`hsetEq` below) rather than matching by `rfl`/defeq alone.
  have hsuitFin : suit = (⟨suitU32.toNat, hidx4⟩ : Fin 4) := Fin.ext hsuitU32.symm
  have hsetEq : ∀ (v : Vector UInt8 4) (x : UInt8),
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
  have hacesFinalEq : acesFinal = gameF.aces.set suitU32.toNat card2 hidx4 := by
    rw [hacesFinalDef]; exact hsetEq gameF.aces card2
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
  have hacesFinalSuit0 : acesFinal.get suit = card2 := by
    rw [hacesFinalDef]
    show (gameF.aces.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
    exact Vector.getElem_set_self suit.isLt
  have hacesFinalFrame : ∀ s : Fin 4, s.val ≠ ctz p.busyAces → acesFinal.get s = p.aces.get s := by
    intro s hs
    have hsne : s ≠ suit := by
      intro hcon; apply hs; rw [hcon]
    have hacesFinalNe : acesFinal.get s = gameF.aces.get s := by
      rw [hacesFinalDef]
      show (gameF.aces.set suit.val card2 suit.isLt)[s.val]'s.isLt =
        gameF.aces[s.val]'s.isLt
      apply Vector.getElem_set_ne suit.isLt s.isLt
      intro hcon
      exact hsne (Fin.ext hcon.symm)
    rw [hacesFinalNe]
    exact hloopframe s hsne
  have hDichotomy :
      (VALUE (acesFinal.get suit)).toNat > (VALUE (p.aces.get suit)).toNat ∨
      (acesFinal = p.aces ∧
        (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)).toNat < p.busyAces.toNat) := by
    rcases hloopdich with ⟨hcardFeq, _, _, hgameFeq⟩ | hgt
    · right
      have hcard2eqA' : card2 = A := by
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
          rw [hacesFinalSuit0, hcard2eqA']
        · have h1 : acesFinal.get t = gameF.aces.get t := by
            rw [hacesFinalDef]
            show (gameF.aces.set suit.val card2 suit.isLt)[t.val]'t.isLt =
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
      have hbitpos : ∀ t : Fin 4, 0 < ((1 : UInt8) <<< t.val.toUInt8).toNat := by decide
      have hbp := hbitpos suit
      omega
    · left
      rw [hacesFinalSuit0, ← hAdef]
      have h1 := hcard2nat
      have h2 := hcard0nat
      have hSc2 := SUIT_toNat card2; have hVc2 := VALUE_toNat card2
      have hSA := SUIT_toNat A; have hVA := VALUE_toNat A
      have hSeq : (SUIT card2).toNat = (SUIT A).toNat := by rw [hSuitCard2, hAsuit]
      omega
  -- Shared pile/suit facts, generic over the final `kings` vector (which
  -- differs between the two `VALUE card2 == 13` branches below, but nothing
  -- pile-level or in `suitClean s` for `s ≠ suit` depends on it).  Named as a
  -- function of `K` (rather than a multi-line `{ gameF with ... }` literal
  -- spliced directly into each call site) to sidestep a parser quirk where a
  -- structure-update literal spanning multiple lines, used as a function
  -- ARGUMENT (not a `let`/`have` body), can mis-parse depending on the
  -- continuation lines' indentation relative to the opening `{`.
  let gameFinalOf : Vector UInt8 4 → SolverPosType := fun K =>
    { gameF with aces := acesFinal, kings := K, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) }
  have pileBaseFinal : ∀ K : Vector UInt8 4, ∀ i : Fin 10,
      PileBase g (gameFinalOf K) i := by
    intro K i
    have hbOld := hmergedF.pileBase i
    refine ⟨hbOld.pileDepth_bound, hbOld.flute_pos, hbOld.flute_empty,
      hbOld.flute_cards_free, ?_⟩
    intro hnewDepthPos boundary hs
    by_cases hSB : SUIT boundary = suit.val.toUInt8
    · have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
        apply Fin.ext; show (SUIT boundary).toNat = suit.val
        rw [hSB, finVal_toUInt8_toNat]
      have hacesFinalSuit : (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toNat =
          card2.toNat := by
        rw [hEqFin]
        show (acesFinal.get suit).toNat = card2.toNat
        have hset : acesFinal.get suit = card2 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
          exact Vector.getElem_set_self suit.isLt
        rw [hset]
      show (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toNat +
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
        show (gameF.aces.set suit.val card2 suit.isLt)[(SUIT boundary).toNat]'hs =
          gameF.aces[(SUIT boundary).toNat]'hs
        apply Vector.getElem_set_ne suit.isLt hs
        intro hcon
        exact hNeFin (Fin.ext hcon.symm)
      show (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩).toNat +
        (gameF.pileFlute.get i).toNat ≤ boundary.toNat
      rw [hacesFinalNe]
      exact hbOld.flute_not_aces hnewDepthPos hs
  have pileMergedFinal : ∀ K : Vector UInt8 4, ∀ i : Fin 10,
      PileMerged g (gameFinalOf K) i (pileBaseFinal K i).pileDepth_bound := by
    intro K i
    have hbOld := hmergedF.pileMerged i
    have hbOldBase := hmergedF.pileBase i
    refine ⟨hbOld.merge_complete, ?_, ?_⟩
    · -- flute_maximal
      by_cases hd0 : gameF.pileDepth.get i = 0
      · left; exact hd0
      · right
        have hgdj : (gameF.pileDepth.get i).toNat > 0 :=
          Nat.pos_of_ne_zero (fun h => hd0 (UInt8.toNat_inj.mp h))
        set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
          by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ with hboundaryDef
        set prevCard := boundary - gameF.pileFlute.get i with hprevCardDef
        show (∃ hs : (SUIT boundary).toNat < 4,
            acesFinal.get ⟨(SUIT boundary).toNat, hs⟩ = prevCard) ∨
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
            have hAeq : (gameF.aces.get suit) = prevCard := heqOld
            have hAeqNat : (gameF.aces.get suit).toNat = prevCard.toNat :=
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
              show (gameF.aces.set suit.val card2 suit.isLt)[
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
      set boundary := (g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
        by have := hbOldBase.pileDepth_bound; simp only [UInt8.toInt_eq] at *; omega⟩ with hboundaryDef
      show ∀ hs : (SUIT boundary).toNat < 4,
        (acesFinal.get ⟨(SUIT boundary).toNat, hs⟩) =
          boundary - gameF.pileFlute.get i →
        (gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8)) &&& ((1 : UInt8) <<< SUIT boundary)
          ≠ 0
      intro hs heqHyp
      by_cases hSB : SUIT boundary = suit.val.toUInt8
      · exfalso
        have hEqFin : (⟨(SUIT boundary).toNat, hs⟩ : Fin 4) = suit := by
          apply Fin.ext; show (SUIT boundary).toNat = suit.val
          rw [hSB, finVal_toUInt8_toNat]
        have hacesFinalSuit : acesFinal.get suit = card2 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
          exact Vector.getElem_set_self suit.isLt
        rw [hEqFin, hacesFinalSuit] at heqHyp
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
          show (gameF.aces.set suit.val card2 suit.isLt)[
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
  have suitCleanNe : ∀ K : Vector UInt8 4, (∀ s : Fin 4, s ≠ suit → K.get s = gameF.kings.get s) →
      ∀ s : Fin 4, s ≠ suit →
      SuitClean g (gameFinalOf K) s (fun i => (pileBaseFinal K i).pileDepth_bound) := by
    intro K hKframe s hsS
    have hbOld := hmergedF.suitClean s
    have hacesEq : acesFinal.get s = gameF.aces.get s := by
      rw [hacesFinalDef]
      show (gameF.aces.set suit.val card2 suit.isLt)[s.val]'s.isLt =
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
    by_cases hcOld : (VALUE c).toNat ≤ (VALUE (gameF.aces.get suit)).toNat
    · exact hbOld.foundation_cards_free c hSc hVc1 hcOld
    · push Not at hcOld
      have hs_c := SUIT_toNat c; have hv_c := VALUE_toNat c
      have hs_A := SUIT_toNat (gameF.aces.get suit)
      have hv_A := VALUE_toNat (gameF.aces.get suit)
      have hSameSuit : (SUIT c).toNat = (SUIT (gameF.aces.get suit)).toNat := by
        rw [hSc, hAFsuit]
      have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
      have hSeqAFc2 : (SUIT card2).toNat = (SUIT (gameF.aces.get suit)).toNat := by
        rw [hSuitCard2, hAFsuit]
      set l := c.toNat - (gameF.aces.get suit).toNat with hldef
      have hl1 : 1 ≤ l := by omega
      have hlfound : (l : Int) ≤ foundF.toInt := by
        have hci := hcard2eqA
        omega
      have hAl256 : (gameF.aces.get suit).toNat + l < 256 := by
        have := c.toNat_lt; omega
      have hceq : c = (gameF.aces.get suit) + UInt8.ofNat l :=
        uint8_eq_add_ofNat_of_toNat_eq hAl256 (by omega)
      rw [hceq]
      exact hfoundfreeF l hl1 hlfound
  have hUsedSpaceDefFinal : (gameF.usedSpace - foundF).toInt = (52 : Int)
      - (gameF.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat)
      - (acesFinal.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          gameF.pileDepth.toList gameF.pileFlute.toList |>.foldl (· + ·) 0 : Nat) := by
    have has_ := aces_sum_foldl_set gameF.aces suit.val suit.isLt card2
    rw [← hacesFinalDef] at has_
    have hAFidxEq : (gameF.aces[suit.val]'suit.isLt) = gameF.aces.get suit := rfl
    rw [hAFidxEq] at has_
    have hmergedU := hmergedF.usedSpace_def
    have hVAeq : (VALUE (gameF.aces.get suit)).toNat + foundF.toInt.toNat =
        (VALUE card2).toNat := by
      have hsa := SUIT_toNat (gameF.aces.get suit)
      have hva := VALUE_toNat (gameF.aces.get suit)
      have hsc := SUIT_toNat card2; have hvc := VALUE_toNat card2
      have hSeq : (SUIT (gameF.aces.get suit)).toNat = (SUIT card2).toNat := by
        rw [hAFsuit, hSuitCard2]
      have hci := hcard2eqA
      omega
    have hcardVAL : (VALUE card2).toNat = (VALUE card2).toNat := rfl
    rw [hcardVAL] at has_
    have husedBound := usedSpace_bounded hwf hmergedF.toSolverInvBase
    -- The counting argument's ace-side mirror (`usedSpace_ge_found_run`,
    -- extracted from `usedSpace_bounded`'s disjointness proof): the `foundF`
    -- cards the ace walk absorbed are all distinct from every card the
    -- layout is currently charging for, so `usedSpace` must already have
    -- room for them.  `hAboveCard2` (proved above) is exactly the fact
    -- ruling out double-counting against another pile's own flute run.
    have hfBound : (foundF.toInt : Int) ≤ gameF.usedSpace.toInt := by
      have hVcard2_le13 : (VALUE card2).toNat ≤ 13 := by
        have hs1 := SUIT_toNat card2; have hv1 := VALUE_toNat card2
        have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
        have hSeq : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
        omega
      have hfound_le13 : foundF.toInt.toNat ≤ 13 - (VALUE (gameF.aces.get suit)).toNat := by
        have := hVAeq; omega
      have hfoundfree' : ∀ l, 1 ≤ l → l ≤ foundF.toInt.toNat →
          isFreeCard g gameF ((gameF.aces.get suit) + UInt8.ofNat l) := by
        intro l hl1 hlle
        exact hfoundfreeF l hl1 (by omega)
      have hcard2natEq : card2.toNat = (gameF.aces.get suit).toNat + foundF.toInt.toNat := by
        have := hcard2eqA; omega
      have hAboveAll' : ∀ (i : Fin 10) (hdi : (gameF.pileDepth.get i).toNat > 0),
          SUIT ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
              by have := hmergedF.pileDepth_bound i; omega⟩) = suit.val.toUInt8 →
          (gameF.aces.get suit).toNat + foundF.toInt.toNat + (gameF.pileFlute.get i).toNat <
            ((g.pos2card.get i).get ⟨(gameF.pileDepth.get i).toNat - 1,
              by have := hmergedF.pileDepth_bound i; omega⟩ : UInt8).toNat := by
        intro i hdi hSB
        have hb := hAboveCard2 i hdi hSB
        omega
      exact usedSpace_ge_found_run hwf hmergedF.toSolverInvBase suit foundF.toInt.toNat
        hfound_le13 hfoundfree' hAboveAll'
    have hsub : (gameF.usedSpace - foundF).toInt = gameF.usedSpace.toInt - foundF.toInt := by
      rw [UInt8.toInt_sub]
      omega
    have hAcesSumEq : (acesFinal.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 :
        Nat) =
        (gameF.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat) +
          foundF.toInt.toNat := by omega
    rw [hAcesSumEq, hsub, hmergedU]
    have hfoundToNat : (foundF.toInt.toNat : Int) = foundF.toInt := by omega
    have hfoldEq : (gameF.pileDepth.toList.foldl (fun acc d => acc + d.toInt.toNat) 0 : Nat) =
        (gameF.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat) := rfl
    push_cast
    omega
  by_cases hVC : (VALUE card2 == (13 : UInt8)) = true
  · simp only [hVC, reduceIte, EStateM.bind, EStateM.set, EStateM.pure, ← hcard2def]
    have hVC13 : (VALUE card2).toNat = 13 := by
      have h := hVC; rw [beq_iff_eq] at h
      rw [h]; decide
    refine ⟨forcedKingsF, _, rfl, ?_, ?_, ?_, hloopDepth⟩
    set kingsFinal : Vector UInt8 4 :=
      gameF.kings.set suit.val card2 suit.isLt with hkingsFinalDef
    have hkingsFinalEq : kingsFinal = gameF.kings.set suitU32.toNat card2 hidx4 := by
      rw [hkingsFinalDef]; exact hsetEq gameF.kings card2
    have hkingsFrame : ∀ s : Fin 4, s ≠ suit → kingsFinal.get s = gameF.kings.get s := by
      intro s hsS
      rw [hkingsFinalDef]
      show (gameF.kings.set suit.val card2 suit.isLt)[s.val]'s.isLt =
        gameF.kings[s.val]'s.isLt
      apply Vector.getElem_set_ne suit.isLt s.isLt
      intro hcon
      exact hsS (Fin.ext hcon.symm)
    have hgameFinalOfEq : gameFinalOf kingsFinal = { gameF with aces := gameF.aces.set suitU32.toNat card2 hidx4, kings := gameF.kings.set suitU32.toNat card2 hidx4, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } := by
      show { gameF with aces := acesFinal, kings := kingsFinal, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } = _
      rw [hacesFinalEq, hkingsFinalEq]
    rw [← hgameFinalOfEq]
    refine SolverInvMerged.of_base ⟨pileBaseFinal kingsFinal, ?_, ?_, ?_, hbusyAces_lt16Final⟩
      (pileMergedFinal kingsFinal) ?_
    · intro s
      by_cases hsS : s = suit
      · subst hsS
        have hbOld := hmergedF.suitClean suit
        have hacesEq : acesFinal.get suit = card2 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
          exact Vector.getElem_set_self suit.isLt
        have hkingsEq : kingsFinal.get suit = card2 := by
          rw [hkingsFinalDef]
          show (gameF.kings.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
          exact Vector.getElem_set_self suit.isLt
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hacesEq, hkingsEq]
          exact ⟨hSuitCard2, hVC13.le, hSuitCard2, hVC13.le, UInt8.le_refl _⟩
        · intro c hSc hVc1 hVc2
          rw [hacesEq] at hVc2
          exact hFoundationCardsFreeSuit c hSc hVc1 hVc2
        · rw [hacesEq]
          exact Or.inl hVC13
        · rw [hacesEq, hkingsEq]
          refine ⟨Or.inl ⟨rfl, Or.inl hVC13⟩, ?_⟩
          intro c hSc hVc1 hVc2
          exfalso
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
    refine ⟨forcedKingsF, _, rfl, ?_, ?_, ?_, hloopDepth⟩
    have hVCne13 : (VALUE card2).toNat ≠ 13 := by
      intro h13
      apply hVC
      rw [beq_iff_eq]
      apply UInt8.toNat_inj.mp
      rw [h13]; decide
    have hkingsFrame : ∀ s : Fin 4, s ≠ suit → gameF.kings.get s = gameF.kings.get s :=
      fun s _ => rfl
    have hgameFinalOfEq : gameFinalOf gameF.kings = { gameF with aces := gameF.aces.set suitU32.toNat card2 hidx4, kings := gameF.kings, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } := by
      show { gameF with aces := acesFinal, kings := gameF.kings, usedSpace := gameF.usedSpace - foundF, busyAces := gameF.busyAces - ((1 : UInt8) <<< suit.val.toUInt8) } = _
      rw [hacesFinalEq]
    rw [← hgameFinalOfEq]
    refine SolverInvMerged.of_base ⟨pileBaseFinal gameF.kings, ?_, ?_, ?_, hbusyAces_lt16Final⟩
      (pileMergedFinal gameF.kings) ?_
    · intro s
      by_cases hsS : s = suit
      · subst hsS
        have hbOld := hmergedF.suitClean suit
        have hacesEq : acesFinal.get suit = card2 := by
          rw [hacesFinalDef]
          show (gameF.aces.set suit.val card2 suit.isLt)[suit.val]'suit.isLt = card2
          exact Vector.getElem_set_self suit.isLt
        have hAKvalid := hbOld.aces_kings_valid
        have hVK13 := hAKvalid.2.2.2.1
        have hSK := hAKvalid.2.2.1
        -- `cardF` is real (`≤ 13`): if it were the value-14 sentinel,
        -- `card2`'s value would be exactly `13` (`hVcard2eq13From`),
        -- contradicting `hVCne13`.
        have hcardFle13 : (VALUE cardF).toNat ≤ 13 := by
          by_contra hcon
          push Not at hcon
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
          have hcardFgtA : (VALUE cardF).toNat > (VALUE (gameF.aces.get suit)).toNat := by
            have hs_cF := SUIT_toNat cardF; have hv_cF := VALUE_toNat cardF
            have hs_A := SUIT_toNat (gameF.aces.get suit)
            have hv_A := VALUE_toNat (gameF.aces.get suit)
            have hSeq : (SUIT cardF).toNat = (SUIT (gameF.aces.get suit)).toNat := by
              rw [hsuitcardF, hAFsuit]
            have hci := hcardeqF
            omega
          have hVcardFgtK : (VALUE cardF).toNat > (VALUE (gameF.kings.get suit)).toNat :=
            by rw [heqAK]; exact hcardFgtA
          exact hbOld.king_frontier.2 cardF hsuitcardF hVcardFgtK hcardFle13
        · have hVcardFleK : (VALUE cardF).toNat ≤ (VALUE (gameF.kings.get suit)).toNat :=
            by
            by_contra hcon
            push Not at hcon
            exact hnf (hbOld.king_frontier.2 cardF hsuitcardF hcon hcardFle13)
          have hcard2ltK_nat : card2.toNat < (gameF.kings.get suit).toNat := by
            have hs_c2 := SUIT_toNat card2; have hv_c2 := VALUE_toNat card2
            have hs_cF := SUIT_toNat cardF; have hv_cF := VALUE_toNat cardF
            have hs_K := SUIT_toNat (gameF.kings.get suit)
            have hv_K := VALUE_toNat (gameF.kings.get suit)
            have hSeq1 : (SUIT card2).toNat = (SUIT cardF).toNat := by rw [hSuitCard2, hsuitcardF]
            have hSeq2 : (SUIT cardF).toNat = (SUIT (gameF.kings.get suit)).toNat := by
              rw [hsuitcardF, hSK]
            omega
          have hcard2ltK : card2 < gameF.kings.get suit := by
            apply UInt8.lt_iff_toInt_lt.mpr
            have hSC24 : (SUIT card2).toNat < 4 := by
              rw [hSuitCard2]; have := suit.isLt; have h := finVal_toUInt8_toNat suit; omega
            have hsvc2 := SUIT_toNat card2; have hvvc2 := VALUE_toNat card2
            simp only [UInt8.toInt_eq]
            exact_mod_cast hcard2ltK_nat
          have hcard2leK : card2 ≤ gameF.kings.get suit :=
            UInt8.le_iff_toInt_le.mpr (le_of_lt (UInt8.lt_iff_toInt_lt.mp hcard2ltK))
          refine ⟨⟨?_, ?_, hSK, hVK13, ?_⟩, ?_, ?_, ?_⟩
          · rw [hacesEq]; exact hSuitCard2
          · rw [hacesEq]; exact hVcard2le13
          · rw [hacesEq]; exact hcard2leK
          · intro c hSc hVc1 hVc2
            rw [hacesEq] at hVc2
            exact hFoundationCardsFreeSuit c hSc hVc1 hVc2
          · rw [hacesEq]
            exact Or.inr (Or.inl (by rw [hcard2p1]; exact hnf))
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

end SolverSpec
