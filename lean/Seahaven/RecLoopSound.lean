import Seahaven.RecStepSound
import Seahaven.KingMoveSim

/-!
# Soundness of `solverRecCheckSolvable`'s pile loop

The loop accumulates `solvable := solvable ||| movable''` over the ten piles
(`Solver.lean:436-456`), and its invariant is exactly

> **every configuration in the `subsetTable` expansion of `solvable` really is
> solvable** — `SoundBits g p solvable` — together with `LocalMask p solvable`,
> which keeps the expansion meaningful.

This file proves that the invariant is established (`SoundBits.zero`) and
maintained, and concludes it for the value the loop returns.

## The two halves

*Per contribution* (`contribution_sound`): one pile's `movable''` is sound.  This
is where the three semantic ingredients meet — `SubsetSound` to get from "the
expansion contains `k`" to a *local* bit and a reachable configuration,
`recStep_sound` for that bit, and `componentSound` for the `component` widening.

*Per loop* (`recLoop_sound`): `SoundBits` is closed under `|||`
(`SoundBits.union`, already proved), so the accumulation is a straight induction
over the pile list.

## Why the body is duplicated

`recBody` below is the explicit twin of the loop body, with the recursive call
abstracted as a parameter `rec` — the same device `componentExplicit`/`drainBody`
use elsewhere.  `solverRecCheckSolvable` is defined by `partial_fixpoint`, so it
*does* have an unfolding equation, and `recCheck_eq` below identifies its pile
loop with `recBody solverRecCheckSolvable …`; the twin is what lets the loop
lemmas be stated and proved before that identification.
-/

open Lean Lean.Order

/-! ## Bit-level helpers -/

/-- A non-zero mask has a set bit. -/
theorem exists_bitSet {w : UInt16} (h : w ≠ 0) : ∃ j : Fin 16, BitSet w j := by
  by_contra hc
  push Not at hc
  refine h (UInt16.toNat_inj.1 ?_)
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  rw [show (0 : UInt16).toNat = 0 from rfl, Nat.zero_testBit]
  by_cases hi : i < 16
  · have := hc ⟨i, hi⟩
    rw [BitSet_toNat] at this
    simpa using this
  · exact Nat.testBit_lt_two_pow (by
      calc w.toNat < 65536 := w.toNat_lt_size
        _ = 2 ^ 16 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))

/-- A local mask only sets bits inside its block. -/
theorem lt_numBits_of_bitSet {p : SolverPosType} {v : UInt16} (hloc : LocalMask p v) {j : Fin 16}
    (hj : BitSet v j) : j.val < (closureInfoOf p).numBits.toNat := by
  by_contra hc
  rw [BitSet_toNat] at hj
  refine absurd hj (by
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hloc
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp)

/-! ## One pile's contribution

`movable''` as the code builds it, with `comp` the `componentTable` entry and
`cs` the recursive call's answer. -/

/-- The `movable'` of `Solver.lean:450-452`. -/
def movablePrime (p p' : SolverPosType) (mv cs fk : UInt16) : UInt16 :=
  mv &&& (subsetAt ((closureInfoOf p').offset.toNat +
    (cs &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat)
      >>> (closureInfoOf p).shiftValue.toUInt16)

/-- The `movable''` of `Solver.lean:453`. -/
def movableComp (mv' comp : UInt16) : UInt16 :=
  if mv' &&& comp ≠ 0 then mv' ||| comp else mv'

theorem localMask_movablePrime {p p' : SolverPosType} {mv cs fk : UInt16} (h : LocalMask p mv) :
    LocalMask p (movablePrime p p' mv cs fk) := LocalMask.and_left _ h

theorem localMask_or {p : SolverPosType} {a b : UInt16}
    (ha : LocalMask p a) (hb : LocalMask p b) : LocalMask p (a ||| b) := by
  rw [LocalMask, UInt16.toNat_or]
  exact Nat.or_lt_two_pow ha hb

theorem localMask_movableComp {p : SolverPosType} {mv' comp : UInt16}
    (h : LocalMask p mv') (hc : LocalMask p comp) : LocalMask p (movableComp mv' comp) := by
  unfold movableComp
  split
  · exact localMask_or h hc
  · exact h

/-- **One pile's contribution to `solvable` is sound.**

Read the three uses in order.  `SubsetSound` turns the queried configuration `k`
into a *local* bit `i` of `movable''` together with a state reachable from `s`
that stands for `i`'s configuration — this is the only step that can move between
configurations of the *same* block, and it is why `SoundBits` is phrased over the
expansion at all.  If bit `i` survived into `movable'`, `recStep_sound` finishes:
the move is affordable at `i` and the child's answer covers what it reaches.
Otherwise bit `i` came from `component`, and `componentSound` transports the
reachability to a bit `j` that *is* in `movable'` — which exists precisely because
the code only ORs `component` in when `movable' &&& component ≠ 0`. -/
theorem contribution_sound (hSS : SubsetSound) (hMS : MoveSimulated)
    {g : Globals} {p p' : SolverPosType} {pile : UInt32} {toPile : UInt8}
    {mv cs fk : UInt16} {comp : UInt8} {kingInfo : KingInfo}
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hmvloc : LocalMask p mv)
    (hcomprun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hkic : KingInfoCorrect p kingInfo)
    (hpile : pile.toNat < 10)
    (hdepth : 0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat)
    (hdest : EStateM.run (solverGetDestination p pile) g = .ok toPile g)
    (hmv : EStateM.run (solverGetMovable kingInfo (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g)
    (hrun : EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p'))
    (hcs : LocalMask p' cs) (hchild : SoundBits g p' cs) :
    SoundBits g p (movableComp (movablePrime p p' mv cs fk) comp.toUInt16) := by
  intro s k hs hbit
  have hmvloc' : LocalMask p (movablePrime p p' mv cs fk) := localMask_movablePrime hmvloc
  have hloc : LocalMask p (movableComp (movablePrime p p' mv cs fk) comp.toUInt16) :=
    localMask_movableComp hmvloc' (localMask_component hcomprun)
  -- the queried configuration reaches a configuration named by a local bit
  obtain ⟨i, hi, hbiti, hreach⟩ :=
    hSS g p s _ k hloc hwf hcanon.toSolverInvMerged
      ⟨s, Relation.ReflTransGen.refl, hs⟩ hbit
  -- that bit is in `movable'`, or `component` put it there
  have hstep : ∀ (n : Nat) (hn : n < (closureInfoOf p).numBits.toNat),
      BitSet (movablePrime p p' mv cs fk) ⟨min n 15, by omega⟩ →
      KingConfigReachable g p s (globalCfg (closureInfoOf p) n) → Solvable s := by
    intro n hn hbn ⟨s1, hr1, hs1⟩
    refine Solvable.of_reach hr1
      (recStep_sound hMS hn hwf hcanon hs1 hkic hpile hdepth hdest hmv hrun hcs hchild ?_)
    exact hbn
  by_cases hmv' : BitSet (movablePrime p p' mv cs fk) ⟨min i 15, by omega⟩
  · exact hstep i hi hmv' hreach
  · -- bit `i` is a component bit, and some component bit is movable
    unfold movableComp at hbiti
    have hne : movablePrime p p' mv cs fk &&& comp.toUInt16 ≠ 0 := by
      by_cases hne : movablePrime p p' mv cs fk &&& comp.toUInt16 ≠ 0
      · exact hne
      · rw [if_neg hne] at hbiti; exact absurd hbiti hmv'
    rw [if_pos hne, BitSet_or] at hbiti
    have hci : BitSet comp.toUInt16 ⟨min i 15, by omega⟩ := hbiti.resolve_left hmv'
    -- a bit that is both movable and in the component
    obtain ⟨j, hj⟩ := exists_bitSet hne
    rw [BitSet_and] at hj
    have hjlt : j.val < (closureInfoOf p).numBits.toNat := lt_numBits_of_bitSet hmvloc' hj.1
    have hjeq : (⟨min j.val 15, by omega⟩ : Fin 16) = j :=
      Fin.ext (min_eq_left (by omega : j.val ≤ 15))
    refine hstep j.val hjlt (by rw [hjeq]; exact hj.1) ?_
    exact componentSound g p s comp i j.val hwf hcanon.toSolverInvMerged hcomprun hi hjlt
      hci (by rw [hjeq]; exact hj.2) hreach

/-! ## The loop invariant -/

/-- **The invariant of `solverRecCheckSolvable`'s pile loop.**  The last two
fields are the invariant proper — *a set bit really means solvable*, and the
accumulator stays inside its block so that the expansion is meaningful.  The
first three are what the loop reads and the recursive call must not disturb:
they are constant across the loop because the only state the call writes is the
memo table. -/
structure LoopInv (p : SolverPosType) (comp : UInt8) (v : UInt16) (g : Globals) : Prop where
  wf : WellFormedLayout g
  canon : IsCanonicalPos g p
  comprun : EStateM.run (computeComponentKingBits p) g = .ok comp g
  sound : SoundBits g p v
  isLocal : LocalMask p v

/-- **The invariant holds at entry**: `solvable` starts at `0`, whose expansion is
empty. -/
theorem LoopInv.zero {p : SolverPosType} {comp : UInt8} {g : Globals}
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hcomprun : EStateM.run (computeComponentKingBits p) g = .ok comp g) :
    LoopInv p comp 0 g where
  wf := hwf
  canon := hcanon
  comprun := hcomprun
  sound := SoundBits.zero g p
  isLocal := by
    have : (0 : UInt16).toNat = 0 := rfl
    simp only [LocalMask, this]
    exact Nat.two_pow_pos _

/-- **What the recursive call must leave alone.**  It writes only the memo table
(`setSlot`, `Solver.lean:252-256`), and every clause of `LoopInv` reads only the
deal arrays — `SoundBits`/`StateMatchesKingConfig` through `pos2card`
(`StateMatchesSolverPos.hashmap_iff`), `computeComponentKingBits` not at all. -/
def LoopFrame (p : SolverPosType) (comp : UInt8) (g g' : Globals) : Prop :=
  (WellFormedLayout g → WellFormedLayout g') ∧
  (IsCanonicalPos g p → IsCanonicalPos g' p) ∧
  (EStateM.run (computeComponentKingBits p) g = .ok comp g →
    EStateM.run (computeComponentKingBits p) g' = .ok comp g') ∧
  (∀ w : UInt16, SoundBits g p w → SoundBits g' p w)

/-- **What one iteration of the pile loop does to the accumulator.**  Either
nothing — the pile is empty, or `movable` adds no bit the accumulator lacks, or
the loop is about to stop — or it ORs in the `movable''` of one real move, whose
data this records: the destination, the mask `solverGetMovable` returned, the
successor position `SolverMove` produced and the answer the recursion gave for
it.

Everything but the frame is stated at the iteration's *entry* globals: the move
and the mask are computed before the recursive call, and the call is the only
thing in the body that writes state. -/
def Contributes (p : SolverPosType) (kingInfo : KingInfo) (comp : UInt8)
    (v : UInt16) (g : Globals) (v' : UInt16) (g' : Globals) : Prop :=
  (v' = v ∧ g' = g) ∨
  ∃ (p' : SolverPosType) (pile : UInt32) (toPile : UInt8) (mv cs fk : UInt16),
    LocalMask p mv ∧
    pile.toNat < 10 ∧
    0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat ∧
    EStateM.run (solverGetDestination p pile) g = .ok toPile g ∧
    EStateM.run (solverGetMovable kingInfo (closureInfoOf p).shiftValue
      (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g ∧
    EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
    LocalMask p' cs ∧ SoundBits g p' cs ∧
    (∃ g'' : Globals, EStateM.run (solverRecCheckSolvable p') g = .ok cs g'') ∧
    v' = v ||| movableComp (movablePrime p p' mv cs fk) comp.toUInt16 ∧
    LoopFrame p comp g g'

/-- **The invariant is maintained.**  `SoundBits` is closed under `|||`
(`SoundBits.union`), so the whole step is: the old accumulator stays sound
(frame), the new contribution is sound (`contribution_sound`), and both are
local. -/
theorem LoopInv.step (hSS : SubsetSound) (hMS : MoveSimulated)
    {p : SolverPosType} {kingInfo : KingInfo} {comp : UInt8} {v v' : UInt16} {g g' : Globals}
    (hcomploc : LocalMask p comp.toUInt16) (hkic : KingInfoCorrect p kingInfo)
    (h : LoopInv p comp v g) (hc : Contributes p kingInfo comp v g v' g') :
    LoopInv p comp v' g' := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨p', pile, toPile, mv, cs, fk, hmvloc, hpile, hdepth, hdest, hmv,
    hrun, hcs, hchild, -, rfl, hframe⟩
  · exact h
  · obtain ⟨hwf, hcanon, hcomprun, hsound⟩ := hframe
    have hcontrib : SoundBits g p (movableComp (movablePrime p p' mv cs fk) comp.toUInt16) :=
      contribution_sound hSS hMS h.wf h.canon hmvloc h.comprun hkic hpile hdepth hdest hmv hrun
        hcs hchild
    have hlocmv : LocalMask p (movableComp (movablePrime p p' mv cs fk) comp.toUInt16) :=
      localMask_movableComp (localMask_movablePrime hmvloc) hcomploc
    exact
      { wf := hwf h.wf
        canon := hcanon h.canon
        comprun := hcomprun h.comprun
        sound := SoundBits.union h.isLocal hlocmv (hsound _ h.sound) (hsound _ hcontrib)
        isLocal := localMask_or h.isLocal hlocmv }

/-! ## The loop -/

/-- A `forIn` over a list preserves any invariant its body preserves. -/
theorem forIn_inv {β : Type} (P : β → Globals → Prop)
    (body : Nat → β → EStateM Error Globals (ForInStep β)) :
    ∀ (l : List Nat),
      (∀ a ∈ l, ∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
        P b g → body a b g = .ok r g' → P r.value g') →
      ∀ (b : β) (g : Globals) (b' : β) (g' : Globals),
        P b g → forIn l b body g = .ok b' g' → P b' g' := by
  intro l
  induction l with
  | nil =>
    intro _ b g b' g' hP hrun
    rw [List.forIn_nil] at hrun
    simp only [pure, EStateM.pure] at hrun
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
    exact hP
  | cons a l ih =>
    intro hstep b g b' g' hP hrun
    rw [List.forIn_cons] at hrun
    simp only [bind, EStateM.bind] at hrun
    cases hba : body a b g with
    | error e g'' => rw [hba] at hrun; simp at hrun
    | ok r g'' =>
      rw [hba] at hrun
      have hPr : P r.value g'' := hstep a (by simp) b g r g'' hP hba
      cases r with
      | done c =>
        simp only [pure, EStateM.pure] at hrun
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
        exact hPr
      | yield c =>
        exact ih (fun x hx => hstep x (by simp [hx])) c g'' b' g' hPr hrun

/-- **The pile loop is sound.**  Every iteration either leaves `solvable` alone or
ORs in a sound contribution, so the value the loop returns satisfies the
invariant: *a set bit in its `subsetTable` expansion means the state really is
solvable*. -/
theorem recLoop_sound (hSS : SubsetSound) (hMS : MoveSimulated)
    {p : SolverPosType} {kingInfo : KingInfo} {comp : UInt8}
    (hcomploc : LocalMask p comp.toUInt16) (hkic : KingInfoCorrect p kingInfo)
    {body : Nat → UInt16 → EStateM Error Globals (ForInStep UInt16)} {l : List Nat}
    (hbody : ∀ a ∈ l, ∀ (v : UInt16) (g : Globals) (r : ForInStep UInt16) (g' : Globals),
      body a v g = .ok r g' → Contributes p kingInfo comp v g r.value g')
    {v v' : UInt16} {g g' : Globals}
    (hinv : LoopInv p comp v g) (hrun : forIn l v body g = .ok v' g') :
    LoopInv p comp v' g' :=
  forIn_inv (LoopInv p comp) body l
    (fun a ha b gg r gg' hP hb => hP.step hSS hMS hcomploc hkic (hbody a ha b gg r gg' hb)) v g v' g'
    hinv hrun

/-- **From an empty accumulator**, which is how the loop starts. -/
theorem recLoop_sound_zero (hSS : SubsetSound) (hMS : MoveSimulated)
    {p : SolverPosType} {kingInfo : KingInfo} {comp : UInt8}
    (hcomploc : LocalMask p comp.toUInt16) (hkic : KingInfoCorrect p kingInfo)
    {body : Nat → UInt16 → EStateM Error Globals (ForInStep UInt16)} {l : List Nat}
    (hbody : ∀ a ∈ l, ∀ (v : UInt16) (g : Globals) (r : ForInStep UInt16) (g' : Globals),
      body a v g = .ok r g' → Contributes p kingInfo comp v g r.value g')
    {v' : UInt16} {g g' : Globals}
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hcomprun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hrun : forIn l (0 : UInt16) body g = .ok v' g') :
    SoundBits g' p v' ∧ LocalMask p v' :=
  let h := recLoop_sound hSS hMS hcomploc hkic hbody (LoopInv.zero hwf hcanon hcomprun) hrun
  ⟨h.sound, h.isLocal⟩

/-! ## The loop body of `solverRecCheckSolvable`

`recBody` is the explicit twin of the pile loop's body (`Solver.lean:449-473`),
with the recursive call abstracted as `rec` — the device
`componentExplicit`/`drainBody` use elsewhere.  `recCheck_eq` below instantiates
it with `solverRecCheckSolvable` itself. -/

def recBody (rec : SolverPosType → EStateM Error Globals UInt16) (game : SolverPosType)
    (ci : ClosureInfo) (kingInfo : KingInfo) (component allkings : UInt16) :
    Nat → UInt16 → EStateM Error Globals (ForInStep UInt16) :=
  fun pile solvable => do
    let pileU32 := UInt32.ofNat pile
    if (← game.pileDepth.getE pileU32) == 0 then
      return .yield solvable
    let fluteLen ← game.pileFlute.getE pileU32
    let toPile ← solverGetDestination game pileU32
    let movable ← solverGetMovable kingInfo ci.shiftValue fluteLen toPile
    if movable &&& ~~~solvable != 0 then
      let globals ← get
      match EStateM.run (SolverMove pileU32 toPile) (globals, game) with
      | .ok forcedKings (newGlobals, childGame) =>
        set newGlobals
        let nci ← closureInfos.getE childGame.freePiles.toInt32.toUInt32
        let childSolvable ← rec childGame
        let childSolvable' := childSolvable &&& (forcedKings >>> nci.shiftValue.toUInt16)
        let movable' := movable &&&
          ((← subsetTable.getE (nci.offset.toUInt32 + childSolvable'.toUInt32))
            >>> ci.shiftValue.toUInt16)
        let movable'' := if movable' &&& component != 0 then movable' ||| component else movable'
        let sol := solvable ||| movable''
        if sol == allkings then return .done sol else return .yield sol
      | .error e _ => throw e
    else
      return .yield solvable

/-- **The real function, one level unfolded**, with its pile loop presented as
`forIn … (recBody solverRecCheckSolvable …)` so that `recLoop_body_sound` applies
to it.

This is what `partial_fixpoint` buys: a `partial def` has no unfolding equation at
all, so no statement about `solverRecCheckSolvable` was provable.  With the
equation in hand, the recursion is handled exactly as the `busyAces` drain loop is
(`SolverSpec.drainBody_run`): induct on a `Nat` bounding the measure — here
`DepthSum game`, which `move_merged` shows strictly drops at every child — and
rewrite with this lemma once per level.  The measure therefore never appears at
the definition site, which is why `Solver.lean` can stay a verbatim transcription.

`conv_lhs` is needed because a bare `rw` would also unfold the copy of
`solverRecCheckSolvable` on the right-hand side. -/
theorem recCheck_eq (game : SolverPosType) :
    solverRecCheckSolvable game = (do
      if game.hash == 0 then return 1
      let closureInfo ← closureInfos.getE game.freePiles.toInt32.toUInt32
      let cachedValue ← getSlot game.hash
      if cachedValue != 0xff then
        return cachedValue.toUInt16
      let kingInfo ← computeKingSpaces closureInfo.shiftValue closureInfo.numBits game
      let allkings := (← kingInfo.possibleKings.getE 0).toUInt16
      let component := (← computeComponentKingBits game).toUInt16
      let solvable ← forIn (List.range 10) (0 : UInt16)
        (recBody solverRecCheckSolvable game closureInfo kingInfo component allkings)
      setSlot game.hash solvable
      return solvable) := by
  conv_lhs => rw [solverRecCheckSolvable.eq_def]
  rfl

/-- **The one syntactic obligation left**: reading the body off the code.  Every
branch of `recBody` either returns the accumulator unchanged or ORs in the
`movable''` of one real move, which is what `Contributes` records.

Discharging it is monadic bookkeeping, and needs exactly five run lemmas, none of
them about solvability:

* `solverGetDestination` and `solverGetMovable` leave `Globals` alone (they only
  read tables), so their results are available in the `.ok v g` form
  `MoveSimulated` wants;
* `SolverMove` leaves `Globals` alone — it threads `(globals, game)` and writes
  back the same `globals` (`Solver.lean:381-390`), and the phase specs
  `removeFlute_merged` / `drain_canonical_of` already return it unchanged;
* `closureInfos.getE childGame.freePiles… = closureInfoOf childGame`, from
  `freePiles ≤ 10` (`SolverInvMerged`), exactly as in `component_run_eq`;
* `subsetTable.getE (nci.offset + childSolvable') = subsetAt (offset + …)`, from
  `LocalMask childGame childSolvable'` and the per-block bound
  `offset + 2 ^ numBits ≤ 100`.

The recursion's own contribution — `SoundBits`, `LocalMask` and `LoopFrame` for
the child call — is the induction hypothesis of the eventual well-founded
induction, and enters here as `hrec`. -/
def RecBodyContributes (rec : SolverPosType → EStateM Error Globals UInt16)
    (p : SolverPosType) (kingInfo : KingInfo) (comp : UInt8) (allkings : UInt16) : Prop :=
  ∀ (pile : Nat), pile < 10 → ∀ (v : UInt16) (g : Globals) (r : ForInStep UInt16) (g' : Globals),
    recBody rec p (closureInfoOf p) kingInfo comp.toUInt16 allkings pile v g = .ok r g' →
    Contributes p kingInfo comp v g r.value g'

/-- **`solvable` is sound when the loop returns it.**  The invariant of the pile
loop, run to the end: every configuration in the `subsetTable` expansion of the
returned mask really is solvable, and the mask stays inside its block.

This is the statement `solverRecCheckSolvable`'s memo write and return value need
(`SolvableBits`' soundness half), with the loop reduced to its three inputs: the
per-contribution soundness proved here, the body-reading obligation above, and
the induction hypothesis inside it. -/
theorem recLoop_body_sound (hSS : SubsetSound) (hMS : MoveSimulated)
    {rec : SolverPosType → EStateM Error Globals UInt16}
    {p : SolverPosType} {kingInfo : KingInfo} {comp : UInt8} {allkings : UInt16}
    (hcomploc : LocalMask p comp.toUInt16) (hkic : KingInfoCorrect p kingInfo)
    (hbody : RecBodyContributes rec p kingInfo comp allkings)
    {v' : UInt16} {g g' : Globals}
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hcomprun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hrun : forIn (List.range 10) (0 : UInt16)
      (recBody rec p (closureInfoOf p) kingInfo comp.toUInt16 allkings) g = .ok v' g') :
    SoundBits g' p v' ∧ LocalMask p v' :=
  recLoop_sound_zero hSS hMS hcomploc hkic
    (fun a ha v gg r gg' hb => hbody a (by simpa using ha) v gg r gg' hb)
    hwf hcanon hcomprun hrun
