import Seahaven.CleanupSim
import Seahaven.SoundnessSkeleton

/-!
# King configurations through the simulation

Tools for carrying a king configuration (`StateMatchesKingConfig`) through the
phases of `SolverMove`, together with the `forcedKings` bookkeeping
(`KingVacates`) that `MoveSimulated` demands.

## The `forcedKings` side

`SolverCleanupPile` factors as `preCleanupPile` then — in the lone-king case
only — `kingMove` (`cleanupRunResult_eq`).  Only `kingMove` vacates a king, so
the `forcedKings` description lives at that level: `kingMove_kingVacates` is the
single-vacate fact, `preCleanupPile` contributes the unit `KingVacates ∅ 0xffff`,
and `cleanupRunResult_kingVacates` dispatches over the factoring.  Whole-move
accumulation is `KingVacates.inter`, mirroring the code's
`forcedKings := forcedKings &&& …`.

## The configuration side

`RealizesKingConfig.mono` picks a sparser reading of the same state — the tool
for choosing `MoveSimulated`'s witness `k'`.  The `frame` lemmas transport
`OwnsPile`/`NoKingPile` across steps that leave the relevant pile, `kings` entry,
and column untouched; the per-phase instantiations ride the `Reach` chains the
matching simulations already build.
-/

/-! ## `forcedKings` values of the cleanup pieces -/

/-- The suit a solver-side `UInt8` suit code denotes. -/
def suitOfCode (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) : Suit :=
  natToSuit ⟨suit.toUInt32.toNat, hs4⟩

/-- **`kingMove` is the only vacate**: its `forcedKings` contribution is exactly
the `kingOnPileMap` row of the drained suit. -/
theorem kingMove_kingVacates (suit : UInt8) (hs4 : suit.toUInt32.toNat < 4) :
    KingVacates {suitOfCode suit hs4} (kingOnPileMap[suit.toUInt32.toNat]'hs4) := by
  have h := KingVacates.single (suitOfCode suit hs4)
  have hfin : finOfSuit (suitOfCode suit hs4) = ⟨suit.toUInt32.toNat, hs4⟩ :=
    Fin.ext (suitToNat_natToSuit _)
  rw [hfin] at h
  exact h

/-- The `forcedKings` component of a whole non-empty cleanup, over the
`preCleanupPile`/`kingMove` factoring: the lone-king branch vacates exactly the
boundary's suit, the ordinary branch nothing. -/
theorem cleanupRunResult_kingVacates (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4)
    (d32 : Int32) (m f : Nat) (p : SolverPosType)
    (hmf128 : (1 + (m : Int) + f) < 128) :
    KingVacates
      (if d32 - Int32.ofNat m == 1 && VALUE (B + UInt8.ofNat m) == 13
        then {suitOfCode (SUIT B) hs4} else ∅)
      (cleanupRunResult pile hpile B ph hs4 d32 m f p).1 := by
  rw [cleanupRunResult_eq pile hpile B ph hs4 d32 m f p hmf128]
  cases hk : (d32 - Int32.ofNat m == 1 && VALUE (B + UInt8.ofNat m) == 13)
  · simp only [Bool.false_eq_true, reduceIte]
    exact KingVacates.empty
  · simp only [reduceIte]
    have h := KingVacates.inter KingVacates.empty (kingMove_kingVacates (SUIT B) hs4)
    rwa [Finset.empty_union] at h

/-! ## Reading a state at a sparser configuration -/

/-- **Withholding assignments is always allowed**: a state realizing `k'` also
realizes any configuration `k''` whose piled (clear-bit) suits are among `k'`'s.
This is how the soundness chain picks `MoveSimulated`'s witness — e.g. a suit
whose run just drained to the foundation may own a spare empty pile, but nothing
forces that reading. -/
theorem RealizesKingConfig.mono {s : State} {p : SolverPosType} {k' k'' : Fin 16}
    (h : RealizesKingConfig s p k')
    (hsub : ∀ su : Suit, ¬ CfgBitSet k'' su → ¬ CfgBitSet k' su) :
    RealizesKingConfig s p k'' := by
  obtain ⟨assign, hown, hinj, hiff⟩ := h
  refine ⟨fun su => if CfgBitSet k'' su then none else assign su, ?_, ?_, ?_⟩
  · intro su i hi
    by_cases hc : CfgBitSet k'' su
    · simp [hc] at hi
    · simp only [hc, ite_false] at hi
      exact hown su i hi
  · intro su su' i hi hi'
    by_cases hc : CfgBitSet k'' su
    · simp [hc] at hi
    by_cases hc' : CfgBitSet k'' su'
    · simp [hc'] at hi'
    simp only [hc, hc', ite_false] at hi hi'
    exact hinj su su' i hi hi'
  · intro su
    by_cases hc : CfgBitSet k'' su
    · simp [hc]
    · simp only [hc, ite_false, hiff su, not_false_iff, iff_true]
      exact hsub su hc

/-! ## Clearing a bit: the configuration a vacate produces

A lone-king vacate piles one more suit, so it *clears* that suit's bit.  This is
the grlex-index level operation; both facts about it are decided over the tables. -/

theorem grlex2bits_lt (k : Fin 16) : (grlex2bits.get k).toNat < 16 := by
  fin_cases k <;> decide

/-- Configuration `k` with suit `su` additionally piled. -/
def clearCfgBit (k : Fin 16) (su : Suit) : Fin 16 :=
  ⟨(bits2grlex.get ⟨(grlex2bits.get k).toNat &&& (15 - 2 ^ suitToNat su), by
      have h := grlex2bits_lt k
      have hle : (grlex2bits.get k).toNat &&& (15 - 2 ^ suitToNat su)
          ≤ (grlex2bits.get k).toNat := Nat.and_le_left
      omega⟩).toNat, bits2grlex_lt _⟩

theorem clearCfgBit_self : ∀ (su : Suit) (k : Fin 16), ¬ CfgBitSet (clearCfgBit k su) su := by
  decide

theorem clearCfgBit_ne : ∀ (su su' : Suit) (k : Fin 16), su' ≠ su →
    (CfgBitSet (clearCfgBit k su) su' ↔ CfgBitSet k su') := by decide

/-! ## Frame lemmas -/

/-- `OwnsPile` only reads the pile's depth, the suit's `kings` entry, and the
column itself. -/
theorem OwnsPile.frame {s s' : State} {p p' : SolverPosType} {su : Suit} {i : Fin 10}
    (h : OwnsPile s p su i)
    (hd : p'.pileDepth.get i = p.pileDepth.get i)
    (hk : p'.kings.get (finOfSuit su) = p.kings.get (finOfSuit su))
    (ht : s'.tableau i = s.tableau i) : OwnsPile s' p' su i := by
  obtain ⟨hdep, hphys⟩ := h
  refine ⟨by rw [hd]; exact hdep, ?_⟩
  rcases hphys with hcard | ⟨hempty, hking⟩
  · exact Or.inl (by rw [ht]; exact hcard)
  · exact Or.inr ⟨by rw [ht]; exact hempty, by rw [hk]; exact hking⟩

/-- `NoKingPile` framing: piles that stay solver-empty keep their column, and a
pile may *become* solver-empty only if its new column carries nothing of the
suit — the two ways that happens in practice are a freshly drained source pile
(empty column) and a vacate for a *different* suit. -/
theorem NoKingPile.frame {s s' : State} {p p' : SolverPosType} {su : Suit}
    (h : NoKingPile s p su)
    (hframe : ∀ i : Fin 10, (p'.pileDepth.get i).toInt.toNat = 0 →
      ((p.pileDepth.get i).toInt.toNat = 0 ∧ s'.tableau i = s.tableau i) ∨
      (∀ d ∈ (s'.tableau i).getLast?, d.suit ≠ su)) :
    NoKingPile s' p' su := by
  intro i hd d hdlast
  rcases hframe i hd with ⟨hd0, ht⟩ | hnew
  · exact h i hd0 d (by rw [← ht]; exact hdlast)
  · exact hnew d hdlast

/-! ## `Simulates` for the two halves of a cleanup

`SolverCleanupPile` factors as `preCleanupPile` — merge plus the freed-predecessor
extension, the only card-moving part — and, in the lone-king case, `kingMove`
(`cleanupRunResult_eq`).  Each half gets its `Simulates`, and `Simulates.trans`
composes them; `preCleanupPile` contributes the neutral mask, `kingMove` the
vacated suit's row. -/

/-- **`preCleanupPile`'s king-configuration side.**  A phase that touches only one
pile which stays non-empty cannot disturb the configuration: every piled suit
owns a *different*, still-empty column, and `kings` is untouched
(`preCleanupPile_kings_eq`).  So `k' = k`, `FK = ∅`, and the contributed mask is
`0xffff`.

The two depth hypotheses are what rule out interference: `a` is not empty before
(so no suit owns it) and not empty after (so no suit must start owning it).  Both
hold for `preCleanupPile`, whose merge count satisfies `m < pileDepth[a]`. -/
theorem StateMatchesKingConfig.framePile {g : Globals} {s v : State} {p q : SolverPosType}
    {k : Fin 16} {a : Fin 10} (hk : StateMatchesKingConfig g s p k)
    (hreach : Reach s v) (hmatch : StateMatchesSolverPos g v q)
    (hda : 0 < (p.pileDepth.get a).toInt.toNat)
    (hqda : 0 < (q.pileDepth.get a).toInt.toNat)
    (hframe : ∀ i : Fin 10, i ≠ a → v.tableau i = s.tableau i)
    (hqdne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i)
    (hqkings : q.kings = p.kings) :
    Simulates g s p k v q k ∅ 0xffff := by
  refine Simulates.ofReach hreach ⟨hmatch, ?_, ?_⟩
  · -- the same assignment still works, pile by pile
    obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    refine ⟨assign, fun su i hi => ?_, hinj, hiff⟩
    have ho := hown su i hi
    have hia : i ≠ a := by
      intro hc; rw [hc] at ho; have := ho.1; omega
    exact ho.frame (hqdne i hia) (by rw [hqkings]) (hframe i hia)
  · -- `q`'s empty piles are `p`'s empty piles, with the same columns
    intro su hsu
    refine (hk.no_pile su hsu).frame (fun i hi => ?_)
    have hia : i ≠ a := by intro hc; rw [hc] at hi; omega
    exact Or.inl ⟨by rw [← hqdne i hia]; exact hi, hframe i hia⟩

/-- **`kingMove`'s king-configuration side** — the one phase that changes the
configuration, and it moves no card at all (`s` on both sides).

Before the vacate the suit is *not* piled by this column: `OwnsPile` demands
solver-depth `0`, and the column still has its depth-1 dealt card — which *is* the
suit's king.  Dropping the depth to `0` is exactly what turns the column into
`su`'s king pile, so `su` becomes piled and the configuration loses its bit.

`su` may nevertheless have been piled already in `k`, on a *genuinely empty*
column via `OwnsPile`'s second disjunct — available precisely when nothing of the
suit is freed yet, which is the case here.  That reading does not survive the
`kings` write, so the assignment is re-pointed at the vacated column either way,
and `clearCfgBit` leaves an already-clear bit alone.  Injectivity is what makes
the re-pointing safe: no other suit can have owned `a`, since `a` had depth `1`. -/
theorem StateMatchesKingConfig.vacatePile {g : Globals} {s v : State} {p q : SolverPosType}
    {k : Fin 16} {a : Fin 10} {su : Suit} (hk : StateMatchesKingConfig g s p k)
    (hreach : Reach s v) (hmatch : StateMatchesSolverPos g v q)
    (hda : 0 < (p.pileDepth.get a).toInt.toNat)
    (hqd : (q.pileDepth.get a).toInt.toNat = 0)
    (hqdne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i)
    (hframe : ∀ i : Fin 10, i ≠ a → v.tableau i = s.tableau i)
    (hbot : ∃ c ∈ (v.tableau a).getLast?, c.suit = su ∧ c.rank = Rank.king)
    (hqkne : ∀ su' : Suit, su' ≠ su →
      q.kings.get (finOfSuit su') = p.kings.get (finOfSuit su')) :
    Simulates g s p k v q (clearCfgBit k su) {su} (kingOnPileMap.get (finOfSuit su)) := by
  -- the vacated column's deepest card is `su`'s king, so no other suit sees it
  have hnotsu : ∀ d ∈ (v.tableau a).getLast?, ∀ x : Suit, x ≠ su → d.suit ≠ x := by
    obtain ⟨c, hc, hcsu, _⟩ := hbot
    intro d hd x hx
    obtain rfl : c = d :=
      Option.some.inj ((Option.mem_def.1 hc).symm.trans (Option.mem_def.1 hd))
    rw [hcsu]; exact fun hcc => hx hcc.symm
  refine Simulates.vacate hreach ⟨hmatch, ?_, ?_⟩
    (fun su' hsu' => clearCfgBit_ne su su' k hsu')
  · -- re-point `su` at the vacated column; everyone else keeps theirs
    obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    set assign' : Suit → Option (Fin 10) := fun x => if x = su then some a else assign x
      with hAdef
    have hAsu : assign' su = some a := by simp [hAdef]
    have hAne : ∀ x : Suit, x ≠ su → assign' x = assign x := by
      intro x hx; simp [hAdef, hx]
    refine ⟨assign', ?_, ?_, ?_⟩
    · intro x i hi
      by_cases hx : x = su
      · subst hx
        rw [hAsu] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨hqd, Or.inl hbot⟩
      · rw [hAne x hx] at hi
        have ho := hown x i hi
        have hia : i ≠ a := by
          intro hc; rw [hc] at ho; have := ho.1; omega
        exact ho.frame (hqdne i hia) (hqkne x hx) (hframe i hia)
    · intro x y i hix hiy
      by_cases hx : x = su <;> by_cases hy : y = su
      · rw [hx, hy]
      · -- `y ≠ su` would have to own `a`, which had depth 1
        exfalso
        rw [hx, hAsu] at hix
        rw [hAne y hy] at hiy
        obtain rfl := Option.some.inj hix
        have := (hown y a hiy).1
        omega
      · exfalso
        rw [hy, hAsu] at hiy
        rw [hAne x hx] at hix
        obtain rfl := Option.some.inj hiy
        have := (hown x a hix).1
        omega
      · rw [hAne x hx] at hix; rw [hAne y hy] at hiy
        exact hinj x y i hix hiy
    · intro x
      by_cases hx : x = su
      · subst hx
        rw [hAsu]
        exact ⟨fun _ => clearCfgBit_self x k, fun _ => rfl⟩
      · rw [hAne x hx, hiff x]
        exact not_congr (clearCfgBit_ne su x k hx).symm
  · -- the only new empty pile carries `su`, whose bit is now clear
    intro x hxbit
    have hx : x ≠ su := by
      intro hc; rw [hc] at hxbit; exact clearCfgBit_self su k hxbit
    refine (hk.no_pile x ((clearCfgBit_ne su x k hx).1 hxbit)).frame (fun i hi => ?_)
    by_cases hia : i = a
    · subst hia
      exact Or.inr (fun d hd => hnotsu d hd x hx)
    · exact Or.inl ⟨by rw [← hqdne i hia]; exact hi, hframe i hia⟩

/-! ### Instantiated at the real terms

The two lemmas above are stated with field equations, the way `cleanupPileSim` and
`cleanupVacate` are, so they compose with them directly.  These corollaries pin
them to the actual `preCleanupPile` / `kingMove` terms, discharging the field
equations from the `SolverSpec` field lemmas. -/

/-- **`Simulates` for `preCleanupPile`.**  The `Reach` and the matching come from
`cleanupPileSim`; `hqda` (the pile is still non-empty afterwards) is the caller's,
since it follows from the merge count's `m < pileDepth[pile]` — read off with
`cleanupRunResult_fields_ordinary`. -/
theorem Simulates.preCleanupPile {g : Globals} {s v : State} {p : SolverPosType} {k : Fin 16}
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {ph : UInt32}
    (hs4 : (SUIT B).toUInt32.toNat < 4) {m f : Nat}
    (hk : StateMatchesKingConfig g s p k) (hreach : Reach s v)
    (hmatch : StateMatchesSolverPos g v
      (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p))
    (hframe : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → v.tableau i = s.tableau i)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat)
    (hqda : 0 < ((preCleanupPile pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).pileDepth.get
        ⟨pile.toNat, hpile⟩).toInt.toNat) :
    Simulates g s p k v
      (preCleanupPile pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p) k ∅ 0xffff :=
  hk.framePile hreach hmatch hda hqda hframe
    (fun i hi => SolverSpec.preCleanupPile_pileDepth_eq_of_ne pile hpile B ph hs4 p m f i
      (fun hc => hi (Fin.ext hc)))
    (SolverSpec.preCleanupPile_kings_eq pile hpile B ph hs4 p m f)

/-- **`Simulates` for `kingMove`** — no card moves, and the configuration gains
exactly the vacated suit.  `hsucode` is the bridge from the solver's suit *code* to
the `Rules` suit, and `hbot` says the depth-1 column really is topped out at that
suit's king (which is the branch's own `VALUE (B + m) = 13` test, transported to
the state — the derivation inside `cleanupPileSimKing`). -/
theorem Simulates.kingMove {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    {pile : UInt32} (hpile : pile.toNat < 10) {suit : UInt8}
    (hs4 : suit.toUInt32.toNat < 4) {ph : UInt32} {su : Suit}
    (hk : StateMatchesKingConfig g s p k)
    (hsucode : suit.toUInt32.toNat = suitToNat su)
    (hmatch : StateMatchesSolverPos g s (kingMove pile hpile suit hs4 ph p))
    (hd1 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat = 1)
    (hbot : ∃ c ∈ (s.tableau ⟨pile.toNat, hpile⟩).getLast?,
      c.suit = su ∧ c.rank = Rank.king) :
    Simulates g s p k s (kingMove pile hpile suit hs4 ph p)
      (clearCfgBit k su) {su} (kingOnPileMap.get (finOfSuit su)) := by
  refine hk.vacatePile Relation.ReflTransGen.refl hmatch (by omega) ?_ ?_
    (fun _ _ => rfl) hbot ?_
  · rw [SolverSpec.kingMove_pileDepth_self]; rfl
  · exact fun i hi => SolverSpec.kingMove_pileDepth_eq_of_ne pile hpile suit hs4 ph p i
      (fun hc => hi (Fin.ext hc))
  · intro su' hsu'
    refine SolverSpec.kingMove_kings_eq_of_ne pile hpile suit hs4 ph p (finOfSuit su') ?_
    rw [hsucode]
    exact fun hc => hsu' (suitToNat_inj hc)

/-! ## From `cleanupPile_eq`'s bundle to the simulation's hypotheses

`cleanupPile_eq` reports the merge loop as "slot `depth - k - 1` holds `B + k`",
indexed in `Int32`; `cleanupPileSim` wants "two consecutive slots differ by one",
indexed in `Nat`.  This is the conversion — the same two steps
`chain_of_mergeGuards` makes, starting one stage later (from the slot facts rather
than from the raw guards). -/

theorem chain_of_mcards {g : Globals} {p : SolverPosType} {pile : UInt32}
    (hpile : pile.toNat < 10) {B : UInt8} {m : Nat}
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hm : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hmcards : ∀ k, k ≤ m → ∃ h5 : ((p.pileDepth[pile.toNat]'hpile).toInt32
          - Int32.ofNat k - 1).toUInt32.toNat < 5,
      (g.pos2card[pile.toNat]'hpile)[((p.pileDepth[pile.toNat]'hpile).toInt32
          - Int32.ofNat k - 1).toUInt32.toNat]'h5 = B + UInt8.ofNat k) :
    ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1 := by
  have hdI : ((p.pileDepth[pile.toNat]'hpile).toInt32).toInt
      = ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat : Int) := uint8_toInt32_toInt _
  -- step 1: re-index the slot facts into `Nat`
  have hslot : ∀ k, k ≤ m → ∀ hk5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k < 5,
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k, hk5⟩ = B + UInt8.ofNat k := by
    intro k hk hk5
    obtain ⟨h5, heq⟩ := hmcards k hk
    have hconv : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat k - 1).toUInt32.toNat
        = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - k := by
      have h1 := SolverSpec.depth_sub_ofNat_sub_one_eq
        (d0 := (p.pileDepth[pile.toNat]'hpile).toInt32) (i := k) (by rw [hdI]; omega)
        (by rw [hdI]; omega)
      rw [int32_toUInt32_toNat _ (by rw [h1, hdI]; omega), h1, hdI]
      omega
    rw [← heq]
    show (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hk5⟩
      = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, h5⟩
    congr 1
    exact Fin.ext hconv.symm
  -- step 2: two consecutive slots differ by one
  intro j hj1' hj2' hj1 hj
  simp only [UInt8.toInt_toNat] at hj1' hj2'
  have hk : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j ≤ m := by omega
  have hk' : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1) ≤ m := by omega
  have h1 := hslot ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) hk (by omega)
  have h2 := hslot ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)) hk' (by omega)
  have hi1 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j), by omega⟩ : Fin 5) = ⟨j, hj⟩ :=
    Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) = j from by omega)
  have hi2 : (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)), by omega⟩ : Fin 5)
      = ⟨j - 1, hj1⟩ :=
    Fin.ext (show (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1
      - ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)) = j - 1 from by omega)
  rw [hi1] at h1
  rw [hi2] at h2
  rw [h1, h2]
  have hstep : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - (j - 1)
      = ((p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 - j) + 1 := by omega
  rw [hstep, UInt8.ofNat_add, UInt8.ofNat_one, UInt8.add_assoc]

/-! ## `Simulates` for a whole `SolverCleanupPile` call

The position and the mask are the solver's own `cleanupRunResult`, so composing
this with `cleanupPile_nonempty_eq` turns the monadic run into a `Simulates` —
the same convention `cleanupRunResult_sim` follows on the matching side, whose
conclusion supplies `hreach`/`hmatch`.

Both branches are handled here, and neither needs the intermediate
`preCleanupPile` position: `framePile` covers the ordinary branch in one step, and
the generalized `vacatePile` covers the lone-king branch in one step — the
extension's moves and the vacate happen at opposite ends of the same call, and the
only pile either touches is the cleaned one.  Composing with the no-op
`Simulates.refl` reproduces the mask exactly as the code accumulates it
(`0xffff &&& kingOnPileMap[suit]`), with `FK = ∅ ∪ {suit}`. -/

theorem Simulates.cleanupPile {g : Globals} {s v : State} {p : SolverPosType}
    {k : Fin 16} {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {ph : UInt32}
    (hs4 : (SUIT B).toUInt32.toNat < 4) {m f : Nat}
    (hk : StateMatchesKingConfig g s p k)
    (hda : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hm : m ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1)
    (hreach : Reach s v)
    (hmatch : StateMatchesSolverPos g v
      (cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2)
    (hframe : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ → v.tableau i = s.tableau i)
    (hbot : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1
          && VALUE (B + UInt8.ofNat m) == 13) = true →
      ∃ c ∈ (v.tableau ⟨pile.toNat, hpile⟩).getLast?,
        c.suit = suitOfCode (SUIT B) hs4 ∧ c.rank = Rank.king) :
    ∃ (k' : Fin 16) (FK : Finset Suit),
      Simulates g s p k v
        (cleanupRunResult pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2
        k' FK
        (cleanupRunResult pile hpile B ph hs4
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).1 := by
  have hdane : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat := hda
  by_cases hbranch : ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m == 1
      && VALUE (B + UInt8.ofNat m) == 13) = true
  · -- LONE KING: the vacate clears the boundary suit's bit
    obtain ⟨hqd, -, -, hqk⟩ := cleanupRunResult_fields_king pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hbranch
    have hfk : (cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).1
        = 0xffff &&& kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4 := by
      unfold _root_.cleanupRunResult
      rw [if_pos hbranch]
    have hfin : kingOnPileMap.get (finOfSuit (suitOfCode (SUIT B) hs4))
        = kingOnPileMap[(SUIT B).toUInt32.toNat]'hs4 := by
      rw [show finOfSuit (suitOfCode (SUIT B) hs4) = (⟨(SUIT B).toUInt32.toNat, hs4⟩ : Fin 4) from
        Fin.ext (suitToNat_natToSuit _)]
      rfl
    refine ⟨clearCfgBit k (suitOfCode (SUIT B) hs4), ∅ ∪ {suitOfCode (SUIT B) hs4}, ?_⟩
    rw [hfk, ← hfin]
    refine (Simulates.refl hk).trans (hk.vacatePile hreach hmatch hdane ?_ ?_ hframe
      (hbot hbranch) ?_)
    · rw [hqd]
      show ((p.pileDepth.set pile.toNat 0 hpile)[pile.toNat]'hpile).toInt.toNat = 0
      rw [Vector.getElem_set_self]
      rfl
    · intro i hi
      rw [hqd]
      show (p.pileDepth.set pile.toNat 0 hpile)[i.val]'i.isLt = p.pileDepth[i.val]'i.isLt
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))
    · intro su' hsu'
      rw [hqk]
      show (p.kings.set (SUIT B).toUInt32.toNat _ hs4)[(finOfSuit su').val]'(finOfSuit su').isLt
        = p.kings[(finOfSuit su').val]'(finOfSuit su').isLt
      refine Vector.getElem_set_ne hs4 (finOfSuit su').isLt (fun hc => hsu' ?_)
      refine suitToNat_inj ?_
      show suitToNat su' = suitToNat (suitOfCode (SUIT B) hs4)
      rw [suitOfCode, suitToNat_natToSuit]
      exact hc.symm
  · -- ORDINARY: nothing is vacated, and the pile stays non-empty
    obtain ⟨hqd, -, -, hqk⟩ := cleanupRunResult_fields_ordinary pile hpile B ph hs4
      (p.pileDepth[pile.toNat]'hpile).toInt32 m f p hbranch
    have hfk : (cleanupRunResult pile hpile B ph hs4
        (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).1 = 0xffff := by
      unfold _root_.cleanupRunResult
      rw [if_neg hbranch]
    refine ⟨k, ∅, ?_⟩
    rw [hfk]
    refine hk.framePile hreach hmatch hdane ?_ hframe ?_ hqk
    · -- the merge leaves at least one dealt card
      rw [hqd]
      show 0 < ((p.pileDepth.set pile.toNat
        ((p.pileDepth[pile.toNat]'hpile).toInt32 - Int32.ofNat m).toUInt32.toUInt8
        hpile)[pile.toNat]'hpile).toInt.toNat
      rw [Vector.getElem_set_self]
      show 0 < (((p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt32
        - Int32.ofNat m).toUInt32.toUInt8).toNat
      rw [depth1_toNat hd5 (by omega)]
      omega
    · intro i hi
      rw [hqd]
      show (p.pileDepth.set pile.toNat _ hpile)[i.val]'i.isLt = p.pileDepth[i.val]'i.isLt
      exact Vector.getElem_set_ne hpile i.isLt (fun hc => hi (Fin.ext hc.symm))

/-! ### End to end, from the matching simulation

`cleanupRunResult_sim` now exports everything the configuration side needs: the
`Reach`, the matching, the frame, and — in the lone-king branch — that the vacated
column's deepest card is the boundary suit's king.  Gluing the two gives a
`Simulates` for a whole `SolverCleanupPile` call from the same hypotheses the
matching simulation takes. -/

theorem Simulates.ofCleanupRun {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k)
    {pile : UInt32} (hpile : pile.toNat < 10) {B : UInt8} {ph : UInt32} {m f : Nat}
    (hs4' : (SUIT B).toUInt32.toNat < 4)
    (hidx : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat)
    (hfl1 : p.pileFlute.get ⟨pile.toNat, hpile⟩ = 1)
    (hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩ = B)
    (hm : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat)
    (hchain : ∀ j, (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - m ≤ j →
      j < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat →
      ∀ (hj1 : j - 1 < 5) (hj : j < 5),
      (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j - 1, hj1⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨j, hj⟩ + 1)
    (hf : f + 1 ≤ (VALUE B).toNat)
    (hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g p (B - UInt8.ofNat l))
    (haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
      p.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l)
    (hBflute1 : ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toInt.toNat →
      ∀ hidxj : (p.pileDepth.get j).toInt.toNat - 1 < 5,
      (g.pos2card.get j).get ⟨_, hidxj⟩ = B → p.pileFlute.get j = 1)
    (hnoshare : ∀ i : Fin 10, i ≠ ⟨pile.toNat, hpile⟩ →
      (p.pileDepth.get i).toInt.toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?, suitToNat d.suit ≠ (SUIT B).toNat) :
    ∃ (v : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g s p k v
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2
        k' FK
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).1 := by
  obtain ⟨v, hreach, hframe, hmatch, hexport⟩ :=
    hk.toMatches.cleanupRunResult_sim hwf hb hpile hs4' hidx hd1 hfl1 hB hm hchain hf hfree
      haces hBflute1 hnoshare
  have hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 :=
    hb.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hmN : m < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hm
  have hdaN : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by omega
  obtain ⟨k', FK, hsim⟩ := Simulates.cleanupPile hpile hs4' hk hdaN hd5 (by omega)
    hreach hmatch hframe
    (fun hbranch => by
      obtain ⟨c, hc, hcsuit, hcrank⟩ := hexport hbranch
      -- the exported suit is stated by code; convert it to the `Suit` the vacate names
      refine ⟨c, hc, ?_, hcrank⟩
      have hfin : (⟨(SUIT B).toUInt32.toNat, hs4'⟩ : Fin 4)
          = ⟨suitToNat c.suit, suitToNat_lt c.suit⟩ :=
        Fin.ext (show (SUIT B).toUInt32.toNat = suitToNat c.suit from by
          rw [UInt8.toNat_toUInt32]; exact hcsuit.symm)
      show c.suit = natToSuit ⟨(SUIT B).toUInt32.toNat, hs4'⟩
      exact (natToSuit_suitToNat c.suit).symm.trans (congrArg natToSuit hfin.symm))
  exact ⟨v, k', FK, hsim⟩

/-! ## The pending run of the `busyAces` drain

`SolverMoveAces` walks up from `aces[suit] + 1`, counting *already free* cards in
`found` without touching the state, and only re-syncs the position when it reaches
a card exposed at its pile's boundary (`cardDepth = 0`, which writes `aces` and
calls `SolverRemoveFlute`).  On the `Rules` side the plays are therefore
**deferred** to those sync points: during the counting steps the position does not
change at all, so the simulation carries over verbatim, and at a sync point the
whole pending run is played at once.

What this section supplies is that the pending run really is playable.  The heart
of it is purely structural: the card sitting directly above a *free* card in a
column always has the same suit and a lower rank, so once the run has been played
up to `c`'s predecessor, nothing can be covering `c`. -/

/-- **A free card in a column sits above its pile's boundary.**  The bottom
`pileDepth` cards of a column are the dealt ones, and a dealt card at or below the
boundary is never free (`depth_card_not_free`). -/
theorem StateMatchesSolverPos.free_above_boundary {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (q : Fin 10) {i : Nat} (hi : i < (s.tableau q).length)
    (hfree : isFreeCard g p (encodeCard ((s.tableau q)[i]'hi))) :
    (p.pileDepth.get q).toInt.toNat ≤ (s.tableau q).length - 1 - i := by
  obtain ⟨hnL, hres, -⟩ := h.depth_match q
  have hd6 := h.depth_lt6 q
  by_contra hlt
  push Not at hlt
  have hj5 : (s.tableau q).length - 1 - i < 5 := by omega
  have hcode : encodeCard ((s.tableau q)[i]'hi)
      = (g.pos2card.get q).get ⟨(s.tableau q).length - 1 - i, hj5⟩ := by
    have hr := hres ⟨(s.tableau q).length - 1 - i, hlt⟩
    rw [List.getElem?_reverse' (j := i)
        (show (s.tableau q).length - 1 - i + i + 1 = (s.tableau q).length from by omega),
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at hr
    exact hr
  exact depth_card_not_free hwf hb q ⟨_, hj5⟩ hlt (hcode ▸ hfree)

/-- **A card above a free card in a column is same-suit and lower.**  Position `a`
is nearer the top than `b`; freeness of `b` places it above the pile's boundary,
hence inside the same-suit descending run, and `a` is then further up that run. -/
theorem StateMatchesSolverPos.column_above {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (q : Fin 10) {a b : Nat} (hab : a < b) (hblt : b < (s.tableau q).length)
    (hfreeb : isFreeCard g p (encodeCard ((s.tableau q)[b]'hblt))) :
    ((s.tableau q)[a]'(by omega)).suit = ((s.tableau q)[b]'hblt).suit ∧
      rankToNat ((s.tableau q)[a]'(by omega)).rank
        < rankToNat ((s.tableau q)[b]'hblt).rank := by
  obtain ⟨hnL, hres, h3⟩ := h.depth_match q
  have hd6 := h.depth_lt6 q
  have hlr : (s.tableau q).reverse.length = (s.tableau q).length := by
    simp only [List.length_reverse]
  have halt : a < (s.tableau q).length := by omega
  have hjbn := h.free_above_boundary hwf hb q hblt hfreeb
  -- the flute part is one same-suit descending run
  obtain ⟨suit, startVal, hsd⟩ : ∃ (suit : UInt8) (startVal : Nat),
      IsSameSuitDescending suit startVal
        (((s.tableau q).reverse.drop (p.pileDepth.get q).toInt.toNat).map encodeCard) := by
    revert h3
    by_cases hn : (p.pileDepth.get q).toInt.toNat > 0
    · rw [dif_pos hn]; exact fun hh => ⟨_, _, hh⟩
    · rw [dif_neg hn]; exact fun hh => ⟨hh.choose, 13, hh.choose_spec⟩
  -- read the run off at a column position above the boundary
  have hentry : ∀ (i : Nat) (hi : i < (s.tableau q).length),
      (p.pileDepth.get q).toInt.toNat ≤ (s.tableau q).length - 1 - i →
      SUIT (encodeCard ((s.tableau q)[i]'hi)) = suit ∧
      (VALUE (encodeCard ((s.tableau q)[i]'hi))).toNat
        = startVal - ((s.tableau q).length - 1 - i - (p.pileDepth.get q).toInt.toNat) := by
    intro i hi hn'
    have hlen : (((s.tableau q).reverse.drop
        (p.pileDepth.get q).toInt.toNat).map encodeCard).length
        = (s.tableau q).length - (p.pileDepth.get q).toInt.toNat := by
      simp only [List.length_map, List.length_drop, List.length_reverse]
    have hidx : (s.tableau q).length - 1 - i - (p.pileDepth.get q).toInt.toNat
        < (((s.tableau q).reverse.drop
            (p.pileDepth.get q).toInt.toNat).map encodeCard).length := by
      rw [hlen]; omega
    obtain ⟨hs, hv⟩ := hsd ⟨_, hidx⟩
    have hget : (((s.tableau q).reverse.drop
        (p.pileDepth.get q).toInt.toNat).map encodeCard).get ⟨_, hidx⟩
        = encodeCard ((s.tableau q)[i]'hi) := by
      have h1 := List.getElem?_eq_getElem hidx
      rw [List.getElem?_map, List.getElem?_drop,
        List.getElem?_reverse' (j := i) (by omega), List.getElem?_eq_getElem hi] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [List.get_eq_getElem]
      exact h1.symm
    rw [hget] at hs hv
    exact ⟨hs, hv⟩
  obtain ⟨hsa, hva⟩ := hentry a halt (by omega)
  obtain ⟨hsb, hvb⟩ := hentry b hblt hjbn
  rw [encodeCard_VALUE] at hva hvb
  have hra := rankToNat_pos ((s.tableau q)[a]'halt).rank
  have hrb := rankToNat_pos ((s.tableau q)[b]'hblt).rank
  refine ⟨?_, by omega⟩
  -- equal suit codes give equal suits
  refine suitToNat_inj ?_
  have h1 : (SUIT (encodeCard ((s.tableau q)[a]'halt))).toNat
      = suitToNat ((s.tableau q)[a]'halt).suit := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat']
    have := suitToNat_lt ((s.tableau q)[a]'halt).suit
    omega
  have h2 : (SUIT (encodeCard ((s.tableau q)[b]'hblt))).toNat
      = suitToNat ((s.tableau q)[b]'hblt).suit := by
    rw [encodeCard_SUIT, UInt8.toNat_ofNat']
    have := suitToNat_lt ((s.tableau q)[b]'hblt).suit
    omega
  rw [← h1, ← h2, hsa, hsb]

/-- **The next foundation card of the drain's run is accessible.**  `u` is a state
reached from `s` by playing cards off the tops of columns (and out of cells) to the
foundations — the pending run so far.  Any *free* card that is next up for its
foundation is then either in a cell or already exposed: whatever sat above it in
its column was same-suit and lower (`column_above`), hence already on that
foundation, hence — the deck being intact — no longer in the column. -/
theorem accessible_of_pending {g : Globals} {s u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (hdrop : ∀ q : Fin 10, ∃ k : Nat, u.tableau q = (s.tableau q).drop k)
    (hcount : ∀ d : Card, countState u d = 1)
    {su : Suit} {c : Card} (hnext : nextFoundationCard u su = some c)
    (hfree : isFreeCard g p (encodeCard c)) :
    Accessible u c := by
  obtain ⟨hsu, hready⟩ := nextFoundationCard_spec hnext
  have hcr : rankToNat c.rank = optRankToNat (u.foundations c.suit) + 1 :=
    nextRankNat _ _ hready.symm
  have hcf : countFoundation u.foundations c = 0 := by
    unfold countFoundation
    rw [if_pos (by omega)]
  rcases NoDupState.location hcount c with hf | ⟨i, hi⟩ | ⟨q, hq⟩
  · exact absurd hf (by omega)
  · exact Or.inl ⟨i, hi⟩
  · refine Or.inr ⟨q, ?_⟩
    obtain ⟨k, hk⟩ := hdrop q
    obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hq
    have hlenu : (u.tableau q).length = (s.tableau q).length - k := by
      rw [hk]; simp only [List.length_drop]
    have hklt : k < (s.tableau q).length := by omega
    -- `c` sits at column position `k + idx`
    have h0 : (s.tableau q)[k + idx]? = some c := by
      have h1 : (u.tableau q)[idx]? = some c := by
        rw [List.getElem?_eq_getElem hidxlt, hidxeq]
      rwa [hk, List.getElem?_drop] at h1
    -- it must be the top one
    have hidx0 : idx = 0 := by
      by_contra hne
      have hkidxlt : k + idx < (s.tableau q).length := by
        rw [List.getElem?_eq_some_iff] at h0
        exact h0.choose
      have hceq : (s.tableau q)[k + idx]'hkidxlt = c := by
        rw [List.getElem?_eq_getElem hkidxlt, Option.some.injEq] at h0
        exact h0
      obtain ⟨hxsuit, hxrank⟩ := h.column_above hwf hb q
        (a := k) (b := k + idx) (by omega) hkidxlt (by rw [hceq]; exact hfree)
      rw [hceq] at hxsuit hxrank
      -- the card above is already on `c`'s foundation
      have hxf : countFoundation u.foundations ((s.tableau q)[k]'hklt) = 1 := by
        unfold countFoundation
        rw [hxsuit, if_neg (by omega)]
      have hxmem : ((s.tableau q)[k]'hklt) ∈ u.tableau q := by
        rw [hk]
        have : ((s.tableau q).drop k)[0]? = some ((s.tableau q)[k]'hklt) := by
          rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hklt]
        exact List.mem_of_getElem? this
      have hxcol : 1 ≤ countColumn (u.tableau q) ((s.tableau q)[k]'hklt) :=
        one_le_countColumn hxmem
      have hxtab : 1 ≤ countTableau u.tableau ((s.tableau q)[k]'hklt) := by
        unfold countTableau
        rw [List.sum_ofFn]
        exact le_trans hxcol
          (Finset.single_le_sum (f := fun j : Fin 10 =>
            countColumn (u.tableau j) ((s.tableau q)[k]'hklt))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      have := hcount ((s.tableau q)[k]'hklt)
      unfold countState at this
      omega
    -- so it is the head
    subst hidx0
    rw [hk, List.head?_drop]
    simpa using h0

/-- **The drain's pending run plays.**  Given that the next `j` cards of the suit
are free in the position — exactly what `MoveAcesInv` supplies for the `found`
cards the walk has counted — they can all be played to the foundation, and the
result is again a state that differs from `s` only by cards taken off column tops.

The bound `j` is why this is a hand-rolled induction rather than an instance of
`exists_playsAll_runFrom`: that driver needs *every* subsequent card to be
accessible, whereas the drain stops after the counted ones. -/
theorem exists_playsAll_pending {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (h : StateMatchesSolverPos g s p)
    (su : Suit) :
    ∀ (j : Nat) (u : State),
      (∀ q : Fin 10, ∃ k : Nat, u.tableau q = (s.tableau q).drop k) →
      (∀ d : Card, countState u d = 1) →
      (∀ d ∈ runFrom (nextFoundationCard u su) j, isFreeCard g p (encodeCard d)) →
      ∃ w, PlaysAll u (runFrom (nextFoundationCard u su) j) w ∧
        (∀ q : Fin 10, ∃ k : Nat, w.tableau q = (s.tableau q).drop k) ∧
        (∀ d : Card, countState w d = 1) := by
  intro j
  induction j with
  | zero => intro u hdrop hcount _; exact ⟨u, PlaysAll.nil u, hdrop, hcount⟩
  | succ j ih =>
    intro u hdrop hcount hfree
    cases hnf : nextFoundationCard u su with
    | none =>
      refine ⟨u, ?_, hdrop, hcount⟩
      rw [runFrom_none]
      exact PlaysAll.nil u
    | some c =>
      have hcfree : isFreeCard g p (encodeCard c) := by
        refine hfree c ?_
        rw [hnf, runFrom_some]
        exact List.mem_cons_self
      have hacc := accessible_of_pending hwf hb h hdrop hcount hnf hcfree
      obtain ⟨hsu, hready⟩ := nextFoundationCard_spec hnf
      obtain ⟨t1, hplay⟩ := PlaysTo.of_accessible hacc hready
      -- the deck is intact after one play
      have hreach1 : Reach u t1 := (PlaysAll.cons hplay (PlaysAll.nil t1)).toReach
      have hcount1 : ∀ d : Card, countState t1 d = 1 := by
        intro d
        rw [congrFun (countState_of_reach hreach1) d]
        exact hcount d
      -- and columns have only lost another top card
      have hdrop1 : ∀ q : Fin 10, ∃ k : Nat, t1.tableau q = (s.tableau q).drop k := by
        intro q
        rcases hplay.cases with ⟨i, -, rfl⟩ | ⟨q0, rest, hcol, rfl⟩
        · simpa using hdrop q
        · obtain ⟨k, hk⟩ := hdrop q
          by_cases hq : q = q0
          · subst hq
            refine ⟨k + 1, ?_⟩
            simp only [updateFoundation_tableau, updateColumn_tableau, update_same]
            have hrest : rest = (u.tableau q).tail := by rw [hcol, List.tail_cons]
            rw [hrest, hk, List.tail_drop]
          · refine ⟨k, ?_⟩
            simp only [updateFoundation_tableau, updateColumn_tableau, update,
              if_neg (show ¬ (q0 = q) from fun hc => hq hc.symm)]
            exact hk
      -- recurse on the rest of the run
      have hnext1 : nextFoundationCard t1 su = nextCard c := nextFoundationCard_playsTo hsu hplay
      have hfree1 : ∀ d ∈ runFrom (nextFoundationCard t1 su) j, isFreeCard g p (encodeCard d) := by
        rw [hnext1]
        intro d hd
        refine hfree d ?_
        rw [hnf, runFrom_some]
        exact List.mem_cons_of_mem c hd
      obtain ⟨w, hall, hw1, hw2⟩ := ih t1 hdrop1 hcount1 hfree1
      refine ⟨w, ?_, hw1, hw2⟩
      rw [runFrom_some]
      rw [hnext1] at hall
      exact PlaysAll.cons hplay hall

/-- Membership in one column bounds the whole-tableau count. -/
theorem one_le_countTableau {t : Fin 10 → Column} {c : Card} {q : Fin 10}
    (h : c ∈ t q) : 1 ≤ countTableau t c := by
  unfold countTableau
  rw [List.sum_ofFn]
  exact le_trans (one_le_countColumn h)
    (Finset.single_le_sum (f := fun j : Fin 10 => countColumn (t j) c)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))

/-- **At a sync point the walk has already passed the whole flute.**

When the drain reaches a card exposed at pile `j`'s boundary, that boundary `B`
sits `found + 1` above the foundation top `A`.  The pile's flute can then be no
longer than `found + 1`: its topmost card carries `B`'s suit and value
`VALUE B - (pileFlute - 1)`, so a longer flute would put a card of that suit at or
below `A` — already on the foundation, and no card is in two places.

This is what makes the sync step's `flute_match` arithmetic work out: *every*
flute interior of the pile is among the `found` cards the walk counted, so playing
the pending run plus the boundary leaves exactly `pileDepth - 1` cards in the
column — which is what the cleanup's entry position (`fluteNorm` of
`removeFlutePre`, with `pileFlute := 1`) claims. -/
theorem StateMatchesSolverPos.flute_walked {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (j : Fin 10)
    (hdj : 0 < (p.pileDepth.get j).toInt.toNat)
    (b : Fin 5) (hb : b.val = (p.pileDepth.get j).toInt.toNat - 1)
    {su : Suit} (found : Nat)
    (hsuit : SUIT ((g.pos2card.get j).get b) = UInt8.ofNat (suitToNat su))
    (hval : (VALUE ((g.pos2card.get j).get b)).toNat
      = (VALUE (p.aces.get (finOfSuit su))).toNat + found + 1) :
    (p.pileFlute.get j).toNat ≤ found + 1 := by
  by_contra hgt
  push Not at hgt
  have hLen : (s.tableau j).length + 1
      = (p.pileDepth.get j).toInt.toNat + (p.pileFlute.get j).toNat := h.flute_match j hdj
  have hnL : (p.pileDepth.get j).toInt.toNat ≤ (s.tableau j).length := (h.depth_match j).1
  have hlt : (0 : Nat) < (s.tableau j).length := by omega
  -- the topmost flute card
  obtain ⟨hs0, hv0⟩ := flute_elem h j hdj b hb 0 (by omega) hlt
  rw [encodeCard_VALUE] at hv0
  have hfv := h.foundation_value su
  -- it carries the boundary's suit
  have hxsuit : ((s.tableau j)[0]'hlt).suit = su := by
    refine suitToNat_inj ?_
    have h1 : (SUIT (encodeCard ((s.tableau j)[0]'hlt))).toNat
        = suitToNat ((s.tableau j)[0]'hlt).suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt ((s.tableau j)[0]'hlt).suit
      omega
    have h2 : (SUIT ((g.pos2card.get j).get b)).toNat = suitToNat su := by
      rw [hsuit, UInt8.toNat_ofNat']
      have := suitToNat_lt su
      omega
    rw [← h1, ← h2, hs0]
  -- and a value at or below the foundation top, so it is already played
  have hxf : countFoundation s.foundations ((s.tableau j)[0]'hlt) = 1 := by
    unfold countFoundation
    rw [hxsuit, if_neg (by omega)]
  have hxtab : 1 ≤ countTableau s.tableau ((s.tableau j)[0]'hlt) :=
    one_le_countTableau (List.getElem_mem hlt)
  have := h.cards_count ((s.tableau j)[0]'hlt)
  unfold countState at this
  omega

theorem rankToNat_inj {r r' : Rank} (h : rankToNat r = rankToNat r') : r = r' := by
  cases r <;> cases r' <;> simp_all [rankToNat]

/-- Same suit and same rank number means the same card. -/
theorem card_eq_of_suit_rank {x y : Card} (hs : x.suit = y.suit)
    (hr : rankToNat x.rank = rankToNat y.rank) : x = y := by
  obtain ⟨xs, xr⟩ := x
  obtain ⟨ys, yr⟩ := y
  simp only [] at hs hr
  rw [hs, rankToNat_inj hr]

/-! ### The sync point's flute, from the invariant alone

At a sync point the walked run and the pile's flute coincide, and this needs no
state-side reasoning at all — the two halves are both invariant clauses:

* `PileBase.flute_not_aces` bounds the flute above: it never reaches past the
  foundation top, so `pileFlute ≤ VALUE boundary - VALUE aces[suit] = found + 1`;
* `PileMerged.flute_maximal` bounds it below: the card just under the flute is
  either the foundation top itself, or not free — and the walk has just certified
  that every card of the suit strictly between the foundation top and the boundary
  *is* free, so the second case forces it to be the foundation top.

Consequently the top `found + 1` cards of the boundary's column are exactly the
walked run plus the boundary, in ascending order from the top — so the sync step
plays them straight off that one column with `playsAll_column`, and no other pile
or cell is touched. -/

/-- **The flute at a sync point is exactly the walked run plus the boundary.** -/
theorem flute_eq_of_walk {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (i : Fin 10) (hm : PileMerged g p i (hb.pileDepth_bound i))
    (hd : 0 < (p.pileDepth.get i).toNat)
    (hidx : (p.pileDepth.get i).toNat - 1 < 5)
    (hs4 : (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat < 4)
    (hfreebelow : ∀ c : UInt8, SUIT c = SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) →
      (VALUE (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat < (VALUE c).toNat →
      (VALUE c).toNat < (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat → isFreeCard g p c) :
    (p.pileFlute.get i).toNat
      = (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (VALUE (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat := by
  have hbcs := SUIT_toNat ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)
  have hbcv := VALUE_toNat ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)
  have hAs := SUIT_toNat (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)
  have hAv := VALUE_toNat (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)
  have hbc256 : (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat < 256 := UInt8.toNat_lt _
  have hA256 : (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).toNat < 256 := UInt8.toNat_lt _
  -- `aces[s]` carries suit `s`
  have hAsuitN : (SUIT (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩)).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := by
    rw [(hb.aces_kings_valid ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).1]
    show (UInt8.ofNat (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat
    rw [UInt8.toNat_ofNat']
    omega
  -- upper bound: the flute never reaches past the foundation top
  have hle : (p.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat, hs4⟩).toNat + (p.pileFlute.get i).toNat
      ≤ (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := (hb.pileBase i).flute_not_aces hd hs4
  have hfl1 : 1 ≤ (p.pileFlute.get i).toNat := (hb.pileBase i).flute_pos
  -- the card just below the flute
  have hsubN : (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i).toNat = (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (p.pileFlute.get i).toNat := by
    rw [UInt8.toNat_sub]
    omega
  have hsubs : (SUIT (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i)).toNat = (SUIT ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat := by
    rw [SUIT_toNat, hsubN]
    omega
  have hsubv : (VALUE (((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩) - p.pileFlute.get i)).toNat
      = (VALUE ((g.pos2card.get i).get ⟨(p.pileDepth.get i).toNat - 1, hidx⟩)).toNat - (p.pileFlute.get i).toNat := by
    rw [VALUE_toNat, hsubN, hbcv]
    omega
  -- lower bound: `flute_maximal`
  rcases hm.flute_maximal with hz | hmax
  · exact absurd (congrArg UInt8.toNat hz) (by
      show ¬ ((p.pileDepth.get i).toNat = (0 : UInt8).toNat)
      have : ((0 : UInt8)).toNat = 0 := by decide
      omega)
  · simp only [] at hmax
    rcases hmax with ⟨hs4', heq⟩ | hnf
    · -- the flute reaches down to the foundation top
      have := congrArg UInt8.toNat heq
      rw [hsubN] at this
      omega
    · -- otherwise the card below would be free, which the walk excludes
      by_contra hne
      refine hnf (hfreebelow _ (UInt8.toNat_inj.mp hsubs) (by rw [hsubv]; omega)
        (by rw [hsubv]; omega))
