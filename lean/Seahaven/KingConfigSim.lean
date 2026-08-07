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

The two depth hypotheses are what rule out interference: `a` is not empty before,
so no suit owns it; and afterwards it is either still non-empty (so no suit must
start owning it) or its *column* is physically empty, so a suit could only claim it
vacuously and `no_pile` survives either way.  `preCleanupPile` takes the first
alternative (its merge count satisfies `m < pileDepth[a]`); the drain's sync step
takes the second when it plays a depth-1 pile out entirely. -/
theorem StateMatchesKingConfig.framePile {g : Globals} {s v : State} {p q : SolverPosType}
    {k : Fin 16} {a : Fin 10} (hk : StateMatchesKingConfig g s p k)
    (hreach : Reach s v) (hmatch : StateMatchesSolverPos g v q)
    (hda : 0 < (p.pileDepth.get a).toInt.toNat)
    (hqda : 0 < (q.pileDepth.get a).toInt.toNat ∨ v.tableau a = [])
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
  · -- `q`'s empty piles are `p`'s empty piles, or the freshly emptied column
    intro su hsu
    refine (hk.no_pile su hsu).frame (fun i hi => ?_)
    by_cases hia : i = a
    · subst hia
      rcases hqda with hpos | hnil
      · omega
      · exact Or.inr (fun d hd => by rw [hnil] at hd; simp at hd)
    · exact Or.inl ⟨by rw [← hqdne i hia]; exact hi, hframe i hia⟩

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
  hk.framePile hreach hmatch hda (Or.inl hqda) hframe
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
    refine hk.framePile hreach hmatch hdane (Or.inl ?_) hframe ?_ hqk
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
      (g.pos2card.get j).get ⟨_, hidxj⟩ = B → p.pileFlute.get j = 1) :
    ∃ (v : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g s p k v
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).2
        k' FK
        (cleanupRunResult pile hpile B ph hs4'
          (p.pileDepth[pile.toNat]'hpile).toInt32 m f p).1 := by
  obtain ⟨v, hreach, hframe, hmatch, hexport⟩ :=
    hk.toMatches.cleanupRunResult_sim hwf hb hpile hs4' hidx hd1 hfl1 hB hm hchain hf hfree
      haces hBflute1
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

/-! ## Where free cards sit in a column

Two structural facts used throughout the simulations, and by `SimulateMoveAces` in
particular: a free card is above its pile's boundary, and the card directly above a
free card is same-suit with a lower rank. -/

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

/-- Membership in one column bounds the whole-tableau count. -/
theorem one_le_countTableau {t : Fin 10 → Column} {c : Card} {q : Fin 10}
    (h : c ∈ t q) : 1 ≤ countTableau t c := by
  unfold countTableau
  rw [List.sum_ofFn]
  exact le_trans (one_le_countColumn h)
    (Finset.single_le_sum (f := fun j : Fin 10 => countColumn (t j) c)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))

theorem rankToNat_inj {r r' : Rank} (h : rankToNat r = rankToNat r') : r = r' := by
  cases r <;> cases r' <;> simp_all [rankToNat]

/-- Same suit and same rank number means the same card. -/
theorem card_eq_of_suit_rank {x y : Card} (hs : x.suit = y.suit)
    (hr : rankToNat x.rank = rankToNat y.rank) : x = y := by
  obtain ⟨xs, xr⟩ := x
  obtain ⟨ys, yr⟩ := y
  simp only [] at hs hr
  rw [hs, rankToNat_inj hr]

/-! ### The column after the sync step

`flute_eq_of_walk` says the top `found + 1` cards of the boundary's column are the
walked run followed by the boundary.  Playing them all off therefore leaves exactly
the dealt cards *below* the old boundary — which is precisely the column
`removeFlutePre`'s decremented depth describes, with an empty flute (`fluteNorm`'s
`pileFlute := 1`).  This is that surgery at the `PileMatches` level. -/

/-- **Dropping a column's whole flute together with its boundary** lowers the depth
by one and empties the flute.  `k` is the number of flute *interiors*, so the column
has `n + k` cards and `k + 1` are removed. -/
theorem PileMatches_drop_flute {g : Globals} {col : Column} {i : Fin 10} {n : Fin 6} {k : Nat}
    (h : PileMatches g col i n) (hn : 0 < n.val) (hlen : col.length = n.val + k)
    (hn6 : n.val - 1 < 6) :
    PileMatches g (col.drop (k + 1)) i ⟨n.val - 1, hn6⟩ := by
  obtain ⟨h1, h2, -⟩ := h
  have hdlen : (col.drop (k + 1)).length = n.val - 1 := by
    simp only [List.length_drop, hlen]
    omega
  have hrev : (col.drop (k + 1)).reverse = List.take (n.val - 1) col.reverse := by
    rw [List.reverse_drop, hlen]
    congr 1
    omega
  have hempty : (col.drop (k + 1)).reverse.drop (n.val - 1) = [] := by
    refine List.drop_eq_nil_of_le ?_
    rw [List.length_reverse, hdlen]
  refine ⟨show n.val - 1 ≤ (col.drop (k + 1)).length from by omega, ?_, ?_⟩
  · -- the surviving dealt cards are still the layout's
    intro j
    have hjlt : j.val < n.val - 1 := j.isLt
    have htake : (List.take (n.val - 1) col.reverse)[j.val]? = col.reverse[j.val]? :=
      List.getElem?_take_of_lt hjlt
    rw [hrev, htake]
    exact h2 ⟨j.val, by omega⟩
  · -- nothing is left above the new boundary
    by_cases hn1 : 0 < n.val - 1
    · rw [dif_pos hn1]
      show IsSameSuitDescending _ _ (((col.drop (k + 1)).reverse.drop (n.val - 1)).map encodeCard)
      rw [hempty]
      intro idx
      exact absurd idx.isLt (by simp)
    · rw [dif_neg hn1]
      refine ⟨0, ?_⟩
      show IsSameSuitDescending _ _ (((col.drop (k + 1)).reverse.drop (n.val - 1)).map encodeCard)
      rw [hempty]
      intro idx
      exact absurd idx.isLt (by simp)

/-! ### The played segment is a run

`playsAll_column` needs the segment coming off the top to be an `IsRun`.  Inside a
column that is exactly what `flute_elem` says: consecutive positions carry the same
suit with the value climbing by one towards the boundary. -/

/-- Consecutive-successor lists are runs. -/
theorem isRun_of_succ : ∀ {l : List Card},
    (∀ (a : Nat) (ha : a + 1 < l.length),
      nextCard (l[a]'(by omega)) = some (l[a + 1]'ha)) → IsRun l
  | [], _ => trivial
  | [_], _ => ⟨by simp, trivial⟩
  | x :: y :: l, h => by
    refine ⟨?_, isRun_of_succ (l := y :: l) (fun a ha => ?_)⟩
    · intro z hz
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h 0 (by simp)
    · exact h (a + 1) (by simpa using ha)

/-- **The top of a column, down to and including the boundary, is a run.** -/
theorem StateMatchesSolverPos.isRun_take {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10)
    (hd : 0 < (p.pileDepth.get i).toInt.toNat) (m : Nat)
    (hm : m ≤ (s.tableau i).length + 1 - (p.pileDepth.get i).toInt.toNat) :
    IsRun ((s.tableau i).take m) := by
  have hidx : (p.pileDepth.get i).toInt.toNat - 1 < 5 := by have := h.depth_lt6 i; omega
  refine isRun_of_succ (fun a ha => ?_)
  have hmlen : ((s.tableau i).take m).length ≤ m := by simp only [List.length_take]; omega
  have ha1 : a + 1 < m := by omega
  have haL : a < (s.tableau i).length := by
    have : ((s.tableau i).take m).length ≤ (s.tableau i).length := by
      simp only [List.length_take]; omega
    omega
  have ha1L : a + 1 < (s.tableau i).length := by
    have : ((s.tableau i).take m).length ≤ (s.tableau i).length := by
      simp only [List.length_take]; omega
    omega
  -- the two entries of the run
  obtain ⟨hsa, hva⟩ := flute_elem h i hd ⟨_, hidx⟩ rfl a (by omega) haL
  obtain ⟨hsb, hvb⟩ := flute_elem h i hd ⟨_, hidx⟩ rfl (a + 1) (by omega) ha1L
  have hget : ∀ (b : Nat) (hb : b < m) (hbL : b < (s.tableau i).length),
      ((s.tableau i).take m)[b]'(by simp only [List.length_take]; omega)
        = (s.tableau i)[b]'hbL := by
    intro b hb hbL
    exact List.getElem_take ..
  rw [hget a (by omega) haL, hget (a + 1) ha1 ha1L]
  refine nextCard_of_encode ?_ ?_
  · rw [hsa, hsb]
  · have hv1 := rankToNat_pos ((s.tableau i)[a]'haL).rank
    have hv2 := rankToNat_pos ((s.tableau i)[a + 1]'ha1L).rank
    rw [encodeCard_VALUE] at hva hvb ⊢
    rw [encodeCard_VALUE]
    omega


/-- **A phase that touches no column at all** carries the king configuration
unchanged: every owned pile keeps its depth, its `kings` entry and its column, and no
new solver-empty pile appears.  This is the drain's tail, where the whole run comes out
of the cells. -/
theorem StateMatchesKingConfig.frameAll {g : Globals} {s v : State} {p q : SolverPosType}
    {k : Fin 16} (hk : StateMatchesKingConfig g s p k)
    (hreach : Reach s v) (hmatch : StateMatchesSolverPos g v q)
    (hframe : ∀ i : Fin 10, v.tableau i = s.tableau i)
    (hqd : ∀ i : Fin 10, q.pileDepth.get i = p.pileDepth.get i)
    (hqkings : q.kings = p.kings) :
    Simulates g s p k v q k ∅ 0xffff := by
  refine Simulates.ofReach hreach ⟨hmatch, ?_, ?_⟩
  · obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    exact ⟨assign, fun su i hi =>
      (hown su i hi).frame (hqd i) (by rw [hqkings]) (hframe i), hinj, hiff⟩
  · intro su hsu
    exact (hk.no_pile su hsu).frame (fun i hi => Or.inl ⟨by rw [← hqd i]; exact hi, hframe i⟩)
