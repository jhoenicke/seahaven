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
  · simp only [hk, Bool.false_eq_true, reduceIte]
    exact KingVacates.empty
  · simp only [hk, reduceIte]
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
    · simp only [hc, if_neg, ite_false] at hi
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
