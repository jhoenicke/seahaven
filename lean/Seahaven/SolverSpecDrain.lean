import Seahaven.SolverSpecMoveAces

/-!
# Spec for the `busyAces` drain loop

`rank`, the termination measure for the `while busyAces ≠ 0 do SolverMoveAces
()` loop, `rank_decrease` (it strictly drops on every iteration, via
`moveAces_merged`'s dichotomy), the exact symbolic run `drainBody_run`, and
`drain_canonical`: draining from a merged state reaches a fully canonical one.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-- **Termination measure for the `busyAces` drain loop.**  A plain sum, over
    the 4 suits, of how far each suit's foundation still has to climb to reach
    `13` (`King`), scaled by `16` and padded with `busyAces.toNat` (`< 16` via
    `busyAces_lt16`, so it never disturbs the ordering set by the first
    term).  `moveAces_merged`'s dichotomy (`rank_decrease` below) shows this
    strictly drops on every drain-loop iteration. -/
private def rank (game : SolverPosType) : Nat :=
  ((13 - (VALUE (game.aces.get (0 : Fin 4))).toNat) +
    (13 - (VALUE (game.aces.get (1 : Fin 4))).toNat) +
    (13 - (VALUE (game.aces.get (2 : Fin 4))).toNat) +
    (13 - (VALUE (game.aces.get (3 : Fin 4))).toNat)) * 16 + game.busyAces.toNat

/-- **`rank` strictly decreases across one `moveAces_merged` step.**  Uses
    exactly the dichotomy exposed by `moveAces_merged`'s strengthened
    conclusion: either the processed suit's own ace strictly advances (so the
    sum term drops by `≥ 1`, swamping any change to the `< 16` remainder), or
    the aces are entirely unchanged and `busyAces.toNat` itself strictly
    drops. -/
private theorem rank_decrease (g : Globals) (game game1 : SolverPosType)
    (hmerged : SolverInvMerged g game) (hmerged1 : SolverInvMerged g game1)
    (hbusy : game.busyAces ≠ 0)
    (hframe1 : ∀ s : Fin 4, s.val ≠ ctz game.busyAces → game1.aces.get s = game.aces.get s)
    (hdich1 : ∀ s : Fin 4, s.val = ctz game.busyAces →
      (VALUE (game1.aces.get s)).toNat > (VALUE (game.aces.get s)).toNat ∨
      (game1.aces = game.aces ∧ game1.busyAces.toNat < game.busyAces.toNat)) :
    rank game1 < rank game := by
  have hsuit4 : ctz game.busyAces < 4 :=
    ctz_lt_four_of_low_nibble game.busyAces (by
      rw [uint8_and_0xF_eq_self_of_lt16 game.busyAces hmerged.busyAces_lt16]; exact hbusy)
  have hb0 : (VALUE (game.aces.get (0 : Fin 4))).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 0).2.1
  have hb1 : (VALUE (game.aces.get (1 : Fin 4))).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 1).2.1
  have hb2 : (VALUE (game.aces.get (2 : Fin 4))).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 2).2.1
  have hb3 : (VALUE (game.aces.get (3 : Fin 4))).toNat ≤ 13 :=
    (hmerged.aces_kings_valid 3).2.1
  have hb0' : (VALUE (game1.aces.get (0 : Fin 4))).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 0).2.1
  have hb1' : (VALUE (game1.aces.get (1 : Fin 4))).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 1).2.1
  have hb2' : (VALUE (game1.aces.get (2 : Fin 4))).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 2).2.1
  have hb3' : (VALUE (game1.aces.get (3 : Fin 4))).toNat ≤ 13 :=
    (hmerged1.aces_kings_valid 3).2.1
  have hbz16 : game1.busyAces.toNat < 16 := by
    have := hmerged1.busyAces_lt16
    rwa [UInt8.lt_iff_toNat_lt, show ((16 : UInt8).toNat = 16) from by decide] at this
  have hcase : ctz game.busyAces = 0 ∨ ctz game.busyAces = 1 ∨ ctz game.busyAces = 2 ∨
      ctz game.busyAces = 3 := by omega
  unfold rank
  rcases hcase with h | h | h | h
  · have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf1, hf2, hf3]
    rcases hdich1 0 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := by
        rw [haeq]
      rw [hf0]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf0, hf2, hf3]
    rcases hdich1 1 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := by
        rw [haeq]
      rw [hf1]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := hframe1 3 (by omega)
    rw [hf0, hf1, hf3]
    rcases hdich1 2 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := by
        rw [haeq]
      rw [hf2]; omega
  · have hf0 : game1.aces.get (0 : Fin 4) = game.aces.get (0 : Fin 4) := hframe1 0 (by omega)
    have hf1 : game1.aces.get (1 : Fin 4) = game.aces.get (1 : Fin 4) := hframe1 1 (by omega)
    have hf2 : game1.aces.get (2 : Fin 4) = game.aces.get (2 : Fin 4) := hframe1 2 (by omega)
    rw [hf0, hf1, hf2]
    rcases hdich1 3 (by omega) with hv | ⟨haeq, hbdec⟩
    · omega
    · have hf3 : game1.aces.get (3 : Fin 4) = game.aces.get (3 : Fin 4) := by
        rw [haeq]
      rw [hf3]; omega

/-- What the drain loop hands to a carried predicate: one `SolverMoveAces` call from a
merged, still-pending position, with the mask the code intersects in.  `Simulates` is
carried across it by `Simulates.moveAces` (see `Simulates.drain`). -/
def DrainStep (g : Globals) (P : UInt16 → SolverPosType → Prop) : Prop :=
  ∀ (fkAcc fk : UInt16) (game game1 : SolverPosType),
    SolverInvMerged g game → game.busyAces ≠ 0 →
    _root_.SolverMoveAces (g, game) = .ok fk (g, game1) →
    P fkAcc game → P (fkAcc &&& fk) game1

/-- **Exact run of the `busyAces` drain loop, with its invariant.**  By
    induction on a `Nat` bounding `rank game` (which strictly decreases on
    every continuing iteration via `rank_decrease`/`moveAces_merged`).  `P` is
    carried across each iteration by `hstep`. -/
private theorem drainBody_run (g : Globals) (hwf : WellFormedLayout g)
    (P : UInt16 → SolverPosType → Prop) (hstep : DrainStep g P) :
    ∀ (n : Nat) (forcedKings : UInt16) (game : SolverPosType),
      rank game < n →
      SolverInvMerged g game →
      P forcedKings game →
      ∃ (forcedKings' : UInt16) (game' : SolverPosType),
        Loop.forIn Loop.mk forcedKings drainBody (g, game) =
          .ok forcedKings' (g, game') ∧
        SolverInvMerged g game' ∧ game'.busyAces = 0 ∧ P forcedKings' game' := by
  intro n
  induction n with
  | zero => intro forcedKings game hmeas _ _; omega
  | succ n ih =>
    intro forcedKings game hmeas hmerged hP
    have hunf := Loop.forIn_eq_of_monadTail (m := EStateM Error (Globals × SolverPosType))
      (l := Loop.mk) (b := forcedKings) (f := drainBody)
    by_cases hbz : game.busyAces = 0
    · refine ⟨forcedKings, game, ?_, hmerged, hbz, hP⟩
      rw [hunf]
      simp only [drainBody, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hbz,
        Bool.false_eq_true, bne_self_eq_false, reduceIte, pure, EStateM.pure]
    · obtain ⟨fk, game1, hrun1, hmerged1, hframe1, hdich1, -⟩ :=
        moveAces_merged g game hwf hmerged hbz
      have hrun1' : _root_.SolverMoveAces (g, game) = .ok fk (g, game1) := hrun1
      have hdec : rank game1 < rank game := rank_decrease g game game1 hmerged hmerged1 hbz
        hframe1 hdich1
      have hmeas1 : rank game1 < n := by omega
      obtain ⟨fk', game', hrun', hmerged', hbz', hP'⟩ :=
        ih (forcedKings &&& fk) game1 hmeas1 hmerged1
          (hstep forcedKings fk game game1 hmerged hbz hrun1' hP)
      refine ⟨fk', game', ?_, hmerged', hbz', hP'⟩
      rw [hunf]
      simp only [drainBody, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hbz,
        bne_iff_ne, ne_eq, not_false_eq_true, reduceIte, hrun1', pure, EStateM.pure]
      exact hrun'

/-- **The drain loop reaches canonical form.**  From a merged state, draining
    `busyAces` via the real `while busyAces ≠ 0 do SolverMoveAces()` loop
    (`drainBody`, shared by `SolverMove` and `SolverConvertFromPilesKings`)
    reaches a fully canonical state. -/
theorem drain_canonical (g : Globals) (p : SolverPosType) (fk0 : UInt16)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) :
    ∃ fk p', Loop.forIn Loop.mk fk0 drainBody (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ DepthLe p p' := by
  obtain ⟨fk, p', hrun, hmerged', hbz, hle⟩ :=
    drainBody_run g hwf (fun _ game => DepthLe p game)
      (by
        -- each iteration is one `SolverMoveAces`, and those never deepen a pile
        intro _fkAcc fk game game1 hm hbz hrunMA hP
        obtain ⟨fk2, p2, hrun2, -, -, -, hle2⟩ := moveAces_merged g game hwf hm hbz
        have hrunMA' : EStateM.run _root_.SolverMoveAces (g, game) = .ok fk (g, game1) := hrunMA
        injection hrun2.symm.trans hrunMA' with h1 h2
        injection h2 with _hg hp2
        subst hp2
        exact hP.trans' hle2)
      (rank p + 1) fk0 p (by omega) hmerged (DepthLe.rfl' p)
  exact ⟨fk, p', hrun, IsCanonicalPos.of_merged_drained hmerged' hbz, hle⟩

/-- **The drain loop, carrying a predicate across each `SolverMoveAces` call.**  Same
run as `drain_canonical`; the extra `P` is what lets the simulation ride along with the
accumulating `forcedKings` mask (`Simulates.drain`). -/
theorem drain_canonical_of (g : Globals) (p : SolverPosType) (fk0 : UInt16)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (P : UInt16 → SolverPosType → Prop) (hstep : DrainStep g P) (hP : P fk0 p) :
    ∃ fk p', Loop.forIn Loop.mk fk0 drainBody (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ P fk p' := by
  obtain ⟨fk, p', hrun, hmerged', hbz, hP'⟩ :=
    drainBody_run g hwf P hstep (rank p + 1) fk0 p (by omega) hmerged hP
  exact ⟨fk, p', hrun, IsCanonicalPos.of_merged_drained hmerged' hbz, hP'⟩

end SolverSpec
