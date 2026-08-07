import Seahaven.MoveAcesSim
import Seahaven.SolverSpecMove
import Seahaven.SolverSpecDrain

/-!
# A whole `SolverMove` call, simulated

`SolverMove` is three phases (`moveDest_run_eq`):

1. the destination bookkeeping write — `moveDestPre`, whose `Rules`-side realization is
   `fluteMoves`/`parkMoves` (`MoveSim.lean`, `StateMatchesKingConfig.movePre_run*`);
2. `SolverRemoveFlute pile` — `Simulates.ofRemoveFlute`, entered at exactly
   `SolverSpec.movePre pile toPile hpile p`, the composed
   `fluteNorm ∘ removeFlutePre ∘ moveDestPre` point;
3. the `while busyAces ≠ 0` drain — `Simulates.moveAces` per iteration, carried through
   the loop by `SolverSpec.drain_canonical_of`.

Phases 2 and 3 are proved here and composed with phase 1, which enters as a hypothesis.
Two things are still needed to discharge it, and neither is in this file:

* `StateMatchesKingConfig.movePre_run` currently yields only `Reach s v` plus the
  *matching* at `movePre …`.  For the configuration side one also needs the **tableau
  frame** — that only the source pile, the destination pile and the cells changed.  The
  underlying `movePre_pileDest`/`movePre_kingDest`/… already return the `fluteMoves`/
  `parkMoves` fold that produced `v` (`movePre_run` discards it), so the frame is a
  statement about those move lists, not new semantic work.
* with the frame in hand, a two-column variant of `StateMatchesKingConfig.framePile`.
  The configuration is *preserved* by every destination — no phase-1 move vacates a king
  (the vacate happens inside `SolverCleanupPile`, which `ofRemoveFlute` already covers):
  the source pile has depth ≥ 1 so no suit owns it, and it either keeps depth ≥ 1 or ends
  up with a physically empty column; a column destination keeps depth ≥ 1; and a king
  destination lands on the column its suit already owns (whose *deepest* card, hence
  `OwnsPile`, is untouched) or, when the suit is unpiled, in the cells — where `no_pile`
  is exactly what licenses the `kings[su]` write.

The free-cell side conditions of phase 1 are what `solverGetMovable`'s spec supplies;
that spec is what `MoveSimulated` will feed in.
-/

open Lean Lean.Order

/-- **Extending a simulation backwards by a phase that keeps the configuration.**  Dual
to `Simulates.extend`: here the *first* phase's mask is dropped and the second's kept,
which is what the composition of `SolverMove` needs — phase 1 contributes no mask of its
own (the solver does not intersect anything before `SolverRemoveFlute` returns), while
phases 2 and 3 contribute the returned `forcedKings`. -/
theorem Simulates.prepend {g : Globals} {s w v : State} {p q r : SolverPosType}
    {k k' : Fin 16} {FK FK' : Finset Suit} {fk fk' : UInt16}
    (h : Simulates g s p k w q k FK fk) (h' : Simulates g w q k v r k' FK' fk') :
    Simulates g s p k v r k' FK' fk' where
  reach := h.reach.trans h'.reach
  cfg := h'.cfg
  vacates := h'.vacates
  bound := h'.bound

/-- **The `busyAces` drain loop is simulated.**  One `Simulates.moveAces` per iteration;
the loop's accumulator `forcedKings := forcedKings &&& (← SolverMoveAces)` is exactly
what `Simulates.trans` does to the masks, so the mask of the result is the mask the loop
returns. -/
theorem Simulates.drain {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) {q : SolverPosType} {fk0 : UInt16}
    (hmerged : SolverInvMerged g q) (hP : MoveAcesSim g s p k fk0 q) :
    ∃ (fk : UInt16) (q' : SolverPosType),
      Loop.forIn Loop.mk fk0 drainBody (g, q) = .ok fk (g, q') ∧
      IsCanonicalPos g q' ∧ MoveAcesSim g s p k fk q' := by
  refine SolverSpec.drain_canonical_of g q fk0 hwf hmerged (MoveAcesSim g s p k) ?_ hP
  intro fkAcc fk game game1 hm hbz hrun hPacc
  obtain ⟨w, kk, FK, hsimW⟩ := hPacc
  obtain ⟨fk2, p2, hrun2, s2, k2, FK2, hsim2⟩ := Simulates.moveAces hwf hm hbz hsimW.cfg
  -- the solver's own run pins the mask and the successor position
  have hrun' : EStateM.run _root_.SolverMoveAces (g, game) = .ok fk (g, game1) := hrun
  injection hrun2.symm.trans hrun' with h1 h2
  injection h2 with _hg hp2
  subst h1
  subst hp2
  exact ⟨s2, k2, FK ∪ FK2, hsimW.trans hsim2⟩

set_option maxHeartbeats 1000000 in
/-- **A whole `SolverMove` call is simulated.**  Phases 2 and 3 are discharged here;
phase 1 — the flute move itself — enters as `hphase1`, in the shape
`StateMatchesKingConfig.movePre_run_of_dest_inv` produces (`Reach` to a state matching
`movePre …`) once its configuration side is added.

The mask is the one `SolverMove` returns, so this composes into
`solverRecCheckSolvable`'s `forcedKings` handling directly (`kingStep_transport`), and the
resulting position is canonical — which is what the next recursion level's
`StateMatchesKingConfig` hypothesis needs. -/
theorem Simulates.move {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (pile : UInt32) (toPile : UInt8) (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hvalid : SolverSpec.MoveValid g p pile toPile) (hpile : pile.toNat < 10)
    (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5) (B : UInt8)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (hdv : SolverSpec.DestValid g p B toPile)
    (hphase1 : ∃ v : State,
      Simulates g s p k v (SolverSpec.movePre pile toPile hpile p) k ∅ 0xffff) :
    ∃ (fk : UInt16) (p' : SolverPosType) (s' : State) (k' : Fin 16) (FK : Finset Suit),
      EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ Simulates g s p k s' p' k' FK fk := by
  obtain ⟨-, htoPile14, hd0⟩ := hvalid
  have hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by
    have heq : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hpile)
    rwa [heq] at hd0
  have hmerged := hcanon.toSolverInvMerged
  have hready := SolverSpec.moveDest_cleanupReady g p pile toPile hpile hwf hmerged hd1 B
    hidx5 hBdef hdv
  -- phase 2: the `SolverRemoveFlute` call
  obtain ⟨fk1, p1, hrun1, hmerged1, -, -⟩ :=
    SolverSpec.removeFlute_merged pile g (SolverSpec.moveDestPre pile toPile hpile p) hpile hwf hready
  have hrun1' : _root_.SolverRemoveFlute pile (g, SolverSpec.moveDestPre pile toPile hpile p)
      = .ok fk1 (g, p1) := hrun1
  obtain ⟨v, hsim1⟩ := hphase1
  obtain ⟨v2, k2, FK2, hsim2⟩ := Simulates.ofRemoveFlute hwf hpile hready hsim1.cfg hrun1'
  -- phase 3: the drain
  obtain ⟨fk2, p2, hrun2, hcanon2, hP2⟩ :=
    Simulates.drain hwf hmerged1 ⟨v2, k2, FK2, hsim1.prepend hsim2⟩
  obtain ⟨s2, k3, FK3, hsim3⟩ := hP2
  refine ⟨fk2, p2, s2, k3, FK3, ?_, hcanon2, hsim3⟩
  -- and the two phases really are the whole call
  rw [SolverSpec.moveDest_run_eq pile toPile g p hpile htoPile14]
  show (_root_.SolverRemoveFlute pile >>= fun fk =>
      Loop.forIn Loop.mk fk drainBody >>= fun r => pure r)
    (g, SolverSpec.moveDestPre pile toPile hpile p) = .ok fk2 (g, p2)
  simp only [bind, EStateM.bind, hrun1', pure, EStateM.pure]
  rw [hrun2]
