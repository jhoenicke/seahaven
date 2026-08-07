import Seahaven.SimulateMoveAces
import Seahaven.SolverSpecMoveAces

/-!
# `SolverMoveAces`, simulated end to end

`SimulateMoveAces.lean` proves the two *kinds* of step the `busyAces` drain makes on
the `Rules` side — the sync step (`Simulates.syncPlays`, composed with
`Simulates.ofCleanupRun`) and the walk's tail (`Simulates.tailPlays`,
`StateMatchesSolverPos.tailPlaysComplete`).  This file runs the loop.

The walk itself is `moveAcesLoop_run`, which is parametric in a predicate carried
across its one position-changing step (`SolverSpec.MoveAcesSyncStep`).  Instantiating
that predicate with

> `MoveAcesSim g s p k fk q` — *`q` is simulated from the entry state `s`, with the
> accumulated `forcedKings` mask `fk`*

turns the loop into the induction we need: the counting iterations leave the position
alone (so the predicate rides along untouched — this is what the deferral design buys),
and the sync iterations are exactly one `Simulates.trans`.  The mask bookkeeping comes
out right because `Simulates.trans` intersects masks exactly as the code's
`forcedKings := forcedKings &&& (← SolverRemoveFlute pile)` does.
-/

/-- **Extending a simulation by a phase that leaves the configuration alone.**
`Simulates.trans` would intersect the masks; here the second phase's mask is
discarded instead, which is what the drain wants at its two "free" joins (the
sync step's `syncPlays` prologue and the walk's tail), where the *solver* does
not intersect anything either. -/
theorem Simulates.extend {g : Globals} {s w v : State} {p q r : SolverPosType}
    {k kk : Fin 16} {FK FK' : Finset Suit} {fk fk' : UInt16}
    (h : Simulates g s p k w q kk FK fk) (h' : Simulates g w q kk v r kk FK' fk') :
    Simulates g s p k v r kk FK fk where
  reach := h.reach.trans h'.reach
  cfg := h'.cfg
  vacates := h.vacates
  bound := h.bound

/-- **The drain's carried relation.**  `fk` is the walk's accumulated `forcedKings`,
`q` the position it has reached; the state that realizes `q` and the configuration
it realizes it at are existential — nothing downstream of the loop needs to name
them. -/
def MoveAcesSim (g : Globals) (s : State) (p : SolverPosType) (k : Fin 16)
    (fk : UInt16) (q : SolverPosType) : Prop :=
  ∃ (w : State) (k' : Fin 16) (FK : Finset Suit), Simulates g s p k w q k' FK fk

/-! ## The sync step -/

/-- **A whole `SolverRemoveFlute` call is simulated**, from the composed
`fluteNorm ∘ removeFlutePre` point the cleanup is entered at — the same state
`removeFlute_merged` is stated at, and the one both `SolverMove`'s phase 1 and the
drain's sync step hand over.

`removeFlute_eq` reduces the call to `SolverCleanupPile` at `removeFlutePre …`, which
differs from the entry point only in the (unread, stale) `pileFlute[pile]`; from there
`cleanupPile_empty_eq` / `cleanupPile_nonempty_eq` give the run and
`Simulates.ofCleanupRun` the simulation.

What is left is `ofCleanupRun`'s remaining hypotheses: the merge chain (`chain_of_mcards`
from the merge guards), the extension's `hfree`/`haces` (the freed guards, via
`isFree_of_card2depth_ge` — `freedIter_eq` makes each guard literally "`B - 1 - i` is
free and outranks the foundation", so no induction is needed), and `hBflute1` (the
boundary is unique by `pos2card_inj`, and `fluteNorm` just set this pile's flute to 1). -/
theorem Simulates.ofRemoveFlute {g : Globals} {v : State} {gameA : SolverPosType}
    {kk : Fin 16} (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hready : SolverSpec.CleanupReady g
      (SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA)) pile)
    (hk : StateMatchesKingConfig g v
      (SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA)) kk)
    {fk : UInt16} {p' : SolverPosType}
    (hrun : _root_.SolverRemoveFlute pile (g, gameA) = .ok fk (g, p')) :
    ∃ (v' : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g v (SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA))
        kk v' p' k' FK fk := by
  sorry

/-- **The walk's one position-changing step is simulated.**  `Simulates.syncPlays`
plays the pile's flute together with its boundary onto the foundation — landing
exactly at the position the cleanup is entered at, since `MoveAcesInv` pins the flute
to the walked run (`found + 1` cards) — and `Simulates.ofRemoveFlute` takes over from
there.  The masks compose by `Simulates.trans`, matching the code's
`forcedKings &&& (← SolverRemoveFlute pile)`. -/
theorem moveAcesSim_sync {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) (suit : Fin 4) :
    SolverSpec.MoveAcesSyncStep g suit (MoveAcesSim g s p k) := by
  intro card found forcedKings fk game gameA q p' pile hpile hinv hdpos hbnd hflute hqdef
    hqds hqdne hqfs hqfne hqk hqas hqane hready hrun hP
  subst hqdef
  obtain ⟨w, kk, FK, hsimW⟩ := hP
  obtain ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
  -- the walked suit, on the `Rules` side
  have hsu : suitToNat (natToSuit suit) = suit.val := suitToNat_natToSuit suit
  have hfin : finOfSuit (natToSuit suit) = suit := Fin.ext hsu
  have hbridge : ∀ x : UInt8, x.toInt.toNat = x.toNat := fun _ => rfl
  have hd5 : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 :=
    hmerged.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hidxN : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by omega
  have hidx : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5 := by
    rw [hbridge]; exact hidxN
  have hd : 0 < (game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat := by
    rw [hbridge]; exact hdpos
  -- the boundary card is `card`
  have hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1, hidx⟩ = card := hbnd hidxN
  have hcardReal : IsRealCard card := by
    rw [← hB]; exact hwf.pos2card_real _ _
  obtain ⟨bc, hbc⟩ := exists_encodeCard hcardReal
  -- the sync step's hypotheses, one by one
  have hbsuit : (SUIT ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1, hidx⟩)).toNat
      = suitToNat (natToSuit suit) := by
    rw [hB, hsuitcard, SolverSpec.finVal_toUInt8_toNat, hsu]
  have hAsuit : SUIT (game.aces.get suit) = suit.val.toUInt8 :=
    (hmerged.aces_kings_valid suit).1
  have hbval : (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1, hidx⟩)).toNat
      = optRankToNat (w.foundations (natToSuit suit)) + found.toNat + 1 := by
    rw [hB, ← hsimW.cfg.toMatches.foundation_value (natToSuit suit), hfin]
    have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
    have hsa := SUIT_toNat (game.aces.get suit); have hva := VALUE_toNat (game.aces.get suit)
    have hSeq : (SUIT card).toNat = (SUIT (game.aces.get suit)).toNat := by
      rw [hsuitcard, hAsuit]
    have hfb : found.toInt = (found.toNat : Int) := rfl
    omega
  have hqd' : ((SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA)).pileDepth.get
      ⟨pile.toNat, hpile⟩).toInt.toNat
      = (game.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 := by
    rw [hbridge, hbridge, hqds]
    exact UInt8.toNat_sub_of_le _ _ (by
      rw [UInt8.le_iff_toNat_le]
      have h1 : (1 : UInt8).toNat = 1 := by decide
      omega)
  have hqf' : ((SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA)).pileFlute.get
      ⟨pile.toNat, hpile⟩).toNat = 1 := by rw [hqfs]; decide
  have hqasu' : (SolverSpec.fluteNorm pile hpile
      (removeFlutePre pile hpile gameA)).aces.get (finOfSuit (natToSuit suit))
      = encodeCard bc := by rw [hfin, hqas, hbc]
  obtain ⟨v, hsim1⟩ :=
    Simulates.syncPlays (su := natToSuit suit) (bc := bc) (found := found.toNat)
      hsimW.cfg ⟨pile.toNat, hpile⟩ hd hidx hbsuit (hbc.trans hB.symm) hflute hbval hqd'
      (fun j hj => hqdne j (fun hc => hj (Fin.ext hc))) hqf'
      (fun j hj => hqfne j (fun hc => hj (Fin.ext hc))) hqk hqasu'
      (fun su' hsu' => hqane (finOfSuit su')
        (fun hc => hsu' (suitToNat_inj (by rw [hsu]; exact congrArg Fin.val hc))))
  -- and the `SolverRemoveFlute` call that follows
  obtain ⟨v', k', FK', hsim2⟩ := Simulates.ofRemoveFlute hwf hpile hready hsim1.cfg hrun
  exact ⟨v', k', FK ∪ FK', (hsimW.extend hsim1).trans hsim2⟩

/-! ## The tail -/

/-- **The walk's tail is simulated.**  After the loop exits, the solver plays the
`found` counted cards to the foundation (`aces[suit] := card - 1`) and, if the suit
ran out, records its king.  On the `Rules` side those are the `PlaysAll` of the
counted run; nothing else about the position changes.

**Still to do.**  Both halves are in `SimulateMoveAces.lean`; what is missing is their
glue to `MoveAcesInv` and to the postlude's writes:

* *Non-completing exit* (`VALUE cardF ≤ 13`, so `hexit`'s right disjunct): apply
  `Simulates.tailPlays` at `stop := cardF`.  Its `hfree` is `MoveAcesInv`'s
  `hfoundfree` transported to `runFrom` membership (`foundation_value` identifies
  `VALUE aces[suit]` with `optRankToNat (w.foundations su)`); its `hnotfree` is
  `SolverSpec.moveAces_lt_of_not_free` (a same-suit card that is not free sits strictly
  above `cardF`, hence outside the window); its `hstopbnd` is the `pos2card_inj`
  argument `moveAces_merged` already makes for `hboundaryNeCardF` — a buried card
  (`cardDepth + 1 < pileDepth`) is nobody's boundary.  `tailPlays` then leaves exactly
  one premise, that `pF.aces` reads off the *new* foundations: for suits other than
  `su` this is `PlaysAll.runFrom_foundations` plus `aces_match`, and for `su` itself
  it is `PlaysAll.foundations_getLast` at the run's last card, whose code is
  `aces[suit] + found = card2` (`found = 0` being the degenerate case where the
  foundation does not move at all).
* *Suit-complete exit* (`VALUE cardF = 14`): `StateMatchesSolverPos.tailPlaysComplete`
  supplies the plays and the per-column dichotomy, but its `Simulates` wrapper needs a
  `StateMatchesKingConfig.framePile` variant that tolerates the `kings[su] := card2`
  write — the emptied column re-owns its suit through `OwnsPile`'s *second* disjunct
  (empty column ∧ `VALUE kings[su] = 13`), so `framePile`'s `q.kings = p.kings` is too
  strong.  That variant is the one genuinely new lemma left in this file. -/
theorem Simulates.moveAcesTail {g : Globals} {w : State} {gameF pF : SolverPosType}
    {kk : Fin 16} (hwf : WellFormedLayout g) {suit : Fin 4} {su : Suit}
    (hsu : suitToNat su = suit.val) {cardF card2 foundF : UInt8}
    (hk : StateMatchesKingConfig g w gameF kk)
    (hinv : SolverSpec.MoveAcesInv g suit cardF foundF gameF)
    (hexit : (VALUE cardF).toNat = 14 ∨
      (¬ isFreeCard g gameF cardF ∧
        ∃ hp64 : (cardPile g cardF).toNat < 10,
          (cardDepth g cardF).toNat + 1 <
            (gameF.pileDepth[(cardPile g cardF).toNat]'hp64).toNat))
    (hcard2 : card2 + 1 = cardF)
    (hpFd : pF.pileDepth = gameF.pileDepth) (hpFf : pF.pileFlute = gameF.pileFlute)
    (hpFa : pF.aces.get suit = card2)
    (hpFane : ∀ t : Fin 4, t ≠ suit → pF.aces.get t = gameF.aces.get t)
    (hpFkne : ∀ t : Fin 4, t ≠ suit → pF.kings.get t = gameF.kings.get t)
    (hpFk : pF.kings.get suit = gameF.kings.get suit ∨
      ((VALUE cardF).toNat = 14 ∧ pF.kings.get suit = card2)) :
    ∃ v : State, Simulates g w gameF kk v pF kk ∅ 0xffff := by
  sorry

/-! ## The whole call -/

set_option maxHeartbeats 1000000 in
/-- **`SolverMoveAces` is simulated.**  One `busyAces` drain step: the solver advances
one suit's foundation as far as the position allows, and the `Rules` side plays exactly
those cards.  The returned `forcedKings` mask is the `Simulates`' own mask, so this
composes straight into `SolverMove`'s accumulator with `Simulates.trans`. -/
theorem Simulates.moveAces {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p) (hbusy : p.busyAces ≠ 0)
    (hk : StateMatchesKingConfig g s p k) :
    ∃ (fk : UInt16) (p' : SolverPosType),
      EStateM.run _root_.SolverMoveAces (g, p) = .ok fk (g, p') ∧
      ∃ (s' : State) (k' : Fin 16) (FK : Finset Suit),
        Simulates g s p k s' p' k' FK fk := by
  -- the walked suit, exactly as `moveAces_merged` fixes it
  have hlow : p.busyAces &&& 0x0F ≠ 0 := by
    rw [SolverSpec.uint8_and_0xF_eq_self_of_lt16 p.busyAces hmerged.busyAces_lt16]
    exact hbusy
  have hsuit4 : ctz p.busyAces < 4 := SolverSpec.ctz_lt_four_of_low_nibble p.busyAces hlow
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
  set card0 : UInt8 := A.toInt32.toUInt32.toUInt8 + 1 with hcard0def
  set found0 : UInt8 := 0 with hfound0def
  -- `MoveAcesInv` at the walk's starting point (as in `moveAces_merged`)
  have hAsuit : SUIT A = suit.val.toUInt8 := (hmerged.aces_kings_valid suit).1
  have hAval13 : (VALUE A).toNat ≤ 13 := (hmerged.aces_kings_valid suit).2.1
  have hroundtrip : A.toInt32.toUInt32.toUInt8 = A := by
    show (A.toUInt32.toInt32).toUInt32.toUInt8 = A
    rw [UInt32.toUInt32_toInt32, UInt8.toUInt8_toUInt32]
  have hcard0eq : card0 = A + 1 := by rw [hcard0def, hroundtrip]
  have hAval15 : (VALUE A).toNat < 15 := by omega
  have hsuitcard0 : SUIT card0 = suit.val.toUInt8 := by
    rw [hcard0eq, SUIT_succ A hAval15]; exact hAsuit
  have hval1_0 : 1 ≤ (VALUE card0).toNat := by
    rw [hcard0eq, VALUE_succ A hAval15]; omega
  have hval14_0 : (VALUE card0).toNat ≤ 14 := by
    rw [hcard0eq, VALUE_succ A hAval15]; omega
  have hAtoNat255 : A.toNat < 255 := by
    have hsn := SUIT_toNat A
    have hs4 : (SUIT A).toNat < 4 := by
      rw [hAsuit]; have := suit.isLt
      have h := SolverSpec.finVal_toUInt8_toNat suit
      omega
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
    exact SolverSpec.ctz_bit_self p.busyAces hbusy
  have hinv0 : SolverSpec.MoveAcesInv g suit card0 found0 p :=
    ⟨hmerged, by rw [hfound0def]; decide, by rw [hfound0def]; decide, hsuitcard0, hval1_0,
      hval14_0, hcard0eqInv, hfoundfree0, hbusybit⟩
  -- run the walk, carrying the simulation
  obtain ⟨cardF, forcedKingsF, foundF, gameF, hloopeq, hloopinv, hloopexit, hloopframe,
      hloopdich, hsimF⟩ :=
    SolverSpec.moveAcesLoop_run g hwf suit suitU32 hsuitU32 (MoveAcesSim g s p k)
      (moveAcesSim_sync hwf suit) 15 card0 0xffff found0 p (by have := hval14_0; omega) hinv0
      ⟨s, k, ∅, Simulates.refl hk⟩
  obtain ⟨hmergedF, hf0F, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩ :=
    hloopinv
  have hloopinv' : SolverSpec.MoveAcesInv g suit cardF foundF gameF :=
    ⟨hmergedF, hf0F, hf13F, hsuitcardF, hval1F, hval14F, hcardeqF, hfoundfreeF, hbitF⟩
  have h1lecardF : (1 : UInt8) ≤ cardF := by
    rw [UInt8.le_iff_toNat_le]
    have hv := VALUE_toNat cardF
    have h1 : (1 : UInt8).toNat = 1 := by decide
    omega
  have hcard2p1 : (cardF - 1) + 1 = cardF := UInt8.sub_add_cancel cardF 1
  rw [hloopeq]
  simp only [Vector.setE, dif_pos hidx4, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, set, EStateM.set]
  -- reading the two `aces`/`kings` writes off the final position
  have hfin4 : (⟨suitU32.toNat, hidx4⟩ : Fin 4) = suit := Fin.ext hsuitU32
  have hsetSelf : ∀ (v : Vector UInt8 4) (x : UInt8),
      (v.set suitU32.toNat x hidx4).get suit = x := by
    intro v x
    rw [← hfin4]
    show (v.set suitU32.toNat x hidx4)[suitU32.toNat]'hidx4 = x
    exact Vector.getElem_set_self hidx4
  have hsetNe : ∀ (v : Vector UInt8 4) (x : UInt8) (t : Fin 4), t ≠ suit →
      (v.set suitU32.toNat x hidx4).get t = v.get t := by
    intro v x t ht
    show (v.set suitU32.toNat x hidx4)[t.val]'t.isLt = v[t.val]'t.isLt
    exact Vector.getElem_set_ne hidx4 t.isLt
      (fun hcon => ht (Fin.ext (hsuitU32.symm.trans hcon)).symm)
  obtain ⟨w, kk, FK, hsimW⟩ := hsimF
  by_cases hVC : (VALUE (cardF - 1) == (13 : UInt8)) = true
  · -- the suit ran out: `kings[suit]` records its king as well
    simp only [hVC, reduceIte, EStateM.bind, EStateM.set, EStateM.pure]
    have hVC13 : (VALUE (cardF - 1)).toNat = 13 := by
      have h := hVC; rw [beq_iff_eq] at h
      rw [h]; decide
    have hVcardF14 : (VALUE cardF).toNat = 14 := by
      rw [← hcard2p1, VALUE_succ (cardF - 1) (by omega), hVC13]
    obtain ⟨v, hsimTail⟩ :=
      Simulates.moveAcesTail (su := natToSuit suit)
        (pF := { gameF with
                   aces := gameF.aces.set suitU32.toNat (cardF - 1) hidx4,
                   kings := gameF.kings.set suitU32.toNat (cardF - 1) hidx4,
                   usedSpace := gameF.usedSpace - foundF,
                   busyAces := gameF.busyAces - (1 : UInt8) <<< UInt8.ofNat (ctz p.busyAces) })
        hwf (suitToNat_natToSuit suit)
        hsimW.cfg hloopinv' hloopexit hcard2p1 rfl rfl (hsetSelf gameF.aces (cardF - 1))
        (fun t ht => hsetNe gameF.aces (cardF - 1) t ht)
        (fun t ht => hsetNe gameF.kings (cardF - 1) t ht)
        (Or.inr ⟨hVcardF14, hsetSelf gameF.kings (cardF - 1)⟩)
    exact ⟨forcedKingsF, _, rfl, v, kk, FK, hsimW.extend hsimTail⟩
  · -- the walk stopped at a buried card: only `aces[suit]` moves
    rw [Bool.not_eq_true] at hVC
    simp only [hVC, Bool.false_eq_true, reduceIte, EStateM.bind, EStateM.set, EStateM.pure]
    obtain ⟨v, hsimTail⟩ :=
      Simulates.moveAcesTail (su := natToSuit suit)
        (pF := { gameF with
                   aces := gameF.aces.set suitU32.toNat (cardF - 1) hidx4,
                   usedSpace := gameF.usedSpace - foundF,
                   busyAces := gameF.busyAces - (1 : UInt8) <<< UInt8.ofNat (ctz p.busyAces) })
        hwf (suitToNat_natToSuit suit)
        hsimW.cfg hloopinv' hloopexit hcard2p1 rfl rfl (hsetSelf gameF.aces (cardF - 1))
        (fun t ht => hsetNe gameF.aces (cardF - 1) t ht) (fun _ _ => rfl) (Or.inl rfl)
    exact ⟨forcedKingsF, _, rfl, v, kk, FK, hsimW.extend hsimTail⟩
