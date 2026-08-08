import Seahaven.SimulateMoveAces
import Seahaven.SolverSpecMoveAces

/-!
# `SolverMoveAces`, simulated end to end

`SimulateMoveAces.lean` proves the two *kinds* of step the `busyAces` drain makes on
the `Rules` side — the sync step (`Simulates.syncPlays`, composed with
`Simulates.ofCleanupRun`) and the walk's tail (`Simulates.tailPlays`,
`StateMatchesSolverPos.tailPlaysComplete`).  This file runs the loop and assembles the
call: **`Simulates.moveAces`** is the end-to-end statement, 0 sorries.

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

/-- Writing the same slot twice keeps only the second write. -/
private theorem vector_set_set {n : Nat} (v : Vector UInt8 n) (k : Nat) (hk hk' : k < n)
    (x y : UInt8) : (v.set k x hk).set k y hk' = v.set k y hk' := by
  refine SolverSpec.vector_ext_get _ _ (fun i => ?_)
  by_cases hi : i.val = k
  · subst hi
    show ((v.set i.val x hk).set i.val y hk')[i.val]'i.isLt = (v.set i.val y hk')[i.val]'i.isLt
    rw [Vector.getElem_set_self, Vector.getElem_set_self]
  · show ((v.set k x hk).set k y hk')[i.val]'i.isLt = (v.set k y hk')[i.val]'i.isLt
    rw [Vector.getElem_set_ne hk' i.isLt (fun hc => hi hc.symm),
      Vector.getElem_set_ne hk i.isLt (fun hc => hi hc.symm),
      Vector.getElem_set_ne hk' i.isLt (fun hc => hi hc.symm)]

/-- **Transporting a matching along field equations.**  `StateMatchesSolverPos` reads
only the four fields below, so a position that agrees on them matches the same states —
`freePiles`/`usedSpace`/`hash`/`busyAces` are pure solver bookkeeping. -/
theorem StateMatchesSolverPos.ofFields {g : Globals} {s : State} {p q : SolverPosType}
    (h : StateMatchesSolverPos g s p) (hd : q.pileDepth = p.pileDepth)
    (hf : q.pileFlute = p.pileFlute) (hkg : q.kings = p.kings) (ha : q.aces = p.aces) :
    StateMatchesSolverPos g s q := by
  refine ⟨h.cards_count, fun i => ?_, fun i => ?_, fun i hi => ?_, fun i hi c hc => ?_,
    fun su => ?_⟩
  · rw [hd]; exact h.depth_lt6 i
  · simp only [hd]; exact h.depth_match i
  · simp only [hd, hf] at hi ⊢; exact h.flute_match i hi
  · simp only [hd, hkg] at hi ⊢; exact h.king_pile i hi c hc
  · rw [ha]; exact h.aces_match su

/-- **The cleanup does not read the stale flute it is handed.**  `SolverCleanupPile`
overwrites `pileFlute[pile]` outright, so normalizing it first (`fluteNorm`, which the
`SolverInvBase` precondition is stated at) changes nothing about the result. -/
private theorem cleanupRunResult_fluteNorm (pile : UInt32) (hpile : pile.toNat < 10)
    (B : UInt8) (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (d32 : UInt8) (m f : Nat)
    (p : SolverPosType) :
    cleanupRunResult pile hpile B ph hs4 d32 m f (SolverSpec.fluteNorm pile hpile p)
      = cleanupRunResult pile hpile B ph hs4 d32 m f p := by
  simp only [cleanupRunResult, SolverSpec.fluteNorm]
  split_ifs <;> simp only [vector_set_set]

/-- **A whole `SolverRemoveFlute` call is simulated**, from the composed
`fluteNorm ∘ removeFlutePre` point the cleanup is entered at — the same state
`removeFlute_merged` is stated at, and the one both `SolverMove`'s phase 1 and the
drain's sync step hand over.

`removeFlute_eq` reduces the call to `SolverCleanupPile` at `removeFlutePre …`, and
`cleanupPile_eq` runs it: the empty-pile case is a `freePiles` bump, invisible to the
matching, and the loop-bearing case hands over exactly the merge/freed data
`Simulates.ofCleanupRun` needs — `hmcards` becomes the chain by `chain_of_mcards`, and
`hffree` is already the extension's per-card freeness.  The entry point differs from
the cleanup's own by the (unread, stale) `pileFlute[pile]`, which
`cleanupRunResult_fluteNorm` discharges. -/
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
  obtain ⟨hb, -, -⟩ := hready
  have hrun' : EStateM.run (_root_.SolverRemoveFlute pile) (g, gameA) = .ok fk (g, p') := hrun
  rw [removeFlute_eq pile g gameA hpile] at hrun'
  set q0 : SolverPosType := removeFlutePre pile hpile gameA with hq0def
  have hdq : (SolverSpec.fluteNorm pile hpile q0).pileDepth = q0.pileDepth := rfl
  rcases SolverSpec.cleanupPile_eq pile g q0 hpile hwf hb with
    ⟨hd0, hsd, hrunE⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- **Empty pile**: only `freePiles` moves, and the matching never reads it.
    injection hrun'.symm.trans hrunE with h1 h2
    injection h2 with _hg hp'eq
    subst h1
    rw [hp'eq, hsd]
    exact ⟨v, kk, ∅, hk.frameAll Relation.ReflTransGen.refl
      (hk.toMatches.ofFields rfl rfl rfl rfl) (fun _ => rfl) (fun _ => rfl) rfl⟩
  · -- **Loop-bearing**: the merge/freed data becomes `ofCleanupRun`'s hypotheses.
    have hBreal : IsRealCard B := by
      rw [← hBdef]
      exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ _
    have hdNat : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        = (q0.pileDepth[pile.toNat]'hpile).toNat := rfl
    have hd5N : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 := hd5
    have hd1N : 1 ≤ (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hd1
    have hidxN : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by omega
    -- the boundary index, in `Nat` form
    have hidxEq : ((q0.pileDepth[pile.toNat]'hpile) - 1).toUInt32.toNat
        = (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
      rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _
        (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]
      rfl
    have hB' : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
        ⟨(q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidxN⟩ = B := by
      rw [← hBdef]
      show (g.pos2card.get ⟨pile.toNat, hpile⟩).get _
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hidx⟩
      congr 1
      exact Fin.ext hidxEq.symm
    -- iteration-count bounds
    have hmN : m < (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by omega
    have hfN : f + 1 ≤ (VALUE B).toNat := by
      have := hBreal.2.1; omega
    -- the merge chain and the flute-1 side condition
    have hchain := chain_of_mcards (p := SolverSpec.fluteNorm pile hpile q0) hpile
      (show 1 ≤ (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat by omega)
      (show (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 from hd5N)
      (show m < (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat by omega) hmcards
    have hfl1 : (SolverSpec.fluteNorm pile hpile q0).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
      show (q0.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile = 1
      exact Vector.getElem_set_self hpile
    have hBflute1 : ∀ (j : Fin 10),
        0 < ((SolverSpec.fluteNorm pile hpile q0).pileDepth.get j).toNat →
        ∀ hidxj : ((SolverSpec.fluteNorm pile hpile q0).pileDepth.get j).toNat - 1 < 5,
        (g.pos2card.get j).get ⟨_, hidxj⟩ = B →
        (SolverSpec.fluteNorm pile hpile q0).pileFlute.get j = 1 := by
      intro j _ hidxj hBj
      have hinj := hwf.pos2card_inj j ⟨pile.toNat, hpile⟩
        ⟨((SolverSpec.fluteNorm pile hpile q0).pileDepth.get j).toNat - 1, hidxj⟩
        ⟨(q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidxN⟩ (by rw [hBj, hB'])
      rw [hinj.1]
      exact hfl1
    -- the extension's per-card facts, and the foundation comparison
    have hfree : ∀ l, 1 ≤ l → l ≤ f →
        isFreeCard g (SolverSpec.fluteNorm pile hpile q0) (B - UInt8.ofNat l) :=
      fun l h1 h2 => (hffree l h1 h2).1
    have haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
        (SolverSpec.fluteNorm pile hpile q0).aces.get ⟨(SUIT B).toNat, hs⟩
          < B - UInt8.ofNat l := by
      intro l h1 h2 hs
      have h := (hffree l h1 h2).2
      have hidxSame : (⟨(SUIT B).toNat, hs⟩ : Fin 4)
          = ⟨(SUIT B).toUInt32.toNat, hs4⟩ := Fin.ext (UInt8.toNat_toUInt32 (SUIT B)).symm
      show (q0.aces.get ⟨(SUIT B).toNat, hs⟩) < B - UInt8.ofNat l
      rw [hidxSame]
      exact h
    obtain ⟨v', k', FK, hsim⟩ :=
      Simulates.ofCleanupRun (p := SolverSpec.fluteNorm pile hpile q0)
        (ph := pileHashes[pile.toNat]'hpile) hwf hb hk hpile hs4
        hidxN hd1N hfl1 hB' hmN hchain hfN hfree haces hBflute1
    -- and the solver's own result is that `cleanupRunResult`
    have hres : cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0 = (fk, p') := by
      rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0]
      rcases hbranch with ⟨hnk, -, -, -, -, -, hrunE⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, -, -, -, -, -, hrunE⟩
      · rw [hnk]
        simp only [Bool.false_eq_true, reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
      · -- the branch test is exactly what this sub-case reports
        have hbr : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
            VALUE (B + UInt8.ofNat m) == 13) = true := by
          have hpdEq : (_root_.preCleanupPile pile hpile B (pileHashes[pile.toNat]'hpile) hs4
              (q0.pileDepth[pile.toNat]'hpile) m f q0).pileDepth[pile.toNat]'hpile =
              ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) := by
            simp only [_root_.preCleanupPile]
            rw [Vector.getElem_set_self]
          have hdm : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m) = 1 := by
            rw [← hpdEq]; exact hd1'
          have hVK : VALUE (B + UInt8.ofNat m) = 13 := by
            apply UInt8.toNat_inj.mp
            rw [← hKeq, hVK13]; decide
          rw [Bool.and_eq_true]
          exact ⟨beq_iff_eq.mpr hdm, beq_iff_eq.mpr hVK⟩
        rw [hbr]
        simp only [reduceIte]
        injection hrun'.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
    have hsim' : Simulates g v (SolverSpec.fluteNorm pile hpile q0) kk v'
        (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (q0.pileDepth[pile.toNat]'hpile) m f
          (SolverSpec.fluteNorm pile hpile q0)).2 k' FK
        (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (q0.pileDepth[pile.toNat]'hpile) m f
          (SolverSpec.fluteNorm pile hpile q0)).1 := hsim
    rw [cleanupRunResult_fluteNorm, hres] at hsim'
    exact ⟨v', k', FK, hsim'⟩

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
  have hbridge : ∀ x : UInt8, x.toNat = x.toNat := fun _ => rfl
  have hd5 : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 :=
    hmerged.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hidxN : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by omega
  have hidx : (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by
    rw [hbridge]; exact hidxN
  have hd : 0 < (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by
    rw [hbridge]; exact hdpos
  -- the boundary card is `card`
  have hB : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx⟩ = card := hbnd hidxN
  have hcardReal : IsRealCard card := by
    rw [← hB]; exact hwf.pos2card_real _ _
  obtain ⟨bc, hbc⟩ := exists_encodeCard hcardReal
  -- the sync step's hypotheses, one by one
  have hbsuit : (SUIT ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx⟩)).toNat
      = suitToNat (natToSuit suit) := by
    rw [hB, hsuitcard, SolverSpec.finVal_toUInt8_toNat, hsu]
  have hAsuit : SUIT (game.aces.get suit) = suit.val.toUInt8 :=
    (hmerged.aces_kings_valid suit).1
  have hbval : (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx⟩)).toNat
      = optRankToNat (w.foundations (natToSuit suit)) + found.toNat + 1 := by
    rw [hB, ← hsimW.cfg.toMatches.foundation_value (natToSuit suit), hfin]
    have hsc := SUIT_toNat card; have hvc := VALUE_toNat card
    have hsa := SUIT_toNat (game.aces.get suit); have hva := VALUE_toNat (game.aces.get suit)
    have hSeq : (SUIT card).toNat = (SUIT (game.aces.get suit)).toNat := by
      rw [hsuitcard, hAsuit]
    have hfb : found.toInt = (found.toNat : Int) := rfl
    omega
  have hqd' : ((SolverSpec.fluteNorm pile hpile (removeFlutePre pile hpile gameA)).pileDepth.get
      ⟨pile.toNat, hpile⟩).toNat
      = (game.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
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

/-! ## The tail

Two facts about the walked run, both shared by the two exits, and both just
`MoveAcesInv` read on the `Rules` side: the run's cards are free, and no *other*
same-suit card in the window is (the walk would have counted it).  Then the foundation
arithmetic: playing the run advances `su`'s foundation by exactly its length, which is
what the postlude's `aces[suit] := card - 1` write records. -/

private theorem exists_natToRank {k : Nat} (h1 : 1 ≤ k) (h13 : k ≤ 13) :
    ∃ r : Rank, natToRank k = some r := by
  interval_cases k <;> exact ⟨_, rfl⟩

/-- **Playing the suit's next `n` cards advances its foundation by `n`.**  The bound
rules out the run being cut short at the king. -/
theorem playsAll_runFrom_foundation {su : Suit} : ∀ (n : Nat) (s v : State),
    PlaysAll s (runFrom (nextFoundationCard s su) n) v →
    optRankToNat (s.foundations su) + n ≤ 13 →
    optRankToNat (v.foundations su) = optRankToNat (s.foundations su) + n := by
  intro n
  induction n with
  | zero => intro s v hall _; cases hall; rfl
  | succ n ih =>
    intro s v hall hle
    obtain ⟨r, hr⟩ :=
      exists_natToRank (k := optRankToNat (s.foundations su) + 1) (by omega) (by omega)
    have hrank : rankToNat r = optRankToNat (s.foundations su) + 1 :=
      natToRankToNat _ r hr
    have hnfc : nextFoundationCard s su = some ({ suit := su, rank := r } : Card) := by
      unfold nextFoundationCard nextRank
      rw [hr]; rfl
    rw [hnfc, runFrom_some] at hall
    cases hall with
    | @cons _ t _ _ _ hc hrest =>
      have hnext : nextFoundationCard t su = nextCard ({ suit := su, rank := r } : Card) :=
        nextFoundationCard_playsTo rfl hc
      rw [← hnext] at hrest
      have hfound : optRankToNat (t.foundations su) = rankToNat r := by
        rw [hc.foundations]
        show optRankToNat (update s.foundations su r su) = rankToNat r
        rw [update_same]
        rfl
      have := ih t v hrest (by omega)
      omega

/-- **The walked run is free.**  `MoveAcesInv` says it in card codes
(`aces[suit] + l` for `1 ≤ l ≤ found`); this is the same fact about `runFrom`. -/
theorem moveAces_runFrom_free {g : Globals} {w : State} {gameF : SolverPosType}
    {suit : Fin 4} {su : Suit} (hsu : suitToNat su = suit.val) {cardF found : UInt8}
    (hm : StateMatchesSolverPos g w gameF)
    (hinv : SolverSpec.MoveAcesInv g suit cardF found gameF) :
    ∀ d ∈ runFrom (nextFoundationCard w su) found.toNat,
      isFreeCard g gameF (encodeCard d) := by
  obtain ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
  have hfin : finOfSuit su = suit := Fin.ext hsu
  have hfv : (VALUE (gameF.aces.get suit)).toNat = optRankToNat (w.foundations su) := by
    rw [← hfin]; exact hm.foundation_value su
  have hAsuit : SUIT (gameF.aces.get suit) = suit.val.toUInt8 :=
    (hmerged.aces_kings_valid suit).1
  have hAsuitN : (SUIT (gameF.aces.get suit)).toNat = suit.val := by
    rw [hAsuit, SolverSpec.finVal_toUInt8_toNat]
  intro d hd
  cases hnf : nextFoundationCard w su with
  | none => rw [hnf, runFrom_none] at hd; simp at hd
  | some c₀ =>
    rw [hnf] at hd
    obtain ⟨hsu0, hready0⟩ := nextFoundationCard_spec hnf
    have hc0rank : rankToNat c₀.rank = optRankToNat (w.foundations su) + 1 := by
      rw [← hsu0]
      exact nextRankNat _ _ hready0.symm
    obtain ⟨hdsuit, hdge, hdlt⟩ := rank_mem_runFrom found.toNat c₀ d hd
    have hdsuitN : suitToNat d.suit = suit.val := by rw [hdsuit, hsu0, hsu]
    have hcodeS : (SUIT (encodeCard d)).toNat = suitToNat d.suit := by
      rw [encodeCard_SUIT, UInt8.toNat_ofNat']
      have := suitToNat_lt d.suit; omega
    have hcodeV : (VALUE (encodeCard d)).toNat = rankToNat d.rank := encodeCard_VALUE d
    have hs1 := SUIT_toNat (encodeCard d); have hv1 := VALUE_toNat (encodeCard d)
    have hs2 := SUIT_toNat (gameF.aces.get suit)
    have hv2 := VALUE_toNat (gameF.aces.get suit)
    have hAlt := (gameF.aces.get suit).toNat_lt
    have hl1 : 1 ≤ rankToNat d.rank - (VALUE (gameF.aces.get suit)).toNat := by omega
    have hlf : ((rankToNat d.rank - (VALUE (gameF.aces.get suit)).toNat : Nat) : Int)
        ≤ found.toInt := by
      have hfb : found.toInt = (found.toNat : Int) := rfl
      omega
    have hAl : (gameF.aces.get suit).toNat
        + (rankToNat d.rank - (VALUE (gameF.aces.get suit)).toNat) < 256 := by
      have := rankBounded d.rank; omega
    have hcode : encodeCard d = (gameF.aces.get suit)
        + UInt8.ofNat (rankToNat d.rank - (VALUE (gameF.aces.get suit)).toNat) := by
      apply UInt8.toNat_inj.mp
      have hlA : (UInt8.ofNat (rankToNat d.rank
          - (VALUE (gameF.aces.get suit)).toNat)).toNat
          = rankToNat d.rank - (VALUE (gameF.aces.get suit)).toNat := by
        rw [UInt8.toNat_ofNat']; omega
      rw [UInt8.toNat_add, hlA, Nat.mod_eq_of_lt hAl]
      omega
    rw [hcode]
    exact hfoundfree _ hl1 hlf

/-- **Nothing else of the suit sits in the walked window.**  A same-suit card that is
not free is strictly above the walk's stopping card (`moveAces_lt_of_not_free`), hence
above the window; the value-`0` sentinel is below the foundation top outright. -/
theorem moveAces_notfree_bound {g : Globals} {gameF : SolverPosType} {suit : Fin 4}
    {cardF found : UInt8} (hinv : SolverSpec.MoveAcesInv g suit cardF found gameF)
    {su : Suit} (hsu : suitToNat su = suit.val) :
    ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g gameF c →
      (VALUE c).toNat ≤ (VALUE (gameF.aces.get (finOfSuit su))).toNat + found.toNat →
      (VALUE c).toNat ≤ (VALUE (gameF.aces.get (finOfSuit su))).toNat := by
  have hfin : finOfSuit su = suit := Fin.ext hsu
  rw [hfin]
  intro c hcsuit hcnf hcle
  obtain ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
  have hAsuitN : (SUIT (gameF.aces.get suit)).toNat = suit.val := by
    rw [(hmerged.aces_kings_valid suit).1, SolverSpec.finVal_toUInt8_toNat]
  have hcardsuitN : (SUIT cardF).toNat = suit.val := by
    rw [hsuitcard, SolverSpec.finVal_toUInt8_toNat]
  have hcsuitN : (SUIT c).toNat = suit.val := by rw [hcsuit, hsu]
  have hs1 := SUIT_toNat c; have hv1 := VALUE_toNat c
  have hs2 := SUIT_toNat cardF; have hv2 := VALUE_toNat cardF
  have hs3 := SUIT_toNat (gameF.aces.get suit); have hv3 := VALUE_toNat (gameF.aces.get suit)
  have hfb : found.toInt = (found.toNat : Int) := rfl
  rcases Nat.eq_zero_or_pos (VALUE c).toNat with hv0 | hvpos
  · omega
  · -- a real same-suit card: it cannot be `cardF` and cannot sit below it
    exfalso
    have hcsuit' : SUIT c = suit.val.toUInt8 := by
      apply UInt8.toNat_inj.mp
      rw [SolverSpec.finVal_toUInt8_toNat]; exact hcsuitN
    by_cases hcc : c = cardF
    · rw [hcc] at hcle
      omega
    · have hlt := SolverSpec.moveAces_lt_of_not_free g suit cardF found gameF
        ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩
        c hcsuit' hvpos hcnf hcc
      omega

/-- An empty column matches a solver-empty pile. -/
private theorem pileMatches_nil {g : Globals} (i : Fin 10) (n : Fin 6) (hn : n.val = 0) :
    PileMatches g [] i n := by
  have hn0 : n = (0 : Fin 6) := Fin.ext hn
  subst hn0
  refine ⟨by simp, fun k => k.elim0, ?_⟩
  simp only [List.reverse_nil, List.drop_nil, List.map_nil]
  split_ifs with h
  · exact absurd h (by omega)
  · exact ⟨0, fun i => i.elim0⟩

/-- **The suit-complete tail, as one `Simulates`.**  The walk has run the suit out to
its king, so the cards it counted are the whole remainder of the suit: they come off the
cells and — for the one solver-empty column that carried the suit's freed run — off that
column, which therefore ends up physically empty.

That column re-owns its suit through `OwnsPile`'s *second* disjunct (empty column ∧
`VALUE kings[su] = 13`), which is exactly what the postlude's `kings[su] := card` write
provides.  `StateMatchesKingConfig.framePile` cannot see this, since it insists on
`q.kings = p.kings`; every other column is untouched, and no *other* suit can own the
emptied one, because a solver-empty column carries a single suit and this one carried
`su`. -/
theorem Simulates.tailPlaysComplete {g : Globals} {w : State} {gameF pF : SolverPosType}
    {kk : Fin 16} (hwf : WellFormedLayout g) (hb : SolverInvBase g gameF)
    (hk : StateMatchesKingConfig g w gameF kk) {su : Suit} {found : Nat}
    (hfree : ∀ d ∈ runFrom (nextFoundationCard w su) found, isFreeCard g gameF (encodeCard d))
    (hnotfree : ∀ c : UInt8, (SUIT c).toNat = suitToNat su → ¬ isFreeCard g gameF c →
      (VALUE c).toNat ≤ 13 → (VALUE c).toNat ≤ (VALUE (gameF.aces.get (finOfSuit su))).toNat)
    (hcomplete : optRankToNat (w.foundations su) + found = 13)
    (hpFd : pF.pileDepth = gameF.pileDepth) (hpFf : pF.pileFlute = gameF.pileFlute)
    (hpFane : ∀ su' : Suit, su' ≠ su →
      pF.aces.get (finOfSuit su') = gameF.aces.get (finOfSuit su'))
    (hpFasu : pF.aces.get (finOfSuit su) = encodeCard ({ suit := su, rank := Rank.king } : Card))
    (hpFkne : ∀ su' : Suit, su' ≠ su →
      pF.kings.get (finOfSuit su') = gameF.kings.get (finOfSuit su'))
    (hpFksu : (VALUE (pF.kings.get (finOfSuit su))).toNat = 13) :
    ∃ v : State, Simulates g w gameF kk v pF kk ∅ 0xffff := by
  obtain ⟨v, hall, hcount, hdich⟩ :=
    hk.toMatches.tailPlaysComplete hwf hb hfree hnotfree
  -- the suit's foundation is now its king; the other foundations do not move
  have hfsu : optRankToNat (v.foundations su) = 13 := by
    rw [playsAll_runFrom_foundation found w v hall (by omega)]; omega
  have hdich' := hdich hfsu
  have hfne : ∀ su' : Suit, su' ≠ su → v.foundations su' = w.foundations su' :=
    fun su' h => hall.runFrom_foundations su' h
  -- so no card of `su` is left in the tableau at all
  have hnosu : ∀ (j : Fin 10) (c : Card), c ∈ v.tableau j → c.suit ≠ su := by
    intro j c hc hcsu
    have h1 : countFoundation v.foundations c = 1 := by
      unfold countFoundation
      rw [if_neg (by rw [hcsu, hfsu]; have := rankBounded c.rank; omega)]
    have h2 : 1 ≤ countTableau v.tableau c := one_le_countTableau hc
    have h3 := hcount c
    unfold countState at h3
    omega
  -- the matching
  have hmatch : StateMatchesSolverPos g v pF := by
    refine ⟨hcount, fun i => ?_, fun i => ?_, fun i hi => ?_, fun i hi c hc => ?_,
      fun su' => ?_⟩
    · rw [hpFd]; exact hk.toMatches.depth_lt6 i
    · simp only [hpFd]
      rcases hdich' i with hsame | ⟨hnil, hd0, -⟩
      · rw [hsame]; exact hk.toMatches.depth_match i
      · rw [hnil]; exact pileMatches_nil i _ hd0
    · simp only [hpFd, hpFf] at hi ⊢
      rcases hdich' i with hsame | ⟨-, hd0, -⟩
      · rw [hsame]; exact hk.toMatches.flute_match i hi
      · omega
    · rcases hdich' i with hsame | ⟨hnil, -, -⟩
      · rw [hsame] at hc
        have hcsu : c.suit ≠ su :=
          hnosu i c (by rw [hsame]; exact List.mem_of_getLast? (Option.mem_def.1 hc))
        rw [hpFkne c.suit hcsu, hsame]
        simp only [hpFd] at hi
        exact hk.toMatches.king_pile i hi c hc
      · rw [hnil] at hc; simp at hc
    · by_cases hsu' : su' = su
      · subst hsu'
        obtain ⟨r, hr⟩ : ∃ r, v.foundations su' = some r := by
          cases hf : v.foundations su' with
          | none => rw [hf] at hfsu; simp only [optRankToNat] at hfsu; omega
          | some r => exact ⟨r, rfl⟩
        have hrk : r = Rank.king := by
          refine rank_king_of_13 ?_
          rw [hr] at hfsu; exact hfsu
        rw [hpFasu, hr, hrk, encodeFoundation_some]
      · rw [hpFane su' hsu', hfne su' hsu']
        exact hk.toMatches.aces_match su'
  -- the king configuration: the emptied column re-owns `su`
  have hrealizes : RealizesKingConfig v pF kk := by
    obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    refine ⟨assign, fun su' i hi => ?_, hinj, hiff⟩
    obtain ⟨hd0, hphys⟩ := hown su' i hi
    refine ⟨by rw [hpFd]; exact hd0, ?_⟩
    by_cases hsu' : su' = su
    · subst hsu'
      refine Or.inr ⟨?_, hpFksu⟩
      rcases hdich' i with hsame | ⟨hnil, -, -⟩
      · rcases hphys with ⟨c, hc, hcsu, -⟩ | ⟨hnil, -⟩
        · exact absurd hcsu
            (hnosu i c (by rw [hsame]; exact List.mem_of_getLast? (Option.mem_def.1 hc)))
        · rw [hsame]; exact hnil
      · exact hnil
    · rcases hdich' i with hsame | ⟨hnil, -, hesuit⟩
      · rcases hphys with ⟨c, hc, hcsu, hcking⟩ | ⟨hnil, hk13⟩
        · exact Or.inl ⟨c, by rw [hsame]; exact hc, hcsu, hcking⟩
        · exact Or.inr ⟨by rw [hsame]; exact hnil, by rw [hpFkne su' hsu']; exact hk13⟩
      · rcases hphys with ⟨c, hc, hcsu, -⟩ | ⟨hnil0, hk13⟩
        · exact absurd (suitToNat_inj (by rw [← hcsu]; exact hesuit c hc)) hsu'
        · exact Or.inr ⟨hnil, by rw [hpFkne su' hsu']; exact hk13⟩
  -- and a suit with no pile still has none
  have hnp : ∀ su'' : Suit, CfgBitSet kk su'' → NoKingPile v pF su'' := by
    intro su'' hbit i hd0 d hd
    rw [hpFd] at hd0
    rcases hdich' i with hsame | ⟨hnil, -, -⟩
    · exact hk.no_pile su'' hbit i hd0 d (by rw [← hsame]; exact hd)
    · rw [hnil] at hd; simp at hd
  exact ⟨v, Simulates.ofReach hall.toReach ⟨hmatch, hrealizes, hnp⟩⟩

/-- **The walk's tail is simulated.**  After the loop exits, the solver plays the
`found` counted cards to the foundation (`aces[suit] := card - 1`) and, if the suit
ran out, records its king.  On the `Rules` side those are the `PlaysAll` of the
counted run; nothing else about the position changes.

The exit the loop reports decides which half applies:

* *`VALUE cardF ≤ 13`* — the walk stopped at a buried card, so the run comes out of the
  cells and the tableau is untouched (`Simulates.tailPlays`).  `hstopbnd` is the
  `pos2card_inj` argument `moveAces_merged` also makes for `hboundaryNeCardF`: a buried
  card (`cardDepth + 1 < pileDepth`) is nobody's boundary.
* *`VALUE cardF = 14`* — the suit ran out, so the run's tail is the suit's whole freed
  king stack and it comes off that one column, which ends up empty
  (`Simulates.tailPlaysComplete`).

Either way the leftover premise is that `pF.aces` reads off the *new* foundations, which
is `playsAll_runFrom_foundation` for `su` and `PlaysAll.runFrom_foundations` plus
`aces_match` for the others.  `hpFk13`/`hpFkid` are stated as implications rather than a
disjunction on purpose: the `kings[su]` write happens *exactly* when the suit completes,
and the suit-complete branch needs `VALUE kings[su] = 13`, which the un-written value need
not satisfy (`kings[su] = aces[su] < 13` is legal while `busyAces` is pending). -/
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
    (hpFk13 : (VALUE cardF).toNat = 14 → pF.kings.get suit = card2)
    (hpFkid : (VALUE cardF).toNat ≠ 14 → pF.kings.get suit = gameF.kings.get suit) :
    ∃ v : State, Simulates g w gameF kk v pF kk ∅ 0xffff := by
  have hinv' := hinv
  obtain ⟨hmerged, hf0, hf13, hsuitcard, hval1, hval14, hcardeq, hfoundfree, hbit⟩ := hinv
  have hfin : finOfSuit su = suit := Fin.ext hsu
  have hfv : (VALUE (gameF.aces.get suit)).toNat = optRankToNat (w.foundations su) := by
    rw [← hfin]; exact hk.toMatches.foundation_value su
  have hAsuitN : (SUIT (gameF.aces.get suit)).toNat = suit.val := by
    rw [(hmerged.aces_kings_valid suit).1, SolverSpec.finVal_toUInt8_toNat]
  have hcardsuitN : (SUIT cardF).toNat = suit.val := by
    rw [hsuitcard, SolverSpec.finVal_toUInt8_toNat]
  have hfb : foundF.toInt = (foundF.toNat : Int) := rfl
  have hs1 := SUIT_toNat cardF; have hv1 := VALUE_toNat cardF
  have hs2 := SUIT_toNat (gameF.aces.get suit); have hv2 := VALUE_toNat (gameF.aces.get suit)
  have hs3 := SUIT_toNat card2; have hv3 := VALUE_toNat card2
  -- `cardF = aces[suit] + found + 1`, so `card2` is the last card the walk counted
  have hVcardF : (VALUE cardF).toNat
      = (VALUE (gameF.aces.get suit)).toNat + foundF.toNat + 1 := by omega
  have hcard2nat : cardF.toNat = card2.toNat + 1 := by
    have h := congrArg UInt8.toNat hcard2
    rw [UInt8.toNat_add, show ((1 : UInt8).toNat = 1) from rfl] at h
    have h256 : card2.toNat < 256 := card2.toNat_lt
    rcases Nat.lt_or_ge card2.toNat 255 with hlt | hge
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    · -- `card2 = 255` would wrap `cardF` to the non-card `0`
      have h255 : card2.toNat = 255 := by omega
      rw [h255] at h
      norm_num at h
      omega
  have hcard2suitN : (SUIT card2).toNat = suit.val := by omega
  have hVcard2 : (VALUE card2).toNat = (VALUE (gameF.aces.get suit)).toNat + foundF.toNat := by
    omega
  -- the two facts about the walked run, shared by both exits
  have hfree := moveAces_runFrom_free hsu hk.toMatches hinv'
  have hnotfree0 := moveAces_notfree_bound hinv' hsu
  have hacesEq : gameF.aces.get (finOfSuit su) = gameF.aces.get suit := by rw [hfin]
  -- `pF`'s `aces` really read off the new foundations
  have hpFaces : ∀ (v : State),
      PlaysAll w (runFrom (nextFoundationCard w su) foundF.toNat) v →
      optRankToNat (v.foundations su) = (VALUE (gameF.aces.get suit)).toNat + foundF.toNat →
      ∀ su' : Suit, pF.aces.get (finOfSuit su') = encodeFoundation su' (v.foundations su') := by
    intro v hall hfsu su'
    by_cases hsu' : su' = su
    · subst hsu'
      rw [hfin, hpFa]
      apply UInt8.toNat_inj.mp
      have hopt : optRankToNat (v.foundations su') ≤ 13 := by omega
      rw [encodeFoundation, CARD_toNat (by have := suitToNat_lt su'; omega) (by omega), hfsu, hsu]
      omega
    · have hne : finOfSuit su' ≠ suit := by
        rw [← hfin]
        exact fun hc => hsu' (suitToNat_inj (congrArg Fin.val hc))
      rw [hpFane _ hne, hall.runFrom_foundations su' hsu']
      exact hk.toMatches.aces_match su'
  by_cases hV14 : (VALUE cardF).toNat = 14
  · -- **the suit ran out**: the run's tail includes the suit's whole freed king stack
    have hcard2king : card2 = encodeCard ({ suit := su, rank := Rank.king } : Card) := by
      apply UInt8.toNat_inj.mp
      have hcs : (SUIT (encodeCard ({ suit := su, rank := Rank.king } : Card))).toNat
          = suitToNat su := by
        rw [encodeCard_SUIT, UInt8.toNat_ofNat']
        show suitToNat su % 256 = suitToNat su
        have := suitToNat_lt su
        omega
      have hcv : (VALUE (encodeCard ({ suit := su, rank := Rank.king } : Card))).toNat
          = rankToNat Rank.king := encodeCard_VALUE _
      have hking : rankToNat Rank.king = 13 := rfl
      have h4 := SUIT_toNat (encodeCard ({ suit := su, rank := Rank.king } : Card))
      have h5 := VALUE_toNat (encodeCard ({ suit := su, rank := Rank.king } : Card))
      omega
    refine Simulates.tailPlaysComplete (found := foundF.toNat) hwf hmerged.toSolverInvBase hk
      hfree (fun c h1 h2 h3 => hnotfree0 c h1 h2 (by rw [hacesEq]; omega)) (by omega)
      hpFd hpFf ?_ ?_ ?_ ?_
    · intro su' hsu'
      refine hpFane _ ?_
      rw [← hfin]
      exact fun hc => hsu' (suitToNat_inj (congrArg Fin.val hc))
    · rw [hfin, hpFa, hcard2king]
    · intro su' hsu'
      refine hpFkne _ ?_
      rw [← hfin]
      exact fun hc => hsu' (suitToNat_inj (congrArg Fin.val hc))
    · rw [hfin, hpFk13 hV14]; omega
  · -- **the walk stopped at a buried card**: the tail comes out of the cells
    obtain ⟨hnf, hp64, hstrict⟩ := hexit.resolve_left hV14
    have hcardFreal : IsRealCard cardF := ⟨by omega, hval1, by omega⟩
    have hcd5 : (cardDepth g cardF).toNat < 5 := by
      have hbound := hmerged.pileDepth_bound (⟨(cardPile g cardF).toNat, hp64⟩ : Fin 10)
      have hlit : gameF.pileDepth[(cardPile g cardF).toNat]'hp64 =
          gameF.pileDepth.get (⟨(cardPile g cardF).toNat, hp64⟩ : Fin 10) := rfl
      rw [hlit] at hstrict
      omega
    have hrt := hwf.round_trip cardF hcardFreal hcd5
    -- a buried card is nobody's boundary
    have hstopbnd : ∀ (j : Fin 10) (_ : 0 < (gameF.pileDepth.get j).toNat)
        (hidxj : (gameF.pileDepth.get j).toNat - 1 < 5),
        (g.pos2card.get j).get ⟨(gameF.pileDepth.get j).toNat - 1, hidxj⟩ ≠ cardF := by
      intro j hdj hidxj hcon
      have hinj := hwf.pos2card_inj j ⟨(cardPile g cardF).toNat, hp64⟩
        ⟨(gameF.pileDepth.get j).toNat - 1, hidxj⟩
        ⟨(cardDepth g cardF).toNat, hcd5⟩ (hcon.trans hrt.symm)
      have hii : j = (⟨(cardPile g cardF).toNat, hp64⟩ : Fin 10) := hinj.1
      have hdval : (gameF.pileDepth.get j).toNat - 1 = (cardDepth g cardF).toNat :=
        congrArg Fin.val hinj.2
      have hstrict' : (cardDepth g cardF).toNat + 1 < (gameF.pileDepth.get j).toNat := by
        rw [hii]
        show (cardDepth g cardF).toNat + 1
          < (gameF.pileDepth[(cardPile g cardF).toNat]'hp64).toNat
        exact hstrict
      omega
    -- the `kings` vector is untouched in this branch
    have hqkings : pF.kings = gameF.kings := by
      refine SolverSpec.vector_ext_get _ _ (fun t => ?_)
      by_cases ht : t = suit
      · subst ht; exact hpFkid hV14
      · exact hpFkne t ht
    obtain ⟨v, hall, himp⟩ :=
      Simulates.tailPlays (found := foundF.toNat) (stop := cardF) hwf
        hmerged.toSolverInvBase hk hfree (by rw [hcardsuitN, hsu])
        (by rw [hfin]; omega) (by omega) hnf (fun j hdj => hstopbnd j hdj _)
        (fun c h1 h2 h3 => hnotfree0 c h1 h2 h3) hpFd hpFf hqkings
    refine ⟨v, himp (hpFaces v hall ?_)⟩
    rw [playsAll_runFrom_foundation foundF.toNat w v hall (by omega)]
    omega

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
  set card0 : UInt8 := A + 1 with hcard0def
  set found0 : UInt8 := 0 with hfound0def
  -- `MoveAcesInv` at the walk's starting point (as in `moveAces_merged`)
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
        (fun _ => hsetSelf gameF.kings (cardF - 1)) (fun h => absurd hVcardF14 h)
    exact ⟨forcedKingsF, _, rfl, v, kk, FK, hsimW.extend hsimTail⟩
  · -- the walk stopped at a buried card: only `aces[suit]` moves
    rw [Bool.not_eq_true] at hVC
    have hsub : (cardF - 1).toNat = cardF.toNat - 1 :=
      UInt8.toNat_sub_of_le _ _ h1lecardF
    have hVC13 : (VALUE (cardF - 1)).toNat ≠ 13 := by
      intro h
      rw [beq_eq_false_iff_ne] at hVC
      exact hVC (UInt8.toNat_inj.mp (by rw [h]; decide))
    have hV14ne : (VALUE cardF).toNat ≠ 14 := by
      intro h
      apply hVC13
      have hv1 := VALUE_toNat cardF; have hv2 := VALUE_toNat (cardF - 1)
      have hs1 := SUIT_toNat cardF; have hs2 := SUIT_toNat (cardF - 1)
      omega
    simp only [hVC, Bool.false_eq_true, reduceIte, EStateM.bind, EStateM.set, EStateM.pure]
    obtain ⟨v, hsimTail⟩ :=
      Simulates.moveAcesTail (su := natToSuit suit)
        (pF := { gameF with
                   aces := gameF.aces.set suitU32.toNat (cardF - 1) hidx4,
                   usedSpace := gameF.usedSpace - foundF,
                   busyAces := gameF.busyAces - (1 : UInt8) <<< UInt8.ofNat (ctz p.busyAces) })
        hwf (suitToNat_natToSuit suit)
        hsimW.cfg hloopinv' hloopexit hcard2p1 rfl rfl (hsetSelf gameF.aces (cardF - 1))
        (fun t ht => hsetNe gameF.aces (cardF - 1) t ht) (fun _ _ => rfl)
        (fun h => absurd h hV14ne) (fun _ => rfl)
    exact ⟨forcedKingsF, _, rfl, v, kk, FK, hsimW.extend hsimTail⟩
