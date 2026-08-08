import Seahaven.MoveSimulatedReduce

/-!
# Phase 1 of `SolverMove`, simulated

`MoveSim` realizes phase 1 by legal `Rules` moves and shows the resulting state
*matches* `movePre`; what is missing for `Simulates` is the **king configuration**.
This file adds it, and closes `Phase1Simulated`.

The configuration is preserved by every destination — no phase-1 move vacates a
king, since vacates happen inside `SolverCleanupPile`, which `ofRemoveFlute`
already covers — so each branch is a frame argument:

* park-only destinations (`EXTRA`, a king pile whose stack is in the cells) change
  one column: `StateMatchesKingConfig.frameToCells`;
* column destinations (an ordinary pile, a king pile sitting on a column) change
  two: `RealizesKingConfig.frameToPile`.

The frame data itself is not new work — `run_fluteMoves`/`run_parkMoves` always
knew which columns they touch, and the four `movePre_*` lemmas now pass it on.
-/

/-! ## The king-pile destination -/

/-- The deepest card of a column that ends in `[d]`. -/
private theorem getLast?_snoc (l : List Card) (d : Card) : (l ++ [d]).getLast? = some d := by
  simp

set_option maxHeartbeats 1000000 in
/-- **A king destination, simulated.**  The bit of `k` decides the shape: a set bit
means the suit's run is in the cells and the whole flute joins it there
(`parkMoves`, one column); a clear bit means it owns a column and the flute moves
onto it (`fluteMoves`, two columns). -/
theorem StateMatchesKingConfig.movePre_king_sim {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hcellsPile : ¬ CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsExtra : CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hdst : ∀ b : Fin 10, OwnsPile s p c.suit b → (s.tableau b).head? = nextCard c)
    (hval : top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    ∃ v : State, Simulates g s p k v (SolverSpec.movePre pile toPile hpile p) k ∅ 0xffff := by
  by_cases hbit : CfgBitSet k c.suit
  · -- the run is in the cells: park the whole flute, one column changes
    obtain ⟨v, _, hreach, _, hm, hva, hvo⟩ := hk.toMatches.movePre_kingCells hpile h10 h14 hcol
      hrest (hcellsExtra hbit) hsu (hk.noKingPile hbit)
    obtain ⟨hda, hqda⟩ := movePre_source_frame pile toPile hpile p hrest hva
    exact ⟨v, hk.frameToCells hreach hm hda hqda hvo
      (movePre_depth_frame pile toPile hpile p)
      (fun x hx => movePre_kings_frame pile toPile hpile h10 h14 p hsu
        (fun hc => hx (hc ▸ hbit)))⟩
  · -- the suit owns a column: move the flute onto it, two columns change
    obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((hiff c.suit).2 hbit)
    have hownb : OwnsPile s p c.suit b := hown c.suit b hb
    obtain ⟨v, _, hreach, _, hm, hva, hvb, hvo⟩ := hk.toMatches.movePre_kingDest hpile h10 h14
      hcol hrest hrun (hcellsPile hbit) (hdst b hownb) hsu hownb hval
    obtain ⟨hda, hqda⟩ := movePre_source_frame pile toPile hpile p hrest hva
    have hba : b ≠ ⟨pile.toNat, hpile⟩ := by
      intro hc; rw [hc] at hownb; have := hownb.1; omega
    have hd0 : ((SolverSpec.movePre pile toPile hpile p).pileDepth.get b).toNat = 0 := by
      rw [movePre_depth_frame pile toPile hpile p b hba]; exact hownb.1
    refine ⟨v, RealizesKingConfig.frameToPile hown hinj hiff hk.no_pile hreach hm hda hqda hvo
      (movePre_depth_frame pile toPile hpile p)
      (fun x hxb _ => movePre_kings_frame pile toPile hpile h10 h14 p hsu
        (fun hc => hxb (hc ▸ hb)))
      (fun x hx => ?_) (fun _ => ⟨c.suit, hb⟩)⟩
    -- only `c.suit` is assigned `b`, and `b`'s deepest card is still its king
    obtain rfl : x = c.suit := hinj x c.suit b hx hb
    rcases List.eq_nil_or_concat (s.tableau b) with hnil | ⟨init, d₀, hcat⟩
    · -- a genuinely empty owned column: it receives the suit's own king
      have hking : c.rank = Rank.king := by
        have hh := hdst b hownb
        rw [hnil] at hh
        simp only [List.head?_nil] at hh
        exact rankInj _ _ (by rw [nextCard_none_rank hh.symm]; rfl)
      have hlast : (v.tableau b).getLast? = some c := by rw [hvb, hnil]; simp
      exact ⟨⟨hd0, Or.inl ⟨c, hlast, rfl, hking⟩⟩, fun d hd => by
        rw [hlast] at hd
        simp only [Option.mem_def, Option.some.injEq] at hd
        rw [← hd]⟩
    · -- an existing king stack: its bottom card is untouched
      have hlast : (v.tableau b).getLast? = some d₀ := by
        rw [hvb, hcat, List.concat_eq_append, ← List.cons_append, ← List.append_assoc]
        exact getLast?_snoc _ _
      have hsuit : d₀.suit = c.suit ∧ d₀.rank = Rank.king := by
        rcases hownb.2 with ⟨e, he, hes, her⟩ | ⟨hnil, -⟩
        · rw [hcat] at he
          simp only [Option.mem_def] at he
          simp at he
          subst he
          exact ⟨hes, her⟩
        · rw [hcat] at hnil; simp at hnil
      exact ⟨⟨hd0, Or.inl ⟨d₀, hlast, hsuit.1, hsuit.2⟩⟩, fun d hd => by
        rw [hlast] at hd
        simp only [Option.mem_def, Option.some.injEq] at hd
        rw [← hd]; exact hsuit.1⟩

/-! ## All four destinations -/

set_option maxHeartbeats 1000000 in
/-- **Phase 1, simulated, whatever `solverGetDestination` returned.**  Same dispatch
as `movePre_run`, carrying the configuration through. -/
theorem StateMatchesKingConfig.movePre_sim {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcellsCol : (toPile.toNat < 10 ∨
      (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧ ¬ CfgBitSet k c.suit)) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨
      (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧ CfgBitSet k c.suit)) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hne : toPile.toNat < 10 → pile.toNat ≠ toPile.toNat)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hdstPile : ∀ h10 : toPile.toNat < 10,
      (s.tableau ⟨toPile.toNat, h10⟩).head? = nextCard c)
    (hsum : ∀ h10 : toPile.toNat < 10, (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
      + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256)
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hdstKing : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      ∀ b : Fin 10, OwnsPile s p c.suit b → (s.tableau b).head? = nextCard c)
    (hval : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    ∃ v : State, Simulates g s p k v (SolverSpec.movePre pile toPile hpile p) k ∅ 0xffff := by
  by_cases h10 : toPile.toNat < 10
  · -- an ordinary pile: two columns change, and the destination stays non-empty
    obtain ⟨assign, hown, hinj, hiff⟩ := hk.realizes
    obtain ⟨v, _, hreach, _, hm, hva, hvb, hvo⟩ := hk.toMatches.movePre_pileDest hpile h10
      (hne h10) hcol hrest hrun (hcellsCol (Or.inl h10)) (hdstPile h10) (hdb h10) (hsum h10)
    obtain ⟨hda, hqda⟩ := movePre_source_frame pile toPile hpile p hrest hva
    -- the destination has positive depth, so no suit owns it before or after
    have hbne : (⟨toPile.toNat, h10⟩ : Fin 10) ≠ ⟨pile.toNat, hpile⟩ :=
      fun hc => hne h10 (congrArg Fin.val hc).symm
    have hqb : ((SolverSpec.movePre pile toPile hpile p).pileDepth.get
        ⟨toPile.toNat, h10⟩).toNat ≠ 0 := by
      rw [movePre_depth_frame pile toPile hpile p _ hbne]
      have := hdb h10
      omega
    refine ⟨v, RealizesKingConfig.frameToPile hown hinj hiff hk.no_pile hreach hm hda hqda hvo
      (movePre_depth_frame pile toPile hpile p)
      (fun x _ _ => by
        rw [SolverSpec.movePre_kings_of_not_king pile toPile hpile p (Or.inl h10)])
      (fun x hx => absurd (hown x _ hx).1 (by
        have := hdb h10; omega))
      (fun hc => absurd hc hqb)⟩
  · by_cases h14 : toPile.toNat < 14
    · exact hk.movePre_king_sim hpile h10 h14 hcol hrest hrun (hsu h10 h14)
        (fun hbit => hcellsCol (Or.inr ⟨h10, h14, hbit⟩))
        (fun hbit => hcellsFull (Or.inr ⟨h10, h14, hbit⟩))
        (hdstKing h10 h14) (hval h10 h14)
    · -- `EXTRA`: the whole flute goes to the cells, one column changes
      obtain ⟨v, _, hreach, _, hm, hva, hvo⟩ := hk.toMatches.movePre_extra hpile h14 hcol hrest
        (hcellsFull (Or.inl h14))
      obtain ⟨hda, hqda⟩ := movePre_source_frame pile toPile hpile p hrest hva
      exact ⟨v, hk.frameToCells hreach hm hda hqda hvo
        (movePre_depth_frame pile toPile hpile p)
        (fun x _ => by
          rw [SolverSpec.movePre_kings_of_not_king pile toPile hpile p (Or.inr h14)])⟩

/-! ## The destination, in the solver's own terms

The same two bridges `movePre_run_of_frontier`/`_of_dest`/`_of_dest_inv` build for
the matching-only version, composed into one wrapper: a king destination owes only
the frontier test `encodeCard c = kings[c.suit]`, a pile destination only
"same suit" and "`VALUE B_dst = VALUE B_src + pileFlute[dst]`". -/

set_option maxHeartbeats 1000000 in
/-- **Phase 1, simulated, from the destination facts `DestValid` carries.** -/
theorem StateMatchesKingConfig.movePre_sim_of_dest {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcellsCol : (toPile.toNat < 10 ∨
      (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧ ¬ CfgBitSet k c.suit)) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨
      (¬ toPile.toNat < 10 ∧ toPile.toNat < 14 ∧ CfgBitSet k c.suit)) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hsuitP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5),
      SUIT ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)
        = SUIT ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩))
    (hgapP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5),
      (VALUE ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)).toNat
        = (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩)).toNat
          + (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat)
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hkc : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      encodeCard c = p.kings.get (finOfSuit c.suit)) :
    ∃ v : State, Simulates g s p k v (SolverSpec.movePre pile toPile hpile p) k ∅ 0xffff := by
  have hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by
    have := hk.toMatches.depth_lt6 ⟨pile.toNat, hpile⟩; omega
  refine hk.movePre_sim hpile hcol hrest hrun hcellsCol hcellsFull (fun h10 => ?_) hdb
    (fun h10 => ?_) (fun h10 => ?_) hsu
    (fun h10 h14 _ hown => hk.toMatches.head_of_ownsPile (hkc h10 h14) hown)
    (fun h10 h14 => by rw [← hkc h10 h14, encodeCard_VALUE]; exact hrun.length_lt_rank)
  · -- the destination is a different pile (`ne_of_flute_gap`)
    have hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5 := by
      have := hk.toMatches.depth_lt6 ⟨toPile.toNat, h10⟩; omega
    exact ne_of_flute_gap hb hpile h10 hib hia (hgapP h10 hib hia)
  · -- the destination's exposed card is `nextCard c` (`head_of_flute_gap`)
    have hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5 := by
      have := hk.toMatches.depth_lt6 ⟨toPile.toNat, h10⟩; omega
    exact hk.toMatches.head_of_flute_gap hcol hrest hia
      (by simpa using hdb h10) hib (hsuitP h10 hib hia) (hgapP h10 hib hia)
  · -- the two flutes cannot overflow a `UInt8`
    have h1 := hb.pileFlute_le_13 hwf ⟨toPile.toNat, h10⟩
    have h2 := hb.pileFlute_le_13 hwf ⟨pile.toNat, hpile⟩
    omega

/-! ## `Phase1Simulated`

Everything assembled: `flute_split` supplies the source column's decomposition,
`getMovable_freeCells` the affordability, and `destValid_of_getDest` the
destination — `DestValid`'s two branches are exactly `movePre_sim_of_dest`'s king
and pile hypotheses, once `boundary_code` identifies the Rules-side boundary card
`c` with the solver's `B` and `dest_flute_eq_walk` identifies the walk length with
the destination's flute. -/

set_option maxHeartbeats 2000000 in
/-- **Phase 1 of `SolverMove` is simulated.**  With `moveSimulated_of_phase1` this
closes `MoveSimulated` up to the two remaining semantic obligations elsewhere. -/
theorem phase1Simulated : Phase1Simulated := by
  intro g s p ki pile toPile mv i hi hwf hcan hs hkic hpile hdepth hdest hmv hbit
  have hb := hcan.toSolverInvBase
  have hfin : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hpile)
  have hd : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by rw [← hfin]; exact hdepth
  have hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by
    have := hs.toMatches.depth_lt6 ⟨pile.toNat, hpile⟩; omega
  have hb5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := hia
  -- the source column, split at its boundary
  obtain ⟨top, rest, c, hcol, hflen, hrest, hrun⟩ :=
    hs.toMatches.flute_split ⟨pile.toNat, hpile⟩ (by omega)
  have hrest' : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hrest
  -- `c` is the solver's boundary card `B`
  set B := (g.pos2card.get ⟨pile.toNat, hpile⟩).get
    ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hb5⟩ with hBdef
  have hcB : encodeCard c = B := by
    have h := hs.toMatches.boundary_code ⟨pile.toNat, hpile⟩ hcol hrest hia
    rw [hBdef]
    convert h using 3
  have hsuitc : (SUIT B).toNat = suitToNat c.suit := by
    rw [← hcB, encodeCard_SUIT, UInt8.toNat_ofNat']
    have := suitToNat_lt c.suit
    omega
  -- what the destination walk guarantees
  obtain ⟨-, hdv⟩ := destValid_of_getDest hwf hcan hpile hd hb5 hdest
  -- the free-cell counts, from `solverGetMovable`
  have hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit := by
    intro h10 h14
    rcases hdv with ⟨su, hsuv, -, htp⟩ | ⟨n, -, -, -, -, hcase⟩
    · rw [htp, hsuv, hsuitc]; omega
    · rcases hcase with ⟨h10', -⟩ | ⟨h14', -⟩
      · exact absurd h10' h10
      · omega
  rw [hfin] at hmv
  obtain ⟨hcellsCol, hcellsFull⟩ :=
    getMovable_freeCells hwf hb hkic (hb.flute_pos ⟨pile.toNat, hpile⟩) hmv hi hs hbit hsu
  -- and the destination itself
  refine hs.movePre_sim_of_dest hpile hwf hb hcol hrest' hrun
    hcellsCol hcellsFull
    (fun h10 => ?_) (fun h10 hib hia' => ?_) (fun h10 hib hia' => ?_) hsu (fun h10 h14 => ?_)
  · -- a pile destination is non-empty
    rcases hdv with ⟨su, -, -, htp⟩ | ⟨n, -, -, -, -, hcase⟩
    · omega
    · rcases hcase with ⟨h10', hd', -⟩ | ⟨h14', -⟩
      · convert hd' using 2
      · omega
  all_goals rcases hdv with ⟨su, hsuv, hkB, htp⟩ | ⟨n, hn1, hnval, hwalk, hnf, hcase⟩
  -- SUIT: the walked card keeps the boundary's suit
  · omega
  · rcases hcase with ⟨h10', hd', hidxt, hBt⟩ | ⟨h14', -⟩
    · obtain ⟨hsn, -⟩ := card_walk_suit_value B n (by omega)
      rw [show (g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩
            = (g.pos2card.get ⟨toPile.toNat, h10'⟩).get ⟨_, hidxt⟩ from by congr 1,
        hBt, hsn]
    · omega
  -- VALUE: the gap equals the destination's flute length
  · omega
  · rcases hcase with ⟨h10', hd', hidxt, hBt⟩ | ⟨h14', -⟩
    · obtain ⟨-, hvn⟩ := card_walk_suit_value B n (by omega)
      have hfl := SolverSpec.dest_flute_eq_walk g p hwf hcan.toSolverInvMerged B (hwf.pos2card_real _ _)
        (by have h := boundary_not_free hwf hb ⟨pile.toNat, hpile⟩ hd; rw [← hBdef] at h; exact h)
        n hn1 (by omega) hwalk ⟨toPile.toNat, h10'⟩ hd' hidxt hBt
      rw [show (g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩
            = (g.pos2card.get ⟨toPile.toNat, h10'⟩).get ⟨_, hidxt⟩ from by congr 1,
        hBt, hvn,
        show (p.pileFlute.get ⟨toPile.toNat, h10⟩) = p.pileFlute.get ⟨toPile.toNat, h10'⟩ from rfl,
        hfl]
    · omega
  -- the king frontier test
  · rw [hcB, hBdef, ← hkB]
    congr 1
    exact Fin.ext (by rw [hsuv, hsuitc]; rfl)
  · rcases hcase with ⟨h10', -⟩ | ⟨h14', -⟩
    · exact absurd h10' h10
    · omega

/-- **`MoveSimulated` is discharged.**  One of the two semantic obligations of
`recCheck_sound_of_semantics`; `SubsetSound` is the other. -/
theorem moveSimulated : MoveSimulated := moveSimulated_of_phase1 phase1Simulated

/-- **`solverRecCheckSolvable` is sound, unconditionally.**  Both semantic
hypotheses are theorems now: `subsetSound` (`KingMoveSim`, via the king-piling
step) and `moveSimulated` just above.  What is left between this and end-to-end
`SolveSound` is the `solve` wrapper — `solverConvert_canonical`, the Rules-side
normalization, and `WellFormedLayout` for the initial deal. -/
theorem recCheckSolvableSound : RecCheckSolvableSound :=
  recCheck_sound_of_semantics subsetSound moveSimulated
