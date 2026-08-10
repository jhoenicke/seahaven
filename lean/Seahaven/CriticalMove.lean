import Seahaven.DepthMatch
import Seahaven.CPNormal

/-!
# The critical move, with the foundations pinned

`DepthMatch.exists_critical_move` splits a winning play at the first move that
changes a pile's depth, but it carries only the depth vector along the prefix.
Step 1 of the completeness argument needs more: the state `t₀` it returns has to
be a **middle-layer match** (`DepthPlusKings`), and `DepthPlusKings.of_depthMatch`
asks for the card count *and* the foundations.

The card count is preserved by every move (`movePreservesCards`).  The foundations
are the interesting half, and this file supplies it:

* `next_foundation_buried` — at a *canonical* position each suit's next foundation
  card sits strictly below its pile's boundary.  "Not free" comes from
  `foundation_maximal_weak` once `busyAces = 0` kills its escape clause; the
  strictness — it is not the boundary card *itself* — comes from `flute_not_aces`
  (a boundary equal to `aces + 1` forces `pileFlute = 1`) and then
  `busyAces_complete`, which contradicts `busyAces = 0` again.
* `no_fmStep_of_depthMatch` — hence no foundation move is available at *any* state
  that still matches the depth vector and the foundations: the card that would have
  to move is buried, and `buried_inaccessible` says a buried card is neither in a
  cell nor on top of a column.
* `exists_critical_move_aces` — so along the prefix every move has a non-foundation
  destination, the foundations never change, and the extraction can carry
  `aces_match` (and the card count) to `t₀`.

`exists_critical_state` packages the result in the form the rest of step 1 wants:
a reachable, still-solvable `t₀` with `DepthPlusKings g t₀ p`, a move out of it that
takes pile `a`'s boundary card, and `|tableau a| = pileDepth a` — the "flute is
already parked" hypothesis of `DeckCount.usedSpace_add_flute_le`.
-/

/-! ## Readiness, without a full match

`StateMatchesSolverPos.ready_code` and the `VALUE aces` computation inside
`not_ready_of_free` both read only the `aces_match` clause.  Along the prefix that
is all that is available, so both are restated over the bare clause. -/

/-- The foundation top, as a value.  (`not_ready_of_free`'s `hVa`, standalone.) -/
theorem value_aces_of_aces {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (su : Suit) :
    (VALUE (p.aces.get (finOfSuit su))).toNat = optRankToNat (u.foundations su) := by
  have hsu : suitToNat su < 4 := suitToNat_lt _
  have hf13 := optRankToNat_le (u.foundations su)
  rw [VALUE_toNat, haces su, encodeFoundation, CARD_toNat (by omega) (by omega)]
  omega

/-- `ready_code`, over the bare `aces_match` clause. -/
theorem ready_code_of_aces {u : State} {p : SolverPosType}
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    {c : Card} (hready : some c.rank = nextRank (u.foundations c.suit)) :
    rankToNat c.rank = optRankToNat (u.foundations c.suit) + 1 ∧
      encodeCard c = p.aces.get (finOfSuit c.suit) + 1 := by
  have hrank : rankToNat c.rank = optRankToNat (u.foundations c.suit) + 1 := by
    unfold nextRank at hready
    exact natToRankToNat _ _ hready.symm
  have hsu : suitToNat c.suit < 4 := suitToNat_lt _
  have hrb : rankToNat c.rank ≤ 13 := rankBounded _
  have hacesN : (p.aces.get (finOfSuit c.suit)).toNat
      = suitToNat c.suit * 16 + optRankToNat (u.foundations c.suit) := by
    rw [haces c.suit, encodeFoundation, CARD_toNat (by omega) (by omega)]
  refine ⟨hrank, ?_⟩
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, encodeCard_toNat]
  have hone : (1 : UInt8).toNat = 1 := rfl
  omega

/-! ## The next foundation card is buried -/

/-- The foundation top's code splits into suit and value. -/
theorem aces_toNat {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p) (s : Fin 4) :
    (p.aces.get s).toNat = s.val * 16 + (VALUE (p.aces.get s)).toNat := by
  obtain ⟨hsA, -, -⟩ := hb.aces_kings_valid s
  have hs4 := s.isLt
  have hSA : (SUIT (p.aces.get s)).toNat = s.val := by
    rw [hsA]
    show (s.val.toUInt8).toNat = s.val
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    omega
  have hS := SUIT_toNat (p.aces.get s)
  have hV := VALUE_toNat (p.aces.get s)
  omega

/-- The code of the next foundation card, in `Nat` terms. -/
theorem aces_succ_toNat {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (s : Fin 4) (h13 : (VALUE (p.aces.get s)).toNat < 13) :
    (p.aces.get s + 1).toNat = s.val * 16 + ((VALUE (p.aces.get s)).toNat + 1) := by
  have hAn := aces_toNat hb s
  have hs4 := s.isLt
  rw [toNat_succ _ (by omega)]
  omega

/-- **The next foundation card is a real card** (its value is `VALUE aces + 1 ≤ 13`). -/
theorem aces_succ_real {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    (s : Fin 4) (h13 : (VALUE (p.aces.get s)).toNat < 13) :
    IsRealCard (p.aces.get s + 1) := by
  have hcode := aces_succ_toNat hb s h13
  have hs4 := s.isLt
  refine ⟨?_, ?_, ?_⟩
  · rw [SUIT_toNat, hcode]; omega
  · rw [VALUE_toNat, hcode]; omega
  · rw [VALUE_toNat, hcode]; omega

/-- **A canonical position buries every suit's next foundation card.**  The card
`aces[s] + 1` lies strictly below its pile's boundary: `foundation_maximal_weak`
plus `busyAces = 0` says it is not free, and it cannot be the boundary itself,
since `flute_not_aces` would then force `pileFlute = 1` and `busyAces_complete`
would demand a set `busyAces` bit.

Stated over an arbitrary code `x` equal to `aces[s] + 1` so that callers can
instantiate it at `encodeCard c` without rewriting under a dependent `Fin`. -/
theorem next_foundation_buried {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (s : Fin 4)
    (h13 : (VALUE (p.aces.get s)).toNat < 13) (x : UInt8) (hx : x = p.aces.get s + 1)
    (hp10 : (cardPile g x).toNat < 10) :
    (cardDepth g x).toNat + 1 < (p.pileDepth.get ⟨(cardPile g x).toNat, hp10⟩).toNat := by
  subst hx
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hz : p.busyAces = 0 := hcan.busyAces_zero
  -- Fold the pile index *first*: `hp10` occurs inside it, so any later abbreviation
  -- of `p.aces.get s` would leave two spellings of the same `Fin` behind.
  set P : Fin 10 := ⟨(cardPile g (p.aces.get s + 1)).toNat, hp10⟩ with hP
  have hcode := aces_succ_toNat hb s h13
  have hs4 := s.isLt
  -- (a) the card is not free
  have hnf : ¬ isFreeCard g p (p.aces.get s + 1) := by
    rcases hb.foundation_maximal_weak s with h | h | h
    · omega
    · exact h
    · rw [hz] at h; simp at h
  -- (b) so its dealt depth is strictly below its pile's current depth
  have hlt : (cardDepth g (p.aces.get s + 1)).toNat < (p.pileDepth.get P).toNat := by
    rw [isFreeCard_iff g p (p.aces.get s + 1) hp10, ← hP] at hnf
    omega
  -- (c) and it is not the boundary card itself
  by_contra hcon
  have heq : (cardDepth g (p.aces.get s + 1)).toNat + 1 = (p.pileDepth.get P).toNat := by omega
  have hD5 : (p.pileDepth.get P).toNat ≤ 5 := hb.pileDepth_bound P
  have hidx5 : (p.pileDepth.get P).toNat - 1 < 5 := by omega
  have hd5 : (cardDepth g (p.aces.get s + 1)).toNat < 5 := by omega
  have hreal : IsRealCard (p.aces.get s + 1) := aces_succ_real hb s h13
  -- the boundary of `P` *is* `aces[s] + 1`
  have hrt : (g.pos2card.get P).get ⟨(cardDepth g (p.aces.get s + 1)).toNat, hd5⟩
      = p.aces.get s + 1 := hwf.round_trip (p.aces.get s + 1) hreal hd5
  have hfin : (⟨(cardDepth g (p.aces.get s + 1)).toNat, hd5⟩ : Fin 5)
      = ⟨(p.pileDepth.get P).toNat - 1, hidx5⟩ := by
    simp only [Fin.mk.injEq]; omega
  have hBdef : (g.pos2card.get P).get ⟨(p.pileDepth.get P).toNat - 1, hidx5⟩
      = p.aces.get s + 1 := hfin ▸ hrt
  set B := (g.pos2card.get P).get ⟨(p.pileDepth.get P).toNat - 1, hidx5⟩ with hB
  have hdpos : 0 < (p.pileDepth.get P).toNat := by omega
  have hAn := aces_toNat hb s
  have hBcode : B.toNat = (p.aces.get s).toNat + 1 := by
    rw [hBdef]; exact toNat_succ _ (by omega)
  have hSB : (SUIT B).toNat = s.val := by rw [SUIT_toNat]; omega
  have hsB4 : (SUIT B).toNat < 4 := by omega
  have hfinB : (⟨(SUIT B).toNat, hsB4⟩ : Fin 4) = s := Fin.ext hSB
  have hfpos : 1 ≤ (p.pileFlute.get P).toNat := hb.flute_pos P
  -- `flute_not_aces` pins the flute to 1 …
  have hfna : (p.aces.get ⟨(SUIT B).toNat, hsB4⟩).toNat + (p.pileFlute.get P).toNat ≤ B.toNat :=
    (hb.pileBase P).flute_not_aces hdpos hsB4
  rw [hfinB] at hfna
  have hf1 : p.pileFlute.get P = 1 := by
    apply UInt8.toNat_inj.mp
    rw [uint8_toNat_one]
    omega
  -- … and then `busyAces_complete` demands a set bit
  have hBle : p.pileFlute.get P ≤ B := by
    rw [UInt8.le_iff_toNat_le, hf1, uint8_toNat_one]; omega
  have haces : p.aces.get ⟨(SUIT B).toNat, hsB4⟩ = B - p.pileFlute.get P := by
    rw [hfinB]
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hBle, hf1, uint8_toNat_one]
    omega
  have hbusy := (hcan.pileMerged P).busyAces_complete hdpos hsB4 haces
  rw [hz] at hbusy
  simp at hbusy

/-! ## No foundation move along the prefix -/

/-- **A depth-matching state with the canonical foundations admits no `FMStep`.**
The card that would advance is `aces[su] + 1`, which `next_foundation_buried` puts
strictly below its boundary and `buried_inaccessible` therefore puts out of reach.

Unlike `StateMatchesSolverPos.no_fmStep` this needs no `flute_match` and no
`king_pile`: parking flute cards into cells cannot expose a foundation card. -/
theorem no_fmStep_of_depthMatch {g : Globals} {u : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    (hcount : ∀ c : Card, countState u c = 1)
    (haces : ∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    ∀ t, ¬ FMStep u t := by
  rintro t ⟨pos, hp⟩
  rw [applyMove_eq] at hp
  obtain ⟨c, s0, htake, hdrop⟩ := hp
  simp only [dropPosition, dropFoundation_eq] at hdrop
  obtain ⟨hready, -⟩ := hdrop
  rw [takeFromPosition_foundations htake] at hready
  obtain ⟨hrank, hcode⟩ := ready_code_of_aces haces hready
  -- the suit is not yet complete, so `aces + 1` is a real, buried card
  have h13 : (VALUE (p.aces.get (finOfSuit c.suit))).toNat < 13 := by
    have hrb : rankToNat c.rank ≤ 13 := rankBounded _
    rw [value_aces_of_aces haces c.suit]
    omega
  have hp10 : (cardPile g (encodeCard c)).toNat < 10 :=
    hwf.pile_lt _ (encodeCard_real c)
  have hbur := next_foundation_buried hwf hcan (finOfSuit c.suit) h13 (encodeCard c) hcode hp10
  obtain ⟨hcell, hhead⟩ := buried_inaccessible hwf hd6 hdm hcount hp10 hbur
  cases pos with
  | foundation => simp [takeFromPosition] at htake
  | cell i =>
    rw [takeFromPosition, takeFromCell_eq] at htake
    exact hcell i htake.1
  | pile q =>
    rw [takeFromPosition, takeFromCol_eq] at htake
    obtain ⟨rest, hcol, -⟩ := htake
    exact hhead q (by rw [hcol]; rfl)

/-- A move that does not end on the foundation leaves the foundations alone. -/
theorem foundations_of_nonFoundation_move {u u' : State} {m : Move}
    (hm : applyMove u m = some u') (hdest : m.dest ≠ Position.foundation) :
    u'.foundations = u.foundations := by
  rw [applyMove_eq] at hm
  obtain ⟨c, s0, htake, hdrop⟩ := hm
  have h0 := takeFromPosition_foundations htake
  cases hd : m.dest with
  | foundation => exact absurd hd hdest
  | cell i =>
    rw [hd, dropPosition, dropCell_eq] at hdrop
    obtain ⟨-, rfl⟩ := hdrop
    exact h0
  | pile q =>
    rw [hd, dropPosition, dropCol_eq] at hdrop
    obtain ⟨-, rfl⟩ := hdrop
    exact h0

/-! ## The extraction, with the card count and the foundations carried along -/

/-- **`exists_critical_move`, upgraded.**  Along the prefix no foundation move is
available (`no_fmStep_of_depthMatch`), so every move's destination is a cell or a
pile and the foundations are constant; the card count is preserved by every move.
Both therefore reach the critical state, which is what turns its depth match into
a `DepthPlusKings` match. -/
theorem exists_critical_move_aces {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    {i₀ : Fin 10} (hpos : 0 < (p.pileDepth.get i₀).toNat) :
    ∀ (ms : List Move) (u w : State), (∀ c : Card, countState u c = 1) →
      DepthMatchesV g u (depthVec p hd6) →
      (∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) →
      List.foldl applyMoveOpt (some u) ms = some w → isGoal w = true →
      ∃ (t₀ t₁ : State) (m : Move) (a : Fin 10) (c : Card) (rest : Column),
        Reach u t₀ ∧ DepthMatchesV g t₀ (depthVec p hd6) ∧
        (∀ c : Card, countState t₀ c = 1) ∧
        (∀ su : Suit, p.aces.get (finOfSuit su) = encodeFoundation su (t₀.foundations su)) ∧
        applyMove t₀ m = some t₁ ∧ Reach t₁ w ∧
        t₀.tableau a = c :: rest ∧ rest.length + 1 = (p.pileDepth.get a).toNat ∧
        m.src = Position.pile a ∧ ¬ DepthMatchesV g t₁ (depthVec p hd6) := by
  intro ms
  induction ms with
  | nil =>
    intro u w hcount hd haces hrun hgoal
    simp only [List.foldl_nil, Option.some.injEq] at hrun
    subst hrun
    exact absurd hd (not_depthMatchesV_of_goal hcount hgoal (i := i₀) hpos)
  | cons m rest ih =>
    intro u w hcount hd haces hrun hgoal
    rw [List.foldl_cons] at hrun
    cases hmv : applyMove u m with
    | none =>
      rw [show applyMoveOpt (some u) m = applyMove u m from rfl, hmv,
        foldl_applyMoveOpt_none] at hrun
      simp at hrun
    | some u' =>
      rw [show applyMoveOpt (some u) m = applyMove u m from rfl, hmv] at hrun
      by_cases hd' : DepthMatchesV g u' (depthVec p hd6)
      · have hcount' : ∀ c : Card, countState u' c = 1 := by
          intro c
          rw [← congrFun (movePreservesCards u m u' hmv) c]
          exact hcount c
        -- the move cannot have been a foundation move
        have hdest : m.dest ≠ Position.foundation := by
          intro hfd
          exact no_fmStep_of_depthMatch hwf hcan hd6 hd hcount haces u'
            ⟨m.src, by rw [Move.foundation_eta hfd]; exact hmv⟩
        have haces' : ∀ su : Suit,
            p.aces.get (finOfSuit su) = encodeFoundation su (u'.foundations su) := by
          intro su
          rw [foundations_of_nonFoundation_move hmv hdest]
          exact haces su
        obtain ⟨t₀, t₁, m', a, c, rst, hr, hdm, hct, hac, hap, hr2, hcol, hlen, hs, hbk⟩ :=
          ih u' w hcount' hd' haces' hrun hgoal
        exact ⟨t₀, t₁, m', a, c, rst, Relation.ReflTransGen.head ⟨m, hmv⟩ hr, hdm, hct, hac,
          hap, hr2, hcol, hlen, hs, hbk⟩
      · obtain ⟨a, c, rst, hs, hcol, hlen⟩ := exists_boundary_of_break hmv hd hd'
        exact ⟨u, u', m, a, c, rst, Relation.ReflTransGen.refl, hd, hcount, haces, hmv,
          reach_of_foldl hrun, hcol, hlen, hs, hd'⟩

/-! ## The packaged first step -/

/-- **Step 1 of the completeness argument.**  From a solvable state matching a
canonical position with some non-empty pile, the winning play reaches a state `t₀`
that

* still matches `p` at the middle layer (`DepthPlusKings` — the flutes may be
  parked in cells, but the depths, the king stacks and the foundations agree),
* is still solvable, and
* has pile `a`'s boundary card on top with **nothing above it**
  (`|tableau a| = pileDepth a`), i.e. pile `a`'s flute is fully parked,

and whose next move takes that boundary card.  The last two facts are exactly the
`hcol`/`hda` hypotheses of `DeckCount.usedSpace_add_flute_le`, so affordability of
`t₀`'s configuration follows immediately (`critical_usedSpace_bound`). -/
theorem exists_critical_state {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hmt : StateMatchesSolverPos g s p) (hsolv : Solvable s)
    {i₀ : Fin 10} (hpos : 0 < (p.pileDepth.get i₀).toNat) :
    ∃ (t₀ t₁ : State) (m : Move) (a : Fin 10) (c : Card) (rest : Column),
      Reach s t₀ ∧ DepthPlusKings g t₀ p ∧ Solvable t₀ ∧
      applyMove t₀ m = some t₁ ∧ Solvable t₁ ∧
      t₀.tableau a = c :: rest ∧ (t₀.tableau a).length = (p.pileDepth.get a).toNat ∧
      0 < (p.pileDepth.get a).toNat ∧
      m.src = Position.pile a ∧ ¬ DepthMatchesV g t₁ (depthVec p hmt.depth_lt6) := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  obtain ⟨sol, hsol⟩ := exists_solution_of_solvable hsolv
  unfold isSolution at hsol
  cases hr : List.foldl applyMoveOpt (some s) sol with
  | none => rw [hr] at hsol; simp at hsol
  | some w =>
    rw [hr] at hsol
    obtain ⟨t₀, t₁, m, a, c, rest, hreach, hdm, hcount, haces, hap, hr2, hcol, hlen,
        hsrc, hbk⟩ :=
      exists_critical_move_aces hwf hcan hmt.depth_lt6 hpos sol s w hmt.cards_count
        hmt.depth_match hmt.aces_match hr hsol
    refine ⟨t₀, t₁, m, a, c, rest, hreach,
      DepthPlusKings.of_depthMatch hwf hb hcan.pileMerged hmt.depth_lt6 hdm hcount haces,
      ?_, hap, ?_, hcol, ?_, ?_, hsrc, hbk⟩
    · exact Solvable.step m hap (Solvable.of_reach hr2 (Solvable.done hsol))
    · exact Solvable.of_reach hr2 (Solvable.done hsol)
    · rw [hcol]; simpa using hlen
    · omega

/-! ## Affordability of the critical state's configuration

`DeckCount.flute_sub_one_le_freeCellsOf_of` is the space count in the direction
completeness needs.  Its three king-side hypotheses all hold at the middle layer:
`king_le` is a field, and the uniqueness of the column carrying a suit's stack
follows from the depth match alone — a solver-empty column is one suit's king run
(`PileMatches.king_run`), so its deepest card is that suit's king, and no card is
in two columns. -/

/-- **The deepest card of a solver-empty column is a king.**  `king_run` read at
index `0`; the middle layer's `king_le` is not needed. -/
theorem DepthPlusKings.empty_pile_king {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) (i : Fin 10) (hd0 : (p.pileDepth.get i).toNat = 0)
    {d : Card} (hlast : (u.tableau i).getLast? = some d) : d.rank = Rank.king := by
  have hr0l : 0 < (u.tableau i).reverse.length := by
    cases hcol : u.tableau i with
    | nil => rw [hcol] at hlast; simp at hlast
    | cons x xs => simp
  have hdeep : (u.tableau i).reverse[0]'hr0l = d := by
    have h1 : (u.tableau i).reverse.head? = some d := by rw [List.head?_reverse]; exact hlast
    have h2 : (u.tableau i).reverse.head? = (u.tableau i).reverse[0]? := List.head?_eq_getElem?
    rw [h1, List.getElem?_eq_getElem hr0l] at h2
    exact (Option.some.inj h2).symm
  obtain ⟨su', hrun⟩ := (h.depth_match i).king_run hd0
  obtain ⟨-, hv⟩ := hrun 0 hr0l
  rw [hdeep, encodeCard_VALUE] at hv
  exact rank_king_of_13 (by omega)

/-- **Distinct solver-empty columns carry distinct suits.**  Both deepest cards
are kings, so equal suits make them the same card — which lives in one column. -/
theorem DepthPlusKings.empty_pile_unique {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) {i j : Fin 10}
    (hi : (p.pileDepth.get i).toNat = 0) (hj : (p.pileDepth.get j).toNat = 0)
    {d e : Card} (hdi : (u.tableau i).getLast? = some d)
    (hej : (u.tableau j).getLast? = some e) (hsuit : d.suit = e.suit) : i = j := by
  have hde : d = e :=
    Card.ext hsuit (by rw [h.empty_pile_king i hi hdi, h.empty_pile_king j hj hej])
  exact h.noDup.pile_unique (List.mem_of_getLast? hdi) (hde ▸ List.mem_of_getLast? hej)

/-- **The space bound over the middle layer.**  This is what makes `k_t`
affordable *by construction*: the play really did park `fluteLen - 1` cards. -/
theorem DepthPlusKingsCfg.flute_sub_one_le_freeCellsOf {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (h : DepthPlusKingsCfg g u p k) (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    ((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p k :=
  flute_sub_one_le_freeCellsOf_of hb h.toDepthPlusKings.cards_count
    h.toDepthPlusKings.aces_match h.toDepthPlusKings.flute_le h.toDepthPlusKings.king_le
    (fun _ _ hi hj {_ _} hd he hsu => h.toDepthPlusKings.empty_pile_unique hi hj hd he hsu)
    h.no_pile a hda hcol

/-- **Step 1, with the affordability read off.**  The winning play reaches a state
`t₀` that matches `p` at the middle layer in the configuration `cfgOf t₀ p` it is
*in*, is still solvable, is about to move pile `a`'s boundary card, and — because
pile `a`'s flute is fully parked — leaves `pileFlute a - 1` cells free at that
configuration.  That last inequality is exactly the bit `solverGetMovable` reads
out of `possibleKings[fluteLen - 1]` (`KingInfoCorrect`), so the solver really does
consider this move. -/
theorem exists_critical_state_affordable {g : Globals} {s : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hmt : StateMatchesSolverPos g s p) (hsolv : Solvable s)
    {i₀ : Fin 10} (hpos : 0 < (p.pileDepth.get i₀).toNat) :
    ∃ (t₀ t₁ : State) (m : Move) (a : Fin 10) (c : Card) (rest : Column),
      Reach s t₀ ∧ DepthPlusKingsCfg g t₀ p (cfgOf t₀ p) ∧ Solvable t₀ ∧
      applyMove t₀ m = some t₁ ∧ Solvable t₁ ∧
      t₀.tableau a = c :: rest ∧ (t₀.tableau a).length = (p.pileDepth.get a).toNat ∧
      0 < (p.pileDepth.get a).toNat ∧
      ((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p (cfgOf t₀ p) ∧
      m.src = Position.pile a ∧ ¬ DepthMatchesV g t₁ (depthVec p hmt.depth_lt6) := by
  obtain ⟨t₀, t₁, m, a, c, rest, hreach, hdpk, hsolv0, hap, hsolv1, hcol, hlen, hda,
      hsrc, hbk⟩ :=
    exists_critical_state hwf hcan hmt hsolv hpos
  exact ⟨t₀, t₁, m, a, c, rest, hreach, hdpk.toCfg, hsolv0, hap, hsolv1, hcol, hlen, hda,
    hdpk.toCfg.flute_sub_one_le_freeCellsOf hcan.toSolverInvBase a hda hlen, hsrc, hbk⟩

/-- **The sharp space bound over the middle layer.**  Free cells at the critical
moment are extra slack, which is what the `EXTRA` and king-pile branches of
`solverGetMovable` need: they index `possibleKings` at `fluteLen`, one higher than a
column destination does. -/
theorem DepthPlusKingsCfg.flute_add_freeCells_le_freeCellsOf {g : Globals} {u : State}
    {p : SolverPosType} {k : Fin 16} (hb : SolverInvBase g p)
    (h : DepthPlusKingsCfg g u p k) (a : Fin 10) (hda : 0 < (p.pileDepth.get a).toNat)
    (hcol : (u.tableau a).length = (p.pileDepth.get a).toNat) :
    ((p.pileFlute.get a).toNat : Int) - 1 + ((freeCells u).length : Int) ≤ freeCellsOf p k :=
  flute_sub_one_add_freeCells_le_freeCellsOf_of hb h.toDepthPlusKings.cards_count
    h.toDepthPlusKings.aces_match h.toDepthPlusKings.flute_le h.toDepthPlusKings.king_le
    (fun _ _ hi hj {_ _} hd he hsu => h.toDepthPlusKings.empty_pile_unique hi hj hd he hsu)
    h.no_pile a hda hcol

/-! ## `k_t`: the piled suits, plus the king about to be piled

The configuration the completeness argument works at is **the piled kings of the
critical position, plus the moved king when the critical move puts a king on an empty
column**.  `cfgOf` (`DepthMatch`) is the base; this section adds the one extra suit.

The extension is well defined *because* the base is physical: `PiledSuit` requires a
solver-empty column with a deepest card, so every suit the base assigns sits on a
**non-empty** column.  The column the king is about to move onto is empty, hence
claimed by nobody, and the enlarged assignment stays injective.  `OwnsPile`'s second
disjunct licenses the claim — it asks exactly for an empty column and
`VALUE kings[su₀] = 13`, which holds because the moved card is the suit's king.

Note the extension is free: `su₀` refunds `13 - VALUE kings[su₀] = 0`, so
`freeCellsOf` does not change.  What it buys is the *branch* — with `su₀` piled,
`solverGetMovable`'s king-pile mask fires through
`possibleKings[fluteLen-1] &&& kingOnPile` rather than `possibleKings[fluteLen]`. -/

open Classical in
/-- The internal mask of "piled suits, plus `su₀`": bit set = no pile. -/
noncomputable def piledPlusMaskNat (u : State) (p : SolverPosType) (su₀ : Suit) : Nat :=
  (if PiledSuit u p Suit.clubs ∨ Suit.clubs = su₀ then 0 else 1)
    + (if PiledSuit u p Suit.diamonds ∨ Suit.diamonds = su₀ then 0 else 2)
    + (if PiledSuit u p Suit.hearts ∨ Suit.hearts = su₀ then 0 else 4)
    + (if PiledSuit u p Suit.spades ∨ Suit.spades = su₀ then 0 else 8)

theorem piledPlusMaskNat_lt (u : State) (p : SolverPosType) (su₀ : Suit) :
    piledPlusMaskNat u p su₀ < 16 := by
  unfold piledPlusMaskNat
  split_ifs <;> omega

theorem piledPlusMaskNat_bit (u : State) (p : SolverPosType) (su₀ su : Suit) :
    piledPlusMaskNat u p su₀ / 2 ^ (suitToNat su) % 2 = 1
      ↔ ¬ (PiledSuit u p su ∨ su = su₀) := by
  unfold piledPlusMaskNat
  cases su <;> simp only [suitToNat] <;> split_ifs <;> simp_all

/-- **`k_t`.**  The configuration the critical state is in, with `su₀` claiming the
column its king is about to occupy. -/
noncomputable def cfgOfPlus (u : State) (p : SolverPosType) (su₀ : Suit) : Fin 16 :=
  cfgOfMask ⟨piledPlusMaskNat u p su₀, piledPlusMaskNat_lt u p su₀⟩

theorem cfgBitSet_cfgOfPlus (u : State) (p : SolverPosType) (su₀ su : Suit) :
    CfgBitSet (cfgOfPlus u p su₀) su ↔ ¬ (PiledSuit u p su ∨ su = su₀) := by
  rw [cfgOfPlus, cfgBitSet_cfgOfMask]
  exact piledPlusMaskNat_bit u p su₀ su

/-- The extension piles more, so affordability transports to it (`freeCellsOf_mono`). -/
theorem maskSub_cfgOfPlus (u : State) (p : SolverPosType) (su₀ : Suit) :
    MaskSub (cfgOfPlus u p su₀) (cfgOf u p) := by
  rw [MaskSub_iff]
  intro su hbit
  rw [cfgBitSet_cfgOf]
  exact fun hp => (cfgBitSet_cfgOfPlus u p su₀ su).1 hbit (Or.inl hp)

open Classical in
/-- **The critical state realizes `k_t`.**  The base assignment is `cfgOf`'s; `su₀` is
sent to the empty column `i₀`, which no other suit can be using because every other
assigned column carries a deepest card. -/
theorem DepthPlusKings.toCfgPlus {g : Globals} {u : State} {p : SolverPosType}
    (h : DepthPlusKings g u p) {su₀ : Suit} {i₀ : Fin 10}
    (hd0 : (p.pileDepth.get i₀).toNat = 0) (hempty : u.tableau i₀ = [])
    (hking : (VALUE (p.kings.get (finOfSuit su₀))).toNat = 13) :
    DepthPlusKingsCfg g u p (cfgOfPlus u p su₀) where
  toDepthPlusKings := h
  no_pile := fun su hbit =>
    noKingPile_of_not_piled (fun hp => (cfgBitSet_cfgOfPlus u p su₀ su).1 hbit (Or.inl hp))
  realizes := by
    refine ⟨fun s' => if hp : PiledSuit u p s' then some hp.choose
                      else if s' = su₀ then some i₀ else none, ?_, ?_, ?_⟩
    · -- every assigned column is owned
      intro su i hassign
      simp only [] at hassign
      by_cases hp : PiledSuit u p su
      · rw [dif_pos hp] at hassign
        have hi : hp.choose = i := Option.some.inj hassign
        obtain ⟨hpd0, d, hd, hsu⟩ := hp.choose_spec
        rw [hi] at hpd0 hd
        exact ⟨hpd0, Or.inl ⟨d, hd, hsu,
          h.empty_pile_king i hpd0 (Option.mem_def.1 hd)⟩⟩
      · rw [dif_neg hp] at hassign
        by_cases hsu : su = su₀
        · rw [if_pos hsu] at hassign
          obtain rfl : i₀ = i := Option.some.inj hassign
          subst hsu
          exact ⟨hd0, Or.inr ⟨hempty, hking⟩⟩
        · rw [if_neg hsu] at hassign
          simp at hassign
    · -- the assignment is injective
      intro su su' i h1 h2
      simp only [] at h1 h2
      -- a piled suit's column is non-empty; `i₀` is empty
      have hne : ∀ s' : Suit, ∀ hp : PiledSuit u p s', hp.choose = i₀ → False := by
        intro s' hp hchoose
        obtain ⟨-, d, hd, -⟩ := hp.choose_spec
        rw [hchoose, hempty] at hd
        simp at hd
      by_cases hp : PiledSuit u p su <;> by_cases hp' : PiledSuit u p su'
      · rw [dif_pos hp] at h1
        rw [dif_pos hp'] at h2
        obtain ⟨-, d, hd, hsu⟩ := hp.choose_spec
        obtain ⟨-, d', hd', hsu'⟩ := hp'.choose_spec
        rw [Option.some.inj h1, Option.mem_def] at hd
        rw [Option.some.inj h2, Option.mem_def] at hd'
        rw [← hsu, ← hsu', congrArg Card.suit (Option.some.inj (hd.symm.trans hd'))]
      · rw [dif_pos hp] at h1
        rw [dif_neg hp'] at h2
        by_cases hsu' : su' = su₀
        · rw [if_pos hsu'] at h2
          exact (hne su hp (by rw [Option.some.inj h1, ← Option.some.inj h2])).elim
        · rw [if_neg hsu'] at h2; simp at h2
      · rw [dif_neg hp] at h1
        rw [dif_pos hp'] at h2
        by_cases hsu : su = su₀
        · rw [if_pos hsu] at h1
          exact (hne su' hp' (by rw [Option.some.inj h2, ← Option.some.inj h1])).elim
        · rw [if_neg hsu] at h1; simp at h1
      · rw [dif_neg hp] at h1
        rw [dif_neg hp'] at h2
        by_cases hsu : su = su₀ <;> by_cases hsu' : su' = su₀
        · rw [hsu, hsu']
        · rw [if_neg hsu'] at h2; simp at h2
        · rw [if_neg hsu] at h1; simp at h1
        · rw [if_neg hsu] at h1; simp at h1
    · -- assigned exactly when the bit is clear
      intro su
      simp only []
      rw [cfgBitSet_cfgOfPlus]
      by_cases hp : PiledSuit u p su
      · simp [hp]
      · by_cases hsu : su = su₀
        · subst hsu; simp [hp]
        · simp [hp, hsu]
