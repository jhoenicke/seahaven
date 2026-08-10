import Seahaven.ExtraDest
import Seahaven.SolverSpecMove

/-!
# The critical move is affordable, in the form `solverGetMovable` reads it

This assembles the destination trichotomy.  `solverGetDestination` returns one of
three shapes (`DestValid`), and `solverGetMovable` indexes `possibleKings`
differently in each:

| destination | mask | cells needed |
|---|---|---|
| a column (`toPile < 10`) | `possibleKings[fluteLen-1]` | `fluteLen - 1` |
| a king pile (`10 ≤ toPile < 14`) | `possibleKings[fluteLen] ||| (possibleKings[fluteLen-1] &&& kingOnPile)` | `fluteLen`, or `fluteLen-1` if the suit is piled |
| `EXTRA` (`toPile = 14`) | `possibleKings[fluteLen]` | `fluteLen` |

`exists_critical_state_affordable` supplies `fluteLen - 1 ≤ freeCellsOf p (cfgOf t₀ p)`,
which is exactly the column branch.  The other two are paid for by the play itself:

* **`EXTRA`** — `no_column_accepts_of_extra` says no column takes the card, so the
  critical move was a park (`cell_dest_of_no_fit'`) and a cell was free
  (`one_le_freeCells_of_no_fit`), lifting the bound to `fluteLen`.
* **a king pile whose suit is unpiled** — `empty_of_accepts_king_frontier` says only an
  *empty* column takes it.  If the play used a cell, the same lift applies.  If it used
  an empty column the card is a king, and then the configuration is `cfgOfPlus` — `k_t`
  with that king counted as piled — which lands in the `kingOnPile` disjunct and needs
  only `fluteLen - 1`.

The conclusion is stated as the disjunction the mask itself is: *either* `fluteLen`
cells are free, *or* `fluteLen - 1` are and the destination is a column or a piled
king.
-/

/-- The suit a king-pile destination names. -/
private theorem suit_of_dest {su : Suit} {s : Fin 4} (h : suitToNat su = s.val) :
    su = natToSuit s := by
  rw [← natToSuit_suitToNat su]
  exact congrArg natToSuit (Fin.ext h)

/-- **The critical move's destination is affordable at a configuration the state
realizes.**  See the module docstring for the shape of the conclusion. -/
theorem critical_dest_affordable {g : Globals} {t₀ t₁ : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (h : DepthPlusKings g t₀ p)
    {a : Fin 10} {c : Card} {rest : Column}
    (hcol : t₀.tableau a = c :: rest)
    (hlen : (t₀.tableau a).length = (p.pileDepth.get a).toNat)
    (hda : 0 < (p.pileDepth.get a).toNat)
    {m : Move} (hsrc : m.src = Position.pile a) (hap : applyMove t₀ m = some t₁)
    (hdst : m.dest ≠ Position.pile a)
    {toPile : UInt8} (hdv : SolverSpec.DestValid g p (encodeCard c) toPile) :
    ∃ k : Fin 16, DepthPlusKingsCfg g t₀ p k ∧
      (((p.pileFlute.get a).toNat : Int) ≤ freeCellsOf p k
        ∨ (((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p k
            ∧ (toPile.toNat < 10
                ∨ (10 ≤ toPile.toNat ∧ toPile.toNat < 14 ∧ ∀ su : Suit,
                    toPile.toNat - 10 = suitToNat su → ¬ CfgBitSet k su)))) := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  -- no foundation move is available at the critical state
  have hnf : ∀ t, ¬ FMStep t₀ t :=
    no_fmStep_of_depthMatch hwf hcan h.depth_lt6 h.depth_match h.cards_count h.aces_match
  -- the two bounds at the base configuration
  have hbase : ((p.pileFlute.get a).toNat : Int) - 1 ≤ freeCellsOf p (cfgOf t₀ p) :=
    h.toCfg.flute_sub_one_le_freeCellsOf hb a hda hlen
  have hcell : 1 ≤ (freeCells t₀).length →
      ((p.pileFlute.get a).toNat : Int) ≤ freeCellsOf p (cfgOf t₀ p) := by
    intro hfc
    have := h.toCfg.flute_add_freeCells_le_freeCellsOf hb a hda hlen
    have hfcZ : (1 : Int) ≤ ((freeCells t₀).length : Int) := by exact_mod_cast hfc
    linarith
  rw [SolverSpec.DestValid] at hdv
  rcases hdv with ⟨s, hsv, hkings, htp⟩ | ⟨n, hn1, hnval, hwalk, hstop, hcase⟩
  · -- ## a king-pile destination
    set su₀ : Suit := natToSuit s with hsu₀
    have hsuv : suitToNat su₀ = s.val := suitToNat_natToSuit s
    have hfin : finOfSuit su₀ = s := Fin.ext hsuv
    by_cases hpiled : PiledSuit t₀ p su₀
    · -- the suit already owns a column: the `kingOnPile` disjunct, at the base config
      have hs4 := s.isLt
      refine ⟨cfgOf t₀ p, h.toCfg,
        Or.inr ⟨hbase, Or.inr ⟨by omega, by omega, fun su hsu => ?_⟩⟩⟩
      have : su = su₀ := by
        rw [hsu₀]
        exact suit_of_dest (by omega)
      rw [this, cfgBitSet_cfgOf]
      exact fun hn => hn hpiled
    · -- unpiled: only an empty column accepts the card
      have hempty : ∀ q : Fin 10, (t₀.tableau q).head? = nextCard c → t₀.tableau q = [] :=
        fun q hq => empty_of_accepts_king_frontier hwf hb h.depth_lt6 h.depth_match
          (by rw [← hkings]) (by rwa [hsu₀] at hpiled) hq
      cases hd : m.dest with
      | foundation => exact absurd ⟨m.src, by rw [Move.foundation_eta hd]; exact hap⟩ (hnf t₁)
      | cell j =>
        -- the play parked: a cell was free
        refine ⟨cfgOf t₀ p, h.toCfg, Or.inl (hcell ?_)⟩
        have hm : (⟨Position.pile a, Position.cell j⟩ : Move) = m := by
          obtain ⟨src, dest⟩ := m
          simp only at hsrc hd
          rw [hsrc, hd]
        exact one_le_freeCells_of_cell_dest (a := a) (v := t₁) (by rw [hm]; exact hap)
      | pile q =>
        -- the play used an empty column, so the card is a king and `q` joins `k_t`
        have hqa : q ≠ a := by
          intro hq; exact hdst (by rw [hd, hq])
        have hhead := dest_head_of_move' hcol hsrc hd hqa hap
        have hqnil : t₀.tableau q = [] := hempty q hhead
        have hnc : nextCard c = none := by
          rw [← hhead, hqnil]; rfl
        have hking13 : rankToNat c.rank = 13 := nextCard_none_rank hnc
        have hd0 : (p.pileDepth.get q).toNat = 0 := by
          have := (h.depth_match q).1
          rw [hqnil] at this
          simp only [List.length_nil] at this
          omega
        have hkv : (VALUE (p.kings.get (finOfSuit su₀))).toNat = 13 := by
          rw [hfin, hkings, encodeCard_VALUE]
          exact hking13
        have hs4 := s.isLt
        refine ⟨cfgOfPlus t₀ p su₀, h.toCfgPlus hd0 hqnil hkv,
          Or.inr ⟨?_, Or.inr ⟨by omega, by omega, fun su hsu => ?_⟩⟩⟩
        · -- affordability transports along `MaskSub` (piling more only helps)
          have hmono := freeCellsOf_mono hb (maskSub_cfgOfPlus t₀ p su₀)
          linarith
        · have : su = su₀ := by
            rw [hsu₀]
            exact suit_of_dest (by omega)
          rw [this, cfgBitSet_cfgOfPlus]
          exact fun hn => hn (Or.inr rfl)
  · -- ## a column or `EXTRA`
    rcases hcase with ⟨h10, -, -, -⟩ | ⟨h14, hnoB⟩
    · exact ⟨cfgOf t₀ p, h.toCfg, Or.inr ⟨hbase, Or.inl h10⟩⟩
    · -- `EXTRA`: nothing takes the card, so the play parked
      refine ⟨cfgOf t₀ p, h.toCfg, Or.inl (hcell ?_)⟩
      have hother : ∀ q : Fin 10, q ≠ a → (t₀.tableau q).head? ≠ nextCard c :=
        fun q _ => no_column_accepts_of_extra hwf hb h.depth_lt6 h.depth_match h.cards_count
          hn1 hnval hwalk hstop hnoB q
      obtain ⟨j, -, hnone⟩ := cell_dest_of_no_fit' hcol hsrc hap hnf hdst hother
      have hmem : j ∈ freeCells t₀ := mem_freeCells.2 hnone
      exact List.length_pos_iff_ne_nil.2 (fun hnil => by rw [hnil] at hmem; simp at hmem)

/-! ## The abstract boundary is the column's head

`DestValid` speaks about `pos2card[a][depth-1]`; the play moves the physical top of
column `a`.  At the critical state the flute is parked, so the two coincide. -/

/-- With the flute parked (`|tableau a| = depth a`), the column's head is the dealt
boundary card. -/
theorem head_eq_boundary {g : Globals} {u : State} {p : SolverPosType}
    (hd6 : ∀ i : Fin 10, (p.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(p.pileDepth.get i).toNat, hd6 i⟩)
    {a : Fin 10} {c : Card} {rest : Column} (hcol : u.tableau a = c :: rest)
    (hlen : (u.tableau a).length = (p.pileDepth.get a).toNat)
    (hda : 0 < (p.pileDepth.get a).toNat) (hidx : (p.pileDepth.get a).toNat - 1 < 5) :
    encodeCard c = (g.pos2card.get a).get ⟨(p.pileDepth.get a).toNat - 1, hidx⟩ := by
  have hL : 0 < (u.tableau a).length := by omega
  have hrl : (u.tableau a).length - 1 < (u.tableau a).reverse.length := by
    simp only [List.length_reverse]; omega
  have htop : (u.tableau a).reverse[(u.tableau a).length - 1]'hrl = c := by
    have h1 := head?_reverse_last hL hrl
    rw [show (u.tableau a).head? = some c from by rw [hcol]; rfl] at h1
    exact (Option.some.inj h1).symm
  rw [← htop, (hdm a).resident_code
    (show (u.tableau a).length - 1 < (p.pileDepth.get a).toNat by omega) hrl]
  congr 1
  exact Fin.ext (by simp; omega)
