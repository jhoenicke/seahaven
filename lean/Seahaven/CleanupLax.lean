import Seahaven.ConvertMatch

/-!
# One cleanup call, from a pile that already carries part of its flute

`CvCleanupSim` (`ConvertMatch`), discharged.

The simulation core is already general: `cleanupPileSim` takes the pile's flute `m₀` as it
finds it and fetches only the `f + 1 - m₀` extension cards the column does not carry.  Two
things are still missing, and this file supplies them:

* the machinery is stated at the *local* invariant layer (`SolverInvLocal`: `PileBase` +
  `SuitClean`, no `hash`/`usedSpace` formula), and the relaxed reading `cvRelax q0 fl`
  satisfies it — `SuitClean` and the depth clauses are `q0`'s own, since a record update
  leaves `pileDepth`/`aces`/`kings` alone, `flute_pos`/`flute_empty` are `CvFlutes`, and
  the two flute clauses are read off the *state*: the run's cards sit above the boundary
  in a column, hence are free and stop above the foundation;
* the walk does not stop short of the run the column carries (`m₀ ≤ f + 1`), which is
  `column_reach_lt` at `t = f + 1` — the solver's own stop condition.
-/

namespace SolverSpec

/-! ## The cards of the run a column carries

`j` steps above the boundary — `j = 0` being the boundary card itself — the column carries
the card coded `B - j`; for `j ≥ 1` that card is free, since it is not a resident of its
own dealt pile. -/

theorem cvRelax_run_card {g : Globals} {v : State} {q0 : SolverPosType}
    {fl : Vector UInt8 10} (hwf : WellFormedLayout g)
    (h : StateMatchesSolverPos g v (cvRelax q0 fl)) (i : Fin 10)
    (hd : 0 < (q0.pileDepth.get i).toNat) (hidx : (q0.pileDepth.get i).toNat - 1 < 5)
    {j : UInt8} (hj : j.toNat + 1 ≤ (fl.get i).toNat) :
    ∃ d : Card, d ∈ v.tableau i ∧
      encodeCard d = (g.pos2card.get i).get ⟨_, hidx⟩ - j ∧
      SUIT (encodeCard d) = SUIT ((g.pos2card.get i).get ⟨_, hidx⟩) ∧
      (VALUE (encodeCard d)).toNat
        = (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat - j.toNat ∧
      (0 < j.toNat → isFreeCard g (cvRelax q0 fl) (encodeCard d)) := by
  have hBreal : IsRealCard ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩)) :=
    hwf.pos2card_real i _
  have hB13 : (VALUE ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat
      ≤ 13 := hBreal.2.2
  have hd6 : ∀ k : Fin 10, ((cvRelax q0 fl).pileDepth.get k).toNat < 6 := h.depth_lt6
  have hdm := h.depth_match
  have hdpos : 0 < ((cvRelax q0 fl).pileDepth.get i).toNat := hd
  have hnv : ((cvRelax q0 fl).pileDepth.get i).toNat = (q0.pileDepth.get i).toNat := rfl
  have hnval : (⟨((cvRelax q0 fl).pileDepth.get i).toNat, hd6 i⟩ : Fin 6).val
      = (q0.pileDepth.get i).toNat := rfl
  have hlen : (v.tableau i).length + 1 = (q0.pileDepth.get i).toNat + (fl.get i).toNat :=
    h.flute_match i hdpos
  -- the card at reverse index `depth - 1 + j`
  have hrl : (q0.pileDepth.get i).toNat - 1 + j.toNat < (v.tableau i).reverse.length := by
    simp only [List.length_reverse]
    omega
  have hBeq : (g.pos2card.get i).get
      ⟨((cvRelax q0 fl).pileDepth.get i).toNat - 1, (by have := hd6 i; omega)⟩
      = (g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩) := rfl
  -- its suit and value: the boundary card itself when `j = 0`, a run card above it otherwise
  have hcode : SUIT (encodeCard ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
          + j.toNat]'hrl))
        = SUIT ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩)) ∧
      (VALUE (encodeCard ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
          + j.toNat]'hrl))).toNat
        = (VALUE ((g.pos2card.get i).get
            (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat - j.toNat := by
    by_cases hj0 : j.toNat = 0
    · have hres := (hdm i).resident_code
        (k := (q0.pileDepth.get i).toNat - 1 + j.toNat)
        (show (q0.pileDepth.get i).toNat - 1 + j.toNat
          < ((cvRelax q0 fl).pileDepth.get i).toNat from by omega) hrl
      rw [show (g.pos2card.get i).get ⟨(q0.pileDepth.get i).toNat - 1 + j.toNat, by omega⟩
            = (g.pos2card.get i).get ⟨(q0.pileDepth.get i).toNat - 1, hidx⟩ from
          congrArg (g.pos2card.get i).get (Fin.ext
            (show (q0.pileDepth.get i).toNat - 1 + j.toNat = (q0.pileDepth.get i).toNat - 1
              from by omega))] at hres
      exact ⟨by rw [hres], by rw [hres, hj0]; omega⟩
    · obtain ⟨hs, hv⟩ := (hdm i).above_code (show 0 < _ from hdpos)
        (r := (q0.pileDepth.get i).toNat - 1 + j.toNat)
        (show ((cvRelax q0 fl).pileDepth.get i).toNat
          ≤ (q0.pileDepth.get i).toNat - 1 + j.toNat from by
            show (q0.pileDepth.get i).toNat ≤ _
            omega) hrl
      rw [hBeq] at hs hv
      exact ⟨hs, by rw [hv]; omega⟩
  -- so its code is `B - j`
  have hpos1 := rankToNat_pos ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
    + j.toNat]'hrl).rank
  have hVenc := encodeCard_VALUE ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
    + j.toNat]'hrl)
  have hjle : j ≤ (g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩) := by
    have h1 := VALUE_toNat ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))
    rw [UInt8.le_iff_toNat_le]
    have h2 := hcode.2
    omega
  refine ⟨(v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1 + j.toNat]'hrl,
    List.mem_reverse.mp (List.getElem_mem ..), ?_, hcode.1, hcode.2, ?_⟩
  · apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hjle]
    have h1 := SUIT_toNat (encodeCard ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
      + j.toNat]'hrl))
    have h2 := VALUE_toNat (encodeCard ((v.tableau i).reverse[(q0.pileDepth.get i).toNat - 1
      + j.toNat]'hrl))
    have h3 := SUIT_toNat ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))
    have h4 := VALUE_toNat ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))
    have h5 := congrArg UInt8.toNat hcode.1
    have h6 := hcode.2
    omega
  · intro hj0
    exact free_of_index_ge hwf hd6 hdm h.cards_count i
      (show ((cvRelax q0 fl).pileDepth.get i).toNat
        ≤ (q0.pileDepth.get i).toNat - 1 + j.toNat from by
          show (q0.pileDepth.get i).toNat ≤ _
          omega) hrl rfl

/-! ## The relaxed reading satisfies the pile-local invariant -/

/-- **The run's cards are free** — `PileBase`'s `flute_cards_free`, for the flutes a state
carries. -/
theorem cvRelax_flute_cards_free {g : Globals} {v : State} {q0 : SolverPosType}
    {fl : Vector UInt8 10} (hwf : WellFormedLayout g)
    (h : StateMatchesSolverPos g v (cvRelax q0 fl)) (i : Fin 10) (j : UInt8)
    (hd : 0 < (q0.pileDepth.get i).toNat) (hj0 : 0 < j.toNat)
    (hjf : j.toNat < (fl.get i).toNat) (hidx : (q0.pileDepth.get i).toNat - 1 < 5) :
    isFreeCard g (cvRelax q0 fl) ((g.pos2card.get i).get ⟨_, hidx⟩ - j) := by
  obtain ⟨d, -, hcode, -, -, hfree⟩ := cvRelax_run_card hwf h i hd hidx (j := j) (by omega)
  rw [← hcode]
  exact hfree hj0

/-- **The run stops above the foundation** — `PileBase`'s `flute_not_aces`.  Its lowest card
is in a column, so the suit's foundation has not reached it. -/
theorem cvRelax_flute_not_aces {g : Globals} {v : State} {q0 : SolverPosType}
    {fl : Vector UInt8 10} (hwf : WellFormedLayout g)
    (h : StateMatchesSolverPos g v (cvRelax q0 fl)) (i : Fin 10)
    (hflpos : 1 ≤ (fl.get i).toNat) (hd : 0 < (q0.pileDepth.get i).toNat)
    (hidx : (q0.pileDepth.get i).toNat - 1 < 5)
    (hs4 : (SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat < 4) :
    (q0.aces.get ⟨(SUIT ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat, hs4⟩).toNat
      + (fl.get i).toNat ≤ ((g.pos2card.get i).get ⟨_, hidx⟩).toNat := by
  have hBreal : IsRealCard ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩)) :=
    hwf.pos2card_real i _
  have hlow : (UInt8.ofNat ((fl.get i).toNat - 1)).toNat = (fl.get i).toNat - 1 := by
    rw [UInt8.toNat_ofNat']
    have h256 : (fl.get i).toNat < 256 := (fl.get i).toNat_lt_size
    omega
  obtain ⟨d, hmem, -, hsuit, hval, -⟩ :=
    cvRelax_run_card hwf h i hd hidx (j := UInt8.ofNat ((fl.get i).toNat - 1)) (by omega)
  -- the foundation has not reached that card
  have hlt := aces_lt_of_mem_column h.aces_match h.cards_count hmem
  have hfin : finOfSuit d.suit
      = (⟨(SUIT ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat,
          hs4⟩ : Fin 4) := by
    refine Fin.ext ?_
    show suitToNat d.suit
      = (SUIT ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat
    have h1 := congrArg UInt8.toNat hsuit
    rw [encodeCard_SUIT, UInt8.toNat_ofNat'] at h1
    have := suitToNat_lt d.suit
    omega
  rw [hfin, UInt8.lt_iff_toNat_lt] at hlt
  have h1 := SUIT_toNat (encodeCard d)
  have h2 := VALUE_toNat (encodeCard d)
  have h3 := SUIT_toNat ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))
  have h4 := VALUE_toNat ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))
  have h5 := congrArg UInt8.toNat hsuit
  have h6 := hBreal.2.2
  have h7 := rankToNat_pos d.rank
  have h8 := encodeCard_VALUE d
  rw [hlow] at hval
  have hac : ((cvRelax q0 fl).aces.get ⟨(SUIT ((g.pos2card.get i).get
      (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat, hs4⟩).toNat
      = (q0.aces.get ⟨(SUIT ((g.pos2card.get i).get
      (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat, hs4⟩).toNat := rfl
  show (q0.aces.get ⟨(SUIT ((g.pos2card.get i).get
    (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩))).toNat, hs4⟩).toNat + (fl.get i).toNat
      ≤ ((g.pos2card.get i).get (⟨(q0.pileDepth.get i).toNat - 1, hidx⟩)).toNat
  omega

/-- **The relaxed reading satisfies the local invariant**: `q0`'s own clauses wherever the
flute is not read, `CvFlutes` for the two length clauses, and the state for the rest. -/
theorem solverInvLocal_cvRelax {g : Globals} {v : State} {q0 : SolverPosType}
    {fl : Vector UInt8 10} (hwf : WellFormedLayout g) (hb : SolverInvBase g q0)
    (hfl : CvFlutes q0 fl) (h : StateMatchesSolverPos g v (cvRelax q0 fl)) :
    SolverInvLocal g (cvRelax q0 fl) where
  pileBase i :=
    { pileDepth_bound := hb.pileDepth_bound i
      flute_pos := hfl.pos i
      flute_empty := fun h0 => hfl.empty i h0
      flute_cards_free := fun j hdi hj0 hjf =>
        cvRelax_flute_cards_free hwf h i j hdi hj0 hjf _
      flute_not_aces := fun hdi hs4 =>
        cvRelax_flute_not_aces hwf h i (hfl.pos i) hdi _ hs4 }
  suitClean s :=
    { aces_kings_valid := (hb.suitClean s).aces_kings_valid
      foundation_cards_free := (hb.suitClean s).foundation_cards_free
      foundation_maximal_weak := (hb.suitClean s).foundation_maximal_weak
      king_frontier := (hb.suitClean s).king_frontier }

/-! ## The walk does not stop short of the run

`SolverCleanupPile`'s freed-predecessor loop stops at `B - 1 - f`, either because the
suit's foundation is there or because the card is not free (`cleanupPile_eq`'s `hfstop`).
Both are exactly what `column_reach_lt` rules out for a card the column carries, so the
run is at most `f + 1` long — the hypothesis `cleanupPileSim` now takes. -/

theorem cvRelax_flute_le_succ {g : Globals} {v : State} {q0 : SolverPosType}
    {fl : Vector UInt8 10} (hwf : WellFormedLayout g)
    (h : StateMatchesSolverPos g v (cvRelax q0 fl)) (i : Fin 10)
    (hd : 0 < (q0.pileDepth.get i).toNat) (hidx : (q0.pileDepth.get i).toNat - 1 < 5)
    {B : UInt8} (hB : (g.pos2card.get i).get ⟨_, hidx⟩ = B)
    {f : Nat} (hf : f + 1 ≤ (VALUE B).toNat) (hs4 : (SUIT B).toNat < 4)
    (hstop : q0.aces.get ⟨(SUIT B).toNat, hs4⟩ = B - 1 - UInt8.ofNat f
        ∨ ¬ isFreeCard g q0 (B - 1 - UInt8.ofNat f)) :
    (fl.get i).toNat ≤ f + 1 := by
  have hBreal : IsRealCard B := by rw [← hB]; exact hwf.pos2card_real i _
  have hd6 : ∀ k : Fin 10, ((cvRelax q0 fl).pileDepth.get k).toNat < 6 := h.depth_lt6
  have hlen : (v.tableau i).length + 1 = (q0.pileDepth.get i).toNat + (fl.get i).toNat :=
    h.flute_match i hd
  -- `B - 1 - f` is `B - (f + 1)`
  have hsucc : B - 1 - UInt8.ofNat f = B - UInt8.ofNat (f + 1) := by
    have h1n : (1 : UInt8).toNat = 1 := rfl
    have hV := VALUE_toNat B
    have hB1 := hBreal.2.1
    have hB13 := hBreal.2.2
    have hle1 : (1 : UInt8) ≤ B := by
      rw [UInt8.le_iff_toNat_le, h1n]
      omega
    have hlef : (UInt8.ofNat f) ≤ B - 1 := by
      rw [UInt8.le_iff_toNat_le, UInt8.toNat_sub_of_le _ _ hle1, UInt8.toNat_ofNat', h1n]
      omega
    have hlef1 : (UInt8.ofNat (f + 1)) ≤ B := by
      rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat']
      omega
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hlef, UInt8.toNat_sub_of_le _ _ hle1,
      UInt8.toNat_sub_of_le _ _ hlef1, UInt8.toNat_ofNat', UInt8.toNat_ofNat', h1n]
    omega
  -- so the column cannot reach `f + 1` cards above its boundary
  have hnv : ((cvRelax q0 fl).pileDepth.get i).toNat = (q0.pileDepth.get i).toNat := rfl
  have hreach := column_reach_lt (p := cvRelax q0 fl) hwf hd6 h.depth_match h.cards_count
    h.aces_match i hd hidx hB (t := f + 1) (by omega) hf ?_
  · omega
  · rcases hstop with hac | hnf
    · exact Or.inl ⟨hs4, hac.trans hsucc⟩
    · refine Or.inr (fun hfr => hnf ?_)
      rw [hsucc]
      exact hfr

/-! ## The cleanup's result, read at the state's flutes

`cleanupRunResult` reads the position's `aces`/`kings`/`pileDepth` and writes
`pileDepth[pile]`, `pileFlute[pile]` and the scalars — never another pile's flute.  So
running it on the relaxed reading gives the relaxed reading of running it on the solver's
own position. -/

/-- **The exit position of a simulated phase may be re-read.**  `SimulatesNorm` mentions
it only through the matching, which reads the four fields below. -/
theorem SimulatesNorm.ofExitFields {g : Globals} {s v : State} {p q q' : SolverPosType}
    {k k' : Fin 16} {FK : Finset Suit} {fk : UInt16}
    (h : SimulatesNorm g s p k v q k' FK fk)
    (hd : q'.pileDepth = q.pileDepth) (hf : q'.pileFlute = q.pileFlute)
    (hkg : q'.kings = q.kings) (ha : q'.aces = q.aces) :
    SimulatesNorm g s p k v q' k' FK fk := by
  refine ⟨h.reach, ⟨h.cfg.toMatches.ofFields hd hf hkg ha, ?_, ?_⟩, h.vacates, h.bound⟩
  · obtain ⟨assign, hown, hinj, hiff⟩ := h.cfg.realizes
    exact ⟨assign, fun su i hi => (hown su i hi).frame (by rw [hd]) (by rw [hkg]) rfl,
      hinj, hiff⟩
  · intro su hsu
    exact (h.cfg.no_pile su hsu).frame (fun i hi => Or.inl ⟨by rw [hd] at hi; exact hi, rfl⟩)

/-- **The cleanup's result, read at the state's flutes**, on the four fields the matching
reads.  The `pileFlute` component is the only one that moves: `cleanupRunResult` writes
`pileFlute[pile]` and never another pile's. -/
theorem cleanupRunResult_cvRelax (pile : UInt32) (hpile : pile.toNat < 10) (B : UInt8)
    (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (d : UInt8) (m f : Nat)
    (q0 : SolverPosType) (fl : Vector UInt8 10) :
    (cleanupRunResult pile hpile B ph hs4 d m f (cvRelax q0 fl)).2.pileDepth
        = (cleanupRunResult pile hpile B ph hs4 d m f q0).2.pileDepth ∧
      (cleanupRunResult pile hpile B ph hs4 d m f (cvRelax q0 fl)).2.pileFlute
        = fl.set pile.toNat
            ((cleanupRunResult pile hpile B ph hs4 d m f q0).2.pileFlute.get
              ⟨pile.toNat, hpile⟩) hpile ∧
      (cleanupRunResult pile hpile B ph hs4 d m f (cvRelax q0 fl)).2.aces
        = (cleanupRunResult pile hpile B ph hs4 d m f q0).2.aces ∧
      (cleanupRunResult pile hpile B ph hs4 d m f (cvRelax q0 fl)).2.kings
        = (cleanupRunResult pile hpile B ph hs4 d m f q0).2.kings := by
  by_cases hk : ((d - UInt8.ofNat m == 1) && (VALUE (B + UInt8.ofNat m) == 13)) = true
  · obtain ⟨hd1, hf1, ha1, hk1⟩ :=
      cleanupRunResult_fields_king pile hpile B ph hs4 d m f (cvRelax q0 fl) hk
    obtain ⟨hd2, hf2, ha2, hk2⟩ := cleanupRunResult_fields_king pile hpile B ph hs4 d m f q0 hk
    refine ⟨by rw [hd1, hd2]; rfl, ?_, by rw [ha1, ha2]; rfl, by rw [hk1, hk2]; rfl⟩
    rw [hf1, hf2]
    show (fl.set pile.toNat (1 : UInt8) hpile) = _
    congr 1
    show (1 : UInt8) = (q0.pileFlute.set pile.toNat (1 : UInt8) hpile)[pile.toNat]'hpile
    rw [Vector.getElem_set_self]
  · obtain ⟨hd1, hf1, ha1, hk1⟩ :=
      cleanupRunResult_fields_ordinary pile hpile B ph hs4 d m f (cvRelax q0 fl)
        (by simpa using hk)
    obtain ⟨hd2, hf2, ha2, hk2⟩ :=
      cleanupRunResult_fields_ordinary pile hpile B ph hs4 d m f q0 (by simpa using hk)
    refine ⟨by rw [hd1, hd2]; rfl, ?_, by rw [ha1, ha2]; rfl, by rw [hk1, hk2]; rfl⟩
    rw [hf1, hf2]
    show (fl.set pile.toNat (1 + UInt8.ofNat m + UInt8.ofNat f) hpile) = _
    congr 1
    show (1 + UInt8.ofNat m + UInt8.ofNat f)
      = (q0.pileFlute.set pile.toNat (1 + UInt8.ofNat m + UInt8.ofNat f) hpile)[pile.toNat]'hpile
    rw [Vector.getElem_set_self]

theorem cleanupRunResult_cvRelax_mask (pile : UInt32) (hpile : pile.toNat < 10) (B : UInt8)
    (ph : UInt32) (hs4 : (SUIT B).toUInt32.toNat < 4) (d : UInt8) (m f : Nat)
    (q0 : SolverPosType) (fl : Vector UInt8 10) :
    (cleanupRunResult pile hpile B ph hs4 d m f (cvRelax q0 fl)).1
      = (cleanupRunResult pile hpile B ph hs4 d m f q0).1 := by
  by_cases hk : ((d - UInt8.ofNat m == 1) && (VALUE (B + UInt8.ofNat m) == 13)) = true
  · simp only [cleanupRunResult, if_pos hk]
  · simp only [cleanupRunResult, if_neg hk]

/-! ## `CvCleanupSim` -/

set_option maxHeartbeats 1000000 in
/-- **One `SolverCleanupPile` call, simulated from the state's own flutes.** -/
theorem cvCleanupSim : CvCleanupSim := by
  intro g v q0 fl kk pile hpile fk p' hwf hb hfl1 hflutes hk hrun
  have hfn : fluteNorm pile hpile q0 = q0 := fluteNorm_self pile hpile q0 hfl1
  have hloc : SolverInvLocal g (cvRelax q0 fl) :=
    solverInvLocal_cvRelax hwf hb hflutes hk.toMatches
  rcases cleanupPile_eq pile g q0 hpile hwf (by rw [hfn]; exact hb) with
    ⟨hd0, hsd, hrunE⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- **Empty pile**: only `freePiles` and the (already trivial) depth move
    injection hrun.symm.trans hrunE with h1 h2
    injection h2 with _hg hp'eq
    subst h1
    subst hp'eq
    refine ⟨v, kk, ∅, ?_⟩
    refine hk.frameAll Relation.ReflTransGen.refl (hk.toMatches.ofFields ?_ ?_ ?_ ?_)
      (fun _ => rfl) (fun i => ?_) ?_
    · show q0.pileDepth.set pile.toNat 0 hpile = q0.pileDepth
      exact hsd
    · show fl.set pile.toNat
        ((q0.pileFlute.set pile.toNat 1 hpile)[pile.toNat]'hpile) hpile = fl
      rw [Vector.getElem_set_self,
        ← show fl.get ⟨pile.toNat, hpile⟩ = 1 from
          hflutes.empty ⟨pile.toNat, hpile⟩ (show q0.pileDepth.get ⟨pile.toNat, hpile⟩ = 0
            from hd0)]
      exact Vector.set_getElem_self hpile
    · rfl
    · rfl
    · show (q0.pileDepth.set pile.toNat 0 hpile).get i = q0.pileDepth.get i
      rw [hsd]
    · rfl
  · -- **Loop-bearing**: the merge/freed data feeds `ofCleanupRun` at the relaxed reading
    have hBreal : IsRealCard B := by
      rw [← hBdef]
      exact hwf.pos2card_real ⟨pile.toNat, hpile⟩ _
    have hd5N : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 := hd5
    have hd1N : 1 ≤ (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := hd1
    have hdNat : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
        = (q0.pileDepth[pile.toNat]'hpile).toNat := rfl
    have hidxN : (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by omega
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
    have hs4' : (SUIT B).toNat < 4 := by rwa [UInt8.toNat_toUInt32] at hs4
    have hidxSame : (⟨(SUIT B).toNat, hs4'⟩ : Fin 4) = ⟨(SUIT B).toUInt32.toNat, hs4⟩ :=
      Fin.ext (UInt8.toNat_toUInt32 (SUIT B)).symm
    have hmN : m < (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by omega
    have hfN : f + 1 ≤ (VALUE B).toNat := by have := hBreal.2.1; omega
    -- the run the column carries is inside the extension
    have hflf : ((cvRelax q0 fl).pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ f + 1 := by
      refine cvRelax_flute_le_succ hwf hk.toMatches ⟨pile.toNat, hpile⟩
        (show 0 < (q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat from by omega) hidxN hB' hfN
        hs4' ?_
      rcases hfstop with hac | hnf
      · refine Or.inl ?_
        rw [hidxSame]
        exact hac
      · exact Or.inr hnf
    -- the pile whose boundary is `B` is this one, so its flute bounds itself
    have hBflute : ∀ (j : Fin 10), 0 < ((cvRelax q0 fl).pileDepth.get j).toNat →
        ∀ hidxj : ((cvRelax q0 fl).pileDepth.get j).toNat - 1 < 5,
        (g.pos2card.get j).get ⟨_, hidxj⟩ = B →
        ((cvRelax q0 fl).pileFlute.get j).toNat
          ≤ ((cvRelax q0 fl).pileFlute.get ⟨pile.toNat, hpile⟩).toNat := by
      intro j _ hidxj hBj
      have hinj := hwf.pos2card_inj j ⟨pile.toNat, hpile⟩
        ⟨((cvRelax q0 fl).pileDepth.get j).toNat - 1, hidxj⟩
        ⟨(q0.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidxN⟩ (by rw [hBj, hB'])
      rw [hinj.1]
    have hchain := chain_of_mcards (p := cvRelax q0 fl) hpile hd1N hd5N hmN hmcards
    have hfree : ∀ l, 1 ≤ l → l ≤ f → isFreeCard g (cvRelax q0 fl) (B - UInt8.ofNat l) :=
      fun l h1 h2 => (hffree l h1 h2).1
    have haces : ∀ l, 1 ≤ l → l ≤ f → ∀ hs : (SUIT B).toNat < 4,
        (cvRelax q0 fl).aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l := by
      intro l h1 h2 hs
      have h := (hffree l h1 h2).2
      show q0.aces.get ⟨(SUIT B).toNat, hs⟩ < B - UInt8.ofNat l
      rw [show (⟨(SUIT B).toNat, hs⟩ : Fin 4) = ⟨(SUIT B).toUInt32.toNat, hs4⟩ from
        Fin.ext (UInt8.toNat_toUInt32 (SUIT B)).symm]
      exact h
    obtain ⟨v', k', FK, hsim⟩ :=
      SimulatesNorm.ofCleanupRun (p := cvRelax q0 fl) (ph := pileHashes[pile.toNat]'hpile)
        hwf hloc hk hpile hs4 hidxN hd1N hflf hB' hmN hchain hfN hfree haces hBflute
    -- the solver's own result is that `cleanupRunResult`, at `q0`
    have hres : cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0 = (fk, p') := by
      rw [cleanupRunResult_eq pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0]
      rcases hbranch with ⟨hnk, -, -, -, -, -, hrunE⟩ |
        ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, -, -, -, -, -, hrunE⟩
      · rw [hnk]
        simp only [Bool.false_eq_true, reduceIte]
        injection hrun.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
      · have hbr : ((q0.pileDepth[pile.toNat]'hpile) - UInt8.ofNat m == 1 &&
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
        injection hrun.symm.trans hrunE with h1 h2
        injection h2 with _hg hp2
        rw [h1, hp2]
    -- so the exit reading is the relaxed reading of the solver's result
    have hsim' : SimulatesNorm g v (cvRelax q0 fl) kk v'
        (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (q0.pileDepth[pile.toNat]'hpile) m f (cvRelax q0 fl)).2 k' FK
        (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
          (q0.pileDepth[pile.toNat]'hpile) m f (cvRelax q0 fl)).1 := hsim
    obtain ⟨hfd, hff, hfa, hfk⟩ := cleanupRunResult_cvRelax pile hpile B
      (pileHashes[pile.toNat]'hpile) hs4 (q0.pileDepth[pile.toNat]'hpile) m f q0 fl
    have hp'snd : (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f q0).2 = p' := congrArg Prod.snd hres
    have hmask : (cleanupRunResult pile hpile B (pileHashes[pile.toNat]'hpile) hs4
        (q0.pileDepth[pile.toNat]'hpile) m f (cvRelax q0 fl)).1 = fk := by
      rw [cleanupRunResult_cvRelax_mask]
      exact congrArg Prod.fst hres
    rw [hp'snd] at hfd hff hfa hfk
    refine ⟨v', k', FK, hmask ▸ SimulatesNorm.ofExitFields hsim' ?_ ?_ ?_ ?_⟩
    · show p'.pileDepth = _
      rw [hfd]
    · show fl.set pile.toNat (p'.pileFlute.get ⟨pile.toNat, hpile⟩) hpile = _
      rw [hff]
    · show p'.kings = _
      rw [hfk]
    · show p'.aces = _
      rw [hfa]


end SolverSpec
