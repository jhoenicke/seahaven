import Seahaven.SubsetTransport
import Seahaven.CompletenessSkeleton

/-!
# The critical iteration sets the bit

The completeness counterpart of `RecCheckSound.recBodyStep`, but for **one** pile only:
the source pile of the critical move.  Every other iteration merely has to *keep* what
the accumulator already has (`CompleteBits.or_left`, `CompAllOrNothing.step`); this one
has to *produce* it.

Two branches, and both deliver:

* the pile is skipped because `movable &&& ~~~solvable == 0` — then `movable`'s bit is
  already in `solvable`, and `solvable` is what the iteration returns;
* the move is taken — then the bit travels
  `movable` → `movable'` → `movable''` → `solvable ||| movable''`, which is
  `exists_movable_bit_of_critical`, `bitSet_movablePrime`, `bitSet_movableComp`,
  `bitSet_accum` in order.

The `break` costs nothing here: `if sol == allkings then .done sol else .yield sol` has
the same `.value` either way.  (Where `allkings` *does* matter is the iterations after
this one, and there `bitSet_allkings_of_cfg` says the break cannot fire early enough to
hurt.)

The one hypothesis that is not local data is `ChildSpecComplete p` — the induction
hypothesis, applicable because `SolverMove` drops `DepthSum` (`move_merged`, carried by
`exists_child_of_critical`).  Reaching it needs the child call's *run*, which is why
`Contributes` records it.
-/

/-- Complementing a mask complements every bit. -/
theorem BitSet_not (x : UInt16) (k : Fin 16) : BitSet (~~~x) k ↔ ¬ BitSet x k := by
  rw [BitSet_toNat, BitSet_toNat,
    show (~~~x).toNat = (~~~x.toBitVec).toNat from rfl,
    show x.toNat = x.toBitVec.toNat from rfl,
    ← BitVec.getLsbD, ← BitVec.getLsbD, BitVec.getLsbD_not]
  simp [k.isLt]

/-- **The iteration at the critical pile sets the critical configuration's bit.**

`i` is the block configuration `solverGetMovable` names, `k` the configuration the
critical state `t₀` is in; the caller closes the remaining gap between `k` and its own
query with `cfg_eq_or_component_bits` and `CompAllOrNothing.transfer`. -/
theorem critical_iteration_bitSet
    {g g' : Globals} {p : SolverPosType} {ki : KingInfo} {comp allkings vacc : UInt16}
    {r : ForInStep UInt16} {pile : Nat} {t₀ t₁ : State} {m : Move}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hkiloc : PossibleKingsLocal p ki) (hkic : KingInfoCorrect p ki)
    (hhm : HashmapComplete g) (hcsp : ChildSpecComplete p)
    (hpile : pile < 10)
    (hdpk : DepthPlusKings g t₀ p)
    (hlen : (t₀.tableau ⟨pile, hpile⟩).length = (p.pileDepth.get ⟨pile, hpile⟩).toNat)
    (hda : 0 < (p.pileDepth.get ⟨pile, hpile⟩).toNat)
    (hsrc : m.src = Position.pile ⟨pile, hpile⟩)
    (hdst : m.dest ≠ Position.pile ⟨pile, hpile⟩)
    (hap : applyMove t₀ m = some t₁) (hsolv : Solvable t₁)
    (hrun : recBody solverRecCheckSolvable p (closureInfoOf p) ki comp allkings pile vacc g
      = .ok r g') :
    ∃ (i : Nat) (k : Fin 16), i < (closureInfoOf p).numBits.toNat ∧
      DepthPlusKingsCfg g t₀ p k ∧ MaskSub (globalCfg (closureInfoOf p) i) k ∧
      BitSet r.value ⟨min i 15, by omega⟩ := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hidx : (UInt32.ofNat pile).toNat < 10 := by
    rw [ofNat_pile_toNat hpile]; exact hpile
  have haeq : (⟨(UInt32.ofNat pile).toNat, hidx⟩ : Fin 10) = ⟨pile, hpile⟩ :=
    Fin.ext (ofNat_pile_toNat hpile)
  have hd : 0 < (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat := by
    rw [haeq]; exact hda
  have hb5 : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat - 1 < 5 := by
    have := hb.pileDepth_bound ⟨(UInt32.ofNat pile).toNat, hidx⟩
    omega
  -- the physical top card of the source column
  obtain ⟨c, rest, hcol⟩ : ∃ (c : Card) (rest : Column), t₀.tableau ⟨pile, hpile⟩ = c :: rest := by
    cases hc : t₀.tableau ⟨pile, hpile⟩ with
    | nil => rw [hc] at hlen; simp at hlen; omega
    | cons c rest => exact ⟨c, rest, rfl⟩
  -- the body, unfolded as far as `movable`
  rw [recBody, bind_ok (vector_getE_apply p.pileDepth (UInt32.ofNat pile) g hidx)] at hrun
  have hdz : ¬ (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩ == 0) = true := by
    intro hc
    have : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat = 0 := by
      rw [show p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩ = 0 from by simpa using hc]
      rfl
    omega
  rw [if_neg hdz,
    bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g = .ok PUnit.unit g from rfl)]
    at hrun
  dsimp only at hrun
  rw [bind_ok (vector_getE_apply p.pileFlute (UInt32.ofNat pile) g hidx)] at hrun
  obtain ⟨toPile, hgd⟩ : ∃ tp : UInt8,
      solverGetDestination p (UInt32.ofNat pile) g = .ok tp g := by
    rcases getDest_spec' hwf hcan hidx hd hb5 with ⟨-, h⟩ | ⟨n, -, -, -, -, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  rw [bind_ok hgd] at hrun
  obtain ⟨mvm, hmvrun, hmvloc⟩ := getMovable_run (g := g) ki
    (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile
    (hb.flute_pos ⟨(UInt32.ofNat pile).toNat, hidx⟩) hkiloc
  have hmvapp : solverGetMovable ki (closureInfoOf p).shiftValue
      (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile g = .ok mvm g := hmvrun
  rw [bind_ok hmvapp] at hrun
  -- the destination is valid, and `DestValid` speaks about the column's head
  obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hidx hd hb5 hgd
  have hdv' : SolverSpec.DestValid g p (encodeCard c) toPile := by
    have hgen : ∀ (n : Nat) (hn : n < 10) (h5 : (p.pileDepth.get ⟨n, hn⟩).toNat - 1 < 5),
        n = pile →
        SolverSpec.DestValid g p
          ((g.pos2card.get ⟨n, hn⟩).get ⟨(p.pileDepth.get ⟨n, hn⟩).toNat - 1, h5⟩) toPile →
        SolverSpec.DestValid g p (encodeCard c) toPile := by
      rintro n hn h5 rfl hdvn
      rw [head_eq_boundary hdpk.depth_lt6 hdpk.depth_match hcol hlen hda h5]
      exact hdvn
    exact hgen _ hidx hb5 (ofNat_pile_toNat hpile) hdv
  -- the `movable` bit, and everything the child assembly needs
  obtain ⟨i, k, hi, hkc, hpres, hms, hmvbit⟩ :=
    exists_movable_bit_of_critical (a := ⟨pile, hpile⟩) hwf hcan hdpk hcol hlen hda hsrc hap hdst
      hdv' hkic (by rw [haeq] at hmvrun; exact hmvrun)
  refine ⟨i, k, hi, hkc, hms, ?_⟩
  by_cases hnew : (mvm &&& ~~~vacc != 0) = true
  · -- the move is taken
    rw [if_pos hnew,
      bind_ok (show (get : EStateM Error Globals Globals) g = .ok g g from rfl)] at hrun
    obtain ⟨fk, p', s', k', FK, hmove, hcan', hmeas, hks', hsolv', hvac, hfk, hsub'⟩ :=
      exists_child_of_critical (pile := UInt32.ofNat pile) hwf hcan hkc hidx hd
        (by rw [haeq]; exact hlen) (by rw [haeq]; exact hsrc) (by rw [haeq]; exact hdst) hap
        hsolv hgd hpres hi hms
    rw [hmove] at hrun
    dsimp only at hrun
    rw [bind_ok (show (set g : EStateM Error Globals PUnit) g = .ok PUnit.unit g from rfl)] at hrun
    have hfp' : p'.freePiles.toNat ≤ 10 := by
      have h := freePiles_bound hcan'.toSolverInvMerged
      have : p'.freePiles.toInt = (p'.freePiles.toNat : Int) := rfl
      omega
    rw [bind_ok (closureInfos_getE_apply g p' hfp')] at hrun
    cases hcs : solverRecCheckSolvable p' g with
    | error e s => rw [bind_error hcs] at hrun; exact absurd hrun (by simp)
    | ok cs g₃ =>
      rw [bind_ok hcs] at hrun
      obtain ⟨⟨hccomp, hcsloc⟩, -, -⟩ := hcsp p' g g₃ cs hmeas hwf hcan' hhm hcs
      -- the `subsetTable` lookup
      have hcsm : (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat
          < 2 ^ (closureInfoOf p').numBits.toNat := LocalMask.and_left _ hcsloc
      have hnb' : (closureInfoOf p').numBits.toNat ≤ 6 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
        exact hh _
      have hoff' : (closureInfoOf p').offset.toNat + 2 ^ (closureInfoOf p').numBits.toNat ≤ 100 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11,
            (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
          decide
        exact hh _
      have hsum : ((closureInfoOf p').offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat
          = (closureInfoOf p').offset.toNat
            + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
        omega
      have h100 : ((closureInfoOf p').offset.toUInt32
          + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat < 100 := by
        rw [hsum]; omega
      rw [bind_ok (vector_getE_apply subsetTable _ _ h100),
        show subsetTable.get ⟨((closureInfoOf p').offset.toUInt32
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat, h100⟩
            = subsetAt ((closureInfoOf p').offset.toNat
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat) from
          congrArg subsetTable.get (Fin.ext (show ((closureInfoOf p').offset.toUInt32
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat
            = min ((closureInfoOf p').offset.toNat
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat) 99 from
            by omega))] at hrun
      obtain ⟨hrval, -⟩ := tail_run hrun
      rw [hrval, movableComp_eq, ← movablePrime]
      refine bitSet_accum (bitSet_movableComp ?_)
      exact bitSet_movablePrime hi hcsloc hvac hmvbit hfk hsub' (hccomp s' k' hks' hsolv')
  · -- the pile is skipped, so `movable`'s bit is already in the accumulator
    rw [if_neg hnew] at hrun
    replace hrun : EStateM.Result.ok (ForInStep.yield vacc) g = .ok r g' := hrun
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
    show BitSet vacc _
    by_contra hc
    have hz : mvm &&& ~~~vacc = 0 := by simpa using hnew
    have := (BitSet_and mvm (~~~vacc) _).2 ⟨hmvbit, (BitSet_not vacc _).2 hc⟩
    rw [hz] at this
    exact BitSet_zero _ this

/-! ## What every *other* iteration does

The critical iteration produces the bit; the rest of the loop only has to keep it.  Two
facts suffice, and neither is semantic:

* the accumulator only ever grows (`solvable ||| movable''`), so a bit once present stays;
* the loop's early `break` returns `sol` **equal to `allkings`**, and `allkings` misses no
  realizable configuration (`bitSet_allkings_of_cfg`), so stopping early is harmless.

The frame — `HashmapComplete` and "only the memo table changed" — is threaded here too,
because the bit is stated at the *entry* globals while the iterations run at later ones.
-/

/-- The body's tail, with the `break`'s value identified.  (`tail_run` without the last
conjunct.) -/
theorem tail_run_done {A allkings : UInt16} {g g' : Globals} {r : ForInStep UInt16}
    (h : (if (A == allkings) = true then (pure (.done A) : EStateM Error Globals (ForInStep UInt16))
        else pure (.yield A)) g = .ok r g') :
    r.value = A ∧ g' = g ∧ ∀ c : UInt16, r = ForInStep.done c → c = allkings := by
  by_cases hb : (A == allkings) = true
  · rw [if_pos hb] at h
    simp only [pure, EStateM.pure] at h
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj h
    exact ⟨rfl, rfl, fun c hc => by
      rw [show c = A from (ForInStep.done.inj hc).symm]; simpa using hb⟩
  · rw [if_neg hb] at h
    simp only [pure, EStateM.pure] at h
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj h
    exact ⟨rfl, rfl, fun c hc => by simp at hc⟩

/-- **One iteration, read for completeness.**  It keeps every bit the accumulator had, a
`break` can only return `allkings`, and the globals gain nothing but a memo write. -/
theorem recBody_complete_step
    {p : SolverPosType} {ki : KingInfo} {comp allkings : UInt16}
    {pile : Nat} {v : UInt16} {g g' : Globals} {r : ForInStep UInt16}
    (hpile : pile < 10) (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hkiloc : PossibleKingsLocal p ki) (hhm : HashmapComplete g)
    (hcsp : ChildSpecComplete p)
    (hrun : recBody solverRecCheckSolvable p (closureInfoOf p) ki comp allkings pile v g
      = .ok r g') :
    (∀ k : Fin 16, BitSet v k → BitSet r.value k) ∧
    (∀ c : UInt16, r = ForInStep.done c → c = allkings) ∧
    HashmapComplete g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } := by
  have hidx : (UInt32.ofNat pile).toNat < 10 := by
    rw [ofNat_pile_toNat hpile]; exact hpile
  rw [recBody, bind_ok (vector_getE_apply p.pileDepth (UInt32.ofNat pile) g hidx)] at hrun
  by_cases hdz : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩ == 0) = true
  · rw [if_pos hdz] at hrun
    replace hrun : EStateM.Result.ok (ForInStep.yield v) g = .ok r g' := hrun
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
    exact ⟨fun _ h => h, fun c hc => by simp at hc, hhm, g.hashmap, rfl⟩
  · rw [if_neg hdz,
      bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g = .ok PUnit.unit g from rfl)]
      at hrun
    dsimp only at hrun
    rw [bind_ok (vector_getE_apply p.pileFlute (UInt32.ofNat pile) g hidx)] at hrun
    have hd : 0 < (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat := by
      rcases Nat.eq_zero_or_pos (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat with h | h
      · exact absurd (by simpa using UInt8.toNat_inj.1 (h.trans rfl.symm)) hdz
      · exact h
    have hb5 : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat - 1 < 5 := by
      have := hcan.toSolverInvBase.pileDepth_bound ⟨(UInt32.ofNat pile).toNat, hidx⟩
      omega
    obtain ⟨toPile, hgd⟩ : ∃ tp : UInt8,
        solverGetDestination p (UInt32.ofNat pile) g = .ok tp g := by
      rcases getDest_spec' hwf hcan hidx hd hb5 with ⟨-, h⟩ | ⟨n, -, -, -, -, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [bind_ok hgd] at hrun
    obtain ⟨mvm, hmvrun, hmvloc⟩ := getMovable_run (g := g) ki
      (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile
      (hcan.toSolverInvBase.flute_pos ⟨(UInt32.ofNat pile).toNat, hidx⟩) hkiloc
    have hmvapp : solverGetMovable ki (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile g = .ok mvm g := hmvrun
    rw [bind_ok hmvapp] at hrun
    by_cases hnew : (mvm &&& ~~~v != 0) = true
    · rw [if_pos hnew,
        bind_ok (show (get : EStateM Error Globals Globals) g = .ok g g from rfl)] at hrun
      obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hidx hd hb5 hgd
      obtain ⟨fk, p', hmove, hcan', hmeas⟩ :=
        SolverSpec.move_merged g p (UInt32.ofNat pile) toPile hwf hcan hvalid hidx hb5 _ rfl hdv
      rw [hmove] at hrun
      dsimp only at hrun
      rw [bind_ok (show (set g : EStateM Error Globals PUnit) g = .ok PUnit.unit g from rfl)]
        at hrun
      have hfp' : p'.freePiles.toNat ≤ 10 := by
        have h := freePiles_bound hcan'.toSolverInvMerged
        have : p'.freePiles.toInt = (p'.freePiles.toNat : Int) := rfl
        omega
      rw [bind_ok (closureInfos_getE_apply g p' hfp')] at hrun
      cases hcs : solverRecCheckSolvable p' g with
      | error e s => rw [bind_error hcs] at hrun; exact absurd hrun (by simp)
      | ok cs g₃ =>
        rw [bind_ok hcs] at hrun
        obtain ⟨⟨-, hcsloc⟩, hm₃, hm, rfl⟩ := hcsp p' g g₃ cs hmeas hwf hcan' hhm hcs
        have hcsm : (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat
            < 2 ^ (closureInfoOf p').numBits.toNat := LocalMask.and_left _ hcsloc
        have hnb' : (closureInfoOf p').numBits.toNat ≤ 6 := by
          unfold closureInfoOf
          have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
          exact hh _
        have hoff' : (closureInfoOf p').offset.toNat
            + 2 ^ (closureInfoOf p').numBits.toNat ≤ 100 := by
          unfold closureInfoOf
          have hh : ∀ f : Fin 11,
              (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
            decide
          exact hh _
        have hsum : ((closureInfoOf p').offset.toUInt32
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat
            = (closureInfoOf p').offset.toNat
              + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toNat := by
          rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
          omega
        have h100 : ((closureInfoOf p').offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p').shiftValue.toUInt16).toUInt32).toNat < 100 := by
          rw [hsum]; omega
        rw [bind_ok (vector_getE_apply subsetTable _ _ h100)] at hrun
        obtain ⟨hrval, rfl, hdone⟩ := tail_run_done hrun
        exact ⟨fun k hk => by rw [hrval]; exact (BitSet_or _ _ k).2 (Or.inl hk), hdone, hm₃, hm, rfl⟩
    · rw [if_neg hnew] at hrun
      replace hrun : EStateM.Result.ok (ForInStep.yield v) g = .ok r g' := hrun
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
      exact ⟨fun _ h => h, fun c hc => by simp at hc, hhm, g.hashmap, rfl⟩

/-! ## The loop skeleton

`forIn_inv` is the soundness shape — *every* iteration preserves the invariant, which is
established before the loop starts.  Completeness needs the opposite: the property is
**produced** by one distinguished iteration, and only the ones after it have to keep it.
So the invariant is really the user's

> the pile index is at most the critical one, **or** the bit is already in `solvable`,

which as an induction over the remaining pile list is: `a` is still to come, or `P`.

Two predicates, because the distinguished iteration needs context of its own: `R` is the
ordinary invariant carried from the start (here the memo frame), `P` the property produced
at `a` and kept afterwards.  The `break` gets its own clause — it can fire before `a` is
reached, and then `P` has to come from the returned value itself. -/

/-- Once `P` holds it survives to the end of the loop. -/
theorem forIn_keep {β : Type} (R : β → Globals → Prop) (P : β → Prop)
    (body : Nat → β → EStateM Error Globals (ForInStep β)) (l : List Nat)
    (hR : ∀ x ∈ l, ∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
      R b g → body x b g = .ok r g' → R r.value g')
    (hP : ∀ x ∈ l, ∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
      R b g → P b → body x b g = .ok r g' → P r.value) :
    ∀ (b : β) (g : Globals) (b' : β) (g' : Globals),
      R b g → P b → forIn l b body g = .ok b' g' → P b' ∧ R b' g' := by
  intro b g b' g' hr hp hrun
  exact forIn_inv (fun x gg => P x ∧ R x gg) body l
    (fun x hx bb gg rr gg' hPR hb =>
      ⟨hP x hx bb gg rr gg' hPR.2 hPR.1 hb, hR x hx bb gg rr gg' hPR.2 hb⟩)
    b g b' g' ⟨hp, hr⟩ hrun

/-- **One iteration establishes `P`, and the loop returns with it.**  The three ways the
loop can end are all covered: it reaches `a` (`hcrit`), it breaks first (`hbreak`), or it
runs past `a` (`forIn_keep`). -/
theorem forIn_reach {β : Type} (R : β → Globals → Prop) (P : β → Prop)
    (body : Nat → β → EStateM Error Globals (ForInStep β)) :
    ∀ (l : List Nat) (a : Nat), a ∈ l →
      (∀ x ∈ l, ∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
        R b g → body x b g = .ok r g' → R r.value g') →
      (∀ x ∈ l, ∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
        R b g → P b → body x b g = .ok r g' → P r.value) →
      (∀ x ∈ l, ∀ (b : β) (g : Globals) (c : β) (g' : Globals),
        R b g → body x b g = .ok (ForInStep.done c) g' → P c) →
      (∀ (b : β) (g : Globals) (r : ForInStep β) (g' : Globals),
        R b g → body a b g = .ok r g' → P r.value) →
      ∀ (b : β) (g : Globals) (b' : β) (g' : Globals),
        R b g → forIn l b body g = .ok b' g' → P b' ∧ R b' g' := by
  intro l
  induction l with
  | nil => intro a ha; simp at ha
  | cons x l ih =>
    intro a ha hR hP hbreak hcrit b g b' g' hr hrun
    rw [List.forIn_cons] at hrun
    simp only [bind, EStateM.bind] at hrun
    cases hbx : body x b g with
    | error e s => rw [hbx] at hrun; simp at hrun
    | ok rr s =>
      rw [hbx] at hrun
      have hr' : R rr.value s := hR x (by simp) b g rr s hr hbx
      cases rr with
      | done c =>
        simp only [pure, EStateM.pure] at hrun
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
        exact ⟨hbreak x (by simp) b g c s hr hbx, hr'⟩
      | yield c =>
        by_cases hxa : x = a
        · subst hxa
          exact forIn_keep R P body l (fun y hy => hR y (by simp [hy]))
            (fun y hy => hP y (by simp [hy])) c s b' g' hr'
            (hcrit b g (ForInStep.yield c) s hr hbx) hrun
        · exact ih a ((List.mem_cons.1 ha).resolve_left (fun h => hxa h.symm))
            (fun y hy => hR y (by simp [hy])) (fun y hy => hP y (by simp [hy]))
            (fun y hy => hbreak y (by simp [hy])) hcrit c s b' g' hr' hrun

/-! ## Matching does not read the memo table

`DepthPlusKings`'s only `g`-dependent clause is `depth_match`, and `PileMatches` reads
`pos2card`; so the transfer is the same three lines as
`StateMatchesSolverPos.hashmap_iff`. -/

theorem DepthPlusKings.hashmap_iff {g : Globals} {u : State} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) :
    DepthPlusKings { g with hashmap := hm } u p ↔ DepthPlusKings g u p := by
  constructor <;> intro h <;>
    exact { cards_count := h.cards_count, depth_lt6 := h.depth_lt6,
            depth_match := h.depth_match, king_le := h.king_le,
            aces_match := h.aces_match, flute_le := h.flute_le }

theorem DepthPlusKingsCfg.hashmap_iff {g : Globals} {u : State} {p : SolverPosType}
    {k : Fin 16} (hm : Vector UInt16 BIG_HASH_SIZE) :
    DepthPlusKingsCfg { g with hashmap := hm } u p k ↔ DepthPlusKingsCfg g u p k := by
  constructor <;> intro h
  · exact { toDepthPlusKings := (DepthPlusKings.hashmap_iff hm).1 h.toDepthPlusKings,
            realizes := h.realizes, no_pile := h.no_pile }
  · exact { toDepthPlusKings := (DepthPlusKings.hashmap_iff hm).2 h.toDepthPlusKings,
            realizes := h.realizes, no_pile := h.no_pile }

/-! ## The pile loop, completeness half -/

/-- What the loop is asked to deliver: some block configuration above one the critical
state stands for, with its bit in the accumulator.  Stated at the loop's *entry* globals,
which is why the memo frame has to travel alongside. -/
def CriticalBit (g : Globals) (t₀ : State) (p : SolverPosType) (v : UInt16) : Prop :=
  ∃ (i : Nat) (k : Fin 16), i < (closureInfoOf p).numBits.toNat ∧
    DepthPlusKingsCfg g t₀ p k ∧ MaskSub (globalCfg (closureInfoOf p) i) k ∧
      BitSet v ⟨min i 15, by omega⟩

/-- **The pile loop sets the critical bit.**  `pile` is the source pile of the critical
move; the loop reaches it unless it breaks first, and a break returns `allkings`, which
misses no realizable configuration. -/
theorem critical_loop_bitSet
    {g g' : Globals} {p : SolverPosType} {ki : KingInfo} {comp allkings vfin : UInt16}
    {pile : Nat} {t₀ t₁ : State} {m : Move}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (hkiloc : PossibleKingsLocal p ki) (hkic : KingInfoCorrect p ki)
    (hhm : HashmapComplete g) (hcsp : ChildSpecComplete p)
    (hallk : allkings = (ki.possibleKings.get ⟨0, by omega⟩).toUInt16)
    (hpile : pile < 10) (hdpk : DepthPlusKings g t₀ p)
    (hlen : (t₀.tableau ⟨pile, hpile⟩).length = (p.pileDepth.get ⟨pile, hpile⟩).toNat)
    (hda : 0 < (p.pileDepth.get ⟨pile, hpile⟩).toNat)
    (hsrc : m.src = Position.pile ⟨pile, hpile⟩)
    (hdst : m.dest ≠ Position.pile ⟨pile, hpile⟩)
    (hap : applyMove t₀ m = some t₁) (hsolv : Solvable t₁)
    (hrun : forIn (List.range 10) (0 : UInt16)
      (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp allkings) g = .ok vfin g') :
    CriticalBit g t₀ p vfin ∧ HashmapComplete g' ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  -- the frame invariant, and what it restores at every iteration's globals
  set R : UInt16 → Globals → Prop := fun _ gg =>
    HashmapComplete gg ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, gg = { g with hashmap := hm }
    with hRdef
  have hctx : ∀ (b : UInt16) (gg : Globals), R b gg →
      WellFormedLayout gg ∧ IsCanonicalPos gg p ∧ HashmapComplete gg := by
    rintro b gg ⟨hhm', hm, rfl⟩
    exact ⟨hwf.set_hashmap hm, hcan.set_hashmap hm, hhm'⟩
  -- the `break`'s configuration, computed once at the entry globals
  have hcfg0 : DepthPlusKingsCfg g t₀ p (cfgOf t₀ p) := hdpk.toCfg
  obtain ⟨i₀, hi₀, hsub₀⟩ := exists_block_cfg_maskSub hcan.toSolverInvMerged hcfg0.realizes
  have hallbit : BitSet allkings ⟨min i₀ 15, by omega⟩ := by
    rw [hallk]; exact bitSet_allkings_of_cfg hb hkic hcfg0 hi₀ hsub₀
  -- the three loop obligations
  have hstep : ∀ (x : Nat), x ∈ List.range 10 → ∀ (b : UInt16) (gg : Globals)
      (r : ForInStep UInt16) (gg' : Globals), R b gg →
      recBody solverRecCheckSolvable p (closureInfoOf p) ki comp allkings x b gg = .ok r gg' →
      (∀ k : Fin 16, BitSet b k → BitSet r.value k) ∧
        (∀ c : UInt16, r = ForInStep.done c → c = allkings) ∧ R r.value gg' := by
    intro x hx b gg r gg' hr hbx
    obtain ⟨hwf', hcan', hhm'⟩ := hctx b gg hr
    obtain ⟨hgrow, hdone, hhm'', hm', hgg'⟩ :=
      recBody_complete_step (List.mem_range.1 hx) hwf' hcan' hkiloc hhm' hcsp hbx
    refine ⟨hgrow, hdone, hhm'', ?_⟩
    obtain ⟨-, hm, rfl⟩ := hr
    exact ⟨hm', by rw [hgg']⟩
  refine forIn_reach R (CriticalBit g t₀ p)
    (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp allkings) (List.range 10) pile
    (List.mem_range.2 hpile)
    (fun x hx b gg r gg' hr hbx => (hstep x hx b gg r gg' hr hbx).2.2)
    (fun x hx b gg r gg' hr hp hbx => ?_) (fun x hx b gg c gg' hr hbx => ?_)
    (fun b gg r gg' hr hbx => ?_) 0 g vfin g' ⟨hhm, g.hashmap, rfl⟩ hrun
  · -- a later iteration keeps the bit
    obtain ⟨i, k, hi, hk, hms, hbit⟩ := hp
    exact ⟨i, k, hi, hk, hms, (hstep x hx b gg r gg' hr hbx).1 _ hbit⟩
  · -- the `break` returns `allkings`
    rw [(hstep x hx b gg (ForInStep.done c) gg' hr hbx).2.1 c rfl]
    exact ⟨i₀, cfgOf t₀ p, hi₀, hcfg0, hsub₀, hallbit⟩
  · -- the critical iteration produces it
    obtain ⟨hwf', hcan', hhm'⟩ := hctx b gg hr
    obtain ⟨-, hm, rfl⟩ := hr
    obtain ⟨i, k, hi, hk, hms, hbit⟩ :=
      critical_iteration_bitSet hwf' hcan' hkiloc hkic hhm' hcsp hpile
        ((DepthPlusKings.hashmap_iff hm).2 hdpk) hlen hda hsrc hdst hap hsolv hbx
    exact ⟨i, k, hi, (DepthPlusKingsCfg.hashmap_iff hm).1 hk, hms, hbit⟩
