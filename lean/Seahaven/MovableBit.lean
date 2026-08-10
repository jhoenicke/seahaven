import Seahaven.CriticalChild
import Seahaven.MaximalCfg
import Seahaven.GetMovableSpec

/-!
# The solver really does consider the critical move

Item 1 of the loop body: the `movable` mask `solverGetMovable` returns has the bit of a
block configuration the critical state stands for.

Everything is already proved; this only joins the two ends.

* `DestAfford.critical_dest_affordable` reads the play's own move as the affordability
  disjunction `solverGetMovable`'s mask *is* — `fluteLen` free cells, or `fluteLen - 1`
  together with a column destination or a king pile whose suit is piled.
* `GetMovableSpec.getMovable_bitSet` turns that disjunction, stated at a **block**
  configuration, into the bit.

Between them sits `MaximalCfg`: the critical state's own configuration is sub-maximal,
so it has no bit of its own, and `exists_block_cfg_maskSub` produces a stored
configuration above it.  `freeCellsOf_mono` carries the affordability up (piling more
only frees cells) and `maskSub_piled` carries the `kingOnPile` clause.

The flute bound `fluteLen ≤ 5` that `getMovable_bitSet` needs is *derived*, not assumed:
the affordability gives `fluteLen - 1 ≤ freeCellsOf`, and `freeCellsOf ≤ 4` because
`kingRefund ≤ usedSpace` (`kingRefund_le_usedSpace`).
-/

/-- The cell budget of any configuration is at most the four cells. -/
theorem freeCellsOf_le_four {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (hb : SolverInvBase g p) (k : Fin 16) : freeCellsOf p k ≤ 4 := by
  have := kingRefund_le_usedSpace hwf hb k
  unfold freeCellsOf
  omega

/-- **`solverGetMovable`'s answer has the critical configuration's bit.**

Returns the block index `i` together with the configuration `k` the critical state is
in and `MaskSub (globalCfg … i) k`, since the caller needs all three: the bit indexes
the loop's masks, `k` is what the child is reached at, and the `MaskSub` is what the
`subsetTable` transport composes with. -/
theorem exists_movable_bit_of_critical
    {g : Globals} {t₀ t₁ : State} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p)
    (h : DepthPlusKings g t₀ p)
    {a : Fin 10} {c : Card} {rest : Column}
    (hcol : t₀.tableau a = c :: rest)
    (hlen : (t₀.tableau a).length = (p.pileDepth.get a).toNat)
    (hda : 0 < (p.pileDepth.get a).toNat)
    {mv : Move} (hsrc : mv.src = Position.pile a) (hap : applyMove t₀ mv = some t₁)
    (hdst : mv.dest ≠ Position.pile a)
    {toPile : UInt8} (hdv : SolverSpec.DestValid g p (encodeCard c) toPile)
    {ki : KingInfo} (hchar : KingInfoCorrect p ki) {m : UInt16}
    (hmvrun : EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue
      (p.pileFlute.get a) toPile) g = .ok m g) :
    ∃ (i : Nat) (k : Fin 16), i < (closureInfoOf p).numBits.toNat ∧
      DepthPlusKingsCfg g t₀ p k ∧ MaskSub (globalCfg (closureInfoOf p) i) k ∧
      BitSet m ⟨min i 15, by omega⟩ := by
  have hb : SolverInvBase g p := hcan.toSolverInvBase
  have hmerged : SolverInvMerged g p := hcan.toSolverInvMerged
  obtain ⟨k, hcfg, haff⟩ :=
    critical_dest_affordable hwf hcan h hcol hlen hda hsrc hap hdst hdv
  -- the block configuration above `k`, and the affordability transported to it
  obtain ⟨i, hi, hsub⟩ := exists_block_cfg_maskSub hmerged hcfg.realizes
  have hmono : freeCellsOf p k ≤ freeCellsOf p (globalCfg (closureInfoOf p) i) :=
    freeCellsOf_mono hb hsub
  -- the flute bounds `getMovable_bitSet` asks for
  have hfl1 : 1 ≤ (p.pileFlute.get a).toNat := hb.flute_pos a
  have h4 : freeCellsOf p k ≤ 4 := freeCellsOf_le_four hwf hb k
  have hfl5 : (p.pileFlute.get a).toNat ≤ 5 := by
    rcases haff with h1 | ⟨h1, -⟩ <;> omega
  refine ⟨i, k, hi, hcfg, hsub, getMovable_bitSet hchar hfl1 hfl5 hmvrun hi ?_⟩
  have hcast : (((p.pileFlute.get a).toNat - 1 : Nat) : Int)
      = ((p.pileFlute.get a).toNat : Int) - 1 := by omega
  rcases haff with h1 | ⟨h1, h2⟩
  · exact Or.inl (le_trans h1 hmono)
  · refine Or.inr ⟨by rw [hcast]; exact le_trans h1 hmono, ?_⟩
    rcases h2 with hlt | ⟨h10, h14, hsu⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨h10, h14, fun su hs => maskSub_piled hsub (hsu su hs)⟩
