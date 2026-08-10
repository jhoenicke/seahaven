import Seahaven.MovableBit
import Seahaven.RecLoopSound

/-!
# Carrying the child's answer back into `movable'`

The mirror of `kingStep_transport`.  Soundness reads the recursion's query *down* —
from the parent's configuration to the one the child state stands for; completeness
reads it *up*, from the bit the child's answer really has to the bit the parent's loop
records.

Both halves of `subsetAt_spec_pos` are used, in opposite directions, and the
`&&& forcedKings` intersection is what makes the up-reading legitimate:

* the child's answer has `k''`'s bit, so some stored child configuration `d` covers
  `k''` (`subsetAt_spec_pos`, `→`);
* `k''` piles every vacated suit, hence so does `d` (`KingVacates.mono`), so `d`
  survives `&&& (forcedKings >>> childShift)`;
* `d` covers `k''` which covers the parent's block configuration, so by transitivity it
  covers that too (`subsetAt_spec_pos`, `←`).

Finally `>>> parentShift` moves the surviving bit into the parent's block, where it
meets the `movable` bit of `MovableBit.exists_movable_bit_of_critical`.

The one thing this does *not* do is produce `hsub` — that the child's configuration
piles at least what the parent's block configuration does.  That is the re-assembly
(`KingAssemble.exists_block_match`), and it is a hypothesis here, as `SubsetSound` was
on the soundness side.
-/

/-- **The completeness reading of the `forcedKings` intersection.**  Converse of
`kingStep_transport`: a bit the child's answer has at a configuration that survives
`fk` is still there after the intersection, at any configuration that configuration
covers. -/
theorem kingStep_transport_complete (p' : SolverPosType) {T fk : UInt16} {FK : Finset Suit}
    {gi k' : Fin 16} (hT : LocalMask p' T) (hv : KingVacates FK fk)
    (hfk : BitSet fk k') (hsub : MaskSub k' gi)
    (hbit : BitSet (subsetAt ((closureInfoOf p').offset.toNat + T.toNat)) k') :
    BitSet (subsetAt ((closureInfoOf p').offset.toNat +
        (T &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat)) gi := by
  have hble : (closureInfoOf p').shiftValue.toNat + (closureInfoOf p').numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p'.freePiles.toNat 10, by omega⟩
  have hbpos : 1 ≤ (closureInfoOf p').numBits.toNat :=
    closureInfo_numBits_pos ⟨min p'.freePiles.toNat 10, by omega⟩
  obtain ⟨i, hi, hbT, hd⟩ := (subsetAt_spec_pos p' hT k').1 hbit
  -- the stored configuration `d` covers `k'`, so it survives `fk` too …
  have hdfk : BitSet fk (globalCfg (closureInfoOf p') i) := hv.mono hd hfk
  refine (subsetAt_spec_pos p' (LocalMask.and_left _ hT) gi).2 ⟨i, hi, ?_, hd.mono hsub⟩
  rw [UInt16.toNat_and, Nat.testBit_and, Bool.and_eq_true]
  refine ⟨hbT, ?_⟩
  -- … and bit `i` of `fk >>> shift` is bit `shift + i` of `fk`
  rw [UInt16.toNat_shiftRight, UInt8.toNat_toUInt16,
    Nat.mod_eq_of_lt (by omega : (closureInfoOf p').shiftValue.toNat < 16),
    Nat.testBit_shiftRight]
  rw [BitSet_toNat, globalCfg_val _ _ (by omega)] at hdfk
  exact hdfk

/-- **The contribution's bit.**  Everything the iteration computes, joined: the
`movable` bit says the solver considers the move at configuration `i`, the child's
answer says the position it leads to is solvable at `k''`, and `k''` both survives
`forcedKings` and covers `i`. -/
theorem bitSet_movablePrime {p p' : SolverPosType} {mv cs fk : UInt16} {FK : Finset Suit}
    {i : Nat} (hi : i < (closureInfoOf p).numBits.toNat)
    (hcs : LocalMask p' cs) (hvac : KingVacates FK fk)
    (hmvbit : BitSet mv ⟨min i 15, by omega⟩)
    {k'' : Fin 16} (hfk : BitSet fk k'')
    (hsub : MaskSub k'' (globalCfg (closureInfoOf p) i))
    (hchild : BitSet (subsetAt ((closureInfoOf p').offset.toNat + cs.toNat)) k'') :
    BitSet (movablePrime p p' mv cs fk) ⟨min i 15, by omega⟩ := by
  have hble : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p.freePiles.toNat 10, by omega⟩
  have htr := kingStep_transport_complete p' hcs hvac hfk hsub hchild
  unfold movablePrime
  rw [BitSet_and]
  refine ⟨hmvbit, ?_⟩
  rw [BitSet_toNat, UInt16.toNat_shiftRight, UInt8.toNat_toUInt16,
    Nat.mod_eq_of_lt (by omega : (closureInfoOf p).shiftValue.toNat < 16),
    Nat.testBit_shiftRight,
    show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega)]
  rw [BitSet_toNat, globalCfg_val _ _ (by omega)] at htr
  exact htr
