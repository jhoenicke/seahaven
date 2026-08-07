import Seahaven.SoundnessSkeleton

/-!
# One contribution of `solverRecCheckSolvable`'s pile loop

The inner loop (`Solver.lean:436-456`) computes, for each non-empty pile,

```
movable   = solverGetMovable kingInfo shift fluteLen toPile
fk, p'    = SolverMove pile toPile
cs        = solverRecCheckSolvable p'                       -- the recursive call
cs'       = cs &&& (fk >>> childShift)                      -- the forcedKings filter
movable'  = movable &&& (subsetTable[childOff + cs'] >>> shift)
movable'' = if movable' &&& component ≠ 0 then movable' ||| component else movable'
solvable ||= movable''
```

This file discharges the **`movable'` step**: everything between the recursive
call and the `component` widening.  Two things enter as hypotheses, and both are
meant to:

* `SoundBits g p' cs` — the recursive call is correct at the child position.  This
  is the induction hypothesis of the eventual well-founded induction (`hash`
  strictly decreases, `IsCanonicalPos_hash_inj`), so it cannot be anything else
  here.
* the simulation of the `SolverMove` — either `MoveSimulated` (the named
  obligation in `SoundnessSkeleton`) or, in `recStep_sound_of_sim`, just the
  `Simulates` package it produces, which is what `Simulates.move` in
  `SolverMoveSim` returns.

The claim, in words: *if local bit `i` of `movable'` is set, then every concrete
state standing for `p` at local king configuration `i` is solvable.*  That is one
disjunct of `SoundBits g p movable''`.  Two further steps are deliberately **not**
here: the `component` widening (`ComponentSound`) and the passage from "local bit
`i` of the accumulator is set" to "`k` lies in the accumulator's `subsetTable`
expansion" (`SubsetSound`) — the latter is the only reason `SoundBits` is phrased
over the expansion at all.  Combining the per-pile contributions into the loop
accumulator is `SoundBits.union`, already proved.

The proof is three lines, because all of the work is elsewhere: the `forcedKings`
intersection carries the recursion's query from the configuration the move was
affordable at to the one the child state actually stands for
(`Simulates.transport`), and the cards the simulation moved are put back on the
`Solvable` side by `Solvable.of_reach`.
-/

/-! ## Reading a bit of a right-shifted mask

`movable'` intersects `movable` with a *global* configuration set shifted down by
the parent's `shiftValue`, so local bit `i` of the result is global bit
`shiftValue + i` — i.e. `globalCfg` — of the set. -/

/-- Local bit `i` of `w >>> ci.shiftValue` is `w`'s bit at global configuration
`globalCfg ci i`. -/
theorem BitSet_shiftRight_globalCfg (w : UInt16) (ci : ClosureInfo) (i : Nat)
    (hlt : ci.shiftValue.toNat + i < 16) :
    BitSet (w >>> ci.shiftValue.toUInt16) ⟨min i 15, by omega⟩ ↔ BitSet w (globalCfg ci i) := by
  rw [BitSet_toNat, BitSet_toNat, globalCfg_val ci i (by omega), UInt16.toNat_shiftRight,
    UInt8.toNat_toUInt16, Nat.mod_eq_of_lt (show ci.shiftValue.toNat < 16 by omega),
    Nat.testBit_shiftRight,
    show (⟨min i 15, by omega⟩ : Fin 16).val = i from min_eq_left (by omega)]

/-! ## The contribution -/

/-- **The `movable'` step, from a simulation package.**  `hbit` is the
`movable'`-side hypothesis with the `movable` conjunct already consumed (it was
what produced `hsim`): local configuration `i` of the parent lies in the
`subsetTable` expansion of the `forcedKings`-filtered child answer.

Note which position each `closureInfo` belongs to: the expansion is read in the
**child's** block (`closureInfoOf p'` — the code's `nextClosureInfo`), at the
**parent's** configuration.  That mismatch is the whole point of the
`forcedKings` intersection and is resolved by `Simulates.transport`. -/
theorem recStep_sound_of_sim {g : Globals} {s : State} {p p' : SolverPosType}
    {i : Nat} {cs fk : UInt16}
    (hsim : ∃ (s' : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g s p (globalCfg (closureInfoOf p) i) s' p' k' FK fk)
    (hcs : LocalMask p' cs) (hchild : SoundBits g p' cs)
    (hbit : BitSet (subsetAt ((closureInfoOf p').offset.toNat +
        (cs &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat))
      (globalCfg (closureInfoOf p) i)) :
    Solvable s := by
  obtain ⟨s', k', FK, hsim⟩ := hsim
  exact Solvable.of_reach hsim.reach (hchild s' k' hsim.cfg (hsim.transport hcs hbit))

/-- **The `movable'` step, as the loop body meets it.**  `hbit` is literally "local
bit `i` of `movable'` is set", with `movable'` spelled as `Solver.lean:450-452`
spells it (`subsetAt` for the `subsetTable.getE`, whose bound is the loop's own
bookkeeping), and the conclusion is that the states this bit speaks about really
are solvable.

The hypotheses split cleanly in two: `hi`/`hwf`/`hcanon`/`hs`/`hmv`/`hrun` are
what `MoveSimulated` consumes about *this* move, and `hcs`/`hchild` are the
induction hypothesis about the recursive call. -/
theorem recStep_sound (hMS : MoveSimulated) {g : Globals} {s : State} {p p' : SolverPosType}
    {pile : UInt32} {toPile : UInt8} {mv cs fk : UInt16} {kingInfo : KingInfo} {i : Nat}
    (hi : i < (closureInfoOf p).numBits.toNat)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hs : StateMatchesKingConfig g s p (globalCfg (closureInfoOf p) i))
    (hmv : EStateM.run (solverGetMovable kingInfo (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨pile.toNat % 10, by omega⟩) toPile) g = .ok mv g)
    (hrun : EStateM.run (SolverMove pile toPile) (g, p) = .ok fk (g, p'))
    (hcs : LocalMask p' cs) (hchild : SoundBits g p' cs)
    (hbit : BitSet (mv &&& (subsetAt ((closureInfoOf p').offset.toNat +
        (cs &&& (fk >>> (closureInfoOf p').shiftValue.toUInt16)).toNat)
          >>> (closureInfoOf p).shiftValue.toUInt16)) ⟨min i 15, by omega⟩) :
    Solvable s := by
  have hble : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 :=
    closureInfo_shift_add_numBits ⟨min p.freePiles.toInt.toNat 10, by omega⟩
  rw [BitSet_and] at hbit
  refine recStep_sound_of_sim (hMS g s p p' pile toPile fk mv kingInfo i hi hwf hcanon hs hmv
    hbit.1 hrun) hcs hchild ?_
  exact (BitSet_shiftRight_globalCfg _ (closureInfoOf p) i (by omega)).1 hbit.2
