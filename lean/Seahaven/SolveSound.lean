import Seahaven.ConvertSim
import Seahaven.Phase1Sim

/-!
# Soundness of `solve`

`solve pk10` returns `SUCCESS = 0` only when the position really is solvable.

The call is three steps, and each one now has its spec:

1. `SolverConvertFromPilesKings pk10` — `SolverSpec.convert_simulates`: the
   resulting position `p` is canonical, and the legal moves it stands for take the
   concrete state `s` (which stands for the prologue's position `convertPre g
   pk10` at the king configuration `pk10[10]` names) to a state `v` standing
   for `p` at some configuration `k'`;
2. the `hash = 0` shortcut — `solvable_of_hash_zero`: a position with all depths
   zero has all four foundations complete, so the matching state *is* the goal;
3. `solverRecCheckSolvable` plus the final `subsetTable` read —
   `recCheckSolvableSound` gives `SoundBits g p cs`, and `Simulates.transport`
   carries the bit the solver tested at the *parent's* configuration over to the
   one the successor state actually realizes.  This is the same `&&& forcedKings`
   transport the recursion itself performs (`kingStep_transport`); at the top level
   the "parent" is the configuration `pk10[10]` supplies.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## The king configuration `pk10[10]` names -/

theorem cv_xor_lt16 {x : UInt8} (h : x.toNat < 16) : (x ^^^ 0xf).toNat < 16 := by
  rw [UInt8.toNat_xor]
  exact Nat.xor_lt_two_pow (n := 4) h (by decide)

/-- **The configuration `solve` tests.**  `pk10[10]` has bit `su` set when suit
    `su`'s king is still in a regular pile; `^^^ 0xf` flips that into the internal
    convention (bit set = the suit has *no* pile), and `bits2grlex` turns the
    bitmask into the grlex index the `subsetTable` blocks are indexed by. -/
def kingCfgOf (pk10 : Vector UInt8 11) (h : (pk10.get ⟨10, by omega⟩).toNat < 16) : Fin 16 :=
  ⟨(bits2grlex.get ⟨((pk10.get ⟨10, by omega⟩) ^^^ 0xf).toNat, cv_xor_lt16 h⟩).toNat,
   bits2grlex_lt _⟩

/-! ## The tail of `solve`, split off -/

/-- Everything `solve` does after the convert call: the `hash = 0` shortcut, the
    recursive check, and the final `subsetTable` read. -/
def solveTail (pk10 : Vector UInt8 11) (forcedKings : UInt16) (game : SolverPosType) :
    EStateM Error Globals UInt8 := do
  if game.hash == 0 then
    return 0  -- SUCCESS: game already solved
  let kingbit ← bits2grlex.getE ((← pk10.getE 10) ^^^ 0xf).toUInt32
  let ci ← closureInfos.getE game.freePiles.toUInt32
  let solvable := (← solverRecCheckSolvable game) &&&
                  (forcedKings >>> ci.shiftValue.toUInt16)
  let tableEntry ← subsetTable.getE (ci.offset.toUInt32 + solvable.toUInt32)
  if tableEntry &&& ((1 : UInt16) <<< kingbit.toUInt16) != 0 then
    return 0  -- SUCCESS
  else
    return 2  -- NOMOVE

/-- The `rfl`-twin of `solve` with its tail named. -/
theorem solve_eq_explicit (pk10 : Vector UInt8 11) :
    _root_.solve pk10 = (do
      let globals ← get
      match EStateM.run (_root_.SolverConvertFromPilesKings pk10)
          (globals, emptySolverPosType) with
      | .error e _ => throw e
      | .ok forcedKings (globals', game) => do
          set globals'
          solveTail pk10 forcedKings game) :=
  rfl

/-! ## `UInt8 → UInt16` and the bit test -/

theorem uint8_toUInt16_eq (x : UInt8) : x.toUInt16 = UInt16.ofNat x.toNat := by
  apply UInt16.toNat_inj.mp
  rw [UInt8.toNat_toUInt16, UInt16.toNat_ofNat']
  have := x.toNat_lt
  omega

/-! ## The tail is sound -/

set_option maxHeartbeats 1000000 in
/-- **What `solve`'s tail knows when it answers `SUCCESS`.**  Either the position
    is already solved (`hash = 0`), or the recursive check returned a sound local
    mask whose `forcedKings`-filtered `subsetTable` expansion contains the
    configuration `pk10[10]` names.  Everything below this is a matter of which
    state that bit is read against. -/
theorem solveTail_bits {g g' : Globals} {pk10 : Vector UInt8 11}
    {p : SolverPosType} {fk : UInt16}
    (hwf : WFGlobals g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hrun : solveTail pk10 fk p g = .ok 0 g') :
    p.hash = 0 ∨ ∃ cs : UInt16, LocalMask p cs ∧ SoundBits g p cs ∧
      BitSet (subsetAt ((closureInfoOf p).offset.toNat
        + (cs &&& (fk >>> (closureInfoOf p).shiftValue.toUInt16)).toNat))
        (kingCfgOf pk10 hs10) := by
  rw [solveTail] at hrun
  by_cases hz : (p.hash == 0) = true
  · exact Or.inl (by simpa using hz)
  · refine Or.inr ?_
    rw [if_neg hz, bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g
      = .ok PUnit.unit g from rfl)] at hrun
    dsimp only at hrun
    -- the `pk10[10]` read
    have h10 : (10 : UInt32).toNat < 11 := by decide
    have h10' : pk10.get ⟨(10 : UInt32).toNat, h10⟩ = pk10.get ⟨10, by omega⟩ := rfl
    rw [bind_ok (vector_getE_apply pk10 10 g h10), h10'] at hrun
    -- the `bits2grlex` read
    have hkb : ((pk10.get ⟨10, by omega⟩ ^^^ 0xf).toUInt32).toNat < 16 := by
      rw [UInt8.toNat_toUInt32]; exact cv_xor_lt16 hs10
    have hkbEq : bits2grlex.get ⟨((pk10.get ⟨10, by omega⟩ ^^^ 0xf).toUInt32).toNat, hkb⟩
        = bits2grlex.get ⟨(pk10.get ⟨10, by omega⟩ ^^^ 0xf).toNat, cv_xor_lt16 hs10⟩ :=
      congrArg bits2grlex.get (Fin.ext (UInt8.toNat_toUInt32 _))
    rw [bind_ok (vector_getE_apply bits2grlex _ g hkb), hkbEq] at hrun
    -- the `closureInfos` read
    have hfple : p.freePiles.toNat ≤ 10 := freePiles_toNat_le hcan.toSolverInvMerged
    have hfp : (p.freePiles.toUInt32).toNat < 11 := by rw [UInt8.toNat_toUInt32]; omega
    have hvaleq : (p.freePiles.toUInt32).toNat = min p.freePiles.toNat 10 := by
      rw [UInt8.toNat_toUInt32]; omega
    have hciEq : closureInfos.get ⟨(p.freePiles.toUInt32).toNat, hfp⟩ = closureInfoOf p := by
      unfold closureInfoOf
      exact congrArg closureInfos.get (Fin.ext hvaleq)
    rw [bind_ok (vector_getE_apply closureInfos _ g hfp), hciEq] at hrun
    -- the recursive check
    cases hrc : solverRecCheckSolvable p g with
    | error e g2 =>
      rw [bind_error hrc] at hrun
      simp at hrun
    | ok cs g2 =>
      obtain ⟨⟨hcssound, hcsloc⟩, -, -⟩ := recCheckSolvableSound g g2 p cs hwf hcan hrc
      rw [bind_ok hrc] at hrun
      -- the `subsetTable` read: the answer stays inside its block, and blocks fit below 100
      have hsolvloc : (cs &&& (fk >>> (closureInfoOf p).shiftValue.toUInt16)).toNat
          < 2 ^ (closureInfoOf p).numBits.toNat := LocalMask.and_left _ hcsloc
      have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
        exact hh _
      have hoff : (closureInfoOf p).offset.toNat + 2 ^ (closureInfoOf p).numBits.toNat ≤ 100 := by
        unfold closureInfoOf
        have hh : ∀ f : Fin 11,
            (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
          decide
        exact hh _
      have h64 : (2 : Nat) ^ (closureInfoOf p).numBits.toNat ≤ 64 :=
        calc (2 : Nat) ^ (closureInfoOf p).numBits.toNat ≤ 2 ^ 6 :=
              Nat.pow_le_pow_right (by omega) hnb
          _ = 64 := by norm_num
      have hsum : ((closureInfoOf p).offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat
          = (closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
        omega
      have h100 : ((closureInfoOf p).offset.toUInt32
          + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat < 100 := by
        rw [hsum]
        omega
      have hidxeq : ((closureInfoOf p).offset.toUInt32
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat
          = min ((closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat) 99 := by
        rw [hsum]; omega
      rw [bind_ok (vector_getE_apply subsetTable _ g2 h100),
        show subsetTable.get ⟨((closureInfoOf p).offset.toUInt32
              + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toUInt32).toNat, h100⟩
            = subsetAt ((closureInfoOf p).offset.toNat
              + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat) from
          congrArg subsetTable.get (Fin.ext hidxeq)] at hrun
      -- the final bit test: returning `0` forces it
      by_cases htest : (subsetAt ((closureInfoOf p).offset.toNat
          + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat)
          &&& ((1 : UInt16) <<< (bits2grlex.get
            ⟨(pk10.get ⟨10, by omega⟩ ^^^ 0xf).toNat, cv_xor_lt16 hs10⟩).toUInt16) != 0) = true
      · have hbit : BitSet (subsetAt ((closureInfoOf p).offset.toNat
            + (cs &&& fk >>> (closureInfoOf p).shiftValue.toUInt16).toNat))
            (kingCfgOf pk10 hs10) := by
          unfold BitSet kingCfgOf
          rw [← uint8_toUInt16_eq]
          exact bne_iff_ne.mp htest
        exact ⟨cs, hcsloc, hcssound, hbit⟩
      · rw [if_neg htest] at hrun
        replace hrun : (EStateM.Result.ok 2 g2 : EStateM.Result Error Globals UInt8)
            = .ok 0 g' := hrun
        obtain ⟨h20, -⟩ := EStateM.Result.ok.inj hrun
        exact absurd h20 (by decide)

/-! ## Reading the bit against a state

Two interfaces, differing only in which position the concrete state is matched
against — and hence in how much of the position the caller has to know:

* `solveTail_sound` matches `s` against the **prologue's** position (all flutes
  `1`), so `s` has no freed card sitting on a non-empty column; the cleanup loop's
  simulation is what builds those runs, and `Simulates.transport` carries the
  tested bit across the lone-king vacates the cleanup performs.
* `solveTail_sound_canonical` matches `s` against the position convert **returns**
  — flute lengths whatever the cleanup computed, so freed runs may already sit on
  the piles.  No simulation is needed: there is no configuration change left to
  transport, and the `&&& forcedKings` intersection is a plain weakening. -/

theorem uint16_and_or_absorb (a b : UInt16) : (a &&& b) ||| a = a := by
  apply UInt16.toNat_inj.mp
  rw [UInt16.toNat_or, UInt16.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and]
  cases a.toNat.testBit i <;> cases b.toNat.testBit i <;> rfl

/-- **Reading the bit through a simulation.**  `s` stands for the prologue's
    position; the moves the cleanup and the drain perform take it to a state
    standing for `p`. -/
theorem solveTail_sound {g g' : Globals} {pk10 : Vector UInt8 11} {s : State}
    {P p : SolverPosType} {fk : UInt16}
    (hwf : WFGlobals g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hsim : ∃ (v : State) (k' : Fin 16) (FK : Finset Suit),
      Simulates g s P (kingCfgOf pk10 hs10) v p k' FK fk)
    (hrun : solveTail pk10 fk p g = .ok 0 g') :
    Solvable s := by
  obtain ⟨v, k', FK, hsim⟩ := hsim
  rcases solveTail_bits hwf hcan hs10 hrun with hz | ⟨cs, hcsloc, hcssound, hbit⟩
  · exact Solvable.of_reach hsim.reach (solvable_of_hash_zero hcan hsim.cfg.toMatches hz)
  · exact Solvable.of_reach hsim.reach
      (hcssound v k' hsim.cfg (hsim.transport hcsloc hbit))

/-- **Reading the bit directly.**  `s` stands for the position convert returns —
    arbitrary flute lengths, freed runs already on the piles — so no moves have to
    be simulated at all. -/
theorem solveTail_sound_canonical {g g' : Globals} {pk10 : Vector UInt8 11} {s : State}
    {p : SolverPosType} {fk : UInt16}
    (hwf : WFGlobals g) (hcan : IsCanonicalPos g p)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hmatch : StateMatchesKingConfig g s p (kingCfgOf pk10 hs10))
    (hrun : solveTail pk10 fk p g = .ok 0 g') :
    Solvable s := by
  rcases solveTail_bits hwf hcan hs10 hrun with hz | ⟨cs, hcsloc, hcssound, hbit⟩
  · exact solvable_of_hash_zero hcan hmatch.toMatches hz
  · exact SoundBits.of_sub (LocalMask.and_left _ hcsloc) hcsloc
      (uint16_and_or_absorb _ _) hcssound s _ hmatch hbit

/-! ## `solve` is sound -/

/-- **`solve` is sound.**  If the concrete state `s` is one of the states the
    prologue's position stands for, at the king configuration `pk10[10]` names,
    and `solve pk10` answers `SUCCESS`, then `s` really is solvable. -/
theorem solve_sound {g g' : Globals} {pk10 : Vector UInt8 11} {s : State}
    (hwf : WFGlobals g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hmatch : StateMatchesKingConfig g s (convertPre g pk10) (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok 0 g') :
    Solvable s := by
  obtain ⟨fk, p, v, k', FK, hrunC, hcan, hsim⟩ :=
    convert_simulates g hwf.layout pk10 hpk emptySolverPosType s
      (kingCfgOf pk10 hs10) hmatch
  have hrun' : _root_.solve pk10 g = .ok 0 g' := hrun
  rw [solve_eq_explicit pk10] at hrun'
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hrunC,
    set, EStateM.set] at hrun'
  exact solveTail_sound hwf hcan hs10 ⟨v, k', FK, hsim.toSimulates⟩ hrun'

/-- **`solve` is sound, read against the position it computes.**  This is the
    interface the front end matches: the concrete state's freed runs are already
    sitting on the piles, with whatever flute lengths the cleanup loop derived, so
    the position to match against is the one convert *returns* rather than the one
    its prologue writes.  Nothing has to be simulated.

    (`p` and `hconv` name that position; convert is deterministic, so `hconv`
    pins it and `IsCanonicalPos g p` comes for free.) -/
theorem solve_sound_canonical {g g' : Globals} {pk10 : Vector UInt8 11} {s : State}
    {p : SolverPosType} {fk : UInt16}
    (hwf : WFGlobals g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hconv : EStateM.run (_root_.SolverConvertFromPilesKings pk10) (g, emptySolverPosType)
      = .ok fk (g, p))
    (hmatch : StateMatchesKingConfig g s p (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok 0 g') :
    Solvable s := by
  obtain ⟨fk2, p2, hrun2, hcan2⟩ := convert_canonical g emptySolverPosType pk10 hwf.layout hpk
  injection hconv.symm.trans hrun2 with hfk hst
  injection hst with _hg hp
  have hcan : IsCanonicalPos g p := by rw [hp]; exact hcan2
  have hrun' : _root_.solve pk10 g = .ok 0 g' := hrun
  rw [solve_eq_explicit pk10] at hrun'
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hconv,
    set, EStateM.set] at hrun'
  exact solveTail_sound_canonical hwf hcan hs10 hmatch hrun'

/-! ## Reaching a matched state is enough

`Simulates`' source position is a phantom parameter, so both readings above
generalize for free from "`s` is matched" to "`s` can *reach* a matched state" —
which is what lets a caller normalize, or park a flute into the cells, before
appealing to the solver. -/

theorem solve_sound_of_reach {g g' : Globals} {pk10 : Vector UInt8 11} {s w : State}
    (hwf : WFGlobals g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hreach : Reach s w)
    (hmatch : StateMatchesKingConfig g w (convertPre g pk10) (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok 0 g') :
    Solvable s :=
  Solvable.of_reach hreach (solve_sound hwf hpk hs10 hmatch hrun)

theorem solve_sound_canonical_of_reach {g g' : Globals} {pk10 : Vector UInt8 11} {s w : State}
    {p : SolverPosType} {fk : UInt16}
    (hwf : WFGlobals g) (hpk : ValidDepths pk10)
    (hs10 : (pk10.get ⟨10, by omega⟩).toNat < 16)
    (hconv : EStateM.run (_root_.SolverConvertFromPilesKings pk10) (g, emptySolverPosType)
      = .ok fk (g, p))
    (hreach : Reach s w)
    (hmatch : StateMatchesKingConfig g w p (kingCfgOf pk10 hs10))
    (hrun : EStateM.run (_root_.solve pk10) g = .ok 0 g') :
    Solvable s :=
  Solvable.of_reach hreach (solve_sound_canonical hwf hpk hs10 hconv hmatch hrun)

end SolverSpec
