import Seahaven.SolverSpecKingMove
import Seahaven.SolverSpecCleanupPile
import Seahaven.SolverSpecRemoveFlute
import Seahaven.SolverSpecMoveAces
import Seahaven.SolverSpecDrain

/-!
# Spec for the composed `move` step

`move_merged`: a single solver move (pile-to-pile or pile-to-foundation),
composed from `cleanupPile`/`removeFlute`/`moveAces`, preserves
`SolverInvMerged`.
-/

namespace SolverSpec

open SolverModel
open Lean Lean.Order

/-! ### The destination-bookkeeping step

`SolverMove` first does a pure "destination bookkeeping" write (a three-way
branch on `toPile`: pile-to-pile flute merge / king-pile / extra), then calls
`SolverRemoveFlute pile`.  `moveDestPre` below is that pure write, mirroring
`moveExplicit`'s pre-`finish` branch exactly, and `moveDest_cleanupReady`
establishes `removeFlute_merged`'s precondition `CleanupReady` at the composed
point `fluteNorm ∘ removeFlutePre ∘ moveDestPre`.
-/

/-- Pure state transform for the "destination bookkeeping" `SolverMove` does
    before calling `SolverRemoveFlute` — mirrors `moveExplicit`'s pre-`finish`
    three-way branch exactly (pile-to-pile / king-pile / extra). -/
def moveDestPre (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) : SolverPosType :=
  if h10 : toPile.toNat < 10 then
    { p with
        pileFlute := p.pileFlute.set toPile.toNat
          ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)) h10 }
  else if h14 : toPile.toNat < 14 then
    { p with
        kings := p.kings.set (toPile.toNat - 10)
          ((p.kings[toPile.toNat - 10]'(by omega)) - (p.pileFlute[pile.toNat]'hpile))
          (by omega),
        usedSpace := p.usedSpace + (p.pileFlute[pile.toNat]'hpile) }
  else
    { p with usedSpace := p.usedSpace + (p.pileFlute[pile.toNat]'hpile) }

/-- The destination write touches `pileFlute`/`kings`/`usedSpace` only — never a depth.
    (The card is not off its source pile yet; that is `removeFlutePre`'s decrement.) -/
theorem moveDestPre_pileDepth (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) : (moveDestPre pile toPile hpile p).pileDepth = p.pileDepth := by
  unfold moveDestPre
  split <;> [skip; split] <;> rfl

/-- The `Int32`-cast boundary index the solver computes is the plain `depth - 1`
    (local twin of `GetDestination.depth_index`, which this file deliberately
    does not import). -/
private theorem dest_idx_eq {d : UInt8} (hd1 : 1 ≤ d.toNat) (_hd5 : d.toNat ≤ 5) :
    (d - 1).toUInt32.toNat = d.toNat - 1 := by
  rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _
    (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]
  rfl

/-- A real card's code is a valid `card2*` index. -/
private theorem real_lt64 {c : UInt8} (h : IsRealCard c) : c.toNat < 64 := by
  have h1 := h.1
  have h2 := h.2.2
  have h3 := SUIT_toNat c
  have h4 := VALUE_toNat c
  omega

/-- **The only card the composed destination step newly frees is `pile`'s own
    boundary card `B`.**  `isFreeCard` reads nothing but `pileDepth`, and the
    composed state's `pileDepth` differs from `p`'s only at `pile`, where it has
    dropped by exactly one — so a real card that is free afterwards but not
    before must sit at original slot `(pile, depth-1)`, i.e. be `B` itself
    (`WellFormedLayout.round_trip`). -/
private theorem dest_free_char (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hqdSelf : q.pileDepth.get ⟨pile.toNat, hpile⟩ = (p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1)
    (hqdNe : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileDepth.get j = p.pileDepth.get j)
    (c : UInt8) (hcreal : IsRealCard c) (hfree : isFreeCard g q c) :
    isFreeCard g p c ∨
      c = (g.pos2card.get ⟨pile.toNat, hpile⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩ := by
  have hc64 : c.toNat < 64 := real_lt64 hcreal
  have hp64 : (cardPile g c).toNat < 10 := hwf.pile_lt c hcreal
  have hge := isFree_to_cardDepth_ge g q hwf c hc64 hp64 hfree
  by_cases hcp : (cardPile g c).toNat = pile.toNat
  · have hidxeq : (⟨(cardPile g c).toNat, hp64⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ := Fin.ext hcp
    have hqEq : q.pileDepth[(cardPile g c).toNat]'hp64 =
        q.pileDepth.get ⟨pile.toNat, hpile⟩ := congrArg q.pileDepth.get hidxeq
    have hpEq : p.pileDepth[(cardPile g c).toNat]'hp64 =
        p.pileDepth.get ⟨pile.toNat, hpile⟩ := congrArg p.pileDepth.get hidxeq
    rw [hqEq, hqdSelf] at hge
    have hsub : ((p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1).toNat =
        (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
      apply UInt8.toNat_sub_of_le
      rw [UInt8.le_iff_toNat_le]
      show (1 : UInt8).toNat ≤ _
      simp only [show (1 : UInt8).toNat = 1 from rfl]
      omega
    rw [hsub] at hge
    by_cases hfull : (cardDepth g c).toNat ≥ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat
    · exact Or.inl (isFree_of_cardDepth_ge g p hwf c hc64 hp64 (by rw [hpEq]; exact hfull))
    · right
      have hcd : (cardDepth g c).toNat = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
        omega
      have hcd5 : (cardDepth g c).toNat < 5 := by omega
      have hrt := hwf.round_trip c hcreal hcd5
      have hi1 : (⟨(cardPile g c).toNat, hwf.pile_lt c hcreal⟩ : Fin 10) =
          ⟨pile.toNat, hpile⟩ := Fin.ext hcp
      have hi2 : (⟨(cardDepth g c).toNat, hcd5⟩ : Fin 5) =
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩ := Fin.ext hcd
      rw [hi1, hi2] at hrt
      exact hrt.symm
  · left
    have hqEq : q.pileDepth[(cardPile g c).toNat]'hp64 =
        p.pileDepth[(cardPile g c).toNat]'hp64 := hqdNe ⟨(cardPile g c).toNat, hp64⟩ hcp
    rw [hqEq] at hge
    exact isFree_of_cardDepth_ge g p hwf c hc64 hp64 hge

/-- `pile`'s own boundary card *is* free at the composed point: its original
    depth `depth − 1` now matches the pile's (decremented) live depth. -/
private theorem dest_B_free (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hqdSelf : q.pileDepth.get ⟨pile.toNat, hpile⟩ = (p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1) :
    isFreeCard g q ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩) := by
  set B := (g.pos2card.get ⟨pile.toNat, hpile⟩).get
    (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩ : Fin 5) with hBdef
  have hreal : IsRealCard B := hwf.pos2card_real _ _
  have hc64 : B.toNat < 64 := real_lt64 hreal
  obtain ⟨hcpB, hcdB⟩ := hwf.round_trip_inv (⟨pile.toNat, hpile⟩ : Fin 10)
    (⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩ : Fin 5)
  have hp64 : (cardPile g B).toNat < 10 := by rw [hcpB]; exact hpile
  apply isFree_of_cardDepth_ge g q hwf B hc64 hp64
  have hidxeq : (⟨(cardPile g B).toNat, hp64⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ := Fin.ext hcpB
  have hqEq : q.pileDepth[(cardPile g B).toNat]'hp64 =
      q.pileDepth.get ⟨pile.toNat, hpile⟩ := congrArg q.pileDepth.get hidxeq
  rw [hqEq, hqdSelf]
  have hsub : ((p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1).toNat =
      (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
    apply UInt8.toNat_sub_of_le
    rw [UInt8.le_iff_toNat_le]
    show (1 : UInt8).toNat ≤ _
    simp only [show (1 : UInt8).toNat = 1 from rfl]
    omega
  rw [hsub, hcdB]

/-- Invariant-free twin of `depth_card_not_free`: a card still physically
    resident in its own pile is not free.  (Only `WellFormedLayout` is needed —
    the tower hypothesis of `depth_card_not_free` is unused there too, but its
    statement fixes the position, which is exactly what we cannot supply while
    still *building* the invariant for the post-move state.) -/
private theorem slot_not_free {g : Globals} {q : SolverPosType} (hwf : WellFormedLayout g)
    (i : Fin 10) (d : Fin 5) (hd : d.val < (q.pileDepth.get i).toNat) :
    ¬ isFreeCard g q ((g.pos2card.get i).get d) := by
  intro hfree
  set c := (g.pos2card.get i).get d with hcdef
  have hreal : IsRealCard c := hwf.pos2card_real i d
  have hc64 : c.toNat < 64 := real_lt64 hreal
  obtain ⟨hcp, hcd⟩ := hwf.round_trip_inv i d
  have hp64 : (cardPile g c).toNat < 10 := by rw [hcp]; exact i.isLt
  have hge := isFree_to_cardDepth_ge g q hwf c hc64 hp64 hfree
  have hidxeq : (⟨(cardPile g c).toNat, hp64⟩ : Fin 10) = i := Fin.ext hcp
  have hqEq : q.pileDepth[(cardPile g c).toNat]'hp64 = q.pileDepth.get i :=
    congrArg q.pileDepth.get hidxeq
  rw [hqEq, hcd] at hge
  omega

/-- `(B + k).toNat = B.toNat + k` for a real card `B` and a small offset. -/
private theorem card_add_toNat {B : UInt8} (hB : B.toNat ≤ 61) {k : Nat} (hk : k ≤ 13) :
    (B + UInt8.ofNat k).toNat = B.toNat + k := by
  have hkof : (UInt8.ofNat k).toNat = k := by rw [UInt8.toNat_ofNat']; omega
  rw [UInt8.toNat_add, hkof]
  omega

/-- Numeric range of a real card. -/
private theorem real_range {B : UInt8} (h : IsRealCard B) :
    1 ≤ B.toNat ∧ B.toNat ≤ 61 ∧ B.toNat = 16 * (SUIT B).toNat + (VALUE B).toNat := by
  have h1 := h.1
  have h2 := h.2.1
  have h3 := h.2.2
  have h4 := SUIT_toNat B
  have h5 := VALUE_toNat B
  omega

/-- **Shape of a pile whose flute sits directly on top of `B`.**  If a pile's
    boundary is `Bj` with flute length `fl` and its flute predecessor
    `Bj - fl` is exactly `B`, then `Bj` sits `fl` above `B` in the same suit —
    the arithmetic core shared by the pile-to-pile/extra
    (`dest_prevCard_forces`) and king-pile (`dest_prevCard_ne_king`) exclusion
    arguments. -/
private theorem dest_prev_arith (Bj B fl : UInt8)
    (hflv : fl.toNat ≤ (VALUE Bj).toNat) (hprev : Bj - fl = B) :
    Bj.toNat = B.toNat + fl.toNat ∧ SUIT Bj = SUIT B ∧
    (VALUE Bj).toNat = (VALUE B).toNat + fl.toNat := by
  have hVBj := VALUE_toNat Bj
  have hfleBj : fl ≤ Bj := by
    rw [UInt8.le_iff_toNat_le]
    have := Nat.mod_le Bj.toNat 16
    omega
  have hsub : (Bj - fl).toNat = Bj.toNat - fl.toNat := UInt8.toNat_sub_of_le _ _ hfleBj
  rw [hprev] at hsub
  refine ⟨by omega, ?_, ?_⟩
  · apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat]
    omega
  · rw [VALUE_toNat, VALUE_toNat]
    omega

/-- **The pile whose flute sits on `B` must be the one holding the walk's
    stopping card `B + n`.**  Given the walk data (`B+1 … B+n−1` free, `B+n`
    not free), a pile `j` whose flute predecessor is `B` necessarily has
    `pileFlute[j] = n` and boundary exactly `B + n`: a shorter flute would make
    `j`'s own boundary one of the (free) walked cards, and a longer one would
    make `B + n` one of `j`'s (free) flute interiors. -/
private theorem dest_prevCard_forces (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (B : UInt8) (hBreal : IsRealCard B) (n : Nat) (hn1 : 1 ≤ n)
    (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n))
    (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidx : (p.pileDepth.get j).toNat - 1 < 5) (Bj : UInt8)
    (hBjeq : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ = Bj)
    (hprev : Bj - p.pileFlute.get j = B) :
    (p.pileFlute.get j).toNat = n ∧ Bj = B + UInt8.ofNat n := by
  have hBjreal : IsRealCard Bj := by rw [← hBjeq]; exact hwf.pos2card_real j _
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE Bj).toNat := by
    rw [← hBjeq]; exact hbase.flute_le_value hwf j hdj
  obtain ⟨hBjnat, _, hVBj⟩ := dest_prev_arith Bj B (p.pileFlute.get j) hflv hprev
  obtain ⟨hB1, hB61, _⟩ := real_range hBreal
  have hfl1 : 1 ≤ (p.pileFlute.get j).toNat := hbase.flute_pos j
  have hfl13 : (p.pileFlute.get j).toNat ≤ 13 := by have := hBjreal.2.2; omega
  have hidxlt : (p.pileDepth.get j).toNat - 1 < (p.pileDepth.get j).toNat := by omega
  have hBjnotfree : ¬ isFreeCard g p Bj := by
    rw [← hBjeq]
    exact slot_not_free hwf j ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ hidxlt
  rcases Nat.lt_trichotomy (p.pileFlute.get j).toNat n with hlt | heq | hgt
  · exfalso
    have hfree := hwalk (p.pileFlute.get j).toNat hfl1 hlt
    have hcard : B + UInt8.ofNat (p.pileFlute.get j).toNat = Bj := by
      apply UInt8.toNat_inj.mp
      rw [card_add_toNat hB61 hfl13]
      omega
    rw [hcard] at hfree
    exact hBjnotfree hfree
  · refine ⟨heq, ?_⟩
    apply UInt8.toNat_inj.mp
    rw [card_add_toNat hB61 (by omega)]
    omega
  · exfalso
    have ho1 : 1 ≤ (p.pileFlute.get j).toNat - n := by omega
    have hoLt : (p.pileFlute.get j).toNat - n < (p.pileFlute.get j).toNat := by omega
    have hoof : (UInt8.ofNat ((p.pileFlute.get j).toNat - n)).toNat =
        (p.pileFlute.get j).toNat - n := by rw [UInt8.toNat_ofNat']; omega
    have hfree : isFreeCard g p (Bj - UInt8.ofNat ((p.pileFlute.get j).toNat - n)) := by
      rw [← hBjeq]
      exact hbase.flute_cards_free j (UInt8.ofNat ((p.pileFlute.get j).toNat - n)) hdj
        (by rw [hoof]; omega) (by rw [hoof]; exact hoLt)
    have hcard : Bj - UInt8.ofNat ((p.pileFlute.get j).toNat - n) = B + UInt8.ofNat n := by
      apply UInt8.toNat_inj.mp
      have hle : UInt8.ofNat ((p.pileFlute.get j).toNat - n) ≤ Bj := by
        rw [UInt8.le_iff_toNat_le, hoof]; omega
      rw [UInt8.toNat_sub_of_le _ _ hle, hoof, card_add_toNat hB61 (by omega)]
      omega
    rw [hcard] at hfree
    exact hstop hfree

/-- **King-pile counterpart of `dest_prevCard_forces`.**  When `B` is the suit's
    king frontier, NO pile's flute can sit directly on top of it: such a pile's
    boundary would be a same-suit card strictly above `kings[s]`, hence free by
    `king_frontier`, contradicting that a pile's boundary is never free. -/
private theorem dest_prevCard_ne_king (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (B : UInt8) (s : Fin 4) (hs : s.val = (SUIT B).toNat)
    (hkB : p.kings.get s = B)
    (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidx : (p.pileDepth.get j).toNat - 1 < 5) (Bj : UInt8)
    (hBjeq : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ = Bj)
    (hprev : Bj - p.pileFlute.get j = B) :
    False := by
  have hBjreal : IsRealCard Bj := by rw [← hBjeq]; exact hwf.pos2card_real j _
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE Bj).toNat := by
    rw [← hBjeq]; exact hbase.flute_le_value hwf j hdj
  obtain ⟨_, hSBj, hVBj⟩ := dest_prev_arith Bj B (p.pileFlute.get j) hflv hprev
  have hfl1 : 1 ≤ (p.pileFlute.get j).toNat := hbase.flute_pos j
  have hsuitU8 : (s.val.toUInt8).toNat = s.val := by
    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
  have hSBjeq : SUIT Bj = s.val.toUInt8 := by
    apply UInt8.toNat_inj.mp
    rw [hSBj, hsuitU8, hs]
  have hfree := (hbase.king_frontier s).2 Bj hSBjeq (by rw [hkB]; omega) hBjreal.2.2
  rw [← hBjeq] at hfree
  have hidxlt : (p.pileDepth.get j).toNat - 1 < (p.pileDepth.get j).toNat := by omega
  exact slot_not_free hwf j ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ hidxlt hfree

/-- **Frame conditions the composed destination step satisfies in all three
    branches.**  `moveDestPre` touches only `pileFlute[toPile]` / `kings` /
    `usedSpace`; `removeFlutePre` then decrements `pileDepth[pile]` (and the
    hash), and `fluteNorm` normalizes `pileFlute[pile]` to `1`.  So *every*
    branch leaves `aces`/`busyAces` alone, drops `pileDepth[pile]` by exactly
    one, keeps all other depths, and sets `pileFlute[pile] := 1`. -/
private structure DestFrame (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) : Prop where
  depthSelf : q.pileDepth.get ⟨pile.toNat, hpile⟩ = (p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1
  depthNe : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileDepth.get j = p.pileDepth.get j
  aces : q.aces = p.aces
  busyAces : q.busyAces = p.busyAces
  fluteSelf : q.pileFlute.get ⟨pile.toNat, hpile⟩ = 1

/-- Depths only ever go down, so freeness only ever goes up. -/
private theorem destFrame_depth_le {g : Globals} {p q : SolverPosType} {pile : UInt32}
    {hpile : pile.toNat < 10}
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfr : DestFrame g p q pile hpile) :
    ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ (p.pileDepth.get i).toNat := by
  intro i
  by_cases hi : i.val = pile.toNat
  · have hii : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hi
    subst hii
    rw [hfr.depthSelf]
    have hsub : ((p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1).toNat =
        (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
      apply UInt8.toNat_sub_of_le
      rw [UInt8.le_iff_toNat_le]
      show (1 : UInt8).toNat ≤ _
      simp only [show (1 : UInt8).toNat = 1 from rfl]
      omega
    omega
  · rw [hfr.depthNe i hi]

/-- Every card free before the destination step is still free after. -/
private theorem destFrame_free_mono {g : Globals} {p q : SolverPosType} {pile : UInt32}
    {hpile : pile.toNat < 10}
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfr : DestFrame g p q pile hpile) {c : UInt8} (h : isFreeCard g p c) :
    isFreeCard g q c :=
  isFreeCard_mono (destFrame_depth_le hd1 hfr) h

/-- **`PileBase` holds for `pile` itself at the composed point.**  Its flute is
    the trivial `1` (`fluteNorm`), so only `flute_not_aces` needs an argument:
    the pile's NEW boundary is still physically resident (depth `d−1` > its own
    slot `d−2`), hence not free, hence not covered by the foundation. -/
private theorem destFrame_pileBase_self (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfr : DestFrame g p q pile hpile) :
    PileBase g q ⟨pile.toNat, hpile⟩ := by
  have hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5 :=
    hbase.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hsub : ((p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1).toNat =
      (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by
    apply UInt8.toNat_sub_of_le
    rw [UInt8.le_iff_toNat_le]
    show (1 : UInt8).toNat ≤ _
    simp only [show (1 : UInt8).toNat = 1 from rfl]
    omega
  have hqd : (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat =
      (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 := by rw [hfr.depthSelf, hsub]
  have hqf : (q.pileFlute.get ⟨pile.toNat, hpile⟩).toNat = 1 := by
    rw [hfr.fluteSelf]; rfl
  refine ⟨by omega, UInt8.le_iff_toNat_le.mpr (Nat.zero_le _), by omega,
    fun _ => hfr.fluteSelf, fun j' _ _ hlt => absurd hlt (by omega), ?_⟩
  intro hdq
  -- `pile`'s new boundary card, still resident at slot `depth − 2`.
  set B' := (g.pos2card.get ⟨pile.toNat, hpile⟩).get
    (⟨(q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩ : Fin 5) with hB'def
  show ∀ hs : (SUIT B').toNat < 4,
    (q.aces.get ⟨(SUIT B').toNat, hs⟩).toNat + (q.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤
      B'.toNat
  intro hs
  rw [hqf, hfr.aces]
  have hB'real : IsRealCard B' := hwf.pos2card_real _ _
  have hidxq : (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5 := by omega
  have hB'notfree : ¬ isFreeCard g q B' := by
    rw [hB'def]
    exact slot_not_free hwf ⟨pile.toNat, hpile⟩
      ⟨(q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidxq⟩
      (show (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 <
        (q.pileDepth.get ⟨pile.toNat, hpile⟩).toNat by omega)
  by_contra hcon
  push Not at hcon
  -- `aces[s] ≥ B'` in the same suit would make `B'` a foundation card, hence free.
  have hAsuit : SUIT (p.aces.get ⟨(SUIT B').toNat, hs⟩) = ((SUIT B').toNat).toUInt8 :=
    (hbase.aces_kings_valid ⟨(SUIT B').toNat, hs⟩).1
  have hAsuitNat : (SUIT (p.aces.get ⟨(SUIT B').toNat, hs⟩)).toNat = (SUIT B').toNat := by
    rw [hAsuit, UInt8.toNat_ofNat']; omega
  have hAv := VALUE_toNat (p.aces.get ⟨(SUIT B').toNat, hs⟩)
  have hAs := SUIT_toNat (p.aces.get ⟨(SUIT B').toNat, hs⟩)
  obtain ⟨hB'1, hB'61, hB'dec⟩ := real_range hB'real
  have hVle : (VALUE B').toNat ≤ (VALUE (p.aces.get ⟨(SUIT B').toNat, hs⟩)).toNat := by omega
  have hsuitEq : SUIT B' = ((⟨(SUIT B').toNat, hs⟩ : Fin 4).val).toUInt8 := by
    show SUIT B' = ((SUIT B').toNat).toUInt8
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  exact hB'notfree (destFrame_free_mono hd1 hfr
    (hbase.foundation_cards_free ⟨(SUIT B').toNat, hs⟩ B' hsuitEq hB'real.2.1 hVle))

/-- **`PileBase` transfers to every pile whose depth AND flute are untouched.**
    Everything but `flute_cards_free` is a literal rewrite; freeness only grows
    (`destFrame_free_mono`). -/
private theorem destFrame_pileBase_ne (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfr : DestFrame g p q pile hpile)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hfl : q.pileFlute.get j = p.pileFlute.get j)
    (hb : PileBase g p j) :
    PileBase g q j := by
  have hdeq := hfr.depthNe j hj
  refine ⟨by rw [hdeq]; exact hb.pileDepth_bound, by rw [hdeq]; exact hb.pileDepth_nonneg,
    by rw [hfl]; exact hb.flute_pos, by rw [hdeq, hfl]; exact hb.flute_empty, ?_, ?_⟩
  · intro j' hd0 h1 h2
    simp only [hdeq] at hd0
    simp only [hfl] at h2
    have h3 := destFrame_free_mono hd1 hfr (hb.flute_cards_free j' hd0 h1 h2)
    simp only [hdeq]
    exact h3
  · intro hd0
    simp only [hdeq] at hd0
    simp only [hdeq, hfl, hfr.aces]
    exact hb.flute_not_aces hd0

/-- **`PileMerged` transfers to every pile whose depth AND flute are untouched,
    provided its flute predecessor is not the one card the step frees.**
    `merge_complete`/`busyAces_complete` are literal rewrites; `flute_maximal`'s
    `¬isFreeCard` disjunct is where `hprevNe` is needed — via `dest_free_char`,
    the ONLY card that changes freeness is `pile`'s own boundary `B`. -/
private theorem destFrame_pileMerged_ne (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (j : Fin 10) (hj : j.val ≠ pile.toNat)
    (hfl : q.pileFlute.get j = p.pileFlute.get j)
    (hb : PileBase g p j) (hpm : PileMerged g p j hb.pileDepth_bound)
    (hprevNe : 0 < (p.pileDepth.get j).toNat → ∀ hidx : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ - p.pileFlute.get j ≠
        (g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, by omega⟩) :
    PileMerged g q j (by rw [hfr.depthNe j hj]; exact hb.pileDepth_bound) := by
  have hdeq := hfr.depthNe j hj
  have hak : ∀ s : Fin 4, SUIT (p.aces.get s) = s.val.toUInt8 :=
    fun s => (hbase.aces_kings_valid s).1
  refine ⟨?_, ?_, ?_⟩
  · simp only [hdeq]
    exact hpm.merge_complete
  · by_cases hd0 : p.pileDepth.get j = 0
    · left; rw [hdeq]; exact hd0
    · have hdj : (p.pileDepth.get j).toNat > 0 := by
        have h2 : (p.pileDepth.get j).toNat ≠ 0 := fun hz => hd0 (UInt8.toNat_inj.mp hz)
        omega
      have hidx5 : (p.pileDepth.get j).toNat - 1 < 5 := by
        have := hb.pileDepth_bound; omega
      right
      simp only [hdeq, hfl, hfr.aces]
      set boundary := (g.pos2card.get j).get
        (⟨(p.pileDepth.get j).toNat - 1, hidx5⟩ : Fin 5) with hbdef
      set prevCard := boundary - p.pileFlute.get j with hprevdef
      have hrealBd : IsRealCard boundary := hwf.pos2card_real j _
      have hs4' : (SUIT boundary).toNat < 4 := hrealBd.1
      have hflv : (p.pileFlute.get j).toNat ≤ (VALUE boundary).toNat :=
        hb.flute_le_value hwf hak hdj
      have hfleB : p.pileFlute.get j ≤ boundary := by
        rw [UInt8.le_iff_toNat_le]
        have := Nat.mod_le boundary.toNat 16
        have := VALUE_toNat boundary
        omega
      have hprevNat : prevCard.toNat = boundary.toNat - (p.pileFlute.get j).toNat :=
        UInt8.toNat_sub_of_le _ _ hfleB
      have hSUITeq : SUIT prevCard = SUIT boundary := by
        apply UInt8.toNat_inj.mp
        rw [SUIT_toNat, SUIT_toNat, hprevNat]
        have := VALUE_toNat boundary
        omega
      have hVALeq : (VALUE prevCard).toNat =
          (VALUE boundary).toNat - (p.pileFlute.get j).toNat := by
        rw [VALUE_toNat, hprevNat]
        have := VALUE_toNat boundary
        omega
      have hsuiteq : SUIT boundary = (⟨(SUIT boundary).toNat, hs4'⟩ : Fin 4).val.toUInt8 := by
        show SUIT boundary = ((SUIT boundary).toNat).toUInt8
        apply UInt8.toNat_inj.mp
        rw [UInt8.toNat_ofNat']
        omega
      show (∃ hs : (SUIT boundary).toNat < 4,
          p.aces.get ⟨(SUIT boundary).toNat, hs⟩ = prevCard) ∨ ¬ isFreeCard g q prevCard
      rcases hpm.flute_maximal.resolve_left hd0 with hOldA | hOldNF
      · exact Or.inl hOldA
      · by_cases hV0 : (VALUE prevCard).toNat = 0
        · -- The suit's zero-value sentinel: `flute_not_aces`'s upper bound plus
          -- the suit-block lower bound pin `aces = prevCard` exactly.
          left
          refine ⟨hs4', ?_⟩
          have hSuitAcesEq : SUIT ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩)) =
              SUIT boundary := by
            rw [hak ⟨(SUIT boundary).toNat, hs4'⟩, ← hsuiteq]
          have hVBnat := VALUE_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSBnat := SUIT_toNat ((p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩))
          have hSeq := congrArg UInt8.toNat hSuitAcesEq
          have hbound2 : (p.aces.get ⟨(SUIT boundary).toNat, hs4'⟩).toNat +
              (p.pileFlute.get j).toNat ≤ boundary.toNat := hb.flute_not_aces hdj hs4'
          have hVprev := VALUE_toNat prevCard
          have hSprev := congrArg UInt8.toNat hSUITeq
          have hSprevN := SUIT_toNat prevCard
          apply UInt8.toNat_inj.mp
          omega
        · right
          have hVle : (VALUE prevCard).toNat ≤ 13 := by
            have := hrealBd.2.2; omega
          have hCrealPrev : IsRealCard prevCard := ⟨hSUITeq ▸ hs4', by omega, hVle⟩
          intro hfreeQ
          rcases dest_free_char g p q pile hpile hwf hd1 hd5 hfr.depthSelf hfr.depthNe
            prevCard hCrealPrev hfreeQ with hfp | hpB
          · exact hOldNF hfp
          · exact hprevNe hdj hidx5 hpB
  · intro hdq
    simp only [hdeq] at hdq
    simp only [hdeq, hfl, hfr.aces, hfr.busyAces]
    exact hpm.busyAces_complete hdq

/-- **`hash_def` at the composed point.**  The hash is the `pileHashes` dot
    product of the depths, and `removeFlutePre` subtracts exactly `pile`'s own
    coefficient while dropping `pile`'s depth by one (`hash_foldl_set`). -/
private theorem destFrame_hash_def (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hbase : SolverInvBase g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hqhash : q.hash = p.hash - (pileHashes[pile.toNat]'hpile))
    (hqdepth : q.pileDepth = p.pileDepth.set pile.toNat
      ((p.pileDepth[pile.toNat]'hpile) - 1) hpile) :
    q.hash = (List.finRange 10).foldl
      (fun acc i => acc + pileHashes.get i * (q.pileDepth.get i).toNat.toUInt32) 0 := by
  set a := pileHashes[pile.toNat]'hpile with hadef
  set d := p.pileDepth[pile.toNat]'hpile with hddef
  have hd1' : 1 ≤ d.toNat := hd1
  have hsub : (d - 1).toNat = d.toNat - 1 := by
    apply UInt8.toNat_sub_of_le
    rw [UInt8.le_iff_toNat_le]
    show (1 : UInt8).toNat ≤ _
    simp only [show (1 : UInt8).toNat = 1 from rfl]
    exact hd1'
  have hd256 : d.toNat < 256 := d.toNat_lt_size
  -- The two depth casts differ by exactly one, as `UInt32`s.
  have huv : d.toNat.toUInt32 = (d - 1).toNat.toUInt32 + 1 := by
    apply UInt32.toNat_inj.mp
    have h1 : (d.toNat.toUInt32).toNat = d.toNat := by rw [UInt32.toNat_ofNat']; omega
    have h2 : ((d - 1).toNat.toUInt32).toNat = d.toNat - 1 := by
      rw [UInt32.toNat_ofNat', hsub]; omega
    rw [h1, UInt32.toNat_add, h2, show (1 : UInt32).toNat = 1 from rfl]
    omega
  have hkey := hash_foldl_set p.pileDepth pile.toNat hpile (d - 1)
  -- `x.toNat` and `x.toNat` agree definitionally on `UInt8`.
  have hkey' : (List.finRange 10).foldl
        (fun acc i => acc + pileHashes.get i *
          ((p.pileDepth.set pile.toNat (d - 1) hpile).get i).toNat.toUInt32) 0
        + a * (d.toNat.toUInt32) =
      (List.finRange 10).foldl
        (fun acc i => acc + pileHashes.get i * (p.pileDepth.get i).toNat.toUInt32) 0
        + a * ((d - 1).toNat.toUInt32) := hkey
  rw [← hbase.hash_def] at hkey'
  rw [huv, UInt32.mul_add, UInt32.mul_one, ← UInt32.add_assoc] at hkey'
  rw [hqdepth, hqhash]
  set G := (List.finRange 10).foldl
    (fun acc i => acc + pileHashes.get i *
      ((p.pileDepth.set pile.toNat (d - 1) hpile).get i).toNat.toUInt32) 0 with hGdef
  set v := (d - 1).toNat.toUInt32 with hvdef
  -- `hkey' : G + a * v + a = p.hash + a * v`
  have hF : p.hash = G + a := by
    have h3 := congrArg (· - a * v) hkey'
    rw [UInt32.add_sub_cancel,
      show G + a * v + a - a * v = G + a from by
        rw [show G + a * v + a = G + a + a * v from by ac_rfl, UInt32.add_sub_cancel]] at h3
    exact h3.symm
  rw [hF, UInt32.add_sub_cancel]

/-- The depth ledger drops by exactly one. -/
private theorem destFrame_depth_sum (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hqdepth : q.pileDepth = p.pileDepth.set pile.toNat
      ((p.pileDepth[pile.toNat]'hpile) - 1) hpile) :
    (q.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0) + 1 =
      p.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 := by
  set d := p.pileDepth[pile.toNat]'hpile with hddef
  have hd1' : 1 ≤ d.toNat := hd1
  have hsub : (d - 1).toNat = d.toNat - 1 := by
    apply UInt8.toNat_sub_of_le
    rw [UInt8.le_iff_toNat_le]
    show (1 : UInt8).toNat ≤ _
    simp only [show (1 : UInt8).toNat = 1 from rfl]
    exact hd1'
  have hkey : (p.pileDepth.set pile.toNat (d - 1) hpile).toList.foldl
        (fun acc x => acc + x.toNat) 0 + d.toNat =
      p.pileDepth.toList.foldl (fun acc x => acc + x.toNat) 0 + (d - 1).toNat :=
    depth_sum_foldl_set p.pileDepth pile.toNat hpile (d - 1)
  rw [hqdepth]
  omega

/-- **`CleanupReady` from the frame conditions plus the per-pile/per-suit facts.**
    Assembles `SolverInvBase` (pile `pile`'s own `PileBase` comes from
    `destFrame_pileBase_self`, `hash_def` from `destFrame_hash_def`,
    `busyAces_lt16` from the untouched bitmask) and discharges `CleanupReady`'s
    `freePiles` count (unchanged, and `pile` itself is not yet empty). -/
private theorem destFrame_cleanupReady (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hfr : DestFrame g p q pile hpile)
    (hqhash : q.hash = p.hash - (pileHashes[pile.toNat]'hpile))
    (hqdepth : q.pileDepth = p.pileDepth.set pile.toNat
      ((p.pileDepth[pile.toNat]'hpile) - 1) hpile)
    (hqfp : q.freePiles = p.freePiles)
    (hpb : ∀ j : Fin 10, j.val ≠ pile.toNat → PileBase g q j)
    (hsc : ∀ (s : Fin 4) (hb : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ 5),
      SuitClean g q s hb)
    (hused : q.usedSpace.toInt =
      (52 : Int)
      - (q.pileDepth.toList.foldl (fun acc d => acc + d.toNat) 0 : Nat)
      - (q.aces.toList.foldl (fun acc a => acc + (VALUE a).toNat) 0 : Nat)
      - (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
          q.pileDepth.toList q.pileFlute.toList |>.foldl (· + ·) 0 : Nat))
    (hpmq : ∀ (j : Fin 10) (hj : j.val ≠ pile.toNat), PileMerged g q j (hpb j hj).pileDepth_bound) :
    CleanupReady g q pile := by
  have hbase := hmerged.toSolverInvBase
  have hpbAll : ∀ i : Fin 10, PileBase g q i := by
    intro i
    by_cases hi : i.val = pile.toNat
    · have hii : i = (⟨pile.toNat, hpile⟩ : Fin 10) := Fin.ext hi
      subst hii
      exact destFrame_pileBase_self g p q pile hpile hwf hbase hd1 hfr
    · exact hpb i hi
  have hnf : SolverInvBase g q :=
    ⟨hpbAll, fun s => hsc s (fun i => (hpbAll i).pileDepth_bound),
     destFrame_hash_def g p q pile hpile hbase hd1 hqhash hqdepth, hused,
     by rw [hfr.busyAces]; exact hbase.busyAces_lt16⟩
  refine ⟨hnf, fun j hj => ?_, ?_⟩
  · exact hpmq j hj
  · -- `freePiles` is untouched, and `pile` itself still has positive depth, so
    -- the `j ≠ pile`-filtered count coincides with the full count.
    rw [hqfp]
    have hframe : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileDepth.get j = p.pileDepth.get j :=
      hfr.depthNe
    rw [cleanupReady_freePiles_frame_eq pile p q hframe]
    have hsplit := cleanupReady_freePiles_split pile hpile p _ rfl
    have hne0 : ¬ (p.pileDepth.get (⟨pile.toNat, hpile⟩ : Fin 10) == 0) = true := by
      simp only [beq_iff_eq]
      intro hz
      rw [hz] at hd1
      exact absurd hd1 (by simp)
    rw [if_neg hne0] at hsplit
    rw [hmerged.freePiles_def]
    omega

/-- **`foundation_maximal_weak` survives the destination step.**  The only card
    it could break on is `pile`'s own boundary `B` becoming free — but if `B` is
    the next foundation card (`aces[s] + 1 = B`) then `flute_not_aces` forces
    `pileFlute[pile] = 1`, i.e. `aces[s] = B − pileFlute[pile]`, and pile
    `pile`'s own `busyAces_complete` has already recorded the pending
    foundation advance in `busyAces` (which the step leaves untouched). -/
private theorem dest_next_ace (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (s : Fin 4) :
    (VALUE (p.aces.get s)).toNat = 13 ∨ ¬ isFreeCard g q ((p.aces.get s) + 1) ∨
      p.busyAces &&& ((1 : UInt8) <<< s.val.toUInt8) ≠ 0 := by
  have hbase := hmerged.toSolverInvBase
  have hdpile : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat > 0 := by omega
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  by_cases h13 : (VALUE (p.aces.get s)).toNat = 13
  · exact Or.inl h13
  refine Or.inr ?_
  rcases hbase.foundation_maximal_weak s with h13' | hnfp | hbusy
  · exact absurd h13' h13
  swap
  · exact Or.inr hbusy
  by_cases hfreeQ : isFreeCard g q ((p.aces.get s) + 1)
  swap
  · exact Or.inl hfreeQ
  right
  -- `aces[s] + 1` is a real card, so `dest_free_char` applies.
  have hAsuit : SUIT (p.aces.get s) = s.val.toUInt8 := (hbase.aces_kings_valid s).1
  have hAv13 : (VALUE (p.aces.get s)).toNat ≤ 13 := (hbase.aces_kings_valid s).2.1
  have hsuitU8 : (s.val.toUInt8).toNat = s.val := by
    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
  have hAsN : (SUIT (p.aces.get s)).toNat = s.val := by rw [hAsuit, hsuitU8]
  have hAsn := SUIT_toNat (p.aces.get s)
  have hAvn := VALUE_toNat (p.aces.get s)
  have hcS : SUIT ((p.aces.get s) + 1) = s.val.toUInt8 := (SUIT_succ _ (by omega)).trans hAsuit
  have hcV : (VALUE ((p.aces.get s) + 1)).toNat = (VALUE (p.aces.get s)).toNat + 1 :=
    VALUE_succ _ (by omega)
  have hcreal : IsRealCard ((p.aces.get s) + 1) :=
    ⟨by rw [hcS, hsuitU8]; exact s.isLt, by omega, by omega⟩
  rcases dest_free_char g p q pile hpile hwf hd1 hd5 hfr.depthSelf hfr.depthNe
    ((p.aces.get s) + 1) hcreal hfreeQ with hfp | hcB
  · exact absurd hfp hnfp
  · -- `aces[s] + 1 = B`: the pending foundation advance is already recorded.
    have hcBeq : (p.aces.get s) + 1 = B := hcB.trans hBdef
    have hAnat : ((p.aces.get s) + 1).toNat = (p.aces.get s).toNat + 1 := by
      rw [UInt8.toNat_add, show (1 : UInt8).toNat = 1 from rfl]
      omega
    have hAB : (p.aces.get s).toNat + 1 = B.toNat := by rw [← hAnat, hcBeq]
    have hs4B : (SUIT B).toNat < 4 := hBreal.1
    have hSBs : (SUIT B).toNat = s.val := by rw [← hcBeq, hcS, hsuitU8]
    have hseq : s = (⟨(SUIT B).toNat, hs4B⟩ : Fin 4) := Fin.ext hSBs.symm
    have hacesIdx : p.aces.get ⟨(SUIT B).toNat, hs4B⟩ = p.aces.get s :=
      congrArg p.aces.get hseq.symm
    have hfna : (p.aces.get ⟨(SUIT B).toNat, hs4B⟩).toNat +
        (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ B.toNat := by
      have h := (hbase.pileBase ⟨pile.toNat, hpile⟩).flute_not_aces hdpile
      simp only [hBdef] at h
      exact h hs4B
    rw [hacesIdx] at hfna
    have hfl1 : 1 ≤ (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
      hbase.flute_pos ⟨pile.toNat, hpile⟩
    have hflEq : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat = 1 := by omega
    have hfleB : p.pileFlute.get ⟨pile.toNat, hpile⟩ ≤ B := by
      rw [UInt8.le_iff_toNat_le]; omega
    have hacesEq : p.aces.get s = B - p.pileFlute.get ⟨pile.toNat, hpile⟩ := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_sub_of_le _ _ hfleB]
      omega
    have hbc : p.busyAces &&& ((1 : UInt8) <<< SUIT B) ≠ 0 := by
      have h := (hmerged.pileMerged ⟨pile.toNat, hpile⟩).busyAces_complete hdpile
      simp only [hBdef] at h
      exact h hs4B (by rw [hacesIdx]; exact hacesEq)
    have hshift : (1 : UInt8) <<< s.val.toUInt8 = (1 : UInt8) <<< SUIT B := by
      congr 1
      apply UInt8.toNat_inj.mp
      rw [hsuitU8, hSBs]
    rw [hshift]
    exact hbc

/-- Suit/value arithmetic for a card offset *upward inside its own suit block*
    (the walk cards `B + k`). -/
private theorem card_add_suit_value {B : UInt8} (hB : IsRealCard B) {k : Nat}
    (hk : (VALUE B).toNat + k ≤ 13) :
    (B + UInt8.ofNat k).toNat = B.toNat + k ∧ SUIT (B + UInt8.ofNat k) = SUIT B ∧
      (VALUE (B + UInt8.ofNat k)).toNat = (VALUE B).toNat + k := by
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hB
  have hV := VALUE_toNat B
  have hnat : (B + UInt8.ofNat k).toNat = B.toNat + k := card_add_toNat hB61 (by omega)
  refine ⟨hnat, ?_, ?_⟩
  · apply UInt8.toNat_inj.mp
    rw [SUIT_toNat, SUIT_toNat, hnat]
    omega
  · rw [VALUE_toNat, hnat]
    omega

/-- **In the two walk branches no suit's king frontier is `pile`'s boundary
    `B`.**  `kings[s] = B` forces `s = SUIT B` (both have suit `s`), and then
    `king_frontier`'s second clause makes *every* higher card of the suit free —
    including the walk's stopping card `B + n`, which by assumption is not. -/
private theorem dest_kings_ne (g : Globals) (p : SolverPosType) (hbase : SolverInvBase g p)
    (B : UInt8) (hBreal : IsRealCard B) (n : Nat) (hn1 : 1 ≤ n)
    (hnval : (VALUE B).toNat + n ≤ 13)
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n)) (s : Fin 4) :
    p.kings.get s ≠ B := by
  intro heq
  obtain ⟨_, _, hKs, _, _⟩ := hbase.aces_kings_valid s
  obtain ⟨_, hSeq, hVeq⟩ := card_add_suit_value hBreal hnval
  have hsuitU8 : (s.val.toUInt8).toNat = s.val := by
    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
  have hSB : SUIT B = s.val.toUInt8 := by rw [← heq]; exact hKs
  exact hstop ((hbase.king_frontier s).2 (B + UInt8.ofNat n) (by rw [hSeq, hSB])
    (by rw [hVeq, heq]; omega) (by omega))

/-- **`SuitClean` transfers for every suit whose `kings` entry the step leaves
    alone**, as long as that entry isn't the one card the step frees.
    `aces`/`busyAces` are untouched (`DestFrame`) and freeness only grows
    (`destFrame_free_mono`), so `aces_kings_valid`/`foundation_cards_free` and
    `king_frontier`'s "everything above the frontier is free" clause are literal
    rewrites; `foundation_maximal_weak` is `dest_next_ace`; and
    `king_frontier`'s "frontier itself not free" disjunct is exactly where
    `hkne` is needed (via `dest_free_char`). -/
private theorem destFrame_suitClean (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (s : Fin 4) (hks : q.kings.get s = p.kings.get s) (hkne : p.kings.get s ≠ B)
    (hb : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ 5) :
    SuitClean g q s hb := by
  have hbase := hmerged.toSolverInvBase
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr.aces, hks]; exact hbase.aces_kings_valid s
  · intro c h1 h2 h3
    rw [hfr.aces] at h3
    exact destFrame_free_mono hd1 hfr (hbase.foundation_cards_free s c h1 h2 h3)
  · rw [hfr.aces, hfr.busyAces]
    exact dest_next_ace g p q pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s
  · rw [hks, hfr.aces, hfr.busyAces]
    rcases (hbase.king_frontier s).1 with hl | ⟨hlt, hnfp⟩
    · exact Or.inl hl
    · refine Or.inr ⟨hlt, ?_⟩
      -- `kings[s]` is a real card here: strictly above `aces[s]` in the same
      -- suit, so its value is at least 1.
      obtain ⟨hSa, hVa, hSk, hVk, _⟩ := hbase.aces_kings_valid s
      have hsuitU8 : (s.val.toUInt8).toNat = s.val := by
        rw [UInt8.toNat_ofNat']; have := s.isLt; omega
      have hSaN : (SUIT (p.aces.get s)).toNat = s.val := by rw [hSa, hsuitU8]
      have hSkN : (SUIT (p.kings.get s)).toNat = s.val := by rw [hSk, hsuitU8]
      have hAd := SUIT_toNat (p.aces.get s)
      have hAv := VALUE_toNat (p.aces.get s)
      have hKd := SUIT_toNat (p.kings.get s)
      have hKv := VALUE_toNat (p.kings.get s)
      have hltN : (p.aces.get s).toNat < (p.kings.get s).toNat := by
        rw [UInt8.lt_iff_toNat_lt] at hlt; exact hlt
      have hKreal : IsRealCard (p.kings.get s) := ⟨by omega, by omega, by omega⟩
      intro hfreeQ
      rcases dest_free_char g p q pile hpile hwf hd1 hd5 hfr.depthSelf hfr.depthNe
        (p.kings.get s) hKreal hfreeQ with hfp | hcB
      · exact hnfp hfp
      · exact hkne (hcB.trans hBdef)
  · intro c h1 h2 h3
    rw [hks] at h2
    exact destFrame_free_mono hd1 hfr ((hbase.king_frontier s).2 c h1 h2 h3)

/-- **`SuitClean` for the king branch's own suit.**  The step lowers `kings[s]`
    from `B` (the suit's old king frontier, which is `pile`'s boundary here) to
    `B − pileFlute[pile]`: the whole flute has joined the suit's king pile.
    `aces_kings_valid`'s `aces[s] ≤ kings[s]` is `pile`'s own `flute_not_aces`;
    `king_frontier`'s first clause splits on whether the foundation has already
    caught up with the new frontier (`busyAces_complete` / `flute_maximal`); and
    its second clause gains exactly the flute cards `B, B−1, …, B−fl+1`, which
    are `dest_B_free` and `flute_cards_free` respectively. -/
private theorem destKing_suitClean (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (s : Fin 4) (hs : s.val = (SUIT B).toNat) (hkB : p.kings.get s = B)
    (hks : q.kings.get s = B - p.pileFlute.get ⟨pile.toNat, hpile⟩)
    (hb : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ 5) :
    SuitClean g q s hb := by
  have hbase := hmerged.toSolverInvBase
  have hdpile : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat > 0 := by omega
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  have hs4B : (SUIT B).toNat < 4 := hBreal.1
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hVB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hseq : s = (⟨(SUIT B).toNat, hs4B⟩ : Fin 4) := Fin.ext hs
  have hsuitU8 : (s.val.toUInt8).toNat = s.val := by
    rw [UInt8.toNat_ofNat']; have := s.isLt; omega
  have hsB : s.val.toUInt8 = SUIT B := UInt8.toNat_inj.mp (by rw [hsuitU8, hs])
  -- Flute bounds and the arithmetic of the new frontier `B − fl`.
  have hflv : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (VALUE B).toNat := by
    have h := hbase.flute_le_value hwf ⟨pile.toNat, hpile⟩ hdpile
    simp only [hBdef] at h; exact h
  have hfl1 : 1 ≤ (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    hbase.flute_pos ⟨pile.toNat, hpile⟩
  have hVB := VALUE_toNat B
  have hSBn := SUIT_toNat B
  have hfleB : p.pileFlute.get ⟨pile.toNat, hpile⟩ ≤ B := by
    rw [UInt8.le_iff_toNat_le]; omega
  have hsubNat : (B - p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat =
      B.toNat - (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    UInt8.toNat_sub_of_le _ _ hfleB
  have hSsub : (SUIT (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat = (SUIT B).toNat := by
    rw [SUIT_toNat, hsubNat]; omega
  have hVsub : (VALUE (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat =
      (VALUE B).toNat - (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat := by
    rw [VALUE_toNat, hsubNat]; omega
  -- `aces[s] + fl ≤ B` — `pile`'s own `flute_not_aces`.
  have hfna : (p.aces.get s).toNat + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ B.toNat := by
    have h := (hbase.pileBase ⟨pile.toNat, hpile⟩).flute_not_aces hdpile
    simp only [hBdef] at h
    have h2 := h hs4B
    rw [← hseq] at h2
    exact h2
  -- `aces[s]` sits in its own suit block.
  obtain ⟨hSa, hVa, hSk, hVk, hak⟩ := hbase.aces_kings_valid s
  have hSaN : (SUIT (p.aces.get s)).toNat = (SUIT B).toNat := by rw [hSa, hsuitU8, hs]
  have hAd := SUIT_toNat (p.aces.get s)
  have hAv := VALUE_toNat (p.aces.get s)
  -- `B` itself is free at the composed point; the interior flute cards already were.
  have hBfreeQ : isFreeCard g q B := by
    have h := dest_B_free g p q pile hpile hwf hd1 hd5 hfr.depthSelf
    simp only [hBdef] at h; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hfr.aces]; exact hSa, by rw [hfr.aces]; exact hVa, ?_, ?_, ?_⟩
    · rw [hks]; exact UInt8.toNat_inj.mp (by rw [hSsub, hsuitU8, hs])
    · rw [hks]; omega
    · rw [hks, hfr.aces, UInt8.le_iff_toNat_le]; omega
  · intro c h1 h2 h3
    rw [hfr.aces] at h3
    exact destFrame_free_mono hd1 hfr (hbase.foundation_cards_free s c h1 h2 h3)
  · rw [hfr.aces, hfr.busyAces]
    exact dest_next_ace g p q pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s
  · rw [hks, hfr.aces, hfr.busyAces]
    by_cases hAeq : p.aces.get s = B - p.pileFlute.get ⟨pile.toNat, hpile⟩
    · -- The foundation has already reached the new frontier: `busyAces_complete`
      -- at `pile` has recorded the pending advance.
      refine Or.inl ⟨hAeq.symm, Or.inr ?_⟩
      have h := (hmerged.pileMerged ⟨pile.toNat, hpile⟩).busyAces_complete hdpile
      simp only [hBdef] at h
      have h2 := h hs4B (by rw [← hseq]; exact hAeq)
      rw [hsB]; exact h2
    · refine Or.inr ⟨?_, ?_⟩
      · rw [UInt8.lt_iff_toNat_lt]
        have hne : (p.aces.get s).toNat ≠
            (B - p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat := fun hz =>
          hAeq (UInt8.toNat_inj.mp hz)
        omega
      · -- `B − fl` is `pile`'s own `prevCard`, and `flute_maximal` says it is not
        -- free (the `aces` disjunct is exactly `hAeq`).
        have hVpos : 1 ≤ (VALUE (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat := by
          by_contra hz
          exact hAeq (UInt8.toNat_inj.mp (by omega))
        have hreal : IsRealCard (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) :=
          ⟨by omega, hVpos, by omega⟩
        have hd0 : p.pileDepth.get ⟨pile.toNat, hpile⟩ ≠ 0 := by
          intro hz; rw [hz] at hdpile; exact absurd hdpile (by simp)
        have hfm := (hmerged.pileMerged ⟨pile.toNat, hpile⟩).flute_maximal.resolve_left hd0
        simp only [hBdef] at hfm
        have hnfp : ¬ isFreeCard g p (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) := by
          rcases hfm with ⟨hs', hA'⟩ | hnf
          · exact absurd (by rw [hseq]; exact hA') hAeq
          · exact hnf
        intro hfreeQ
        rcases dest_free_char g p q pile hpile hwf hd1 hd5 hfr.depthSelf hfr.depthNe
          (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) hreal hfreeQ with hfp | hcB
        · exact hnfp hfp
        · rw [hBdef] at hcB
          have := congrArg UInt8.toNat hcB
          omega
  · -- Above the new frontier: old frontier cards (free in `p`) plus the flute.
    intro c h1 h2 h3
    rw [hks, hVsub] at h2
    have hSc : (SUIT c).toNat = (SUIT B).toNat := by rw [h1, hsuitU8, hs]
    have hScN := SUIT_toNat c
    have hVcN := VALUE_toNat c
    by_cases hcv : (VALUE B).toNat < (VALUE c).toNat
    · refine destFrame_free_mono hd1 hfr ((hbase.king_frontier s).2 c h1 ?_ h3)
      rw [hkB]; omega
    · -- `c = B − k` with `0 ≤ k < fl`.
      have hck : c.toNat = B.toNat - ((VALUE B).toNat - (VALUE c).toNat) := by omega
      by_cases hk0 : (VALUE c).toNat = (VALUE B).toNat
      · have hcB : c = B := UInt8.toNat_inj.mp (by omega)
        rw [hcB]; exact hBfreeQ
      · have hkof : (UInt8.ofNat ((VALUE B).toNat - (VALUE c).toNat)).toNat =
            (VALUE B).toNat - (VALUE c).toNat := by
          rw [UInt8.toNat_ofNat']; omega
        have hkle : UInt8.ofNat ((VALUE B).toNat - (VALUE c).toNat) ≤ B := by
          rw [UInt8.le_iff_toNat_le, hkof]; omega
        have hcard : B - UInt8.ofNat ((VALUE B).toNat - (VALUE c).toNat) = c := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hkle, hkof]
          omega
        have hfree := hbase.flute_cards_free ⟨pile.toNat, hpile⟩
          (UInt8.ofNat ((VALUE B).toNat - (VALUE c).toNat)) hdpile
          (by rw [hkof]; omega) (by rw [hkof]; omega)
        simp only [hBdef, hcard] at hfree
        exact destFrame_free_mono hd1 hfr hfree

/-- **`pile`'s own `prevCard` still satisfies `flute_maximal`'s disjunction at
    the composed point.**  `B − fl` is the card `flute_maximal` talks about for
    `pile`, and it is never the one card the step frees (`B` itself, since
    `fl ≥ 1`), so `dest_free_char` carries the `¬isFreeCard` disjunct across.
    The degenerate `VALUE (B − fl) = 0` case (where `B − fl` isn't a real card,
    so `dest_free_char` doesn't apply) is pinned to the `aces` disjunct by
    `flute_not_aces` plus the suit-block lower bound on `aces[s]`. -/
private theorem dest_prevCard_maximal (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B) :
    (∃ hs : (SUIT B).toNat < 4,
        p.aces.get ⟨(SUIT B).toNat, hs⟩ = B - p.pileFlute.get ⟨pile.toNat, hpile⟩) ∨
      ¬ isFreeCard g q (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) := by
  have hbase := hmerged.toSolverInvBase
  have hdpile : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat > 0 := by omega
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  have hs4B : (SUIT B).toNat < 4 := hBreal.1
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hVB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hVB := VALUE_toNat B
  have hSBn := SUIT_toNat B
  have hflv : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (VALUE B).toNat := by
    have h := hbase.flute_le_value hwf ⟨pile.toNat, hpile⟩ hdpile
    simp only [hBdef] at h; exact h
  have hfl1 : 1 ≤ (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    hbase.flute_pos ⟨pile.toNat, hpile⟩
  have hfleB : p.pileFlute.get ⟨pile.toNat, hpile⟩ ≤ B := by
    rw [UInt8.le_iff_toNat_le]; omega
  have hsubNat : (B - p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat =
      B.toNat - (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    UInt8.toNat_sub_of_le _ _ hfleB
  have hSsub : (SUIT (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat = (SUIT B).toNat := by
    rw [SUIT_toNat, hsubNat]; omega
  have hVsub : (VALUE (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat =
      (VALUE B).toNat - (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat := by
    rw [VALUE_toNat, hsubNat]; omega
  have hfna : (p.aces.get ⟨(SUIT B).toNat, hs4B⟩).toNat +
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ B.toNat := by
    have h := (hbase.pileBase ⟨pile.toNat, hpile⟩).flute_not_aces hdpile
    simp only [hBdef] at h
    exact h hs4B
  obtain ⟨hSa, hVa, _, _, _⟩ := hbase.aces_kings_valid ⟨(SUIT B).toNat, hs4B⟩
  have hsuitU8 : (((⟨(SUIT B).toNat, hs4B⟩ : Fin 4).val).toUInt8).toNat = (SUIT B).toNat := by
    show ((SUIT B).toNat).toUInt8.toNat = (SUIT B).toNat
    rw [UInt8.toNat_ofNat']; omega
  have hSaN : (SUIT (p.aces.get ⟨(SUIT B).toNat, hs4B⟩)).toNat = (SUIT B).toNat := by
    rw [hSa, hsuitU8]
  have hAd := SUIT_toNat (p.aces.get ⟨(SUIT B).toNat, hs4B⟩)
  have hAv := VALUE_toNat (p.aces.get ⟨(SUIT B).toNat, hs4B⟩)
  by_cases hV0 : (VALUE (B - p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat = 0
  · -- The suit's zero-value sentinel: `flute_not_aces`'s upper bound and the
    -- suit-block lower bound on `aces` pin them to the same card.
    exact Or.inl ⟨hs4B, UInt8.toNat_inj.mp (by omega)⟩
  · have hd0 : p.pileDepth.get ⟨pile.toNat, hpile⟩ ≠ 0 := by
      intro hz; rw [hz] at hdpile; exact absurd hdpile (by simp)
    have hfm := (hmerged.pileMerged ⟨pile.toNat, hpile⟩).flute_maximal.resolve_left hd0
    simp only [hBdef] at hfm
    rcases hfm with hA | hnfp
    · exact Or.inl hA
    · refine Or.inr ?_
      have hreal : IsRealCard (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) :=
        ⟨by omega, by omega, by omega⟩
      intro hfreeQ
      rcases dest_free_char g p q pile hpile hwf hd1 hd5 hfr.depthSelf hfr.depthNe
        (B - p.pileFlute.get ⟨pile.toNat, hpile⟩) hreal hfreeQ with hfp | hcB
      · exact hnfp hfp
      · rw [hBdef] at hcB
        have := congrArg UInt8.toNat hcB
        omega

/-- **The destination pile's flute length is exactly the walk length `n`.**
    `pile`'s boundary `B` is not free, so `flute_stays_above` keeps the
    destination flute from reaching down to `B`, giving `pileFlute[j] ≤ n`.
    Conversely a *shorter* flute would put its `prevCard` at one of the walked
    (free) cards `B+1 … B+n−1`, so `flute_maximal` would force it to be
    `aces[s]` — but then `B` itself would be covered by the foundation and hence
    free, contradiction.

    Exported (it used to be `private`): the phase-1 simulation needs it to turn
    `DestValid`'s walk into `movePre_sim_of_dest`'s gap hypothesis. -/
theorem dest_flute_eq_walk (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (B : UInt8) (hBreal : IsRealCard B) (hBnf : ¬ isFreeCard g p B)
    (n : Nat) (hn1 : 1 ≤ n) (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidx : (p.pileDepth.get j).toNat - 1 < 5)
    (hBjeq : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ = B + UInt8.ofNat n) :
    (p.pileFlute.get j).toNat = n := by
  have hbase := hmerged.toSolverInvBase
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  have hs4B : (SUIT B).toNat < 4 := hBreal.1
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  obtain ⟨hBjnat, hSBj, hVBj⟩ := card_add_suit_value hBreal hnval
  have hVBjB : (VALUE (B + UInt8.ofNat n)).toNat ≤ (B + UInt8.ofNat n).toNat := by
    rw [VALUE_toNat]; omega
  have hflv : (p.pileFlute.get j).toNat ≤ (VALUE (B + UInt8.ofNat n)).toNat := by
    have h := hbase.flute_le_value hwf j hdj
    simp only [hBjeq] at h; exact h
  have hfl1 : 1 ≤ (p.pileFlute.get j).toNat := hbase.flute_pos j
  -- `≤ n`: the flute cannot reach down to the un-freed `B`.
  have hle : (p.pileFlute.get j).toNat ≤ n := by
    have hoff : (UInt8.ofNat ((p.pileFlute.get j).toNat - 1)).toNat =
        (p.pileFlute.get j).toNat - 1 := by rw [UInt8.toNat_ofNat']; omega
    have hstay := flute_stays_above hwf hbase j hdj B hBnf
      (by simp only [hBjeq]; omega) (UInt8.ofNat ((p.pileFlute.get j).toNat - 1))
      (by rw [hoff]; omega)
    simp only [hBjeq] at hstay
    have hoffle : UInt8.ofNat ((p.pileFlute.get j).toNat - 1) ≤ B + UInt8.ofNat n := by
      rw [UInt8.le_iff_toNat_le, hoff]; omega
    rw [UInt8.toNat_sub_of_le _ _ hoffle, hoff] at hstay
    omega
  -- `≥ n`: a shorter flute's `prevCard` is a walked card, and `flute_maximal`
  -- would then make `B` a foundation card.
  by_contra hne
  have hlt : (p.pileFlute.get j).toNat < n := by omega
  have hm1 : 1 ≤ n - (p.pileFlute.get j).toNat := by omega
  have hmof : (UInt8.ofNat (n - (p.pileFlute.get j).toNat)).toNat =
      n - (p.pileFlute.get j).toNat := by rw [UInt8.toNat_ofNat']; omega
  have hprevEq : (B + UInt8.ofNat n) - p.pileFlute.get j
      = B + UInt8.ofNat (n - (p.pileFlute.get j).toNat) := by
    apply UInt8.toNat_inj.mp
    have hle' : p.pileFlute.get j ≤ B + UInt8.ofNat n := by
      rw [UInt8.le_iff_toNat_le]; omega
    rw [UInt8.toNat_sub_of_le _ _ hle', hBjnat,
      card_add_toNat hB61 (show n - (p.pileFlute.get j).toNat ≤ 13 by omega)]
    omega
  have hfreePrev : isFreeCard g p ((B + UInt8.ofNat n) - p.pileFlute.get j) := by
    rw [hprevEq]
    exact hwalk _ hm1 (by omega)
  have hd0 : p.pileDepth.get j ≠ 0 := by
    intro hz; rw [hz] at hdj; exact absurd hdj (by simp)
  have hfm := (hmerged.pileMerged j).flute_maximal.resolve_left hd0
  simp only [hBjeq] at hfm
  rcases hfm with ⟨hs', hA'⟩ | hnf
  · -- `aces[SUIT B] = B + (n − fl)`, so `B` is covered by the foundation.
    have hSeq : (SUIT (B + UInt8.ofNat n)).toNat = (SUIT B).toNat := by rw [hSBj]
    have hidxEq : (⟨(SUIT (B + UInt8.ofNat n)).toNat, hs'⟩ : Fin 4)
        = ⟨(SUIT B).toNat, hs4B⟩ := Fin.ext hSeq
    rw [hidxEq, hprevEq] at hA'
    obtain ⟨_, _, hVw⟩ := card_add_suit_value hBreal
      (show (VALUE B).toNat + (n - (p.pileFlute.get j).toNat) ≤ 13 by omega)
    have hsuitU8 : (((⟨(SUIT B).toNat, hs4B⟩ : Fin 4).val).toUInt8) = SUIT B := by
      show ((SUIT B).toNat).toUInt8 = SUIT B
      apply UInt8.toNat_inj.mp; rw [UInt8.toNat_ofNat']; omega
    exact hBnf (hbase.foundation_cards_free ⟨(SUIT B).toNat, hs4B⟩ B hsuitU8.symm hVB1
      (by rw [hA', hVw]; omega))
  · exact hnf hfreePrev

/-- **The destination pile stays clean after absorbing `pile`'s flute.**  Given
    the contiguity `Bt − pileFlute[toPile] = B` (the destination's exposed top
    card is `B + 1`, so `pile`'s flute extends it), the merged pile's flute
    footprint is exactly the old destination footprint, plus `pile`'s boundary
    `B` (free at the composed point, `dest_B_free`), plus `pile`'s own old flute
    interior — so `flute_cards_free` holds.  Everything else *shifts*: the merged
    flute's `prevCard` is literally `pile`'s own `B − fl`, so `flute_maximal` and
    `busyAces_complete` are `pile`'s clauses read at the destination, and
    `flute_not_aces` is `pile`'s bound plus `Bt = B + pileFlute[toPile]`. -/
private theorem destFlute_toPile (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hd5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat ≤ 5)
    (hfr : DestFrame g p q pile hpile)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (t : Fin 10) (ht : t.val ≠ pile.toNat) (hdt : 0 < (p.pileDepth.get t).toNat)
    (hidxt : (p.pileDepth.get t).toNat - 1 < 5) (Bt : UInt8)
    (hBt : (g.pos2card.get t).get ⟨(p.pileDepth.get t).toNat - 1, hidxt⟩ = Bt)
    (hprev : Bt - p.pileFlute.get t = B)
    (hqf : q.pileFlute.get t = p.pileFlute.get t + p.pileFlute.get ⟨pile.toNat, hpile⟩)
    (hbnd : (q.pileDepth.get t).toNat ≤ 5) :
    PileBase g q t ∧ PileMerged g q t hbnd := by
  have hbase := hmerged.toSolverInvBase
  have hdeq := hfr.depthNe t ht
  have hdpile : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat > 0 := by omega
  have hBtreal : IsRealCard Bt := by rw [← hBt]; exact hwf.pos2card_real t _
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  obtain ⟨hBt1, hBt61, hBtdec⟩ := real_range hBtreal
  have hs4B : (SUIT B).toNat < 4 := hBreal.1
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hVB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hVBt13 : (VALUE Bt).toNat ≤ 13 := hBtreal.2.2
  have hVBtN := VALUE_toNat Bt
  have hftv : (p.pileFlute.get t).toNat ≤ (VALUE Bt).toNat := by
    have h := hbase.flute_le_value hwf t hdt; simp only [hBt] at h; exact h
  obtain ⟨hBtnat, hSBt, hVBt⟩ := dest_prev_arith Bt B (p.pileFlute.get t) hftv hprev
  have hflv : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (VALUE B).toNat := by
    have h := hbase.flute_le_value hwf ⟨pile.toNat, hpile⟩ hdpile
    simp only [hBdef] at h; exact h
  have hft1 : 1 ≤ (p.pileFlute.get t).toNat := hbase.flute_pos t
  have hfl1 : 1 ≤ (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    hbase.flute_pos ⟨pile.toNat, hpile⟩
  have hqfN : (q.pileFlute.get t).toNat =
      (p.pileFlute.get t).toNat + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat := by
    rw [hqf, UInt8.toNat_add]; omega
  have hSBtN : (SUIT Bt).toNat = (SUIT B).toNat := by rw [hSBt]
  -- `pile`'s own `flute_not_aces`, at the destination's suit index.
  have hfna : (p.aces.get ⟨(SUIT B).toNat, hs4B⟩).toNat +
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ B.toNat := by
    have h := (hbase.pileBase ⟨pile.toNat, hpile⟩).flute_not_aces hdpile
    simp only [hBdef] at h
    exact h hs4B
  -- The merged flute's `prevCard` is literally `pile`'s own `B − fl`.
  have hfleB : p.pileFlute.get ⟨pile.toNat, hpile⟩ ≤ B := by
    rw [UInt8.le_iff_toNat_le]; omega
  have hsumleBt : q.pileFlute.get t ≤ Bt := by rw [UInt8.le_iff_toNat_le]; omega
  have hprev2 : Bt - q.pileFlute.get t = B - p.pileFlute.get ⟨pile.toNat, hpile⟩ := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_sub_of_le _ _ hsumleBt, UInt8.toNat_sub_of_le _ _ hfleB, hqfN]
    omega
  have hBfreeQ : isFreeCard g q B := by
    have h := dest_B_free g p q pile hpile hwf hd1 hd5 hfr.depthSelf
    simp only [hBdef] at h; exact h
  have hpb : PileBase g q t := by
    refine ⟨by rw [hdeq]; exact hbase.pileDepth_bound t,
      by rw [hdeq]; exact hbase.pileDepth_nonneg t,
      by rw [hqfN]; omega, ?_, ?_, ?_⟩
    · intro hz
      rw [hdeq] at hz
      rw [hz] at hdt
      exact absurd hdt (by simp)
    · intro k _ hk0 hklt
      rw [hqfN] at hklt
      simp only [hdeq, hBt]
      rcases Nat.lt_trichotomy k.toNat (p.pileFlute.get t).toNat with hlt | heq | hgt
      · have h := hbase.flute_cards_free t k hdt hk0 hlt
        simp only [hBt] at h
        exact destFrame_free_mono hd1 hfr h
      · have hkle : k ≤ Bt := by rw [UInt8.le_iff_toNat_le]; omega
        have hkB : Bt - k = B := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hkle]; omega
        rw [hkB]; exact hBfreeQ
      · have hmof : (UInt8.ofNat (k.toNat - (p.pileFlute.get t).toNat)).toNat =
            k.toNat - (p.pileFlute.get t).toNat := by rw [UInt8.toNat_ofNat']; omega
        have h := hbase.flute_cards_free ⟨pile.toNat, hpile⟩
          (UInt8.ofNat (k.toNat - (p.pileFlute.get t).toNat)) hdpile
          (by rw [hmof]; omega) (by rw [hmof]; omega)
        simp only [hBdef] at h
        have hkle : k ≤ Bt := by rw [UInt8.le_iff_toNat_le]; omega
        have hmle : UInt8.ofNat (k.toNat - (p.pileFlute.get t).toNat) ≤ B := by
          rw [UInt8.le_iff_toNat_le, hmof]; omega
        have heqc : B - UInt8.ofNat (k.toNat - (p.pileFlute.get t).toNat) = Bt - k := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_sub_of_le _ _ hmle, UInt8.toNat_sub_of_le _ _ hkle, hmof]
          omega
        rw [heqc] at h
        exact destFrame_free_mono hd1 hfr h
    · intro _
      simp only [hdeq, hfr.aces, hBt]
      intro hs
      have hie : (⟨(SUIT Bt).toNat, hs⟩ : Fin 4) = ⟨(SUIT B).toNat, hs4B⟩ := Fin.ext hSBtN
      rw [hie, hqfN]
      omega
  refine ⟨hpb, ?_, ?_, ?_⟩
  · simp only [hdeq]
    exact (hmerged.pileMerged t).merge_complete
  · refine Or.inr ?_
    simp only [hdeq, hfr.aces, hBt, hprev2]
    rcases dest_prevCard_maximal g p q pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef with
      ⟨_, hA⟩ | hnf
    · refine Or.inl ⟨hBtreal.1, ?_⟩
      have hie : (⟨(SUIT Bt).toNat, hBtreal.1⟩ : Fin 4) = ⟨(SUIT B).toNat, hs4B⟩ :=
        Fin.ext hSBtN
      rw [hie]; exact hA
    · exact Or.inr hnf
  · intro _
    simp only [hdeq, hfr.aces, hfr.busyAces, hBt, hprev2]
    intro hs hA
    have hie : (⟨(SUIT Bt).toNat, hs⟩ : Fin 4) = ⟨(SUIT B).toNat, hs4B⟩ := Fin.ext hSBtN
    rw [hie] at hA
    have h := (hmerged.pileMerged ⟨pile.toNat, hpile⟩).busyAces_complete hdpile
    simp only [hBdef] at h
    rw [hSBt]
    exact h hs4B hA

/-- **Only the destination pile's flute sits directly on `B`.**  Any pile whose
    flute predecessor is `B` has boundary exactly `B + n`
    (`dest_prevCard_forces`), and `pos2card` is injective across the whole
    layout — so it *is* the destination pile.  This is what feeds
    `destFrame_pileMerged_ne`'s `hprevNe` for all the untouched piles. -/
private theorem dest_prevNe_of_toPile (g : Globals) (p : SolverPosType)
    (hwf : WellFormedLayout g) (hbase : SolverInvBase g p)
    (B : UInt8) (hBreal : IsRealCard B) (n : Nat) (hn1 : 1 ≤ n)
    (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n))
    (t : Fin 10) (hidxt : (p.pileDepth.get t).toNat - 1 < 5)
    (hBt : (g.pos2card.get t).get ⟨(p.pileDepth.get t).toNat - 1, hidxt⟩ = B + UInt8.ofNat n)
    (j : Fin 10) (hjt : j ≠ t) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hidx : (p.pileDepth.get j).toNat - 1 < 5) :
    (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ - p.pileFlute.get j ≠ B := by
  intro hprev
  obtain ⟨_, hBjeq⟩ := dest_prevCard_forces g p hwf hbase B hBreal n hn1 hnval hwalk hstop
    j hdj hidx _ rfl hprev
  obtain ⟨hje, _⟩ := hwf.pos2card_inj j t ⟨_, hidx⟩ ⟨_, hidxt⟩ (by rw [hBjeq, hBt])
  exact hjt hje

/-- Flute-only counterpart of `usedSpace_term_foldl_set`: the depth entry at that
    index is left alone (obtained by re-`set`ting it to its own value). -/
private theorem usedSpace_term_setFlute (dv flv : Vector UInt8 10)
    (k : Nat) (hk : k < 10) (xf : UInt8) :
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        dv.toList (flv.set k xf hk).toList).foldl (·+·) 0
      + (if (dv[k]'hk) ≠ (0 : UInt8) then (flv[k]'hk).toNat - 1 else 0) =
    (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        dv.toList flv.toList).foldl (·+·) 0
      + (if (dv[k]'hk) ≠ (0 : UInt8) then xf.toNat - 1 else 0) := by
  have h := usedSpace_term_foldl_set dv flv k hk (dv[k]'hk) xf
  rwa [Vector.set_getElem_self hk] at h

/-! ### Field-by-field shape of the composed destination state

`moveDest_shape_*` spell out
`fluteNorm ∘ removeFlutePre ∘ moveDestPre` as a single record update per
branch, so the branch proofs below can read every field off by `rfl`. -/

/-- Pile-to-pile branch (`toPile < 10`). -/
private theorem moveDest_shape_pile (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10) :
    fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)) =
      { p with
        hash := p.hash - pileHashes[pile.toNat]'hpile,
        pileDepth := p.pileDepth.set pile.toNat ((p.pileDepth[pile.toNat]'hpile) - 1) hpile,
        pileFlute := (p.pileFlute.set toPile.toNat
          ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)) h10).set
            pile.toNat 1 hpile } := by
  simp only [fluteNorm, removeFlutePre, moveDestPre, dif_pos h10]

/-- King-pile branch (`10 ≤ toPile < 14`). -/
private theorem moveDest_shape_king (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hpile : pile.toNat < 10) (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    (hk4 : toPile.toNat - 10 < 4) :
    fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)) =
      { p with
        hash := p.hash - pileHashes[pile.toNat]'hpile,
        pileDepth := p.pileDepth.set pile.toNat ((p.pileDepth[pile.toNat]'hpile) - 1) hpile,
        pileFlute := p.pileFlute.set pile.toNat 1 hpile,
        kings := p.kings.set (toPile.toNat - 10)
          ((p.kings[toPile.toNat - 10]'hk4) - (p.pileFlute[pile.toNat]'hpile)) hk4,
        usedSpace := p.usedSpace + (p.pileFlute[pile.toNat]'hpile) } := by
  simp only [fluteNorm, removeFlutePre, moveDestPre, dif_neg h10, dif_pos h14]

/-- Extra-slot branch (`toPile = 14`). -/
private theorem moveDest_shape_extra (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hpile : pile.toNat < 10) (h10 : ¬ toPile.toNat < 10) (h14 : ¬ toPile.toNat < 14) :
    fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)) =
      { p with
        hash := p.hash - pileHashes[pile.toNat]'hpile,
        pileDepth := p.pileDepth.set pile.toNat ((p.pileDepth[pile.toNat]'hpile) - 1) hpile,
        pileFlute := p.pileFlute.set pile.toNat 1 hpile,
        usedSpace := p.usedSpace + (p.pileFlute[pile.toNat]'hpile) } := by
  simp only [fluteNorm, removeFlutePre, moveDestPre, dif_neg h10, dif_neg h14]

/-- **Shared body of the king-pile and extra-slot branches.**  Neither touches
    any pile's `pileFlute`, so every pile other than `pile` transfers verbatim
    (`destFrame_pileBase_ne` / `destFrame_pileMerged_ne`), and the `usedSpace`
    bump by `fl` is exactly the flute term `pile` loses when its flute
    normalizes to `1`.  The two branches differ only in `hsc` (which suit's
    `kings` entry moved) — supplied by the caller. -/
private theorem moveDest_ready_noFlute (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hqhash : q.hash = p.hash - (pileHashes[pile.toNat]'hpile))
    (hqdepth : q.pileDepth = p.pileDepth.set pile.toNat
      ((p.pileDepth[pile.toNat]'hpile) - 1) hpile)
    (hqflute : q.pileFlute = p.pileFlute.set pile.toNat 1 hpile)
    (hqaces : q.aces = p.aces) (hqbusy : q.busyAces = p.busyAces)
    (hqfp : q.freePiles = p.freePiles)
    (hqused : q.usedSpace = p.usedSpace + (p.pileFlute[pile.toNat]'hpile))
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (hprevNe : ∀ j : Fin 10, j.val ≠ pile.toNat → 0 < (p.pileDepth.get j).toNat →
      ∀ hidx : (p.pileDepth.get j).toNat - 1 < 5,
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ - p.pileFlute.get j ≠ B)
    (hsc : DestFrame g p q pile hpile → ∀ (s : Fin 4)
      (hb : ∀ i : Fin 10, (q.pileDepth.get i).toNat ≤ 5), SuitClean g q s hb) :
    CleanupReady g q pile := by
  have hbase := hmerged.toSolverInvBase
  have hd5 := hbase.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hdne0 : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) := by
    intro hz
    have h0 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat = 0 := by
      rw [show p.pileDepth.get ⟨pile.toNat, hpile⟩ = p.pileDepth[pile.toNat]'hpile from rfl, hz]
      rfl
    omega
  -- Frame conditions.
  have hfr : DestFrame g p q pile hpile := by
    refine ⟨?_, ?_, hqaces, hqbusy, ?_⟩
    · rw [hqdepth]; exact Vector.getElem_set_self hpile
    · intro j hj; rw [hqdepth]; exact Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)
    · rw [hqflute]; exact Vector.getElem_set_self hpile
  -- The untouched piles keep their flute, hence their whole per-pile state.
  have hfleq : ∀ j : Fin 10, j.val ≠ pile.toNat → q.pileFlute.get j = p.pileFlute.get j := by
    intro j hj; rw [hqflute]; exact Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)
  have hpb : ∀ j : Fin 10, j.val ≠ pile.toNat → PileBase g q j := fun j hj =>
    destFrame_pileBase_ne g p q pile hpile hd1 hfr j hj (hfleq j hj) (hbase.pileBase j)
  -- The flute-term ledger: `pile`'s term drops from `fl − 1` to `0`.
  have hTsum : (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        q.pileDepth.toList q.pileFlute.toList).foldl (·+·) 0
      + ((p.pileFlute[pile.toNat]'hpile).toNat - 1) =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList).foldl (·+·) 0 := by
    rw [hqdepth, hqflute]
    have h := usedSpace_term_foldl_set p.pileDepth p.pileFlute pile.toNat hpile
      ((p.pileDepth[pile.toNat]'hpile) - 1) 1
    rw [if_pos hdne0, show (if ((p.pileDepth[pile.toNat]'hpile) - 1) ≠ (0 : UInt8)
        then (1 : UInt8).toNat - 1 else 0) = 0 from by split <;> rfl] at h
    omega
  refine destFrame_cleanupReady g p q pile hpile hwf hmerged hd1 hfr hqhash hqdepth hqfp
    hpb (hsc hfr) ?_ ?_
  · -- `usedSpace` ledger.
    have hUsed := hbase.usedSpace_def
    have hDsum := destFrame_depth_sum p q pile hpile hd1 hqdepth
    have hflv : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤
        (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩)).toNat :=
      hbase.flute_le_value hwf ⟨pile.toNat, hpile⟩ (by omega)
    have hfl13 : (p.pileFlute[pile.toNat]'hpile).toNat ≤ 13 := by
      have h := (hwf.pos2card_real ⟨pile.toNat, hpile⟩
        ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩).2.2
      exact le_trans hflv h
    have hfl1 : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat :=
      hbase.flute_pos ⟨pile.toNat, hpile⟩
    obtain ⟨hus0, hus52⟩ := usedSpace_nonneg hwf hbase
    have haddN : (p.usedSpace + (p.pileFlute[pile.toNat]'hpile)).toNat
        = p.usedSpace.toNat + (p.pileFlute[pile.toNat]'hpile).toNat := by
      rw [UInt8.toNat_add]
      simp only [UInt8.toInt_eq] at hus52
      omega
    rw [hqused, hqaces]
    simp only [UInt8.toInt_eq] at hUsed ⊢
    rw [haddN]
    push_cast
    omega
  · -- `PileMerged` for every pile but `pile`.
    intro j hj
    refine destFrame_pileMerged_ne g p q pile hpile hwf hbase hd1 hd5 hfr j hj (hfleq j hj)
      (hbase.pileBase j) (hmerged.pileMerged j) ?_
    intro hdj hidx
    rw [hBdef]
    exact hprevNe j hj hdj hidx

/-- `Fin`-indexed `Vector.getElem_set_self`, with the index equation explicit. -/
private theorem vector_set_get_self {α : Type} {m : Nat} (v : Vector α m) (k : Nat) (hk : k < m)
    (x : α) (i : Fin m) (hik : i.val = k) : (v.set k x hk).get i = x := by
  cases hik
  exact Vector.getElem_set_self hk

/-- `Fin`-indexed `Vector.getElem_set_ne`. -/
private theorem vector_set_get_ne {α : Type} {m : Nat} (v : Vector α m) (k : Nat) (hk : k < m)
    (x : α) (i : Fin m) (hik : i.val ≠ k) : (v.set k x hk).get i = v.get i :=
  Vector.getElem_set_ne hk i.isLt (Ne.symm hik)

/-- **`CleanupReady` after the destination step — extra-slot branch
    (`toPile = 14`).**  The flute went to a free cell, so no pile but `pile`
    changes.  `hnoB` (no pile's boundary is the walk's stopping card `B + n`) is
    exactly what the solver's `pftVal ≠ 1` test guarantees, and it rules out a
    foreign flute sitting directly on `B`. -/
private theorem moveDest_cleanupReady_extra (g : Globals) (p : SolverPosType) (pile : UInt32)
    (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : ¬ toPile.toNat < 14)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (n : Nat) (hn1 : 1 ≤ n) (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n))
    (hnoB : ∀ (j : Fin 10) (hidx : (p.pileDepth.get j).toNat - 1 < 5),
      0 < (p.pileDepth.get j).toNat →
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩ ≠ B + UInt8.ofNat n) :
    CleanupReady g
      (fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)))
      pile := by
  have hbase := hmerged.toSolverInvBase
  have hd5 := hbase.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  rw [moveDest_shape_extra p pile toPile hpile h10 h14]
  refine moveDest_ready_noFlute g p _ pile hpile hwf hmerged hd1 rfl rfl rfl rfl rfl rfl rfl
    B hidx5 hBdef ?_ ?_
  · intro j _ hdj hidx hprev
    obtain ⟨_, hBjeq⟩ := dest_prevCard_forces g p hwf hbase B hBreal n hn1 hnval hwalk hstop
      j hdj hidx _ rfl hprev
    exact hnoB j hidx hdj hBjeq
  · intro hfr s hb
    exact destFrame_suitClean g p _ pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s rfl
      (dest_kings_ne g p hbase B hBreal n hn1 hnval hstop s) hb

/-- **`CleanupReady` after the destination step — king-pile branch
    (`10 ≤ toPile < 14`).**  `B` is the suit's king frontier, so
    `dest_prevCard_ne_king` rules out *any* pile's flute sitting on `B`, and the
    affected suit's `SuitClean` is `destKing_suitClean`; all other suits keep
    their `kings` entry (and can't have `B` as their frontier, wrong suit). -/
private theorem moveDest_cleanupReady_king (g : Globals) (p : SolverPosType) (pile : UInt32)
    (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (s : Fin 4) (hsv : s.val = (SUIT B).toNat) (hkB : p.kings.get s = B)
    (htp : toPile.toNat - 10 = s.val) :
    CleanupReady g
      (fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)))
      pile := by
  have hbase := hmerged.toSolverInvBase
  have hd5 := hbase.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hk4 : toPile.toNat - 10 < 4 := by rw [htp]; exact s.isLt
  rw [moveDest_shape_king p pile toPile hpile h10 h14 hk4]
  refine moveDest_ready_noFlute g p _ pile hpile hwf hmerged hd1 rfl rfl rfl rfl rfl rfl rfl
    B hidx5 hBdef ?_ ?_
  · intro j _ hdj hidx hprev
    exact dest_prevCard_ne_king g p hwf hbase B s hsv hkB j hdj hidx _ rfl hprev
  · intro hfr s' hb
    by_cases hss : s' = s
    · subst hss
      refine destKing_suitClean g p _ pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s'
        hsv hkB ?_ hb
      rw [vector_set_get_self _ _ hk4 _ s' htp.symm]
      congr 1
      rw [show (p.kings[toPile.toNat - 10]'hk4) = p.kings.get ⟨toPile.toNat - 10, hk4⟩ from rfl,
        show (⟨toPile.toNat - 10, hk4⟩ : Fin 4) = s' from Fin.ext htp]
      exact hkB
    · refine destFrame_suitClean g p _ pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s'
        (vector_set_get_ne _ _ hk4 _ s' (by rw [htp]; exact fun h => hss (Fin.ext h))) ?_ hb
      intro heq
      have hSk := (hbase.aces_kings_valid s').2.2.1
      rw [heq] at hSk
      have hsuitU8 : ((s'.val).toUInt8).toNat = s'.val := by
        rw [UInt8.toNat_ofNat']; have := s'.isLt; omega
      exact hss (Fin.ext (by rw [hsv, hSk, hsuitU8]))

/-- **`CleanupReady` after the destination step — pile-to-pile branch
    (`toPile < 10`), stated with the composed state's fields abstracted.**  The
    destination pile is handled by `destFlute_toPile` (its flute grew), every
    other pile by `destFrame_pileBase_ne`/`destFrame_pileMerged_ne` (flute
    untouched, and `dest_prevNe_of_toPile` rules out a foreign flute on `B`), and
    the `usedSpace` ledger balances: `pile`'s flute term loses `fl − 1` while
    `toPile`'s gains `fl`, a net `+1` cancelling the depth sum's `−1`. -/
private theorem moveDest_ready_flute (g : Globals) (p q : SolverPosType) (pile : UInt32)
    (toPile : UInt8) (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hqhash : q.hash = p.hash - (pileHashes[pile.toNat]'hpile))
    (hqdepth : q.pileDepth = p.pileDepth.set pile.toNat
      ((p.pileDepth[pile.toNat]'hpile) - 1) hpile)
    (hqflute : q.pileFlute = (p.pileFlute.set toPile.toNat
      ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)) h10).set
        pile.toNat 1 hpile)
    (hqaces : q.aces = p.aces) (hqkings : q.kings = p.kings) (hqbusy : q.busyAces = p.busyAces)
    (hqfp : q.freePiles = p.freePiles) (hqused : q.usedSpace = p.usedSpace)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (n : Nat) (hn1 : 1 ≤ n) (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n))
    (hdt : 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hidxt : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5)
    (hBt : (g.pos2card.get ⟨toPile.toNat, h10⟩).get
      ⟨(p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1, hidxt⟩ = B + UInt8.ofNat n) :
    CleanupReady g q pile := by
  have hbase := hmerged.toSolverInvBase
  have hd5 := hbase.pileDepth_bound ⟨pile.toNat, hpile⟩
  have hdpile : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat > 0 := by omega
  have hBreal : IsRealCard B := by rw [← hBdef]; exact hwf.pos2card_real _ _
  obtain ⟨hB1, hB61, hBdec⟩ := real_range hBreal
  have hVB1 : 1 ≤ (VALUE B).toNat := hBreal.2.1
  have hVB13 : (VALUE B).toNat ≤ 13 := hBreal.2.2
  have hBn : (B + UInt8.ofNat n).toNat = B.toNat + n := card_add_toNat hB61 (by omega)
  -- The destination is a *different* pile: otherwise `B = B + n`.
  have htne : toPile.toNat ≠ pile.toNat := by
    intro heq
    have h1 : (⟨toPile.toNat, h10⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ := Fin.ext heq
    have h2 : (g.pos2card.get ⟨toPile.toNat, h10⟩).get
        ⟨(p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1, hidxt⟩
        = (g.pos2card.get ⟨pile.toNat, hpile⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ := by simp only [h1]
    rw [hBt, hBdef] at h2
    have h3 := congrArg UInt8.toNat h2
    omega
  -- `pile`'s boundary is not free, so the destination flute is exactly `n` long.
  have hBnf : ¬ isFreeCard g p B := by
    have h := boundary_not_free hwf hbase ⟨pile.toNat, hpile⟩ hdpile
    simp only [hBdef] at h; exact h
  have hftn : (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat = n :=
    dest_flute_eq_walk g p hwf hmerged B hBreal hBnf n hn1 hnval hwalk
      ⟨toPile.toNat, h10⟩ hdt hidxt hBt
  have hprev : (B + UInt8.ofNat n) - p.pileFlute.get ⟨toPile.toNat, h10⟩ = B := by
    apply UInt8.toNat_inj.mp
    have hle : p.pileFlute.get ⟨toPile.toNat, h10⟩ ≤ B + UInt8.ofNat n := by
      rw [UInt8.le_iff_toNat_le]; omega
    rw [UInt8.toNat_sub_of_le _ _ hle]; omega
  -- Flute lengths and their sum.
  have hflv : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (VALUE B).toNat := by
    have h := hbase.flute_le_value hwf ⟨pile.toNat, hpile⟩ hdpile
    simp only [hBdef] at h; exact h
  have hfl1 : 1 ≤ (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat :=
    hbase.flute_pos ⟨pile.toNat, hpile⟩
  have hsum : ((p.pileFlute.get ⟨toPile.toNat, h10⟩) +
      (p.pileFlute.get ⟨pile.toNat, hpile⟩)).toNat =
      (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat +
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat := by
    rw [UInt8.toNat_add]; omega
  have hdne0 : (p.pileDepth[pile.toNat]'hpile) ≠ (0 : UInt8) := by
    intro hz
    have h0 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat = 0 := by
      rw [show p.pileDepth.get ⟨pile.toNat, hpile⟩ = p.pileDepth[pile.toNat]'hpile from rfl, hz]
      rfl
    omega
  have hdtne0 : (p.pileDepth[toPile.toNat]'h10) ≠ (0 : UInt8) := by
    intro hz
    have h0 : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat = 0 := by
      rw [show p.pileDepth.get ⟨toPile.toNat, h10⟩ = p.pileDepth[toPile.toNat]'h10 from rfl, hz]
      rfl
    omega
  -- Frame conditions.
  have hfr : DestFrame g p q pile hpile := by
    refine ⟨?_, ?_, hqaces, hqbusy, ?_⟩
    · rw [hqdepth]; exact Vector.getElem_set_self hpile
    · intro j hj; rw [hqdepth]; exact Vector.getElem_set_ne hpile j.isLt (Ne.symm hj)
    · rw [hqflute]; exact Vector.getElem_set_self hpile
  have hfleq : ∀ j : Fin 10, j.val ≠ pile.toNat → j.val ≠ toPile.toNat →
      q.pileFlute.get j = p.pileFlute.get j := by
    intro j hj hjt
    rw [hqflute, vector_set_get_ne _ _ hpile _ j hj, vector_set_get_ne _ _ h10 _ j hjt]
  have hqfT : q.pileFlute.get ⟨toPile.toNat, h10⟩ =
      p.pileFlute.get ⟨toPile.toNat, h10⟩ + p.pileFlute.get ⟨pile.toNat, hpile⟩ := by
    rw [hqflute, vector_set_get_ne _ _ hpile _ ⟨toPile.toNat, h10⟩ htne,
      vector_set_get_self _ _ h10 _ ⟨toPile.toNat, h10⟩ rfl]
    rfl
  have hbndT : (q.pileDepth.get ⟨toPile.toNat, h10⟩).toNat ≤ 5 := by
    rw [hqdepth, vector_set_get_ne _ _ hpile _ ⟨toPile.toNat, h10⟩ htne]
    exact hbase.pileDepth_bound _
  -- The destination pile, and the piles nothing touched.
  have hdest := destFlute_toPile g p q pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef
    ⟨toPile.toNat, h10⟩ htne hdt hidxt (B + UInt8.ofNat n) hBt hprev hqfT hbndT
  have hpb : ∀ j : Fin 10, j.val ≠ pile.toNat → PileBase g q j := by
    intro j hj
    by_cases hjt : j.val = toPile.toNat
    · have hje : j = (⟨toPile.toNat, h10⟩ : Fin 10) := Fin.ext hjt
      subst hje
      exact hdest.1
    · exact destFrame_pileBase_ne g p q pile hpile hd1 hfr j hj (hfleq j hj hjt)
        (hbase.pileBase j)
  -- The flute-term ledger: `pile` loses `fl − 1`, `toPile` gains `fl`.
  have hTsum : (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        q.pileDepth.toList q.pileFlute.toList).foldl (·+·) 0 =
      (List.zipWith (fun d f => if d ≠ (0 : UInt8) then f.toNat - 1 else 0)
        p.pileDepth.toList p.pileFlute.toList).foldl (·+·) 0 + 1 := by
    rw [hqdepth, hqflute]
    have h1 := usedSpace_term_foldl_set p.pileDepth (p.pileFlute.set toPile.toNat
      ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)) h10)
      pile.toNat hpile ((p.pileDepth[pile.toNat]'hpile) - 1) 1
    rw [show ((p.pileFlute.set toPile.toNat ((p.pileFlute[toPile.toNat]'h10) +
          (p.pileFlute[pile.toNat]'hpile)) h10)[pile.toNat]'hpile)
        = p.pileFlute[pile.toNat]'hpile from Vector.getElem_set_ne h10 hpile htne,
      if_pos hdne0, show (if ((p.pileDepth[pile.toNat]'hpile) - 1) ≠ (0 : UInt8)
        then (1 : UInt8).toNat - 1 else 0) = 0 from by split <;> rfl] at h1
    have h2 := usedSpace_term_setFlute p.pileDepth p.pileFlute toPile.toNat h10
      ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile))
    rw [if_pos hdtne0, if_pos hdtne0] at h2
    have hftn' : (p.pileFlute[toPile.toNat]'h10).toNat = n := hftn
    have hsum' : ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)).toNat =
        (p.pileFlute[toPile.toNat]'h10).toNat + (p.pileFlute[pile.toNat]'hpile).toNat := hsum
    have hfl1' : 1 ≤ (p.pileFlute[pile.toNat]'hpile).toNat := hfl1
    omega
  refine destFrame_cleanupReady g p q pile hpile hwf hmerged hd1 hfr hqhash hqdepth hqfp
    hpb ?_ ?_ ?_
  · -- Every suit's `kings` entry is untouched, and none of them is `B`.
    intro s hb
    exact destFrame_suitClean g p q pile hpile hwf hmerged hd1 hd5 hfr B hidx5 hBdef s
      (by rw [hqkings]) (dest_kings_ne g p hbase B hBreal n hn1 hnval hstop s) hb
  · -- `usedSpace` ledger.
    have hUsed := hbase.usedSpace_def
    have hDsum := destFrame_depth_sum p q pile hpile hd1 hqdepth
    rw [hqused, hqaces, hTsum]
    simp only [UInt8.toInt_eq] at hUsed ⊢
    push_cast
    omega
  · -- `PileMerged` for every pile but `pile`.
    intro j hj
    by_cases hjt : j.val = toPile.toNat
    · have hje : j = (⟨toPile.toNat, h10⟩ : Fin 10) := Fin.ext hjt
      subst hje
      exact hdest.2
    · refine destFrame_pileMerged_ne g p q pile hpile hwf hbase hd1 hd5 hfr j hj
        (hfleq j hj hjt) (hbase.pileBase j) (hmerged.pileMerged j) ?_
      intro hdj hidx
      rw [hBdef]
      exact dest_prevNe_of_toPile g p hwf hbase B hBreal n hn1 hnval hwalk hstop
        ⟨toPile.toNat, h10⟩ hidxt hBt j (fun h => hjt (congrArg Fin.val h)) hdj hidx

/-- **`CleanupReady` after the destination step — pile-to-pile branch. -/
private theorem moveDest_cleanupReady_pile (g : Globals) (p : SolverPosType) (pile : UInt32)
    (toPile : UInt8) (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10)
    (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (n : Nat) (hn1 : 1 ≤ n) (hnval : (VALUE B).toNat + n ≤ 13)
    (hwalk : ∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k))
    (hstop : ¬ isFreeCard g p (B + UInt8.ofNat n))
    (hdt : 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hidxt : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5)
    (hBt : (g.pos2card.get ⟨toPile.toNat, h10⟩).get
      ⟨(p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1, hidxt⟩ = B + UInt8.ofNat n) :
    CleanupReady g
      (fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)))
      pile := by
  rw [moveDest_shape_pile p pile toPile hpile h10]
  exact moveDest_ready_flute g p _ pile toPile hpile h10 hwf hmerged hd1 rfl rfl rfl rfl rfl
    rfl rfl rfl B hidx5 hBdef n hn1 hnval hwalk hstop hdt hidxt hBt

/-- **The destination data `solverGetDestination` delivers**, packaged as a
    precondition for `moveDest_cleanupReady`.  Mirrors `GetDestination`'s
    `getDest_spec` exactly: either `pile`'s boundary `B` *is* its suit's king
    frontier (`toPile = 10 + SUIT B`), or the freed-predecessor walk `B+1 … B+n`
    stops at an un-freed `B + n`, and then the destination is that card's own
    pile when `B + n` is a pile *boundary* (`pftVal = 1`) and the extra slot
    (`toPile = 14`) otherwise. -/
def DestValid (g : Globals) (p : SolverPosType) (B : UInt8) (toPile : UInt8) : Prop :=
  (∃ s : Fin 4, s.val = (SUIT B).toNat ∧ p.kings.get s = B ∧ toPile.toNat = 10 + s.val)
  ∨ (∃ n : Nat, 1 ≤ n ∧ (VALUE B).toNat + n ≤ 13 ∧
      (∀ k, 1 ≤ k → k < n → isFreeCard g p (B + UInt8.ofNat k)) ∧
      ¬ isFreeCard g p (B + UInt8.ofNat n) ∧
      ((∃ (h10 : toPile.toNat < 10) (_ : 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
            (hidxt : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1 < 5),
            (g.pos2card.get ⟨toPile.toNat, h10⟩).get
              ⟨(p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat - 1, hidxt⟩ = B + UInt8.ofNat n)
       ∨ (toPile.toNat = 14 ∧
            ∀ (j : Fin 10) (hidx : (p.pileDepth.get j).toNat - 1 < 5),
              0 < (p.pileDepth.get j).toNat →
              (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hidx⟩
                ≠ B + UInt8.ofNat n)))

/-- **`SolverMove`'s destination bookkeeping establishes `removeFlute_merged`'s
    precondition.**  A three-way branch on `toPile`, assembled from the per-branch
    lemmas above (`moveDest_cleanupReady_king` / `_pile` / `_extra`), all three of
    which end in `destFrame_cleanupReady`.  This is the pure flute-transfer fact
    `move_merged` is missing: at the composed point
    `fluteNorm ∘ removeFlutePre ∘ moveDestPre` the moved cards are free, the
    destination's `flute_maximal` is `pile`'s own clause read one flute higher,
    and the `usedSpace` ledger balances. -/
theorem moveDest_cleanupReady (g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hpile : pile.toNat < 10) (hwf : WellFormedLayout g) (hmerged : SolverInvMerged g p)
    (hd1 : 1 ≤ (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (B : UInt8) (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (hdv : DestValid g p B toPile) :
    CleanupReady g
      (fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p)))
      pile := by
  rcases hdv with ⟨s, hsv, hkB, htp⟩ | ⟨n, hn1, hnval, hwalk, hstop, hcase⟩
  · have hs4 := s.isLt
    exact moveDest_cleanupReady_king g p pile toPile hpile (by omega) (by omega) hwf hmerged
      hd1 B hidx5 hBdef s hsv hkB (by omega)
  · rcases hcase with ⟨h10, hdt, hidxt, hBt⟩ | ⟨h14, hnoB⟩
    · exact moveDest_cleanupReady_pile g p pile toPile hpile h10 hwf hmerged hd1 B hidx5 hBdef
        n hn1 hnval hwalk hstop hdt hidxt hBt
    · exact moveDest_cleanupReady_extra g p pile toPile hpile (by omega) (by omega) hwf hmerged
        hd1 B hidx5 hBdef n hn1 hnval hwalk hstop hnoB

/-- **Exact run of `SolverMove`'s destination-bookkeeping prefix.**  The real
    monadic three-way branch — read `pile`'s flute length, then depending on
    `toPile` read/write `pileFlute[toPile]` or `kings`/`usedSpace` — reduces,
    given the index bounds, to the pure `moveDestPre`, then falls through to
    `SolverRemoveFlute pile` and the drain loop exactly as `moveExplicit`
    defines `finish`. -/
theorem moveDest_run_eq (pile : UInt32) (toPile : UInt8) (g : Globals) (p : SolverPosType)
    (hpile : pile.toNat < 10) (htoPile14 : toPile.toNat ≤ 14) :
    EStateM.run (_root_.SolverMove pile toPile) (g, p) =
    EStateM.run
      (_root_.SolverRemoveFlute pile >>= fun forcedKings =>
        Loop.forIn Loop.mk forcedKings drainBody >>= fun r => pure r)
      (g, moveDestPre pile toPile hpile p) := by
  show moveExplicit pile toPile (g, p) =
    (_root_.SolverRemoveFlute pile >>= fun forcedKings =>
        Loop.forIn Loop.mk forcedKings drainBody >>= fun r => pure r)
      (g, moveDestPre pile toPile hpile p)
  unfold moveExplicit moveDestPre
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, Vector.getE, getElem?_pos, hpile, pure, EStateM.pure,
    UInt8.toNat_toUInt32]
  by_cases h10 : toPile.toNat < 10
  · have hlt : toPile < (10 : UInt8) := by
      rw [UInt8.lt_iff_toNat_lt, show (10 : UInt8).toNat = 10 from rfl]; exact h10
    have hget : (p.pileFlute[toPile.toNat]? : Option UInt8) =
        some (p.pileFlute[toPile.toNat]'h10) := getElem?_pos p.pileFlute toPile.toNat h10
    simp only [if_pos hlt, hget, EStateM.pure, EStateM.bind]
    simp only [Vector.setE, UInt8.toNat_toUInt32, EStateM.set, pure]
    simp only [dif_pos h10, EStateM.pure]
  · have hge : ¬ toPile < (10 : UInt8) := by
      rw [UInt8.lt_iff_toNat_lt, show (10 : UInt8).toNat = 10 from rfl]; exact h10
    simp only [if_neg hge]
    rw [dif_neg h10]
    by_cases h14 : toPile.toNat < 14
    · have hlt14 : toPile < (14 : UInt8) := by
        rw [UInt8.lt_iff_toNat_lt, show (14 : UInt8).toNat = 14 from rfl]; exact h14
      have h10le : (10 : UInt8) ≤ toPile := by
        rw [UInt8.le_iff_toNat_le, show (10 : UInt8).toNat = 10 from rfl]; omega
      have hksub : (toPile - 10).toNat = toPile.toNat - 10 := by
        rw [UInt8.toNat_sub_of_le _ _ h10le, show (10 : UInt8).toNat = 10 from rfl]
      have hkbound : toPile.toNat - 10 < 4 := by omega
      have hgetk : (p.kings[toPile.toNat - 10]? : Option UInt8) =
          some (p.kings[toPile.toNat - 10]'hkbound) :=
        getElem?_pos p.kings (toPile.toNat - 10) hkbound
      simp only [if_pos hlt14, hksub, hgetk, EStateM.pure, EStateM.bind]
      simp only [Vector.setE, UInt8.toNat_toUInt32, hksub, EStateM.set, pure]
      simp only [dif_pos hkbound, dif_pos h14, EStateM.pure]
    · have hge14 : ¬ toPile < (14 : UInt8) := by
        rw [UInt8.lt_iff_toNat_lt, show (14 : UInt8).toNat = 14 from rfl]; exact h14
      simp only [if_neg hge14, dif_neg h14, EStateM.pure, EStateM.bind, EStateM.set]

/-- **`SolverMove` preserves canonical form.**  From a canonical state, a
    valid solver move yields another canonical state — the per-node invariant
    maintenance behind the soundness proof.

    Assembled from `moveDest_run_eq` (the destination write reduces to
    `moveDestPre`), `moveDest_cleanupReady` (the composed point is
    `CleanupReady`), `removeFlute_merged` (consumes it, running
    `SolverRemoveFlute`), and `drain_canonical` (runs the trailing
    `while busyAces ≠ 0` drain to completion, which is exactly what recovers
    full canonicity — `SolverInvMerged` alone is re-established already after
    `removeFlute_merged`).

    It also reports **progress**: `DepthSum p' < DepthSum p`.  Every phase is
    depth-monotone (`removeFlute_depth_le`, `drain_canonical`), and the source pile
    loses its whole flute, so the total pile depth strictly drops — the well-founded
    measure the search's termination (and its freedom from cycles) rests on. -/
theorem move_merged (g : Globals) (p : SolverPosType) (pile : UInt32) (toPile : UInt8)
    (hwf : WellFormedLayout g) (hcanon : IsCanonicalPos g p)
    (hvalid : MoveValid g p pile toPile)
    (hpile : pile.toNat < 10)
    (hidx5 : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1 < 5)
    (B : UInt8)
    (hBdef : (g.pos2card.get ⟨pile.toNat, hpile⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat - 1, hidx5⟩ = B)
    (hdv : DestValid g p B toPile) :
    ∃ fk p', EStateM.run (_root_.SolverMove pile toPile) (g, p) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧ DepthSum p' < DepthSum p := by
  obtain ⟨_, htoPile14, hd0⟩ := hvalid
  have hd1 : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat := by
    have heq : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hpile)
    rwa [heq] at hd0
  have hmerged := hcanon.toSolverInvMerged
  have hready := moveDest_cleanupReady g p pile toPile hpile hwf hmerged hd1 B hidx5 hBdef hdv
  obtain ⟨fk1, p1, hrun1, hmerged1, haces1, hbusyMono1⟩ :=
    removeFlute_merged pile g (moveDestPre pile toPile hpile p) hpile hwf hready
  obtain ⟨fk2, p', hrun2, hcanon', hdrainLe⟩ := drain_canonical g p1 fk1 hwf hmerged1
  -- progress: `moveDestPre` leaves the depths alone, `SolverRemoveFlute` takes exactly
  -- one card off `pile` (and deepens nothing), the drain deepens nothing.
  have hqd := moveDestPre_pileDepth pile toPile hpile p
  obtain ⟨hnfq, -, -⟩ := hready
  obtain ⟨fk3, p3, hrun3, hle3, hlt3⟩ :=
    removeFlute_depth_le pile g (moveDestPre pile toPile hpile p) hpile hwf
      (by rw [show (moveDestPre pile toPile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩
            = p.pileDepth.get ⟨pile.toNat, hpile⟩ from by rw [hqd]]; omega) hnfq
  -- both runs of `SolverRemoveFlute` are the same run, so `p3 = p1`
  have hrun3' : EStateM.run (_root_.SolverRemoveFlute pile)
      (g, moveDestPre pile toPile hpile p) = .ok fk1 (g, p1) := hrun1
  injection hrun3.symm.trans hrun3' with _hfk h2
  injection h2 with _hg hp3
  rw [hp3] at hle3 hlt3
  have hdepthLt : DepthSum p' < DepthSum p := by
    refine DepthLe.sum_lt (DepthLe.trans' ?_ (DepthLe.trans' hle3 hdrainLe))
      ⟨pile.toNat, hpile⟩ ?_
    · intro i
      rw [hqd]
    · have hpile' := hdrainLe ⟨pile.toNat, hpile⟩
      rw [show (moveDestPre pile toPile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩
        = p.pileDepth.get ⟨pile.toNat, hpile⟩ from by rw [hqd]] at hlt3
      omega
  refine ⟨fk2, p', ?_, hcanon', hdepthLt⟩
  rw [moveDest_run_eq pile toPile g p hpile htoPile14]
  show (_root_.SolverRemoveFlute pile >>= fun fk =>
      Loop.forIn Loop.mk fk drainBody >>= fun r => pure r)
    (g, moveDestPre pile toPile hpile p) = .ok fk2 (g, p')
  have hrun1' : _root_.SolverRemoveFlute pile (g, moveDestPre pile toPile hpile p) =
      .ok fk1 (g, p1) := hrun1
  have hrun2' : Loop.forIn Loop.mk fk1 drainBody (g, p1) = .ok fk2 (g, p') := hrun2
  simp only [bind, EStateM.bind, hrun1', hrun2', pure, EStateM.pure]

end SolverSpec
