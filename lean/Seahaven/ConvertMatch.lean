import Seahaven.SolveCorrect

/-!
# The convert call, entered from a state nobody has normalized

`ConvertSim`'s `convert_simulates` asks the caller for
`StateMatchesKingConfig g s (convertPre g pk) k` — a state matching the position the
*prologue* computes.  That is more than a caller can deliver.  `convertPre`

* has all its flutes at `1`, so `flute_match` forces `|tableau i| = pk[i]`: no pile may
  carry a run at all; and
* has `aces = cvAceVal`, the *maximal* foundation the depth vector allows, so
  `aces_match` forces every freed card of every suit's initial run to be on its
  foundation already.

A state the game is actually in has runs on its piles and cards it has not bothered
to play.  What it does match is the same position read at its **own** flutes,
foundations and king frontiers — and closing the gap is convert's own job:

| loop | what the solver writes | what the state has to do |
|------|------------------------|--------------------------|
| 1 | depths from `pk`, flutes `1` | nothing — `pk` *is* the state's depth vector |
| 2 | `aces := cvAceVal`, `kings := cvKingVal` | play each suit's freed prefix to its foundation, and complete each king pile from the cells |
| 3 | merge + extend each pile's flute | drop the freed predecessors the pile does not carry yet |
| 4 | the `busyAces` drain | play the flutes that reached their foundation |

Loops 3 and 4 are already simulated (`SimulatesNorm.ofCleanupPile`,
`SimulatesNorm.drain`) — except that `ofCleanupPile` is stated at `fluteNorm`, i.e.
for a state whose pile carries *no* run.  So exactly two things are new, and they are
the two named `Prop`s of this file:

* `CvPrologueSim` — loop 2's writes are realized by normalizing moves;
* `CvCleanupSim` — one cleanup call, simulated from a state whose pile already carries
  part of the extension (`SimulatesNorm.ofCleanupPile` is the case where it carries
  none).

Everything else — the cleanup loop's induction, the drain, and the hand-over to
`solveTail_correct` — is proved here.  The moves involved are foundation plays and
cell→pile drops throughout, so the whole call stays a `SimulatesNorm` and the answer
is about the state the caller handed in.

Flutes are never a choice: `cvFluteOf` reads them off the state
(`|tableau i| + 1 - pileDepth[i]`, and `1` where the solver sees an empty pile) and
`matches_cvFluteOf` / `StateMatchesKingConfig.reflute` show that vector always works.
So neither `CvEntry` nor `CvPrologueSim` mentions a flute vector, and neither has to
produce one.
-/

namespace SolverSpec

open Lean Lean.Order

/-! ## Reading a position at the state's own flutes

The only field of a position that the entry state disagrees with the solver on for
more than one loop is `pileFlute`, and `cvRelax` is the position with that field
replaced.  It is *not* a solver position — its `usedSpace` no longer matches its
flutes — which is precisely why it may not be assumed to satisfy `SolverInvBase`.
The matching, though, never reads `usedSpace`. -/

/-- `q`, read at the flutes `fl`. -/
def cvRelax (q : SolverPosType) (fl : Vector UInt8 10) : SolverPosType :=
  { q with pileFlute := fl }

@[simp] theorem cvRelax_pileDepth (q : SolverPosType) (fl : Vector UInt8 10) :
    (cvRelax q fl).pileDepth = q.pileDepth := rfl

@[simp] theorem cvRelax_pileFlute (q : SolverPosType) (fl : Vector UInt8 10) :
    (cvRelax q fl).pileFlute = fl := rfl

@[simp] theorem cvRelax_aces (q : SolverPosType) (fl : Vector UInt8 10) :
    (cvRelax q fl).aces = q.aces := rfl

@[simp] theorem cvRelax_kings (q : SolverPosType) (fl : Vector UInt8 10) :
    (cvRelax q fl).kings = q.kings := rfl

theorem cvRelax_self (q : SolverPosType) : cvRelax q q.pileFlute = q := rfl

theorem cvRelax_eq (q : SolverPosType) {fl : Vector UInt8 10}
    (h : ∀ i : Fin 10, fl.get i = q.pileFlute.get i) : cvRelax q fl = q := by
  rw [show fl = q.pileFlute from vector_ext_get fl q.pileFlute h]
  exact cvRelax_self q

/-- `fluteNorm` is the relaxed reading with the flute *shortened* to `1` — so
`SimulatesNorm.ofCleanupPile` is literally `CvCleanupSim`'s `fl[pile] = 1` case. -/
theorem fluteNorm_eq_cvRelax (pile : UInt32) (hpile : pile.toNat < 10) (q : SolverPosType) :
    fluteNorm pile hpile q = cvRelax q (q.pileFlute.set pile.toNat 1 hpile) := rfl

/-- **A flute vector a state can supply.**  At least one card everywhere (the boundary
card itself), and exactly one at the piles the solver treats as empty — where the
matching does not read the flute at all, so the canonical reading `1` is free. -/
structure CvFlutes (q : SolverPosType) (fl : Vector UInt8 10) : Prop where
  pos : ∀ i : Fin 10, 1 ≤ (fl.get i).toNat
  empty : ∀ i : Fin 10, q.pileDepth.get i = 0 → fl.get i = 1

/-! ## The flute vector is not a choice

There is never a reason to go looking for one: the state's own flutes are *forced* by
the depth vector.  Above a boundary the column is the boundary card together with
everything stacked on it, so `flute_match` reads

> `pileFlute[i] = |tableau i| + 1 - pileDepth[i]`,

and at a pile the solver treats as empty the matching does not read the flute at all.
`cvFluteOf` is that vector and `matches_cvFluteOf` discharges `flute_match` outright —
which is why neither obligation below mentions a flute vector: they are about the depth
vector, the foundations and the king piles only.

The one thing to check is that the flute fits in a `UInt8`, and it does with room to
spare: above the boundary the column is a same-suit descending run of real cards, whose
values fall by one per card and never reach `0`, so it is at most as long as the
boundary's value — a nibble (`PileMatches.length_le`). -/

/-- **A matched column is short.**  Bounded by its dealt part plus one descending run. -/
theorem PileMatches.length_le {g : Globals} {col : Column} {a : Fin 10} {n : Fin 6}
    (h : PileMatches g col a n) : col.length ≤ n.val + 15 := by
  obtain ⟨hnL, -, h3⟩ := h
  -- the run above the boundary, together with a bound on where it starts
  have hex : ∃ (suit : UInt8) (startVal : Nat), startVal ≤ 15 ∧
      IsSameSuitDescending suit startVal ((col.reverse.drop n.val).map encodeCard) := by
    simp only [] at h3
    by_cases hn : n.val > 0
    · rw [dif_pos hn] at h3
      exact ⟨_, _, by rw [VALUE_toNat]; omega, h3⟩
    · rw [dif_neg hn] at h3
      obtain ⟨suit, hsuit⟩ := h3
      exact ⟨suit, 13, by omega, hsuit⟩
  obtain ⟨suit, startVal, hstart, hsd⟩ := hex
  by_contra hlt
  -- read the run off at its topmost card: its value would have run out
  have hflen : ((col.reverse.drop n.val).map encodeCard).length = col.length - n.val := by
    simp
  have hmlt : col.length - n.val - 1 < ((col.reverse.drop n.val).map encodeCard).length := by
    rw [hflen]; omega
  obtain ⟨-, hv⟩ := hsd ⟨col.length - n.val - 1, hmlt⟩
  have hv' : (VALUE (((col.reverse.drop n.val).map encodeCard)[col.length - n.val - 1]'hmlt)).toNat
      = startVal - (col.length - n.val - 1) := hv
  obtain ⟨c, -, hc⟩ := List.mem_map.1 (List.getElem_mem hmlt)
  rw [← hc, encodeCard_VALUE] at hv'
  have := rankToNat_pos c.rank
  omega

/-- **The flutes a state carries.**  `|tableau i| + 1 - pileDepth[i]` above a boundary,
`1` at the piles the solver treats as empty. -/
def cvFluteOf (u : State) (d : Vector UInt8 10) : Vector UInt8 10 :=
  Vector.ofFn (fun i => if (d.get i).toNat = 0 then 1
    else UInt8.ofNat ((u.tableau i).length + 1 - (d.get i).toNat))

theorem cvFluteOf_get (u : State) (d : Vector UInt8 10) (i : Fin 10) :
    (cvFluteOf u d).get i = if (d.get i).toNat = 0 then 1
      else UInt8.ofNat ((u.tableau i).length + 1 - (d.get i).toNat) := by
  show (Vector.ofFn (fun i : Fin 10 => if (d.get i).toNat = 0 then 1
    else UInt8.ofNat ((u.tableau i).length + 1 - (d.get i).toNat)))[i.val]'i.isLt = _
  rw [Vector.getElem_ofFn]

/-- **The flute clause, for free.**  Both bounds come off the depth match: the column is
at least as long as its dealt part and at most `15` cards longer. -/
theorem flute_match_cvFluteOf {g : Globals} {u : State} {d : Vector UInt8 10}
    (hd6 : ∀ i : Fin 10, (d.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(d.get i).toNat, hd6 i⟩)
    (i : Fin 10) (hpos : 0 < (d.get i).toNat) :
    (u.tableau i).length + 1 = (d.get i).toNat + ((cvFluteOf u d).get i).toNat := by
  have hle : (d.get i).toNat ≤ (u.tableau i).length := (hdm i).1
  have hb : (u.tableau i).length ≤ (d.get i).toNat + 15 := PileMatches.length_le (hdm i)
  rw [cvFluteOf_get, if_neg (by omega), UInt8.toNat_ofNat']
  omega

theorem cvFlutes_cvFluteOf {g : Globals} {u : State} {q : SolverPosType}
    (hd6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(q.pileDepth.get i).toNat, hd6 i⟩) :
    CvFlutes q (cvFluteOf u q.pileDepth) where
  pos := fun i => by
    rw [cvFluteOf_get]
    by_cases h0 : (q.pileDepth.get i).toNat = 0
    · rw [if_pos h0]; decide
    · have hle : (q.pileDepth.get i).toNat ≤ (u.tableau i).length := (hdm i).1
      have hb : (u.tableau i).length ≤ (q.pileDepth.get i).toNat + 15 :=
        PileMatches.length_le (hdm i)
      rw [if_neg h0, UInt8.toNat_ofNat']
      omega
  empty := fun i hi => by
    rw [cvFluteOf_get, if_pos (show (q.pileDepth.get i).toNat = 0 from by rw [hi]; rfl)]

/-- **A state matches at its own flutes.**  Everything but `flute_match` has to be
supplied; `flute_match` is `flute_match_cvFluteOf`. -/
theorem matches_cvFluteOf {g : Globals} {u : State} {q : SolverPosType}
    (hcount : ∀ c : Card, countState u c = 1)
    (hd6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(q.pileDepth.get i).toNat, hd6 i⟩)
    (hking : ∀ i : Fin 10, (q.pileDepth.get i).toNat = 0 →
      ∀ c ∈ (u.tableau i).getLast?,
        (u.tableau i).length + (VALUE (q.kings.get (finOfSuit c.suit))).toNat = 13)
    (haces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su)) :
    StateMatchesSolverPos g u (cvRelax q (cvFluteOf u q.pileDepth)) where
  cards_count := hcount
  depth_lt6 := hd6
  depth_match := hdm
  flute_match := fun i hi => flute_match_cvFluteOf hd6 hdm i hi
  king_pile := hking
  aces_match := haces

/-- The same at a configuration: `RealizesKingConfig` and `NoKingPile` read only the
depths and `kings`, so they are the position's flute-independent part. -/
theorem matchesKingConfig_cvFluteOf {g : Globals} {u : State} {q : SolverPosType} {k : Fin 16}
    (hcount : ∀ c : Card, countState u c = 1)
    (hd6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6)
    (hdm : ∀ i : Fin 10, PileMatches g (u.tableau i) i ⟨(q.pileDepth.get i).toNat, hd6 i⟩)
    (hking : ∀ i : Fin 10, (q.pileDepth.get i).toNat = 0 →
      ∀ c ∈ (u.tableau i).getLast?,
        (u.tableau i).length + (VALUE (q.kings.get (finOfSuit c.suit))).toNat = 13)
    (haces : ∀ su : Suit, q.aces.get (finOfSuit su) = encodeFoundation su (u.foundations su))
    (hreal : RealizesKingConfig u q k)
    (hnp : ∀ su : Suit, CfgBitSet k su → NoKingPile u q su) :
    StateMatchesKingConfig g u (cvRelax q (cvFluteOf u q.pileDepth)) k where
  toMatches := matches_cvFluteOf hcount hd6 hdm hking haces
  realizes := hreal
  no_pile := hnp

/-- **Re-fluting a match.**  A state matching *some* position matches every position with
the same depths, foundations and king frontiers — at its own flutes.  This is the shape
the obligations below are discharged in: the flutes never have to be mentioned, only the
three fields the solver actually computes. -/
theorem StateMatchesKingConfig.reflute {g : Globals} {u : State} {r q : SolverPosType}
    {k : Fin 16} (h : StateMatchesKingConfig g u r k)
    (hd : q.pileDepth = r.pileDepth) (ha : q.aces = r.aces) (hk : q.kings = r.kings) :
    StateMatchesKingConfig g u (cvRelax q (cvFluteOf u q.pileDepth)) k := by
  have hd6 : ∀ i : Fin 10, (q.pileDepth.get i).toNat < 6 := by
    intro i; rw [hd]; exact h.toMatches.depth_lt6 i
  have hd0 : ∀ i : Fin 10, q.pileDepth.get i = r.pileDepth.get i := by intro i; rw [hd]
  have hd0' : ∀ i : Fin 10, (q.pileDepth.get i).toNat = (r.pileDepth.get i).toNat :=
    fun i => congrArg UInt8.toNat (hd0 i)
  refine matchesKingConfig_cvFluteOf h.toMatches.cards_count hd6
    (fun i => PileMatches_of_val_eq (h.toMatches.depth_match i)
      (show (q.pileDepth.get i).toNat = (r.pileDepth.get i).toNat from hd0' i))
    (fun i hi c hc => ?_) (fun su => ?_) ?_ (fun su hsu i hi => ?_)
  · rw [hk]
    exact h.toMatches.king_pile i ((hd0' i).symm.trans hi) c hc
  · rw [ha]; exact h.toMatches.aces_match su
  · -- `RealizesKingConfig`, transported field by field
    obtain ⟨assign, hown, hinj, hiff⟩ := h.realizes
    refine ⟨assign, fun su i hs => ?_, hinj, hiff⟩
    obtain ⟨hz, hcases⟩ := hown su i hs
    refine ⟨(hd0' i).trans hz, ?_⟩
    rcases hcases with hphys | ⟨hnil, hking13⟩
    · exact Or.inl hphys
    · exact Or.inr ⟨hnil, by rw [hk]; exact hking13⟩
  · exact h.no_pile su hsu i ((hd0' i).symm.trans hi)

/-! ## What a caller has to know -/

/-- **The entry relation.**  The state `s` is one of the states *some* position stands
for, whose pile depths are the ones the query reports.  Nothing is said about that
position's flutes, foundations or king frontiers beyond what `s` itself determines:
they are `s`'s own, not the normalized ones `convertPre` computes.

This is what a caller can actually establish — for `pk = pilesKingsFromState s` the
depth vector *is* `|removeFlute (tableau i)|`, and the flutes are then the runs the
columns carry. -/
structure CvEntry (g : Globals) (pk : Vector UInt8 11) (s : State) (game' : SolverPosType)
    (k : Fin 16) : Prop where
  /-- The position's depths are the queried ones. -/
  depths : game'.pileDepth = cvDepths pk
  /-- And it is matched by `s`, at the configuration the query names.  Nothing is asked
      about its flutes: at a pile with a boundary they are forced (`flute_match`), and at
      a solver-empty pile they are never read — see `StateMatchesKingConfig.reflute`. -/
  cfg : StateMatchesKingConfig g s game' k
  /-- **A suit the configuration piles does not have its king in a cell.**

      This is what keeps loop 2's king-run completion inside the normalizing moves.  The
      completion drops the suit's freed run onto its pile, and a drop onto an *empty*
      column — which is what a king in a cell would call for — is invertible
      (`applyMove_cell_pile_inv`) but **not** a `NormStep`: `CPStep` demands
      `tableau q ≠ []`.  With the king out of the cells it is either already on the pile
      (so every drop lands on a non-empty column) or on a foundation / still a resident,
      and then `cvKingVal = 13` and there is nothing to drop at all.

      Stated negatively on purpose: no move loop 2 makes ever puts a card *into* a cell, so
      this survives the whole phase for free.  And for the query's own encoding it is
      immediate — `kingBit` fires exactly for a column that *is* a king run, so the king is
      sitting in that column. -/
  kingNotInCell : ∀ su : Suit, ¬ CfgBitSet k su →
    ∀ i : Fin 4, s.cells i ≠ some ⟨su, Rank.king⟩

/-! ## Obligation A: the prologue's writes are realized by moves

Loop 2 writes, for each suit, the maximal foundation the depth vector allows
(`aces = cvAceVal`) and the frontier of the freed king run (`kings = cvKingVal`).  Both
are claims about the *state*, and both are reached by normalizing moves:

* **foundations.**  The cards `A … cvAceVal` of a suit are all free, so none of them is
  a resident dealt card; each is therefore in a cell, on its foundation already, or
  inside a pile's run — and in a run its own predecessors sit *above* it, so playing
  the suit in ascending order always finds the next card exposed.
* **king piles.**  A card of the freed king run cannot sit above a non-empty pile's
  boundary (the run below it would end at a resident card of the same suit, which
  would then be free too), so it is in a cell or on the suit's king pile.  Dropping the
  ones in cells onto that pile — `KingAssemble`'s `kingPileEquiv` walk — completes it.
  For a suit whose bit is *set* the position's `kings` entry is not read by the matching
  at all, so nothing has to happen.

Neither kind of move changes a pile's boundary, so the depth vector — and with it `pk`
and the configuration `k` — is untouched; and both kinds are normalizing, so the entry
state stays equi-solvable.  The flutes do change (a foundation play shortens a run, a
drop lengthens one) but they need not be named: `cvFluteOf` reads them off the state the
moves produce, and `StateMatchesKingConfig.reflute` turns any match of `u` into this
one.  So what is to be proved is about the foundations and the king piles only. -/
def CvPrologueSim : Prop :=
  ∀ (g : Globals) (pk : Vector UInt8 11) (s : State) (game' : SolverPosType) (k : Fin 16),
    WellFormedLayout g → ValidDepths pk → CvEntry g pk s game' k →
    ∃ u : State, NormReach s u ∧
      StateMatchesKingConfig g u
        (cvRelax (convertPre g pk) (cvFluteOf u (convertPre g pk).pileDepth)) k

/-! ## Obligation B: one cleanup call, from a pile that already carries part of its flute

`SimulatesNorm.ofCleanupPile` is this statement with `fl[pile] = 1`: there the whole
freed-predecessor extension is fetched out of the cells, and the state's column grows by
all `f` of it.  Here the column already carries the first `fl[pile] - 1` extension cards
and only the rest is fetched.

Two things that the `fl[pile] = 1` proof gets for free have to be *derived* in the
general case, and both come out of the matching:

* the cards the column already carries are a **prefix** of the extension the solver
  walks — they are the run above the boundary, i.e. `B-1, B-2, …`, in that order;
* the walk does not stop short of them: each is free (it is not a resident of its own
  dealt pile) and above its suit's foundation top (it is on a column, so it is not on
  the foundation), which are exactly the two conditions of the extension loop.  Hence
  `fl[pile] - 1 ≤ f` and the number of cards still to drop is `f + 1 - fl[pile]`.

The other two branches move no card at all: the merge trades depth for flute inside the
dealt cards (`StateMatchesSolverPos.cleanupMerge`) and the lone-king vacate is a
reclassification (`cleanupVacate`), neither of which reads the entry flute. -/
def CvCleanupSim : Prop :=
  ∀ (g : Globals) (v : State) (q0 : SolverPosType) (fl : Vector UInt8 10) (kk : Fin 16)
    (pile : UInt32) (hpile : pile.toNat < 10) (fk : UInt16) (p' : SolverPosType),
    WellFormedLayout g → SolverInvBase g q0 →
    q0.pileFlute.get ⟨pile.toNat, hpile⟩ = 1 → CvFlutes q0 fl →
    StateMatchesKingConfig g v (cvRelax q0 fl) kk →
    EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p') →
    ∃ (v' : State) (k' : Fin 16) (FK : Finset Suit),
      SimulatesNorm g v (cvRelax q0 fl) kk v'
        (cvRelax p' (fl.set pile.toNat (p'.pileFlute.get ⟨pile.toNat, hpile⟩) hpile))
        k' FK fk

/-! ## The cleanup's flute frame

`solverCleanupPile_step` exports the depth frame but not the flute one, and the loop
invariant needs it: a pile the loop has already passed must keep the flute the state
agreed with it on. -/

/-- **`SolverCleanupPile pile` writes no flute but `pileFlute[pile]`.** -/
theorem cleanupPile_pileFlute_frame {g : Globals} {q0 : SolverPosType}
    (hwf : WellFormedLayout g) {pile : UInt32} (hpile : pile.toNat < 10)
    (hb : SolverInvBase g (fluteNorm pile hpile q0))
    {fk : UInt16} {p' : SolverPosType}
    (hrun : EStateM.run (_root_.SolverCleanupPile pile) (g, q0) = .ok fk (g, p'))
    (i : Fin 10) (hi : i.val ≠ pile.toNat) :
    p'.pileFlute.get i = q0.pileFlute.get i := by
  rcases cleanupPile_eq pile g q0 hpile hwf hb with
    ⟨hd0, hsd, hrunE⟩ | ⟨B, hs4, hd, hd1, hd5, hidx, hBdef, hBrange, hnfp, m, f,
      hm_le, hmcards, hmstop, hf_le, hf_le_tight, hffree, hfstop, hak, hbranch⟩
  · -- **Empty pile**: `pileFlute[pile] := 1`, nothing else
    injection hrun.symm.trans hrunE with h1 h2
    injection h2 with _hg hp'eq
    rw [hp'eq]
    show (q0.pileFlute.set pile.toNat 1 hpile)[i.val]'i.isLt = q0.pileFlute[i.val]'i.isLt
    exact Vector.getElem_set_ne hpile i.isLt (Ne.symm hi)
  · rcases hbranch with ⟨hnk, -, -, -, -, -, hrunE⟩ |
      ⟨hd1', K, hKdef, hVK13, hsuiteq, hKeq, -, -, -, -, -, hrunE⟩
    · -- **Ordinary**: the merge/extension write only `pileFlute[pile]`
      injection hrun.symm.trans hrunE with h1 h2
      injection h2 with _hg hp2
      rw [hp2]
      exact preCleanupPile_pileFlute_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile)
        hs4 q0 m f i hi
    · -- **Lone king**: and the vacate writes none
      injection hrun.symm.trans hrunE with h1 h2
      injection h2 with _hg hp2
      rw [hp2, kingMove_pileFlute_eq_of_ne pile hpile (SUIT B) hs4
        (pileHashes[pile.toNat]'hpile) _ i hi]
      exact preCleanupPile_pileFlute_eq_of_ne pile hpile B (pileHashes[pile.toNat]'hpile)
        hs4 q0 m f i hi

/-! ## Loop 3, from the state's own flutes

The `cvCleanupLoop_sim` induction, with the state's flute vector riding along: the piles
the loop has passed carry the flutes the solver computed for them, the ones it has not
carry whatever the state has.  At `j = 10` the two vectors agree, so the relaxed reading
*is* the solver's position and the drain can take over unchanged. -/

theorem cvCleanupLoop_lax (hB : CvCleanupSim) (g : Globals) (hwf : WellFormedLayout g)
    (s : State) (P : SolverPosType) (k : Fin 16) :
    ∀ (n j : Nat), j + n = 10 → ∀ (fk : UInt16) (q : SolverPosType) (fl : Vector UInt8 10),
      MergedUpTo g q j → CvFlutes q fl →
      (∀ i : Fin 10, i.val < j → fl.get i = q.pileFlute.get i) →
      MoveAcesSim g s P k fk (cvRelax q fl) →
      ∃ (fk' : UInt16) (q' : SolverPosType),
        forIn (List.range' j n) fk cvCleanupBody (g, q) = .ok fk' (g, q') ∧
        MergedUpTo g q' 10 ∧ MoveAcesSim g s P k fk' q' := by
  intro n
  induction n with
  | zero =>
    intro j hj fk q fl hq hfl hfld hP
    obtain rfl : j = 10 := by omega
    refine ⟨fk, q, rfl, hq, ?_⟩
    rwa [cvRelax_eq q (fun i => hfld i i.isLt)] at hP
  | succ n ih =>
    intro j hj fk q fl hq hfl hfld hP
    have hjlt : j < 10 := by omega
    have hpile : (UInt32.ofNat j).toNat < 10 := by rw [UInt32.toNat_ofNat']; omega
    have hpkn : (UInt32.ofNat j).toNat = j := by rw [UInt32.toNat_ofNat']; omega
    -- the solver's own step
    obtain ⟨fk0, q1, hrun1, hq1, hdframe⟩ := solverCleanupPile_step g q j hjlt hwf hq
    obtain ⟨hnf, -, -, hfluteRest⟩ := hq
    have hnf1 : SolverInvBase g q1 := hq1.1
    -- pile `j` has not been touched yet, so its flute is still the default
    have hfl1j : q.pileFlute.get ⟨(UInt32.ofNat j).toNat, hpile⟩ = 1 :=
      hfluteRest ⟨(UInt32.ofNat j).toNat, hpile⟩
        (show j ≤ (UInt32.ofNat j).toNat from le_of_eq hpkn.symm)
    have hfn : fluteNorm (UInt32.ofNat j) hpile q = q := fluteNorm_self _ hpile q hfl1j
    -- the state side: one relaxed cleanup step, chained onto what we already have
    obtain ⟨w, kk, FK, hsim⟩ := hP
    obtain ⟨w', kk', FK', hsim'⟩ :=
      hB g w q fl kk (UInt32.ofNat j) hpile fk0 q1 hwf hnf hfl1j hfl hsim.cfg hrun1
    -- the state's new flute vector
    set fl1 : Vector UInt8 10 :=
      fl.set (UInt32.ofNat j).toNat (q1.pileFlute.get ⟨(UInt32.ofNat j).toNat, hpile⟩) hpile
      with hfl1def
    have hfl1get : fl1.get ⟨(UInt32.ofNat j).toNat, hpile⟩
        = q1.pileFlute.get ⟨(UInt32.ofNat j).toNat, hpile⟩ := by
      rw [hfl1def]
      show (fl.set (UInt32.ofNat j).toNat _ hpile)[(UInt32.ofNat j).toNat]'hpile = _
      exact Vector.getElem_set_self hpile
    have hfl1ne : ∀ i : Fin 10, i.val ≠ (UInt32.ofNat j).toNat → fl1.get i = fl.get i := by
      intro i hi
      rw [hfl1def]
      show (fl.set (UInt32.ofNat j).toNat _ hpile)[i.val]'i.isLt = fl[i.val]'i.isLt
      exact Vector.getElem_set_ne hpile i.isLt (Ne.symm hi)
    -- it is still a legal flute vector, now for `q1`
    have hflNew : CvFlutes q1 fl1 := by
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · by_cases hij : i.val = (UInt32.ofNat j).toNat
        · rw [show i = ⟨(UInt32.ofNat j).toNat, hpile⟩ from Fin.ext hij, hfl1get]
          exact hnf1.flute_pos _
        · rw [hfl1ne i hij]; exact hfl.pos i
      · by_cases hij : i.val = (UInt32.ofNat j).toNat
        · rw [show i = ⟨(UInt32.ofNat j).toNat, hpile⟩ from Fin.ext hij] at hi ⊢
          rw [hfl1get]
          exact hnf1.flute_empty _ hi
        · rw [hfl1ne i hij]
          refine hfl.empty i ?_
          rw [← hdframe i (by rw [hpkn] at hij; exact hij)]
          exact hi
    -- and it agrees with the solver on every pile the loop has now passed
    have hfldNew : ∀ i : Fin 10, i.val < j + 1 → fl1.get i = q1.pileFlute.get i := by
      intro i hi
      by_cases hij : i.val = (UInt32.ofNat j).toNat
      · rw [show i = ⟨(UInt32.ofNat j).toNat, hpile⟩ from Fin.ext hij, hfl1get]
      · rw [hpkn] at hij
        rw [hfl1ne i (by rw [hpkn]; exact hij), hfld i (by omega),
          cleanupPile_pileFlute_frame hwf hpile (by rw [hfn]; exact hnf) hrun1 i
            (by rw [hpkn]; exact hij)]
    have hP1 : MoveAcesSim g s P k (fk &&& fk0) (cvRelax q1 fl1) :=
      ⟨w', kk', FK ∪ FK', hsim.trans hsim'⟩
    obtain ⟨fk', q', hrun', hq', hP'⟩ :=
      ih (j + 1) (by omega) (fk &&& fk0) q1 fl1 hq1 hflNew hfldNew hP1
    refine ⟨fk', q', ?_, hq', hP'⟩
    rw [List.range'_succ, List.forIn_cons]
    show (cvCleanupBody j fk >>= _) (g, q) = _
    simp only [bind, EStateM.bind, cvCleanupBody_run j fk fk0 g q q1 hrun1]
    exact hrun'

/-! ## The whole call -/

/-- **`SolverConvertFromPilesKings`, simulated from the entry state.**  The
`convert_simulates` of a caller that has *not* normalized: `s` need only match some
position with the queried depths, and the call's own moves — loop 2's foundation plays
and king-pile drops, loop 3's freed-predecessor drops, loop 4's drain — take it to a
state matching the canonical position the call returns. -/
theorem convert_simulates_lax (hA : CvPrologueSim) (hB : CvCleanupSim)
    (g : Globals) (hwf : WellFormedLayout g) (pk : Vector UInt8 11) (hpk : ValidDepths pk)
    (p0 : SolverPosType) (s : State) (game' : SolverPosType) (k : Fin 16)
    (hentry : CvEntry g pk s game' k) :
    ∃ (fk : UInt16) (p' : SolverPosType) (s' : State) (k' : Fin 16) (FK : Finset Suit),
      EStateM.run (_root_.SolverConvertFromPilesKings pk) (g, p0) = .ok fk (g, p') ∧
      IsCanonicalPos g p' ∧
      SimulatesNorm g s game' k s' p' k' FK fk := by
  have hcount : CvCountBound g pk := cvCountBound g hwf pk hpk
  -- loops 1 and 2: the solver reaches `convertPre`, the state catches up with its writes
  obtain ⟨u, hru, hmu⟩ := hA g pk s game' k hwf hpk hentry
  set fl : Vector UInt8 10 := cvFluteOf u (convertPre g pk).pileDepth with hfldef
  have hfl : CvFlutes (convertPre g pk) fl :=
    cvFlutes_cvFluteOf
      (show ∀ i : Fin 10, ((convertPre g pk).pileDepth.get i).toNat < 6 from
        hmu.toMatches.depth_lt6)
      (show ∀ i : Fin 10, PileMatches g (u.tableau i) i
          ⟨((convertPre g pk).pileDepth.get i).toNat, hmu.toMatches.depth_lt6 i⟩ from
        hmu.toMatches.depth_match)
  have hP0 : MoveAcesSim g s game' k 0xffff (cvRelax (convertPre g pk) fl) :=
    ⟨u, k, ∅, SimulatesNorm.ofNormReach hru hmu⟩
  -- loop 3
  obtain ⟨fk1, q1, hrun1, hq1, hP1⟩ :=
    cvCleanupLoop_lax hB g hwf s game' k 10 0 rfl 0xffff (convertPre g pk) fl
      (convertPre_mergedUpTo_zero g pk hwf hpk) hfl (fun i hi => absurd hi (by omega)) hP0
  have hmerged : SolverInvMerged g q1 := mergedUpTo_ten_iff.mp hq1
  -- loop 4
  obtain ⟨fk2, q2, hrun2, hcan, hP2⟩ := SimulatesNorm.drain hwf hmerged hP1
  obtain ⟨s', k', FK, hsim⟩ := hP2
  refine ⟨fk2, q2, s', k', FK, ?_, hcan, hsim⟩
  show _root_.SolverConvertFromPilesKings pk (g, p0) = _
  rw [convert_run_eq g hwf pk p0 hpk hcount]
  show (forIn (List.range 10) (0xffff : UInt16) cvCleanupBody >>= fun fk =>
      Loop.forIn Loop.mk fk drainBody >>= fun r => pure r) (g, convertPre g pk) = _
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    show List.range 10 = List.range' 0 10 from by rw [List.range_eq_range'], hrun1, hrun2]

/-- **`solve` is correct on the state it was asked about.**  `solve_correct` with its
matching hypothesis replaced by the entry relation: no normalization, no maximal
foundation, no run-free piles. -/
theorem solve_correct_lax (hA : CvPrologueSim) (hB : CvCleanupSim)
    {g g' : Globals} {pk : Vector UInt8 11} {s : State} {game' : SolverPosType} {r : UInt8}
    (hwf : WellFormedLayout g) (hcor : HashmapCorrect g) (hpk : ValidDepths pk)
    (hs10 : (pk.get ⟨10, by omega⟩).toNat < 16)
    (hentry : CvEntry g pk s game' (kingCfgOf pk hs10))
    (hrun : EStateM.run (_root_.solve pk) g = .ok r g') :
    (HashmapCorrect g' ∧ ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }) ∧
    ((r = UInt8.ofNat NOMOVE ∧ ¬ isSolvable s) ∨ (r = UInt8.ofNat SUCCESS ∧ isSolvable s)) := by
  obtain ⟨fk, p, v, k', FK, hrunC, hcan, hsim⟩ :=
    convert_simulates_lax hA hB g hwf pk hpk emptySolverPosType s game' (kingCfgOf pk hs10)
      hentry
  have hrun' : _root_.solve pk g = .ok r g' := hrun
  rw [solve_eq_explicit pk] at hrun'
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hrunC,
    set, EStateM.set] at hrun'
  exact solveTail_correct hwf hcor hcan hs10 hsim hrun'

end SolverSpec
