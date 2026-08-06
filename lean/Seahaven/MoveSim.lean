import Seahaven.SolvableBits
import Seahaven.SolverSpecMove

/-!
# Simulating one `SolverMove`, part 1: the flute move

`SolverMove pile toPile` is three phases:

1. **destination bookkeeping** (`moveDestPre`: the flute merge / `kings` /
   `usedSpace` write) followed by `SolverRemoveFlute`'s own preamble
   (`removeFlutePre`: `pileDepth[pile] -= 1`, `hash -= pileHashes[pile]`) and the
   flute reset `pileFlute[pile] := 1` (`fluteNorm`);
2. `SolverCleanupPile pile` — merge the newly exposed run, absorb freed
   predecessors, vacate a lone king;
3. the `busyAces` drain — `SolverMoveAces` until no suit is pending.

This file does **phase 1**, on the `Rules` side, for all four solver
destinations.  Two of them land on a column — a genuine pile, and a king pile that
physically sits on an empty column — and are realized by `fluteMoves`: park the
`L-1` cards above the boundary into cells, move the boundary card, drop the parked
cards back.  The other two put the whole flute in the cells — `EXTRA`, and a king
pile whose stack is in the cells rather than on a column — and are realized by
`parkMoves` alone, costing one cell more.  In each case the theorem is that the
resulting concrete state matches the abstract position phase 1 computes.

Phase 1 is exactly the part that has a *pure* `Rules` counterpart: it moves cards
without touching foundations, and the abstract position it produces is generally
**not** canonical (the destination flute is un-merged, `pile`'s own flute is the
trivial `1` even though a run may now be exposed).  That is fine — matching
(`StateMatchesSolverPos`) is deliberately insensitive to canonicity.

Phases 2 and 3 are `CPStep`/`PlaysAll` work and are not in this file.

Two preconditions are assumed here and discharged by the caller, i.e. by
`solverRecCheckSolvable`'s pile loop:

* the source pile is non-empty — the loop `continue`s on `pileDepth[pile] == 0`.
  It appears here as `hrest : |rest| + 1 = pileDepth[pile]`, which is also what
  `flute_split` needs, so no separate hypothesis is required;
* the move is affordable — enough free cells for the flute, which is what
  `solverGetMovable` decides.  See the free-cell discussion at "Phase 1, end to
  end" below.
-/

/-! ## Reachability preserves the card count -/

theorem countState_of_reach {s t : State} (h : Reach s t) : countState t = countState s := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => obtain ⟨m, hm⟩ := hbc; rw [← movePreservesCards _ m _ hm]; exact ih

/-! ## `PileMatches` under the two column edits a flute move performs -/

/-- `getLast?` of a column with a run dropped on top of it: the deepest card is
unchanged unless the column was empty, in which case it is the boundary card. -/
theorem getLast?_append_cons (l : List Card) (c : Card) (r : List Card) :
    (l ++ c :: r).getLast? = some (r.getLast?.getD c) := by
  rw [List.getLast?_append, show c :: r = [c] ++ r from rfl, List.getLast?_append]
  cases r.getLast? <;> simp

/-- **Dropping a whole run onto a column preserves `PileMatches`** with the same
depth.  Iterated `PileMatches_cons`; the `IsRun` hypothesis supplies the
`dropCol` guard at each intermediate step, and `hdst` supplies it for the
boundary card itself. -/
theorem PileMatches_append_run {g : Globals} {col : Column} {p : Fin 10} {n : Fin 6}
    {l : List Card} {c : Card}
    (hm : PileMatches g col p n) (hrun : IsRun (l ++ [c]))
    (hdst : col.head? = nextCard c) :
    PileMatches g (l ++ c :: col) p n := by
  induction l with
  | nil => exact PileMatches_cons hm hdst
  | cons x xs ih =>
    simp only [List.cons_append] at hrun ⊢
    refine PileMatches_cons (ih hrun.tail) ?_
    obtain ⟨y, hy⟩ : ∃ y, (xs ++ [c]).head? = some y := by
      cases h : xs ++ [c] with
      | nil => simp at h
      | cons y ys => exact ⟨y, by simp⟩
    rw [head?_append_cons, hy]
    exact (hrun.head y (Option.mem_def.2 hy)).symm

/-- **A bottom segment of a matching column matches at its own depth.**  Removing
the flute *and* the boundary card from a pile leaves the dealt cards below, which
match with the (smaller) depth and a trivial flute. -/
theorem PileMatches_of_suffix {g : Globals} {col : Column} {p : Fin 10} {n m : Fin 6}
    {pre rest : Column}
    (hm : PileMatches g col p n) (hcol : col = pre ++ rest)
    (hlen : rest.length = m.val) (hle : m.val ≤ n.val) :
    PileMatches g rest p m := by
  obtain ⟨_, hbot, _⟩ := hm
  refine ⟨by omega, ?_, ?_⟩
  · intro k
    have hkr : k.val < rest.reverse.length := by
      rw [List.length_reverse]; omega
    have hk := hbot ⟨k.val, by omega⟩
    rw [hcol, List.reverse_append, List.getElem?_append_left hkr] at hk
    exact hk
  · have hnil : rest.reverse.drop m.val = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_reverse]; omega)
    simp only [hnil, List.map_nil]
    split_ifs
    · exact fun i => i.elim0
    · exact ⟨0, fun i => i.elim0⟩

/-! ## The abstract effect of phase 1 -/

/-- The deepest card of pile `b` once a flute headed by boundary card `c` has
landed on it: `c` itself if `b` was empty, otherwise `b`'s own deepest card. -/
def stackBottom (c : Card) (col : Column) : Card := col.getLast?.getD c

/-- **What phase 1 of `SolverMove a → b` does to the abstract position**, stated
as the field equations `StateMatchesSolverPos` actually reads, and only those.

`fl` is the flute length (`= |top| + 1`).  Both column destinations satisfy this:

* a genuine pile (`toPile < 10`) merges the flutes — `flute_dst` — and leaves
  `kings` alone, so `kings_ne`/`kings_dst` hold trivially (`b` has positive depth,
  making `kings_dst` vacuous);
* a king pile (`10 ≤ toPile < 14`) sitting on the empty column `b` charges
  `kings[su] -= fl` — `kings_dst` — and `flute_dst` is vacuous.

`aces` is untouched in both, which is why phase 1 needs no foundation move.  Note
what is *not* mentioned: `usedSpace`, `freePiles`, `busyAces`, `hash`.  Matching
does not read them; the invariant side (`SolverSpecMove`) is where they are
accounted for. -/
structure FluteMoveAbs (s : State) (c : Card) (p q : SolverPosType) (a b : Fin 10)
    (fl : Nat) : Prop where
  /-- The source pile loses its boundary card. -/
  depth_src : (q.pileDepth.get a).toNat + 1 = (p.pileDepth.get a).toNat
  /-- No other depth changes. -/
  depth_ne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i
  /-- The source flute is reset (`fluteNorm`); the run cleanup would expose is
      only recognized in phase 2. -/
  flute_src : (q.pileFlute.get a).toNat = 1
  /-- A pile destination absorbs the flute. -/
  flute_dst : 0 < (p.pileDepth.get b).toNat →
      (q.pileFlute.get b).toNat = (p.pileFlute.get b).toNat + fl
  /-- No other flute changes. -/
  flute_ne : ∀ i : Fin 10, i ≠ a → i ≠ b → q.pileFlute.get i = p.pileFlute.get i
  /-- Foundations are untouched. -/
  aces : q.aces = p.aces
  /-- Every *other* suit's king frontier is untouched — i.e. `b` really is the
      pile carrying the suit whose frontier moves. -/
  kings_ne : ∀ i : Fin 10, i ≠ b → (p.pileDepth.get i).toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit)
  /-- A king-pile destination advances that suit's frontier by the flute length. -/
  kings_dst : (p.pileDepth.get b).toNat = 0 →
      (VALUE (q.kings.get (finOfSuit (stackBottom c (s.tableau b)).suit))).toNat + fl
        = (VALUE (p.kings.get (finOfSuit (stackBottom c (s.tableau b)).suit))).toNat
  /-- Landing on a genuinely empty column means the suit had freed nothing yet,
      so `c` is its king. -/
  kings_empty : (p.pileDepth.get b).toNat = 0 → s.tableau b = [] →
      (VALUE (p.kings.get (finOfSuit c.suit))).toNat = 13

/-! ## The flute length a matching state exhibits -/

/-- The physical run above a pile's boundary card is `pileFlute - 1` long.  Lets a
caller phrase `FluteMoveAbs`'s `fl` as the solver's `pileFlute[a]`. -/
theorem StateMatchesSolverPos.flute_len {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (a : Fin 10) {top rest : Column} {c : Card}
    (hcol : s.tableau a = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get a).toNat) :
    (p.pileFlute.get a).toNat = top.length + 1 := by
  have hd : 0 < (p.pileDepth.get a).toInt.toNat := by
    simp only [UInt8.toInt_toNat]; omega
  have hfm := h.flute_match a hd
  rw [hcol] at hfm
  simp only [UInt8.toInt_toNat, List.length_append, List.length_cons] at hfm
  omega

/-! ## Phase 1, realized -/

/-- **One abstract flute move is simulated by `fluteMoves`.**

Given a state `s` matching `p`, a split of the source pile into flute / boundary
card / dealt remainder, enough free cells to park the flute, and a destination
column that accepts the boundary card, the `2·fl - 1` concrete moves run and land
in a state matching the abstract successor position.

The three hypotheses about `s` beyond matching — `hcol`, `hrest`, `hrun` — are
exactly what `StateMatchesSolverPos.flute_split` provides, and `cells.length =
|top|` is `pileFlute[a] - 1` free cells (`flute_len`). -/
theorem StateMatchesSolverPos.fluteMove {g : Globals} {s : State} {p q : SolverPosType}
    {a b : Fin 10} {top rest : Column} {c : Card} {cells : List (Fin 4)}
    (h : StateMatchesSolverPos g s p)
    (hab : a ≠ b)
    (hcol : s.tableau a = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get a).toNat)
    (hrun : IsRun (top ++ [c]))
    (hlen : cells.length = top.length)
    (hnd : cells.Nodup)
    (hfree : ∀ i ∈ cells, s.cells i = none)
    (hdst : (s.tableau b).head? = nextCard c)
    (habs : FluteMoveAbs s c p q a b (top.length + 1)) :
    ∃ v : State, List.foldl applyMoveOpt (some s) (fluteMoves a b cells) = some v ∧
      StateMatchesSolverPos g v q := by
  obtain ⟨v, hfold, hva, hvb, hvo, hvcells, hvf⟩ :=
    run_fluteMoves hab hcol hrun hlen hnd hfree hdst
  refine ⟨v, hfold, ?_⟩
  have hba : b ≠ a := Ne.symm hab
  -- `q`'s depth at `a` is exactly what is left below the boundary card.
  have hqa : (q.pileDepth.get a).toNat = rest.length := by
    have := habs.depth_src; omega
  have hlt6 : ∀ i : Fin 10, (q.pileDepth.get i).toInt.toNat < 6 := by
    intro i
    by_cases hi : i = a
    · subst hi
      have h6 := h.depth_lt6 i
      simp only [UInt8.toInt_toNat] at h6 ⊢
      omega
    · rw [habs.depth_ne i hi]; exact h.depth_lt6 i
  -- The index conversion used at every pile other than `a`.
  have hidx : ∀ i : Fin 10, i ≠ a →
      (⟨(q.pileDepth.get i).toInt.toNat, hlt6 i⟩ : Fin 6)
        = ⟨(p.pileDepth.get i).toInt.toNat, h.depth_lt6 i⟩ :=
    fun i hi => by
      have hdeq : q.pileDepth.get i = p.pileDepth.get i := habs.depth_ne i hi
      simp only [hdeq]
  refine ⟨?_, hlt6, ?_, ?_, ?_, ?_⟩
  · -- cards_count: legal moves conserve cards.
    intro d
    rw [congrFun (countState_of_reach (reach_fluteMoves hfold)) d]
    exact h.cards_count d
  · -- depth_match
    intro i
    by_cases hia : i = a
    · subst hia
      rw [hva]
      refine PileMatches_of_suffix (h.depth_match i) (pre := top ++ [c]) ?_ ?_ ?_
      · rw [hcol]; simp
      · simp only [UInt8.toInt_toNat]; omega
      · simp only [UInt8.toInt_toNat]; omega
    · by_cases hib : i = b
      · subst hib
        rw [hvb, hidx i hia]
        exact PileMatches_append_run (h.depth_match i) hrun hdst
      · rw [hvo i hia hib, hidx i hia]
        exact h.depth_match i
  · -- flute_match
    intro i hdi
    by_cases hia : i = a
    · subst hia
      rw [hva]
      simp only [UInt8.toInt_toNat] at hdi ⊢
      rw [habs.flute_src]
      omega
    · by_cases hib : i = b
      · subst hib
        simp only [UInt8.toInt_toNat] at hdi ⊢
        rw [habs.depth_ne i hia] at hdi ⊢
        have hfm := h.flute_match i (by simp only [UInt8.toInt_toNat]; exact hdi)
        simp only [UInt8.toInt_toNat] at hfm
        rw [habs.flute_dst hdi, hvb]
        simp only [List.length_append, List.length_cons]
        omega
      · rw [hvo i hia hib, habs.depth_ne i hia, habs.flute_ne i hia hib]
        exact h.flute_match i (by rw [habs.depth_ne i hia] at hdi; exact hdi)
  · -- king_pile
    intro i hdi
    simp only [UInt8.toInt_toNat] at hdi
    by_cases hia : i = a
    · -- the source pile is empty only if nothing was left below the boundary
      subst hia
      have hrnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hva, hrnil]
      simp
    · by_cases hib : i = b
      · subst hib
        rw [habs.depth_ne i hia] at hdi
        intro d hd
        rw [hvb, getLast?_append_cons] at hd
        have hdeq : d = stackBottom c (s.tableau i) :=
          (Option.some.inj (Option.mem_def.1 hd)).symm
        subst hdeq
        have hkd := habs.kings_dst hdi
        rw [hvb]
        simp only [List.length_append, List.length_cons]
        cases hlast : (s.tableau i).getLast? with
        | none =>
          have hnil : s.tableau i = [] := by
            rcases hnil' : s.tableau i with _ | ⟨x, xs⟩
            · rfl
            · rw [hnil'] at hlast; simp at hlast
          have hsb : stackBottom c (s.tableau i) = c := by
            simp only [stackBottom, hlast]; rfl
          rw [hsb] at hkd ⊢
          have h13 := habs.kings_empty hdi hnil
          rw [hnil]
          simp only [List.length_nil]
          omega
        | some e =>
          have hsb : stackBottom c (s.tableau i) = e := by
            simp only [stackBottom, hlast]; rfl
          rw [hsb] at hkd ⊢
          have hkp := h.king_pile i (by simp only [UInt8.toInt_toNat]; exact hdi) e
            (Option.mem_def.2 hlast)
          omega
      · rw [habs.depth_ne i hia] at hdi
        rw [hvo i hia hib]
        intro d hd
        rw [habs.kings_ne i hib hdi d hd]
        exact h.king_pile i (by simp only [UInt8.toInt_toNat]; exact hdi) d hd
  · -- aces_match
    intro su
    rw [habs.aces, hvf]
    exact h.aces_match su


/-! ## Instantiating at the real solver functions

`SolverMove`'s phase 1 is the composition `fluteNorm ∘ removeFlutePre ∘
moveDestPre` — the state at which `removeFlute_merged` and the `cleanupPile`
specs are stated, i.e. exactly the point where phase 1 hands over to phase 2. -/

/-- `Vector.get` at an explicit index, as `getElem` — the form the `Vector.set`
lemmas are stated in. -/
private theorem vget_eq {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) :
    v.get ⟨i, hi⟩ = v[i]'hi := rfl

namespace SolverSpec

/-- **Phase 1 of `SolverMove pile toPile`, as a pure state transform.**
Destination bookkeeping, then `SolverRemoveFlute`'s own depth/hash decrement,
then the source flute reset. -/
def movePre (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) : SolverPosType :=
  fluteNorm pile hpile (removeFlutePre pile hpile (moveDestPre pile toPile hpile p))

/-! ### The fields of `movePre`

Stated per field so that the simulation proofs never unfold the composition. -/

/-- The destination write touches neither depths nor foundations. -/
theorem moveDestPre_depth_aces (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) :
    (moveDestPre pile toPile hpile p).pileDepth = p.pileDepth ∧
      (moveDestPre pile toPile hpile p).aces = p.aces := by
  unfold moveDestPre
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem movePre_pileDepth (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) :
    (movePre pile toPile hpile p).pileDepth
      = p.pileDepth.set pile.toNat ((p.pileDepth[pile.toNat]'hpile) - 1) hpile := by
  show ((moveDestPre pile toPile hpile p).pileDepth.set pile.toNat _ hpile) = _
  rw [(moveDestPre_depth_aces pile toPile hpile p).1]

theorem movePre_aces (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) : (movePre pile toPile hpile p).aces = p.aces :=
  (moveDestPre_depth_aces pile toPile hpile p).2

theorem movePre_depth_self (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) :
    (movePre pile toPile hpile p).pileDepth.get ⟨pile.toNat, hpile⟩
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩) - 1 := by
  rw [vget_eq, movePre_pileDepth, Vector.getElem_set_self hpile]
  rfl

theorem movePre_depth_ne (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) (i : Fin 10) (hi : i.val ≠ pile.toNat) :
    (movePre pile toPile hpile p).pileDepth.get i = p.pileDepth.get i := by
  show (movePre pile toPile hpile p).pileDepth[i.val] = p.pileDepth[i.val]
  rw [movePre_pileDepth, Vector.getElem_set_ne hpile i.isLt (Ne.symm hi)]

/-- Pile-to-pile: the destination flute absorbs the source's, then the source
flute is reset. -/
theorem movePre_pileFlute_lt10 (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : toPile.toNat < 10) (p : SolverPosType) :
    (movePre pile toPile hpile p).pileFlute
      = (p.pileFlute.set toPile.toNat
          ((p.pileFlute[toPile.toNat]'h10) + (p.pileFlute[pile.toNat]'hpile)) h10).set
          pile.toNat 1 hpile := by
  show ((moveDestPre pile toPile hpile p).pileFlute.set pile.toNat 1 hpile) = _
  unfold moveDestPre
  rw [dif_pos h10]

/-- King pile or `EXTRA`: only the source flute is reset. -/
theorem movePre_pileFlute_ge10 (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (p : SolverPosType) :
    (movePre pile toPile hpile p).pileFlute = p.pileFlute.set pile.toNat 1 hpile := by
  show ((moveDestPre pile toPile hpile p).pileFlute.set pile.toNat 1 hpile) = _
  unfold moveDestPre
  rw [dif_neg h10]
  split_ifs <;> rfl

theorem movePre_flute_self (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) :
    (movePre pile toPile hpile p).pileFlute.get ⟨pile.toNat, hpile⟩ = 1 := by
  rw [vget_eq]
  by_cases h10 : toPile.toNat < 10
  · rw [movePre_pileFlute_lt10 pile toPile hpile h10 p, Vector.getElem_set_self hpile]
  · rw [movePre_pileFlute_ge10 pile toPile hpile h10 p, Vector.getElem_set_self hpile]

/-- Pile-to-pile, at the destination. -/
theorem movePre_flute_dst (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : toPile.toNat < 10) (hne : pile.toNat ≠ toPile.toNat) (p : SolverPosType) :
    (movePre pile toPile hpile p).pileFlute.get ⟨toPile.toNat, h10⟩
      = (p.pileFlute.get ⟨toPile.toNat, h10⟩) + (p.pileFlute.get ⟨pile.toNat, hpile⟩) := by
  rw [vget_eq, movePre_pileFlute_lt10 pile toPile hpile h10 p,
    Vector.getElem_set_ne hpile h10 hne, Vector.getElem_set_self h10]
  rfl

theorem movePre_flute_ne_lt10 (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : toPile.toNat < 10) (p : SolverPosType) (i : Fin 10)
    (hia : i.val ≠ pile.toNat) (hib : i.val ≠ toPile.toNat) :
    (movePre pile toPile hpile p).pileFlute.get i = p.pileFlute.get i := by
  show (movePre pile toPile hpile p).pileFlute[i.val] = p.pileFlute[i.val]
  rw [movePre_pileFlute_lt10 pile toPile hpile h10 p,
    Vector.getElem_set_ne hpile i.isLt (Ne.symm hia),
    Vector.getElem_set_ne h10 i.isLt (Ne.symm hib)]

theorem movePre_flute_ne_ge10 (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (p : SolverPosType) (i : Fin 10) (hia : i.val ≠ pile.toNat) :
    (movePre pile toPile hpile p).pileFlute.get i = p.pileFlute.get i := by
  show (movePre pile toPile hpile p).pileFlute[i.val] = p.pileFlute[i.val]
  rw [movePre_pileFlute_ge10 pile toPile hpile h10 p,
    Vector.getElem_set_ne hpile i.isLt (Ne.symm hia)]

/-- Pile-to-pile and `EXTRA` leave the king frontiers alone. -/
theorem movePre_kings_of_not_king (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (p : SolverPosType) (hnk : toPile.toNat < 10 ∨ ¬ toPile.toNat < 14) :
    (movePre pile toPile hpile p).kings = p.kings := by
  show (moveDestPre pile toPile hpile p).kings = p.kings
  unfold moveDestPre
  rcases hnk with h10 | h14
  · rw [dif_pos h10]
  · rw [dif_neg (by omega), dif_neg h14]

/-- The king-pile branch advances one suit's frontier by the flute length. -/
theorem movePre_kings_kingDest (pile : UInt32) (toPile : UInt8) (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14) (p : SolverPosType) :
    (movePre pile toPile hpile p).kings
      = p.kings.set (toPile.toNat - 10)
          ((p.kings[toPile.toNat - 10]'(by omega)) - (p.pileFlute[pile.toNat]'hpile))
          (by omega) := by
  show (moveDestPre pile toPile hpile p).kings = _
  unfold moveDestPre
  rw [dif_neg h10, dif_pos h14]

end SolverSpec

/-- `x - 1` counts down by one on `UInt8` when `x ≠ 0`. -/
private theorem uint8_sub_one_toNat {x : UInt8} (h : 1 ≤ x.toNat) :
    (x - 1).toNat + 1 = x.toNat := by
  have hle : (1 : UInt8) ≤ x := by
    rw [UInt8.le_iff_toNat_le]; simpa using h
  rw [UInt8.toNat_sub_of_le _ _ hle]
  simp only [show (1 : UInt8).toNat = 1 from rfl]
  omega

/-- Subtracting within the value nibble does not borrow from the suit nibble. -/
private theorem VALUE_sub_toNat {k f : UInt8} (h : f.toNat ≤ (VALUE k).toNat) :
    (VALUE (k - f)).toNat + f.toNat = (VALUE k).toNat := by
  have hv := VALUE_toNat k
  have hle : f ≤ k := by
    rw [UInt8.le_iff_toNat_le]
    have := Nat.mod_le k.toNat 16
    omega
  rw [VALUE_toNat, UInt8.toNat_sub_of_le _ _ hle]
  omega

/-! ### Destination is a genuine pile -/

/-- **The pile-to-pile branch of phase 1 satisfies `FluteMoveAbs`.**  `hsum` (the
merged flute does not wrap `UInt8`) is what `SolverInvBase.flute_le_value` gives:
each flute is at most `13`. -/
theorem fluteMoveAbs_pileDest {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10)
    (hne : pile.toNat ≠ toPile.toNat) {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hdb : 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hsum : (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
              + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256) :
    FluteMoveAbs s c p (SolverSpec.movePre pile toPile hpile p)
      ⟨pile.toNat, hpile⟩ ⟨toPile.toNat, h10⟩ (top.length + 1) := by
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  refine ⟨?_, ?_, ?_, ?_, ?_, SolverSpec.movePre_aces .., ?_, ?_, ?_⟩
  · rw [SolverSpec.movePre_depth_self]
    exact uint8_sub_one_toNat (by omega)
  · exact fun i hi => SolverSpec.movePre_depth_ne _ _ _ _ i (fun hc => hi (Fin.ext hc))
  · rw [SolverSpec.movePre_flute_self]; rfl
  · intro _
    rw [SolverSpec.movePre_flute_dst pile toPile hpile h10 hne, UInt8.toNat_add, ← hfl]
    exact Nat.mod_eq_of_lt hsum
  · exact fun i hia hib => SolverSpec.movePre_flute_ne_lt10 _ _ _ h10 _ i
      (fun hc => hia (Fin.ext hc)) (fun hc => hib (Fin.ext hc))
  · intro i _ _ d _
    rw [SolverSpec.movePre_kings_of_not_king _ _ _ _ (Or.inl h10)]
  · intro hz; omega
  · intro hz; omega

/-! ### Destination is a king pile sitting on an empty column -/

theorem suitToNat_inj {su su' : Suit} (h : suitToNat su = suitToNat su') : su = su' := by
  rw [← natToSuit_suitToNat su, ← natToSuit_suitToNat su']
  congr 1
  exact Fin.ext h

/-- **No two solver-empty piles carry the same suit's king stack.**  Either `b`
already shows that suit's king as its deepest card — and a card is in one pile
only — or the king is still somewhere with positive depth, so no empty pile can
hold it. -/
theorem StateMatchesSolverPos.empty_pile_owner {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {b : Fin 10} {su : Suit}
    (hdb : (p.pileDepth.get b).toInt.toNat = 0)
    (hown : (∃ e ∈ (s.tableau b).getLast?, e.suit = su) ∨
      (∃ j : Fin 10, 0 < (p.pileDepth.get j).toInt.toNat ∧
        ({ suit := su, rank := Rank.king } : Card) ∈ s.tableau j)) :
    ∀ i : Fin 10, i ≠ b → (p.pileDepth.get i).toInt.toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?, d.suit ≠ su := by
  intro i hib hdi d hd hsuit
  have hdlast : (s.tableau i).getLast? = some d := Option.mem_def.1 hd
  rcases hown with ⟨e, he, hesuit⟩ | ⟨j, hdj, hmem⟩
  · exact hib (h.empty_pile_unique hdi hdb hdlast (Option.mem_def.1 he) (by rw [hsuit, hesuit]))
  · have hdeq : d = ({ suit := su, rank := Rank.king } : Card) :=
      Card.ext hsuit (h.empty_pile_king i hdi hdlast)
    have hij : i = j :=
      h.noDup.pile_unique (hdeq ▸ List.mem_of_getLast? hdlast) hmem
    rw [hij] at hdi
    omega

/-- **The king-pile branch of phase 1 satisfies `FluteMoveAbs`.**

`hown` (`OwnsPile s p c.suit b`) is what `StateMatchesKingConfig.owns` hands over
for a suit whose configuration bit is clear:
column `b` is the one carrying `c.suit`'s freed king run — or is genuinely empty
because nothing of the suit is freed yet.  `hsu` is the solver's own choice of
destination (`solverGetDestination` returns `KINGPILE + SUIT B`), and `hval` is
`king_frontier`: the frontier is at least a whole flute above the foundation. -/
theorem fluteMoveAbs_kingDest {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {b : Fin 10} {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hdst : (s.tableau b).head? = nextCard c)
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hown : OwnsPile s p c.suit b)
    (hval : top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    FluteMoveAbs s c p (SolverSpec.movePre pile toPile hpile p)
      ⟨pile.toNat, hpile⟩ b (top.length + 1) := by
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  obtain ⟨hdb, hstack⟩ := hown
  have hdb' : (p.pileDepth.get b).toNat = 0 := hdb
  have hkings := SolverSpec.movePre_kings_kingDest pile toPile hpile h10 h14 p
  -- The suit whose frontier moves is `c`'s, whichever card ends up deepest.
  have hsbsuit : (stackBottom c (s.tableau b)).suit = c.suit := by
    cases hlast : (s.tableau b).getLast? with
    | none => simp only [stackBottom, hlast]; rfl
    | some e =>
      simp only [stackBottom, hlast]
      rcases hstack with ⟨e', he', hsuit', _⟩ | ⟨hnil, _⟩
      · rw [Option.mem_def, hlast] at he'
        rw [Option.some.inj he']
        exact hsuit'
      · rw [hnil] at hlast; simp at hlast
  -- `hval` in `UInt8` form: the flute fits below the frontier.
  have hvalu : (p.pileFlute[pile.toNat]'hpile).toNat
      ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat := by
    rw [show (p.pileFlute[pile.toNat]'hpile) = p.pileFlute.get ⟨pile.toNat, hpile⟩ from rfl, hfl]
    exact hval
  refine ⟨?_, ?_, ?_, ?_, ?_, SolverSpec.movePre_aces .., ?_, ?_, ?_⟩
  · rw [SolverSpec.movePre_depth_self]
    exact uint8_sub_one_toNat (by omega)
  · exact fun i hi => SolverSpec.movePre_depth_ne _ _ _ _ i (fun hc => hi (Fin.ext hc))
  · rw [SolverSpec.movePre_flute_self]; rfl
  · intro hz; omega
  · exact fun i hia _ => SolverSpec.movePre_flute_ne_ge10 _ _ _ h10 _ i
      (fun hc => hia (Fin.ext hc))
  · -- every other empty pile keeps its own suit's frontier
    intro i hib _ d hd
    have hne : d.suit ≠ c.suit := by
      refine h.empty_pile_owner (b := b) hdb ?_ i hib (by
        show (p.pileDepth.get i).toInt.toNat = 0
        simpa using ‹(p.pileDepth.get i).toNat = 0›) d hd
      rcases hstack with ⟨e', he', hsuit', _⟩ | ⟨hnil, _⟩
      · exact Or.inl ⟨e', he', hsuit'⟩
      · refine Or.inr ⟨⟨pile.toNat, hpile⟩, by simpa using (by omega : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat), ?_⟩
        have hck : c.rank = Rank.king := by
          rw [hnil] at hdst
          exact rankInj _ _ (by rw [nextCard_none_rank (by simpa using hdst.symm)]; rfl)
        have hceq : ({ suit := c.suit, rank := Rank.king } : Card) = c :=
          Card.ext rfl hck.symm
        rw [hceq, hcol]
        simp
    rw [vget_eq, hkings, Vector.getElem_set _ (finOfSuit d.suit).isLt,
      if_neg (by rw [hsu]; exact fun hc => hne (suitToNat_inj hc.symm))]
    rfl
  · -- the destination suit's frontier drops by the flute length
    intro _
    have hidx4 : finOfSuit c.suit = (⟨toPile.toNat - 10, by omega⟩ : Fin 4) := Fin.ext hsu.symm
    have hflu : top.length + 1 = (p.pileFlute[pile.toNat]'hpile).toNat := by
      rw [show (p.pileFlute[pile.toNat]'hpile) = p.pileFlute.get ⟨pile.toNat, hpile⟩ from rfl, hfl]
    rw [hsbsuit, hidx4, hflu]
    simp only [vget_eq, hkings, Vector.getElem_set_self]
    exact VALUE_sub_toNat (by rw [hidx4] at hvalu; simpa only [vget_eq] using hvalu)
  · -- landing on a genuinely empty column: nothing of the suit is freed yet
    intro _ hnil
    rcases hstack with ⟨e', he', _⟩ | ⟨_, h13⟩
    · rw [Option.mem_def, hnil] at he'; simp at he'
    · exact h13

/-! ## Phase 1, end to end

The shape the move-simulation obligation (`MoveSimulated`) consumes: from a state
matching `p`, the concrete moves run, are legal (`Reach`), and land in a state
matching the position phase 1 of `SolverMove` computes.  Here for the two column
destinations; `movePre_extra`/`movePre_kingCells` below are the cell ones.

**The free-cell budget.**  These take the affordability condition in the solver's
own terms — `pileFlute[pile]` against the number of free cells — and pick the cells
themselves, since which ones are used is immaterial:

* a column destination needs `pileFlute[pile] - 1` cells (the boundary card goes
  onto the destination column, the rest are parked and unparked);
* a cell destination needs `pileFlute[pile]` cells (the boundary card is parked
  too).

That is exactly what `solverGetMovable` decides — `possibleKings[fluteLen - 1]`
versus `possibleKings[fluteLen]` — so this hypothesis is where its (unwritten)
spec will plug in.  `flute_len` is what turns the solver's `pileFlute[pile]` into
the physical run length `|top| + 1` that `fluteMoves`/`parkMoves` consume. -/

/-- **Pile-to-pile.** -/
theorem StateMatchesSolverPos.movePre_pileDest {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10)
    (hne : pile.toNat ≠ toPile.toNat) {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcells : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hdst : (s.tableau ⟨toPile.toNat, h10⟩).head? = nextCard c)
    (hdb : 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hsum : (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
              + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256) :
    ∃ (v : State) (cells : List (Fin 4)), Reach s v ∧
      List.foldl applyMoveOpt (some s)
        (fluteMoves ⟨pile.toNat, hpile⟩ ⟨toPile.toNat, h10⟩ cells) = some v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  obtain ⟨cells, hnd, hlen, hfree⟩ := exists_free_cells (s := s) (k := top.length) (by omega)
  obtain ⟨v, hfold, hm⟩ := h.fluteMove (b := ⟨toPile.toNat, h10⟩)
    (fun hc => hne (congrArg Fin.val hc)) hcol hrest hrun hlen hnd hfree hdst
    (fluteMoveAbs_pileDest hpile h10 hne h hcol hrest hdb hsum)
  exact ⟨v, cells, reach_fluteMoves hfold, hfold, hm⟩

/-- **To a king pile that physically sits on the empty column `b`.** -/
theorem StateMatchesSolverPos.movePre_kingDest {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {b : Fin 10} {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcells : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hdst : (s.tableau b).head? = nextCard c)
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hown : OwnsPile s p c.suit b)
    (hval : top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    ∃ (v : State) (cells : List (Fin 4)), Reach s v ∧
      List.foldl applyMoveOpt (some s) (fluteMoves ⟨pile.toNat, hpile⟩ b cells) = some v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  -- the source has positive depth, the destination none, so they are distinct
  have hab : (⟨pile.toNat, hpile⟩ : Fin 10) ≠ b := by
    intro hc
    have hd0 : (p.pileDepth.get b).toNat = 0 := hown.1
    rw [hc] at hrest
    omega
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  obtain ⟨cells, hnd, hlen, hfree⟩ := exists_free_cells (s := s) (k := top.length) (by omega)
  obtain ⟨v, hfold, hm⟩ := h.fluteMove hab hcol hrest hrun hlen hnd hfree hdst
    (fluteMoveAbs_kingDest hpile h10 h14 h hcol hrest hdst hsu hown hval)
  exact ⟨v, cells, reach_fluteMoves hfold, hfold, hm⟩


/-! ## Phase 1 with the flute parked in the cells

The other two destinations — `EXTRA`, and a king pile whose stack is *not* on a
column but in the cells — move the whole flute, boundary card included, into free
cells.  The realization is the parking phase alone (`run_parkMoves`), costing `fl`
cells instead of `fl - 1`, and there is no destination column to re-match.

`StateMatchesSolverPos` does not constrain the cells (only `cards_count` sees
them), so this direction is strictly easier than the column destinations: no
`IsRun` hypothesis is needed either, since nothing is dropped back onto a pile. -/

/-- **What phase 1 does to the abstract position when the flute goes to the
cells.**  Note the flute length does not appear in any field: abstractly it feeds
only `usedSpace`, which matching does not read.  It is still needed on the
concrete side — it is the number of cells `parkMove` must be handed. -/
structure ParkMoveAbs (s : State) (p q : SolverPosType) (a : Fin 10) : Prop where
  /-- The source pile loses its boundary card. -/
  depth_src : (q.pileDepth.get a).toNat + 1 = (p.pileDepth.get a).toNat
  /-- No other depth changes. -/
  depth_ne : ∀ i : Fin 10, i ≠ a → q.pileDepth.get i = p.pileDepth.get i
  /-- The source flute is reset (`fluteNorm`). -/
  flute_src : (q.pileFlute.get a).toNat = 1
  /-- No other flute changes — there is no destination pile. -/
  flute_ne : ∀ i : Fin 10, i ≠ a → q.pileFlute.get i = p.pileFlute.get i
  /-- Foundations are untouched. -/
  aces : q.aces = p.aces
  /-- Every king stack that sits on a column keeps its frontier: the suit whose
      frontier moves (if any) is one whose stack is in the cells. -/
  kings : ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 →
      ∀ d ∈ (s.tableau i).getLast?,
        q.kings.get (finOfSuit d.suit) = p.kings.get (finOfSuit d.suit)

/-- **The flute-to-cells move is simulated by `parkMoves`.**  `cells` must hold
the whole flute, boundary card included: `|top| + 1` cards, which by `flute_len` is
exactly the solver's `pileFlute[a]` — one cell more than a column destination
needs.  That count is the concrete content of the abstract `pileDepth[a] -= 1,
pileFlute[a] := 1`: those `pileFlute[a]` cards leave the pile, and all of them go
to cells. -/
theorem StateMatchesSolverPos.parkMove {g : Globals} {s : State} {p q : SolverPosType}
    {a : Fin 10} {top rest : Column} {c : Card} {cells : List (Fin 4)}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau a = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get a).toNat)
    (hlen : cells.length = top.length + 1)
    (hnd : cells.Nodup)
    (hfree : ∀ i ∈ cells, s.cells i = none)
    (habs : ParkMoveAbs s p q a) :
    ∃ v : State, List.foldl applyMoveOpt (some s) (parkMoves a cells) = some v ∧
      StateMatchesSolverPos g v q := by
  obtain ⟨v, hfold, hva, hvo, hvf, _, _⟩ :=
    run_parkMoves (a := a) (top := top ++ [c]) (rest := rest)
      (by rw [hcol]; simp) (by simpa using hlen) hnd hfree
  refine ⟨v, hfold, ?_⟩
  have hlt6 : ∀ i : Fin 10, (q.pileDepth.get i).toInt.toNat < 6 := by
    intro i
    by_cases hi : i = a
    · subst hi
      have h6 := h.depth_lt6 i
      simp only [UInt8.toInt_toNat] at h6 ⊢
      have := habs.depth_src
      omega
    · rw [habs.depth_ne i hi]; exact h.depth_lt6 i
  have hidx : ∀ i : Fin 10, i ≠ a →
      (⟨(q.pileDepth.get i).toInt.toNat, hlt6 i⟩ : Fin 6)
        = ⟨(p.pileDepth.get i).toInt.toNat, h.depth_lt6 i⟩ :=
    fun i hi => by
      have hdeq : q.pileDepth.get i = p.pileDepth.get i := habs.depth_ne i hi
      simp only [hdeq]
  refine ⟨?_, hlt6, ?_, ?_, ?_, ?_⟩
  · -- cards_count
    intro d
    rw [congrFun (countState_of_reach (reach_of_foldl hfold)) d]
    exact h.cards_count d
  · -- depth_match
    intro i
    by_cases hia : i = a
    · subst hia
      rw [hva]
      refine PileMatches_of_suffix (h.depth_match i) (pre := top ++ [c]) ?_ ?_ ?_
      · rw [hcol]; simp
      · simp only [UInt8.toInt_toNat]
        have := habs.depth_src
        omega
      · simp only [UInt8.toInt_toNat]
        have := habs.depth_src
        omega
    · rw [hvo i hia, hidx i hia]
      exact h.depth_match i
  · -- flute_match
    intro i hdi
    by_cases hia : i = a
    · subst hia
      rw [hva]
      simp only [UInt8.toInt_toNat] at hdi ⊢
      rw [habs.flute_src]
      have := habs.depth_src
      omega
    · rw [hvo i hia, habs.depth_ne i hia, habs.flute_ne i hia]
      exact h.flute_match i (by rw [habs.depth_ne i hia] at hdi; exact hdi)
  · -- king_pile
    intro i hdi
    simp only [UInt8.toInt_toNat] at hdi
    by_cases hia : i = a
    · subst hia
      have hrnil : rest = [] := List.eq_nil_of_length_eq_zero (by
        have := habs.depth_src; omega)
      rw [hva, hrnil]
      simp
    · rw [habs.depth_ne i hia] at hdi
      rw [hvo i hia]
      intro d hd
      rw [habs.kings i hdi d hd]
      exact h.king_pile i (by simp only [UInt8.toInt_toNat]; exact hdi) d hd
  · -- aces_match
    intro su
    rw [habs.aces, hvf]
    exact h.aces_match su

/-! ### `EXTRA` -/

/-- **The `EXTRA` branch of phase 1 satisfies `ParkMoveAbs`.**  Nothing but
`usedSpace` moves besides the source pile's own bookkeeping. -/
theorem parkMoveAbs_extra {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10) (h14 : ¬ toPile.toNat < 14)
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat) :
    ParkMoveAbs s p (SolverSpec.movePre pile toPile hpile p) ⟨pile.toNat, hpile⟩ := by
  have h10 : ¬ toPile.toNat < 10 := by omega
  refine ⟨?_, ?_, ?_, ?_, SolverSpec.movePre_aces .., ?_⟩
  · rw [SolverSpec.movePre_depth_self]
    exact uint8_sub_one_toNat (by omega)
  · exact fun i hi => SolverSpec.movePre_depth_ne _ _ _ _ i (fun hc => hi (Fin.ext hc))
  · rw [SolverSpec.movePre_flute_self]; rfl
  · exact fun i hi => SolverSpec.movePre_flute_ne_ge10 _ _ _ h10 _ i (fun hc => hi (Fin.ext hc))
  · intro i _ d _
    rw [SolverSpec.movePre_kings_of_not_king _ _ _ _ (Or.inr h14)]

/-! ### A king pile whose stack is in the cells -/

/-- **The king-pile branch satisfies `ParkMoveAbs` when no column carries the
suit's stack.**  `hnopile` is the *physical* reading of "suit `c.suit` has no king
pile" — `StateMatchesKingConfig.noKingPile` for a suit whose configuration bit is
set.  It is load-bearing, not bookkeeping — if some column did carry a partial
stack of `c.suit`, that column's `king_pile` clause would break as soon as
`kings[c.suit]` drops, and the successor state would match no position at all. -/
theorem parkMoveAbs_kingDest {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14) {c : Card}
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hnopile : NoKingPile s p c.suit) :
    ParkMoveAbs s p (SolverSpec.movePre pile toPile hpile p) ⟨pile.toNat, hpile⟩ := by
  refine ⟨?_, ?_, ?_, ?_, SolverSpec.movePre_aces .., ?_⟩
  · rw [SolverSpec.movePre_depth_self]
    exact uint8_sub_one_toNat (by omega)
  · exact fun i hi => SolverSpec.movePre_depth_ne _ _ _ _ i (fun hc => hi (Fin.ext hc))
  · rw [SolverSpec.movePre_flute_self]; rfl
  · exact fun i hi => SolverSpec.movePre_flute_ne_ge10 _ _ _ h10 _ i (fun hc => hi (Fin.ext hc))
  · intro i hdi d hd
    have hne : d.suit ≠ c.suit := hnopile i (by simpa using hdi) d hd
    rw [vget_eq, SolverSpec.movePre_kings_kingDest pile toPile hpile h10 h14 p,
      Vector.getElem_set _ (finOfSuit d.suit).isLt,
      if_neg (by rw [hsu]; exact fun hc => hne (suitToNat_inj hc.symm))]
    rfl

/-! ### Phase 1 with a cell destination, end to end -/

/-- **To `EXTRA`.** -/
theorem StateMatchesSolverPos.movePre_extra {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10) (h14 : ¬ toPile.toNat < 14)
    {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hcells : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length) :
    ∃ (v : State) (cells : List (Fin 4)), Reach s v ∧
      List.foldl applyMoveOpt (some s) (parkMoves ⟨pile.toNat, hpile⟩ cells) = some v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  obtain ⟨cells, hnd, hlen, hfree⟩ :=
    exists_free_cells (s := s) (k := top.length + 1) (by omega)
  obtain ⟨v, hfold, hm⟩ := h.parkMove hcol hrest hlen hnd hfree
    (parkMoveAbs_extra hpile h14 (by omega))
  exact ⟨v, cells, reach_of_foldl hfold, hfold, hm⟩

/-- **To a king pile whose stack is in the cells.** -/
theorem StateMatchesSolverPos.movePre_kingCells {g : Globals} {s : State} {p : SolverPosType}
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {top rest : Column} {c : Card}
    (h : StateMatchesSolverPos g s p)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hcells : (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hnopile : NoKingPile s p c.suit) :
    ∃ (v : State) (cells : List (Fin 4)), Reach s v ∧
      List.foldl applyMoveOpt (some s) (parkMoves ⟨pile.toNat, hpile⟩ cells) = some v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  have hfl := h.flute_len ⟨pile.toNat, hpile⟩ hcol hrest
  obtain ⟨cells, hnd, hlen, hfree⟩ :=
    exists_free_cells (s := s) (k := top.length + 1) (by omega)
  obtain ⟨v, hfold, hm⟩ := h.parkMove hcol hrest hlen hnd hfree
    (parkMoveAbs_kingDest hpile h10 h14 (by omega) hsu hnopile)
  exact ⟨v, cells, reach_of_foldl hfold, hfold, hm⟩

/-! ## Phase 1 of a king-pile move, dispatched by the king configuration

`solverGetDestination` returns `KINGPILE + SUIT B` without saying where that
suit's freed run physically is; the king configuration does.  A clear bit hands
over a column to move onto (`fluteMoves`, `fluteLen - 1` cells), a set bit says the
run is in the cells and the whole flute joins it there (`parkMoves`, `fluteLen`
cells).  The two free-cell hypotheses are guarded accordingly, mirroring
`solverGetMovable`'s `possibleKings[fluteLen] ||| (possibleKings[fluteLen-1] &&&
kingOnPile)` exactly. -/

theorem StateMatchesKingConfig.movePre_king {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    -- affordability, as `solverGetMovable` splits it
    (hcellsPile : ¬ CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsExtra : CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    -- the column the suit owns accepts the boundary card (the `getDestination` bridge)
    (hdst : ∀ b : Fin 10, OwnsPile s p c.suit b → (s.tableau b).head? = nextCard c)
    (hval : top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  by_cases hbit : CfgBitSet k c.suit
  · -- the run is in the cells: park the whole flute
    obtain ⟨v, _, hreach, _, hm⟩ := hk.toMatches.movePre_kingCells hpile h10 h14 hcol hrest
      (hcellsExtra hbit) hsu (hk.noKingPile hbit)
    exact ⟨v, hreach, hm⟩
  · -- the suit owns a column: move the flute onto it
    obtain ⟨b, hown⟩ := hk.owns hbit
    obtain ⟨v, _, hreach, _, hm⟩ := hk.toMatches.movePre_kingDest hpile h10 h14 hcol hrest hrun
      (hcellsPile hbit) (hdst b hown) hsu hown hval
    exact ⟨v, hreach, hm⟩

/-! ## Phase 1, all destinations

The dispatch on `toPile`, closing phase 1: whatever destination
`solverGetDestination` returned, phase 1 of `SolverMove` is realized by legal moves
and lands in a state matching `movePre`.

Every hypothesis is guarded by the branch that needs it, which is also how the
solver itself splits them: `solverGetMovable` charges `fluteLen - 1` cells for a
column destination and `fluteLen` for a cell destination, and the destination facts
(`hdstPile`/`hdstKing`, `hsu`, `hval`) are what the `getDestination` bridge will
supply. -/
theorem StateMatchesKingConfig.movePre_run {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    -- affordability: `fluteLen - 1` cells for a column destination, `fluteLen` for a
    -- cell destination — exactly how `solverGetMovable` splits it
    (hcellsCol : (toPile.toNat < 10 ∨ ¬ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    -- a pile destination: distinct, non-empty, accepts the boundary card, no wrap
    (hne : toPile.toNat < 10 → pile.toNat ≠ toPile.toNat)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hdstPile : ∀ h10 : toPile.toNat < 10,
      (s.tableau ⟨toPile.toNat, h10⟩).head? = nextCard c)
    (hsum : ∀ h10 : toPile.toNat < 10, (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
      + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256)
    -- a king destination: the suit is `c`'s, its column accepts `c`, the flute fits
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hdstKing : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      ∀ b : Fin 10, OwnsPile s p c.suit b → (s.tableau b).head? = nextCard c)
    (hval : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      top.length + 1 ≤ (VALUE (p.kings.get (finOfSuit c.suit))).toNat) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  by_cases h10 : toPile.toNat < 10
  · -- pile to pile
    obtain ⟨v, _, hreach, _, hm⟩ := hk.toMatches.movePre_pileDest hpile h10 (hne h10) hcol hrest
      hrun (hcellsCol (Or.inl h10)) (hdstPile h10) (hdb h10) (hsum h10)
    exact ⟨v, hreach, hm⟩
  · by_cases h14 : toPile.toNat < 14
    · -- king pile: `movePre_king` splits on whether the suit owns a column
      exact hk.movePre_king hpile h10 h14 hcol hrest hrun (hsu h10 h14)
        (fun hbit => hcellsCol (Or.inr hbit)) (fun hbit => hcellsFull (Or.inr hbit))
        (hdstKing h10 h14)
        (hval h10 h14)
    · -- EXTRA: the whole flute goes to the cells
      obtain ⟨v, _, hreach, _, hm⟩ := hk.toMatches.movePre_extra hpile h14 hcol hrest
        (hcellsFull (Or.inl h14))
      exact ⟨v, hreach, hm⟩

/-! ## The king-destination bridge

`solverGetDestination` returns `KINGPILE + SUIT B` exactly when the pile's boundary
card *is* the suit's king frontier: `card == kings[suit]`.  That single fact implies
both remaining destination hypotheses:

* `hval` — the flute fits below the frontier — because a run of `L` cards topping out
  at `c` forces `rankToNat c.rank ≥ L`;
* `hdst` — the owned column accepts `c` — because that column holds exactly
  `kings[su] + 1 … CARD su 13` (`king_pile_contents`), so its exposed card is
  `kings[su] + 1 = nextCard c`; and if the column is empty then nothing of the suit
  is freed, i.e. `c` is the king itself and `nextCard c = none`. -/

private theorem isRun_rank_aux (c : Card) : ∀ (l : List Card), IsRun (l ++ [c]) →
    ∀ x ∈ (l ++ [c]).head?, rankToNat x.rank + l.length = rankToNat c.rank := by
  intro l
  induction l with
  | nil =>
    intro _ x hx
    simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    rw [← hx]
    simp
  | cons a as ih =>
    intro hrun x hx
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    rw [← hx]
    obtain ⟨y, hy⟩ : ∃ y, (as ++ [c]).head? = some y := by
      cases hl : as ++ [c] with
      | nil => simp at hl
      | cons y ys => exact ⟨y, by simp⟩
    simp only [List.cons_append] at hrun
    have hnext : nextCard a = some y := hrun.head y (Option.mem_def.2 hy)
    have hy' := ih hrun.tail y (Option.mem_def.2 hy)
    have hrank := nextCard_rank hnext
    simp only [List.length_cons]
    omega

/-- **A run's boundary card outranks the run's length.** -/
theorem IsRun.length_lt_rank {l : List Card} {c : Card} (h : IsRun (l ++ [c])) :
    l.length + 1 ≤ rankToNat c.rank := by
  obtain ⟨x, hx⟩ : ∃ x, (l ++ [c]).head? = some x := by
    cases hl : l ++ [c] with
    | nil => simp at hl
    | cons y ys => exact ⟨y, by simp⟩
  have h1 := isRun_rank_aux c l h x (Option.mem_def.2 hx)
  have h2 := rankToNat_pos x.rank
  omega

/-- **The column a suit owns accepts the suit's frontier card.** -/
theorem StateMatchesSolverPos.head_of_ownsPile {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {c : Card} {b : Fin 10}
    (hkc : encodeCard c = p.kings.get (finOfSuit c.suit))
    (hown : OwnsPile s p c.suit b) :
    (s.tableau b).head? = nextCard c := by
  obtain ⟨hd0, hcases⟩ := hown
  have hVc : (VALUE (p.kings.get (finOfSuit c.suit))).toNat = rankToNat c.rank := by
    rw [← hkc, encodeCard_VALUE]
  rcases hcases with ⟨d, hd, hdsuit, _⟩ | ⟨hnil, h13⟩
  · -- `b` carries the stack; its exposed card is `kings[su] + 1`
    have hlast : (s.tableau b).getLast? = some d := Option.mem_def.1 hd
    obtain ⟨hlen, hcont⟩ := h.king_pile_contents b hd0 hlast
    rw [hdsuit] at hlen hcont
    have hne : s.tableau b ≠ [] := by
      intro hnil; rw [hnil] at hlast; simp at hlast
    have hpos : 0 < (s.tableau b).length := List.length_pos_iff_ne_nil.mpr hne
    have hrev : (s.tableau b).length - 1 < (s.tableau b).reverse.length := by
      simp only [List.length_reverse]; omega
    -- the top card sits at reverse index `length - 1`
    have hhead : (s.tableau b).head? = some ((s.tableau b)[0]'hpos) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    have hidx : (s.tableau b).reverse[(s.tableau b).length - 1]'hrev = (s.tableau b)[0]'hpos := by
      rw [List.getElem_reverse hrev]
      congr 1
      omega
    have hcode := hcont ((s.tableau b).length - 1) hrev
    rw [hidx] at hcode
    -- its code is `c`'s code plus one, in `c`'s suit
    have hsu4 : suitToNat c.suit < 4 := suitToNat_lt _
    have hr13 : rankToNat c.rank ≤ 13 := rankBounded _
    have hval : 13 - ((s.tableau b).length - 1) = rankToNat c.rank + 1 := by omega
    rw [hval] at hcode
    have hct1 : (CARD (UInt8.ofNat (suitToNat c.suit))
        (UInt8.ofNat (rankToNat c.rank + 1))).toNat
        = (suitToNat c.suit) * 16 + (rankToNat c.rank + 1) :=
      CARD_toNat (by omega) (by omega)
    have hct2 : (encodeCard c).toNat = (suitToNat c.suit) * 16 + rankToNat c.rank := by
      rw [encodeCard]
      exact CARD_toNat (by omega) (by omega)
    rw [hhead]
    refine (nextCard_of_encode ?_ ?_).symm
    · apply UInt8.toNat_inj.mp
      rw [SUIT_toNat, SUIT_toNat, hcode, hct1, hct2]
      omega
    · rw [hcode, VALUE_toNat, VALUE_toNat, hct1, hct2]
      omega
  · -- `b` is empty and nothing of the suit is freed, so `c` is the king
    have hking : c.rank = Rank.king := rankInj _ _ (by rw [← hVc, h13]; rfl)
    rw [hnil]
    have hnone : nextCard c = none := by
      unfold nextCard
      rw [show nextRank c.rank = none from by rw [hking]; exact nextRank_king]
    rw [hnone]
    rfl

/-- **Phase 1 to a king pile, from the solver's own frontier test.**  `hkc` is
exactly `solverGetDestination`'s `card == kings[suit]`; the destination and
flute-fits hypotheses are derived from it. -/
theorem StateMatchesKingConfig.movePre_king_of_frontier {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    (h10 : ¬ toPile.toNat < 10) (h14 : toPile.toNat < 14)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hsu : toPile.toNat - 10 = suitToNat c.suit)
    (hkc : encodeCard c = p.kings.get (finOfSuit c.suit))
    (hcellsPile : ¬ CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsExtra : CfgBitSet k c.suit →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) :=
  hk.movePre_king hpile h10 h14 hcol hrest hrun hsu hcellsPile hcellsExtra
    (fun _ hown => hk.toMatches.head_of_ownsPile hkc hown)
    (by rw [← hkc, encodeCard_VALUE]; exact hrun.length_lt_rank)

/-- **Phase 1, all destinations, with the king branch reduced to the frontier test.** -/
theorem StateMatchesKingConfig.movePre_run_of_frontier {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcellsCol : (toPile.toNat < 10 ∨ ¬ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hne : toPile.toNat < 10 → pile.toNat ≠ toPile.toNat)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hdstPile : ∀ h10 : toPile.toNat < 10,
      (s.tableau ⟨toPile.toNat, h10⟩).head? = nextCard c)
    (hsum : ∀ h10 : toPile.toNat < 10, (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
      + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256)
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hkc : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      encodeCard c = p.kings.get (finOfSuit c.suit)) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) :=
  hk.movePre_run hpile hcol hrest hrun hcellsCol hcellsFull hne hdb hdstPile hsum hsu
    (fun h10 h14 _ hown => hk.toMatches.head_of_ownsPile (hkc h10 h14) hown)
    (fun h10 h14 => by rw [← hkc h10 h14, encodeCard_VALUE]; exact hrun.length_lt_rank)

/-! ## The pile-destination bridge

`solverGetDestination` walks up from the source boundary `B_src` over free cards and
stops at the first resident one, returning its pile when that card is the pile's own
*boundary*.  So the destination boundary is `B_src + n`, and the `n - 1` cards
between them are free — which under `flute_maximal` makes the destination's flute
exactly `n` long.  The destination flute therefore need **not** be trivial; what
matters is that its length equals the gap between the two boundary cards, because
then the card it exposes is `B_src + 1 = nextCard c`.

Both facts below are stated on that gap, so the solver side owes only "same suit" and
"`VALUE B_dst = VALUE B_src + pileFlute[dst]`". -/

/-- The code of a matching pile's *exposed* card: `pileFlute - 1` below its boundary. -/
theorem StateMatchesSolverPos.head_code {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (i : Fin 10)
    (hd : 0 < (p.pileDepth.get i).toInt.toNat)
    (hidx : (p.pileDepth.get i).toInt.toNat - 1 < 5) :
    ∃ e : Card, (s.tableau i).head? = some e ∧
      SUIT (encodeCard e) = SUIT ((g.pos2card.get i).get ⟨_, hidx⟩) ∧
      (VALUE (encodeCard e)).toNat + (p.pileFlute.get i).toNat
        = (VALUE ((g.pos2card.get i).get ⟨_, hidx⟩)).toNat + 1 := by
  have hfm := h.flute_match i hd
  have hnL : (p.pileDepth.get i).toInt.toNat ≤ (s.tableau i).length := (h.depth_match i).1
  have hpos : 0 < (s.tableau i).length := by omega
  obtain ⟨hs, hv⟩ := flute_elem h i hd ⟨_, hidx⟩ rfl 0 (by omega) hpos
  refine ⟨(s.tableau i)[0]'hpos, ?_, hs, by omega⟩
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]

/-- `c` is the source pile's boundary card. -/
theorem StateMatchesSolverPos.boundary_code {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) (a : Fin 10) {top rest : Column} {c : Card}
    (hcol : s.tableau a = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get a).toInt.toNat)
    (hidx : (p.pileDepth.get a).toInt.toNat - 1 < 5) :
    encodeCard c = (g.pos2card.get a).get ⟨_, hidx⟩ := by
  have hd : 0 < (p.pileDepth.get a).toInt.toNat := by omega
  have hnL : (p.pileDepth.get a).toInt.toNat ≤ (s.tableau a).length := (h.depth_match a).1
  have hlen : (s.tableau a).length = top.length + (rest.length + 1) := by
    rw [hcol]; simp
  have hlt : top.length < (s.tableau a).length := by omega
  have hidxc : (s.tableau a)[top.length]'hlt = c := by
    have h1 : (s.tableau a)[top.length]? = some c := by
      rw [hcol, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [List.getElem?_eq_getElem hlt] at h1
    exact Option.some.inj h1
  obtain ⟨hs, hv⟩ := flute_elem h a hd ⟨_, hidx⟩ rfl top.length (by omega) (by omega)
  rw [hidxc] at hs hv
  -- same suit and same value ⇒ same code
  apply UInt8.toNat_inj.mp
  have h1 := SUIT_toNat (encodeCard c)
  have h2 := VALUE_toNat (encodeCard c)
  have h3 := SUIT_toNat ((g.pos2card.get a).get ⟨_, hidx⟩)
  have h4 := VALUE_toNat ((g.pos2card.get a).get ⟨_, hidx⟩)
  have h5 := congrArg UInt8.toNat hs
  omega

/-- **The pile-destination bridge.**  If the destination's flute length is the gap
between the two boundary cards, the destination exposes `nextCard c`. -/
theorem StateMatchesSolverPos.head_of_flute_gap {g : Globals} {s : State} {p : SolverPosType}
    (h : StateMatchesSolverPos g s p) {a b : Fin 10} {top rest : Column} {c : Card}
    (hcol : s.tableau a = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get a).toInt.toNat)
    (hia : (p.pileDepth.get a).toInt.toNat - 1 < 5)
    (hdb : 0 < (p.pileDepth.get b).toInt.toNat)
    (hib : (p.pileDepth.get b).toInt.toNat - 1 < 5)
    (hsuit : SUIT ((g.pos2card.get b).get ⟨_, hib⟩)
      = SUIT ((g.pos2card.get a).get ⟨_, hia⟩))
    (hgap : (VALUE ((g.pos2card.get b).get ⟨_, hib⟩)).toNat
      = (VALUE ((g.pos2card.get a).get ⟨_, hia⟩)).toNat + (p.pileFlute.get b).toNat) :
    (s.tableau b).head? = nextCard c := by
  obtain ⟨e, hhead, hes, hev⟩ := h.head_code b hdb hib
  have hcb := h.boundary_code a hcol hrest hia
  rw [hhead]
  refine (nextCard_of_encode ?_ ?_).symm
  · rw [hes, hsuit, ← hcb]
  · rw [hcb]
    omega

/-- **Phase 1, all destinations, from the solver's own destination facts.**

Neither destination hypothesis mentions the concrete state any more:

* a pile destination needs only that its boundary card sits `pileFlute[toPile]`
  above the source's, in the same suit — what `solverGetDestination`'s walk
  establishes together with `flute_maximal`;
* a king destination needs only `encodeCard c = kings[c.suit]` — the walk's
  `card == kings[suit]` test.

What is left over (`hne`, `hdb`, `hsum`) is pure bookkeeping about `toPile`. -/
theorem StateMatchesKingConfig.movePre_run_of_dest {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcellsCol : (toPile.toNat < 10 ∨ ¬ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hne : toPile.toNat < 10 → pile.toNat ≠ toPile.toNat)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hsum : ∀ h10 : toPile.toNat < 10, (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat
      + (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat < 256)
    -- pile destination: the boundary gap *is* the destination's flute length
    (hsuitP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5),
      SUIT ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)
        = SUIT ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩))
    (hgapP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5),
      (VALUE ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)).toNat
        = (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩)).toNat
          + (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat)
    -- king destination: the frontier test
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hkc : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      encodeCard c = p.kings.get (finOfSuit c.suit)) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  have hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5 := by
    have := hk.toMatches.depth_lt6 ⟨pile.toNat, hpile⟩; omega
  refine hk.movePre_run_of_frontier hpile hcol hrest hrun hcellsCol hcellsFull hne hdb
    (fun h10 => ?_) hsum hsu hkc
  have hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5 := by
    have := hk.toMatches.depth_lt6 ⟨toPile.toNat, h10⟩; omega
  exact hk.toMatches.head_of_flute_gap hcol hrest hia
    (by simpa using hdb h10) hib (hsuitP h10 hib hia) (hgapP h10 hib hia)

/-! ## Two of the three leftovers come from the invariant

`hsum` (no `UInt8` wrap when the flutes merge) is just "a flute is at most 13 long",
and `hne` (a pile is not its own destination) follows from the gap fact, since a
flute is at least one card long.  `hdb` does *not* follow from the invariant — see
the note on `movePre_run_of_dest_inv`. -/

/-- **Every flute is at most 13 cards.**  Empty piles carry the trivial flute; on a
non-empty pile `flute_le_value` bounds it by the boundary card's value. -/
theorem SolverInvBase.pileFlute_le_13 {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p) (i : Fin 10) :
    (p.pileFlute.get i).toNat ≤ 13 := by
  by_cases hd : (p.pileDepth.get i).toNat = 0
  · have h0 : p.pileDepth.get i = 0 := UInt8.toNat_inj.mp (by simpa using hd)
    rw [(hb.pileBase i).flute_empty h0]
    decide
  · have hd0 : (p.pileDepth.get i).toNat > 0 := by omega
    have hbnd := hb.pileDepth_bound i
    have hBreal := hwf.pos2card_real i (⟨(p.pileDepth.get i).toNat - 1, by omega⟩ : Fin 5)
    have hflv := hb.flute_le_value hwf i hd0
    have := hBreal.2.2
    omega

/-- **A pile is never its own destination.**  The gap fact makes the destination
boundary strictly above the source's, and a flute is at least one card long. -/
theorem ne_of_flute_gap {g : Globals} {p : SolverPosType} (hb : SolverInvBase g p)
    {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10) (h10 : toPile.toNat < 10)
    (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5)
    (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5)
    (hgap : (VALUE ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)).toNat
      = (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩)).toNat
        + (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat) :
    pile.toNat ≠ toPile.toNat := by
  intro heq
  have hfin : (⟨toPile.toNat, h10⟩ : Fin 10) = ⟨pile.toNat, hpile⟩ := Fin.ext heq.symm
  have hdeq : (p.pileDepth.get ⟨toPile.toNat, h10⟩) = p.pileDepth.get ⟨pile.toNat, hpile⟩ :=
    congrArg _ hfin
  have hsame : ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)
      = ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩) := by
    have h1 : g.pos2card.get ⟨toPile.toNat, h10⟩ = g.pos2card.get ⟨pile.toNat, hpile⟩ :=
      congrArg _ hfin
    rw [h1]
    exact congrArg _ (Fin.ext (show (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1
      = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 from by rw [hdeq]))
  rw [hsame, hfin] at hgap
  have := (hb.pileBase ⟨pile.toNat, hpile⟩).flute_pos
  omega

/-- **Phase 1, all destinations, with `hne`/`hsum` discharged from the invariant.**

`hdb` (the destination pile is non-empty) stays a hypothesis on purpose: it does
*not* follow from `SolverInvBase` plus the gap.  It comes from the walk itself —
`solverGetDestination` stops only when `posFromTop = pileDepth[toPile] -
cardDepth[card] > 0`, which gives `pileDepth[toPile] ≥ 1` directly.  (Without it the
gap alone is satisfiable: a card dealt to an empty pile can sit as another pile's
flute card, and then the physical destination would be that other pile — exactly the
case `posFromTop ≤ 0` makes the walk skip.) -/
theorem StateMatchesKingConfig.movePre_run_of_dest_inv {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} {pile : UInt32} {toPile : UInt8} (hpile : pile.toNat < 10)
    {top rest : Column} {c : Card}
    (hwf : WellFormedLayout g) (hb : SolverInvBase g p)
    (hk : StateMatchesKingConfig g s p k)
    (hcol : s.tableau ⟨pile.toNat, hpile⟩ = top ++ c :: rest)
    (hrest : rest.length + 1 = (p.pileDepth.get ⟨pile.toNat, hpile⟩).toNat)
    (hrun : IsRun (top ++ [c]))
    (hcellsCol : (toPile.toNat < 10 ∨ ¬ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat - 1 ≤ (freeCells s).length)
    (hcellsFull : (¬ toPile.toNat < 14 ∨ CfgBitSet k c.suit) →
      (p.pileFlute.get ⟨pile.toNat, hpile⟩).toNat ≤ (freeCells s).length)
    (hdb : ∀ h10 : toPile.toNat < 10, 0 < (p.pileDepth.get ⟨toPile.toNat, h10⟩).toNat)
    (hsuitP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5),
      SUIT ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)
        = SUIT ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩))
    (hgapP : ∀ (h10 : toPile.toNat < 10)
      (hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5)
      (hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5),
      (VALUE ((g.pos2card.get ⟨toPile.toNat, h10⟩).get ⟨_, hib⟩)).toNat
        = (VALUE ((g.pos2card.get ⟨pile.toNat, hpile⟩).get ⟨_, hia⟩)).toNat
          + (p.pileFlute.get ⟨toPile.toNat, h10⟩).toNat)
    (hsu : ¬ toPile.toNat < 10 → toPile.toNat < 14 → toPile.toNat - 10 = suitToNat c.suit)
    (hkc : ¬ toPile.toNat < 10 → toPile.toNat < 14 →
      encodeCard c = p.kings.get (finOfSuit c.suit)) :
    ∃ v : State, Reach s v ∧
      StateMatchesSolverPos g v (SolverSpec.movePre pile toPile hpile p) := by
  have hia : (p.pileDepth.get ⟨pile.toNat, hpile⟩).toInt.toNat - 1 < 5 := by
    have := hk.toMatches.depth_lt6 ⟨pile.toNat, hpile⟩; omega
  refine hk.movePre_run_of_dest hpile hcol hrest hrun hcellsCol hcellsFull
    (fun h10 => ?_) hdb (fun h10 => ?_) hsuitP hgapP hsu hkc
  · have hib : (p.pileDepth.get ⟨toPile.toNat, h10⟩).toInt.toNat - 1 < 5 := by
      have := hk.toMatches.depth_lt6 ⟨toPile.toNat, h10⟩; omega
    exact ne_of_flute_gap hb hpile h10 hib hia (hgapP h10 hib hia)
  · have h1 := hb.pileFlute_le_13 hwf ⟨toPile.toNat, h10⟩
    have h2 := hb.pileFlute_le_13 hwf ⟨pile.toNat, hpile⟩
    omega
