import Seahaven.MatchesPos
import Mathlib.Data.Nat.Bitwise

/-!
# What the solver's king-configuration bitmasks mean

`solverRecCheckSolvable` and the memo table in `Globals` answer the same
question, in the same encoding, so they get one shared specification:
`SolvableBits`.

## The encoding

A *king configuration* records, for each suit, whether that suit's freed king
stack has a pile of its own or sits in the cells.  It is a 4-bit mask, with

> **bit `su` set  ⟺  suit `su` has *no* dedicated king pile.**

(Cross-check: `computeKingSpaces` refunds `13 - VALUE kings[su]` exactly when
bit `su` is *clear* — i.e. for the suits whose stack is on a pile and therefore
must not be charged to the cells.  And `kingOnPileMap[0] = 0x469d` is precisely
the set of grlex indices `k` with `grlex2bits[k]` even, i.e. bit 0 clear.)

Masks are indexed in *graded lexicographic* order by `bits2grlex`, so that all
configurations with the same popcount are contiguous.  `closureInfos[freePiles]`
selects that contiguous block: `shiftValue` is where it starts and `numBits` how
long it is.  `solverRecCheckSolvable` therefore returns a **local** bitmask whose
bit `i` refers to global grlex index `shiftValue + i`, and `subsetTable` closes a
local set under king reshuffling, expanding it back to a full 16-bit global set.

## Why state it through `subsetTable`

Because the recursion itself does: at `Solver.lean:394-397` the child's answer is
consumed as `subsetTable[childCI.offset + child'] >>> parentCI.shiftValue`.
Phrasing the specification the same way makes it compose — and makes one
statement serve both the function and the memo table, which stores exactly the
value the function returns (`Solver.lean:402`).

## Why the specification must pin the configuration down (`StateMatchesKingConfig`)

`SolvableBits` is stated over `StateMatchesKingConfig` — matching *plus*
`RealizesKingConfig` *plus* the negative clause `no_pile` — and the negative
clause is load-bearing.  With bare `RealizesKingConfig` the specification is
**unsatisfiable** (a refuted shortcut, recorded so it is not tried a third time):

Suppose the position arose by force-vacating suit A's lone king onto a pile, and
it is solvable only with B and C piled and A's run in the cells — an honest
answer sets only that configuration's bit, call it `d_BC`.  `subsetTable`'s
downward closure makes `d_BC` cover the sparser configuration `gi` = "only C
piled, A's bit set".  But `RealizesKingConfig` merely *withholds* assignments,
so the actual state `s'` — A's run physically on a pile, B's in the cells —
*also* realizes `gi`, and the specification would demand `Solvable s'`.  That is
false: which king sits in the cells changes solvability.  `no_pile` breaks the
masquerade: `s'` does not `StateMatchesKingConfig`-stand for `gi` (A's bit is
set, yet a solver-empty pile carries A's king), so the specification only speaks
at A-clear configurations — and transporting the recursion's query from `gi` to
such a configuration is exactly what `forcedKings` is for (`kingStep_transport`
in `SoundnessSkeleton`).
-/

/-! ## Pure, total accessors

`solve` and `solverRecCheckSolvable` index `closureInfos` and `subsetTable`
monadically, with bounds discharged at run time.  For specification purposes we
want total functions; both are clamped, and under `SolverInvMerged` the clamp
never fires (`freePiles ≤ 10`, and `offset + v` stays inside the table). -/

/-- `closureInfos` entry for a position's free-pile count. -/
def closureInfoOf (p : SolverPosType) : ClosureInfo :=
  closureInfos.get ⟨min p.freePiles.toNat 10, by omega⟩

/-- `subsetTable` lookup. -/
def subsetAt (idx : Nat) : UInt16 := subsetTable.get ⟨min idx 99, by omega⟩

/-- A local bitmask is one that fits in its block.  The value
`solverRecCheckSolvable` returns (and the memo table stores) must satisfy this —
`subsetTable` is only meaningful at in-block indices, so the property has to be
threaded through the recursion (`RecCheckSolvableSpec`, `HashmapCorrect`). -/
def LocalMask (p : SolverPosType) (v : UInt16) : Prop :=
  v.toNat < 2 ^ (closureInfoOf p).numBits.toNat

/-- Intersecting only shrinks a local mask (`childSolvable &&& (forcedKings >>> …)`
stays in the block). -/
theorem LocalMask.and_left {p : SolverPosType} {a : UInt16} (b : UInt16)
    (ha : LocalMask p a) : LocalMask p (a &&& b) :=
  lt_of_le_of_lt (by rw [UInt16.toNat_and]; exact Nat.and_le_left) ha

/-- Bit `k` of a 16-bit configuration set, spelled as the solver spells it
(`Solver.lean:499`). -/
def BitSet (w : UInt16) (k : Fin 16) : Prop :=
  w &&& ((1 : UInt16) <<< (UInt16.ofNat k.val)) ≠ 0

instance (w : UInt16) (k : Fin 16) : Decidable (BitSet w k) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem bits2grlex_lt (b : Fin 16) : (bits2grlex.get b).toNat < 16 := by
  fin_cases b <;> decide

/-! ## `BitSet` algebra -/

theorem nat_and_shiftLeft_ne_zero (n k : Nat) :
    (n &&& (1 <<< k) ≠ 0) ↔ n.testBit k = true := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow]
  cases h : n.testBit k <;> simp

theorem uint16_mask_toNat (k : Fin 16) :
    ((1 : UInt16) <<< (UInt16.ofNat k.val)).toNat = 1 <<< k.val := by
  fin_cases k <;> decide

theorem BitSet_toNat (w : UInt16) (k : Fin 16) : BitSet w k ↔ w.toNat.testBit k.val := by
  unfold BitSet
  rw [← nat_and_shiftLeft_ne_zero, ← uint16_mask_toNat k, ← UInt16.toNat_and]
  constructor
  · intro h hz; exact h (UInt16.toNat_inj.1 (by simpa using hz))
  · intro h hz; exact h (by rw [hz]; rfl)

theorem BitSet_or (x y : UInt16) (k : Fin 16) :
    BitSet (x ||| y) k ↔ BitSet x k ∨ BitSet y k := by
  simp [BitSet_toNat, UInt16.toNat_or, Nat.testBit_or]

theorem BitSet_zero (k : Fin 16) : ¬ BitSet 0 k := by simp [BitSet_toNat]

theorem BitSet_and (x y : UInt16) (k : Fin 16) :
    BitSet (x &&& y) k ↔ BitSet x k ∧ BitSet y k := by
  simp [BitSet_toNat, UInt16.toNat_and, Nat.testBit_and]

/-! ### Machine-checked cross-checks of the encoding

The three facts the prose above relies on, as `decide` proofs over the tables. -/

def popCount4 (n : Nat) : Nat := (n % 2) + (n / 2 % 2) + (n / 4 % 2) + (n / 8 % 2)

/-- `bits2grlex` and `grlex2bits` are mutually inverse. -/
theorem grlex_bits_inv (b : Fin 16) :
    (grlex2bits.get ⟨(bits2grlex.get b).toNat, bits2grlex_lt b⟩).toNat = b.val := by
  fin_cases b <;> decide

/-- **The bit polarity.**  `kingOnPileMap su` — the mask `SolverCleanupPile`
intersects `forcedKings` with when suit `su`'s king vacates a pile — is exactly
the set of grlex indices whose mask has bit `su` *clear*.  So a clear bit means
"this suit has a pile of its own". -/
theorem kingOnPileMap_eq (su : Fin 4) :
    kingOnPileMap.get su
      = (List.finRange 16).foldl
          (fun acc k => if (grlex2bits.get k).toNat / (2 ^ su.val) % 2 = 0
                        then acc ||| ((1 : UInt16) <<< UInt16.ofNat k.val) else acc) 0 := by
  fin_cases su <;> decide

/-- **The block structure.**  `closureInfos[f]` selects exactly the grlex indices
whose mask has popcount `4 - min f 4`: with `f` free piles, exactly `min f 4`
suits get a dedicated king pile and the rest are charged to the cells. -/
theorem closureInfo_block (f : Fin 11) (i : Fin 16) :
    ((closureInfos.get f).shiftValue.toNat ≤ i.val ∧
      i.val < (closureInfos.get f).shiftValue.toNat + (closureInfos.get f).numBits.toNat)
    ↔ popCount4 (grlex2bits.get i).toNat = 4 - min f.val 4 := by
  fin_cases f <;> revert i <;> decide

/-! ## The king configuration a concrete state realizes

This is a *relation*, not a function.  A pile the solver treats as empty can be
"reserved" for a suit in two ways: it physically carries that suit's king run, or
it is genuinely empty because the suit's stack has already gone to the
foundation — and in the latter case the pile stays reserved, because nothing else
can be put there that would contradict the reservation.  So one state can be read
as realizing several configurations, and `hasKingPile`-as-a-function would be
wrong. -/

/-- Suit `su` owns pile `i` in `s`: `i` is a pile the solver treats as empty and
either physically carries `su`'s king run, or is genuinely empty *and* `su` has
no freed king-stack card to place (`kings su` is still the king — true both
before any king of the suit is freed and after the whole suit has reached the
foundation).

The second disjunct must carry that side condition.  Without it any suit could
reserve any empty pile — including one a flute move just emptied — and claim a
`computeKingSpaces` refund for a stack that is really still in the cells. -/
def OwnsPile (s : State) (p : SolverPosType) (su : Suit) (i : Fin 10) : Prop :=
  (p.pileDepth.get i).toNat = 0 ∧
    ((∃ c ∈ (s.tableau i).getLast?, c.suit = su ∧ c.rank = Rank.king) ∨
      (s.tableau i = [] ∧ (VALUE (p.kings.get (finOfSuit su))).toNat = 13))

/-- Bit `su` of the internal mask of grlex configuration `k` — set means suit
`su` has *no* pile of its own. -/
def CfgBitSet (k : Fin 16) (su : Suit) : Prop :=
  (grlex2bits.get k).toNat / 2 ^ (suitToNat su) % 2 = 1

instance (k : Fin 16) (su : Suit) : Decidable (CfgBitSet k su) :=
  inferInstanceAs (Decidable (_ = _))

/-- `s` can be read as realizing king configuration `k`: the suits whose bit is
clear are assigned distinct piles that they own. -/
def RealizesKingConfig (s : State) (p : SolverPosType) (k : Fin 16) : Prop :=
  ∃ assign : Suit → Option (Fin 10),
    (∀ su i, assign su = some i → OwnsPile s p su i) ∧
    (∀ su su' i, assign su = some i → assign su' = some i → su = su') ∧
    (∀ su, (assign su).isSome ↔ ¬ CfgBitSet k su)

/-- Suit `su` has **no** king pile in `s`: no pile the solver treats as empty
carries a card of that suit.  The exact negation of the physical half of
`OwnsPile` — a genuinely empty column reserved for a suit is *not* excluded, since
nothing of the suit sits on it. -/
def NoKingPile (s : State) (p : SolverPosType) (su : Suit) : Prop :=
  ∀ i : Fin 10, (p.pileDepth.get i).toNat = 0 →
    ∀ d ∈ (s.tableau i).getLast?, d.suit ≠ su

/-- **A state matched against a position *and* a king configuration.**

`StateMatchesSolverPos` is silent about which empty column carries which suit's
freed king run — deliberately, since the abstract position does not record it.
That information is what `k` adds, and both directions of it are needed:

* bit `su` **clear** (suit `su` owns a pile): `su` is assigned a column of its own,
  which either physically carries its run — by `king_pile_contents` exactly the
  cards `kings[su] + 1 … CARD su 13` — or is genuinely empty because nothing of the
  suit is freed yet (`VALUE kings[su] = 13`).  Distinct suits get distinct columns.
* bit `su` **set** (suit `su` has no pile): no solver-empty column carries `su` at
  all.  `RealizesKingConfig` alone does *not* say this — it only withholds an
  assignment — and the difference is load-bearing: a `kings[su]` write while a
  column holds a partial run of `su` would break that column's `king_pile` clause,
  so the simulation of a to-cells king move needs `no_pile` as a real hypothesis
  (see `MoveSim`'s `parkMoveAbs_kingDest`).

Reading a configuration off a state stays many-to-many, as it must: a suit whose
stack has entirely reached the foundation satisfies both branches, so it may be
recorded as owning a spare empty column or as owning nothing. -/
structure StateMatchesKingConfig (g : Globals) (s : State) (p : SolverPosType)
    (k : Fin 16) : Prop where
  toMatches : StateMatchesSolverPos g s p
  realizes : RealizesKingConfig s p k
  no_pile : ∀ su : Suit, CfgBitSet k su → NoKingPile s p su

/-- A suit with its bit clear owns a column. -/
theorem StateMatchesKingConfig.owns {g : Globals} {s : State} {p : SolverPosType} {k : Fin 16}
    (h : StateMatchesKingConfig g s p k) {su : Suit} (hk : ¬ CfgBitSet k su) :
    ∃ i : Fin 10, OwnsPile s p su i := by
  obtain ⟨assign, hown, _, hiff⟩ := h.realizes
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff su).2 hk)
  exact ⟨i, hown su i hi⟩

/-- A suit with its bit set has its freed run in the cells, not on a column. -/
theorem StateMatchesKingConfig.noKingPile {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} (h : StateMatchesKingConfig g s p k) {su : Suit} (hk : CfgBitSet k su) :
    NoKingPile s p su := h.no_pile su hk

/-! ### Dedicated piles, counted

Every suit with its bit clear has a column of its own — `RealizesKingConfig`'s
assignment is injective, so two suits never share one, not even in the
`VALUE kings[su] = 13` case where the column is genuinely empty.  The counting
consequence is that a configuration cannot claim more king piles than the position
has empty columns. -/

/-- Injectivity of the assignment, as a count: at most as many suits have their
bit clear as there are piles the solver treats as empty. -/
theorem RealizesKingConfig.card_clear_le_empty {s : State} {p : SolverPosType} {k : Fin 16}
    (h : RealizesKingConfig s p k) :
    (Finset.univ.filter (fun su : Suit => ¬ CfgBitSet k su)).card
      ≤ (Finset.univ.filter (fun i : Fin 10 => p.pileDepth.get i = 0)).card := by
  obtain ⟨assign, hown, hinj, hiff⟩ := h
  refine Finset.card_le_card_of_injOn (fun su => (assign su).getD 0) ?_ ?_
  · intro su hsu
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff su).2 (Finset.mem_filter.1 hsu).2)
    have hd := (hown su i hi).1
    simp only [hi, Option.getD_some, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    exact UInt8.toNat_inj.mp
      (show (p.pileDepth.get i).toNat = (0 : UInt8).toNat from by simpa using hd)
  · intro su hsu su' hsu' heq
    have hb : (assign su).getD 0 = (assign su').getD 0 := heq
    have h1 : ¬ CfgBitSet k su := (Finset.mem_filter.1 (Finset.mem_coe.1 hsu)).2
    have h2 : ¬ CfgBitSet k su' := (Finset.mem_filter.1 (Finset.mem_coe.1 hsu')).2
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((hiff su).2 h1)
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 ((hiff su').2 h2)
    rw [hi, hi', Option.getD_some, Option.getD_some] at hb
    exact hinj su su' i hi (hb ▸ hi')

/-- The number of piles of depth `0`, as a `Finset` card, is what `freePiles`
counts. -/
theorem card_empty_piles_eq_freePiles {g : Globals} {p : SolverPosType}
    (hm : SolverInvMerged g p) :
    (Finset.univ.filter (fun i : Fin 10 => p.pileDepth.get i = 0)).card
      = p.freePiles.toNat := by
  have hlist : p.pileDepth.toList.countP (· == 0)
      = (List.finRange 10).countP (fun i => p.pileDepth.get i == 0) := by
    rw [show p.pileDepth.toList = (List.finRange 10).map (fun i => p.pileDepth.get i) from by
      apply List.ext_getElem <;> simp [Vector.get]]
    rw [List.countP_map]
    rfl
  have hcard : (Finset.univ.filter (fun i : Fin 10 => p.pileDepth.get i = 0)).card
      = (List.finRange 10).countP (fun i => p.pileDepth.get i == 0) := by
    simp only [List.countP_eq_length_filter, Finset.filter, Finset.univ, Fintype.elems,
      Finset.card, Multiset.filter, Multiset.card]
    rfl
  have hfp := hm.freePiles_def
  have hcast : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
  rw [hcard, ← hlist]
  omega

/-- **A configuration cannot claim more king piles than `freePiles`.** -/
theorem RealizesKingConfig.card_clear_le_freePiles {g : Globals} {s : State}
    {p : SolverPosType} {k : Fin 16} (h : RealizesKingConfig s p k)
    (hm : SolverInvMerged g p) :
    (Finset.univ.filter (fun su : Suit => ¬ CfgBitSet k su)).card ≤ p.freePiles.toNat := by
  rw [← card_empty_piles_eq_freePiles hm]
  exact h.card_clear_le_empty

/-! ## The specification -/

/-- `SolvableBits g p v` : the **local** king-configuration bitmask `v` is the
correct answer for position `p`.

For every concrete state `s` that `p` stands for *at configuration `k`*, `s` is
solvable exactly when `k`'s bit is set in the `subsetTable` expansion of `v`.
This is the property shared by `solverRecCheckSolvable`'s return value and by
whatever the memo table holds for `p.hash`.

The hypothesis must be `StateMatchesKingConfig`, not bare `RealizesKingConfig` —
see the module docstring for the counterexample otherwise. -/
def SolvableBits (g : Globals) (p : SolverPosType) (v : UInt16) : Prop :=
  ∀ (s : State) (k : Fin 16), StateMatchesKingConfig g s p k →
    (Solvable s ↔ BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) k)

/-- Matching reads only the deal arrays, never the memo table. -/
theorem StateMatchesSolverPos.hashmap_iff {g : Globals} {s : State} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) :
    StateMatchesSolverPos { g with hashmap := hm } s p ↔ StateMatchesSolverPos g s p := by
  constructor <;> intro h <;>
    exact { cards_count := h.cards_count, depth_lt6 := h.depth_lt6,
            depth_match := h.depth_match, flute_match := h.flute_match,
            king_pile := h.king_pile, aces_match := h.aces_match }

/-- `StateMatchesKingConfig` likewise never reads the memo table — its two extra
clauses mention `g` not at all. -/
theorem StateMatchesKingConfig.hashmap_iff {g : Globals} {s : State} {p : SolverPosType}
    {k : Fin 16} (hm : Vector UInt16 BIG_HASH_SIZE) :
    StateMatchesKingConfig { g with hashmap := hm } s p k ↔ StateMatchesKingConfig g s p k := by
  constructor <;> intro h
  · exact { toMatches := (StateMatchesSolverPos.hashmap_iff hm).1 h.toMatches,
            realizes := h.realizes, no_pile := h.no_pile }
  · exact { toMatches := (StateMatchesSolverPos.hashmap_iff hm).2 h.toMatches,
            realizes := h.realizes, no_pile := h.no_pile }

/-- Consequently a memo-table write cannot invalidate a `SolvableBits` fact. -/
theorem SolvableBits.set_hashmap {g : Globals} {p : SolverPosType} {v : UInt16}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SolvableBits g p v) :
    SolvableBits { g with hashmap := hm } p v :=
  fun s k hs => h s k ((StateMatchesKingConfig.hashmap_iff hm).1 hs)

/-- **Each hash identifies at most one canonical position.**  This is what makes
`HashmapCorrect` well posed: a slot keyed by `p.hash` can only ever be about `p`.
Composition of the two theorems already in `SolverInvariant`. -/
theorem IsCanonicalPos_of_hash_eq (g : Globals) (p q : SolverPosType)
    (hwf : WellFormedLayout g) (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (h : p.hash = q.hash) : p = q :=
  IsCanonicalPos_unique g p q hwf hp hq (IsCanonicalPos_hash_inj g p q hp hq h)

/-- **Memo table correctness.**  Every slot either reads back as `FREESLOT` — the
table is allowed to forget, since collisions silently evict — or holds the
correct bitmask for the unique canonical position with that hash.

The `LocalMask` conjunct is needed because consumers feed the stored mask to
`subsetTable` arithmetic that is only meaningful in-block, and `getSlot` by
itself can return up to 7 bits — wider than any block. -/
def HashmapCorrect (g : Globals) : Prop :=
  ∀ (p : SolverPosType), IsCanonicalPos g p →
    ∀ v : UInt8, EStateM.run (getSlot p.hash) g = .ok v g →
      v = UInt8.ofNat FREESLOT ∨ (SolvableBits g p v.toUInt16 ∧ LocalMask p v.toUInt16)

/-! ## The two statements to discharge

Written as named `Prop`s rather than `sorry`d theorems, so that the eventual
proofs read `theorem … : RecCheckSolvableSpec := …` and nothing here is
unproved. -/

/-- What `solverRecCheckSolvable` must satisfy.  To be proved by well-founded
induction on the pile depths (equivalently on `hash`, which strictly decreases
on every child — see `IsCanonicalPos_hash_inj`).  Note it must also *carry the
memo invariant forward*, since the function writes to the table.

`LocalMask g p v` is part of the induction: the parent applies
`kingStep_transport` to the child's answer, which reads `subsetTable` at the
*un*intersected mask — an index the run itself never touches, so its bound must
come from the spec.  (Provable: `computeKingSpaces` sets only bits `< numBits`,
`componentTable` entries fit their block — `componentTable_localBound` — the
`hash == 0` leaf returns 1, and the memo path carries it via `HashmapCorrect`.) -/
def RecCheckSolvableSpec : Prop :=
  ∀ (g : Globals) (p : SolverPosType),
    WellFormedLayout g → IsCanonicalPos g p → HashmapCorrect g →
    ∃ (v : UInt16) (g' : Globals),
      EStateM.run (solverRecCheckSolvable p) g = .ok v g' ∧
      (SolvableBits g p v ∧ LocalMask p v) ∧ HashmapCorrect g' ∧ g'.pos2card = g.pos2card

/-- **The specification, read at a run the caller already has.**  `EStateM` is
deterministic, so the existential pins the caller's own `v` and `g'`.  This is the
form every consumer used before totality was part of the statement. -/
theorem RecCheckSolvableSpec.apply (h : RecCheckSolvableSpec) {g g' : Globals}
    {p : SolverPosType} {v : UInt16}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hcor : HashmapCorrect g)
    (hrun : EStateM.run (solverRecCheckSolvable p) g = .ok v g') :
    (SolvableBits g p v ∧ LocalMask p v) ∧ HashmapCorrect g' ∧ g'.pos2card = g.pos2card := by
  obtain ⟨v', g'', hrun', hres⟩ := h g p hwf hcan hcor
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (hrun'.symm.trans hrun)
  exact hres

/-- What the whole `solve` entry point must satisfy: it answers `SUCCESS` exactly
for solvable positions.  `pk` carries the pile depths and, in slot 10, the
king mask in the *external* convention (`pk[10] = internal ^^^ 0xf`, so bit
`su` set means suit `su` *does* have a pile).

The input configuration must be supplied as `StateMatchesKingConfig` — the
caller asserts not only that the piled suits own piles but also that the other
suits have none.  With bare `RealizesKingConfig` a state with an unreported king
pile could masquerade as `pk[10]` and the equivalence would be false (module
docstring). -/
def SolveSpec : Prop :=
  ∀ (g g' : Globals) (s : State) (p : SolverPosType) (pk : Vector UInt8 11) (r : UInt8),
    WellFormedLayout g → HashmapCorrect g → IsCanonicalPos g p →
    (∃ k : Fin 16, StateMatchesKingConfig g s p k ∧ (pk.get 10) = (grlex2bits.get k) ^^^ 0xf) →
    EStateM.run (solve pk) g = .ok r g' →
    (r = UInt8.ofNat SUCCESS ↔ Solvable s)
