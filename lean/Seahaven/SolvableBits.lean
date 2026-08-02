import Seahaven.MatchesPos

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
-/

/-! ## Pure, total accessors

`solve` and `solverRecCheckSolvable` index `closureInfos` and `subsetTable`
monadically, with bounds discharged at run time.  For specification purposes we
want total functions; both are clamped, and under `SolverInvMerged` the clamp
never fires (`freePiles ≤ 10`, and `offset + v` stays inside the table). -/

/-- `closureInfos` entry for a position's free-pile count. -/
def closureInfoOf (p : SolverPosType) : ClosureInfo :=
  closureInfos.get ⟨min p.freePiles.toInt.toNat 10, by omega⟩

/-- `subsetTable` lookup. -/
def subsetAt (idx : Nat) : UInt16 := subsetTable.get ⟨min idx 99, by omega⟩

/-- Bit `k` of a 16-bit configuration set, spelled as the solver spells it
(`Solver.lean:499`). -/
def BitSet (w : UInt16) (k : Fin 16) : Prop :=
  w &&& ((1 : UInt16) <<< (UInt16.ofNat k.val)) ≠ 0

instance (w : UInt16) (k : Fin 16) : Decidable (BitSet w k) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem bits2grlex_lt (b : Fin 16) : (bits2grlex.get b).toNat < 16 := by
  fin_cases b <;> decide

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

/-! ## The king configuration a concrete state realizes -/

/-- Suit `su` has a *dedicated king pile* in `s`: one of the piles the solver
treats as empty physically carries `su`'s king stack. -/
def hasKingPile (s : State) (p : SolverPosType) (su : Suit) : Bool :=
  (List.finRange 10).any fun i =>
    ((p.pileDepth.get i).toInt.toNat == 0) &&
      (match (s.tableau i).getLast? with
       | some c => (c.suit == su) && (c.rank == Rank.king)
       | none => false)

/-- The solver's internal 4-bit king mask for `s`: bit `su` set means suit `su`
has no pile of its own, so `computeKingSpaces` charges its stack to the cells. -/
def kingBitmapOf (s : State) (p : SolverPosType) : Fin 16 :=
  ⟨(if hasKingPile s p Suit.clubs then 0 else 1)
     + (if hasKingPile s p Suit.diamonds then 0 else 2)
     + (if hasKingPile s p Suit.hearts then 0 else 4)
     + (if hasKingPile s p Suit.spades then 0 else 8),
   by split_ifs <;> omega⟩

/-- The graded-lex index of that configuration — the `kingbit` of `Solver.lean:495`. -/
def kingConfigOf (s : State) (p : SolverPosType) : Fin 16 :=
  ⟨(bits2grlex.get (kingBitmapOf s p)).toNat, bits2grlex_lt _⟩

/-! ## The specification -/

/-- `SolvableBits g p v` : the **local** king-configuration bitmask `v` is the
correct answer for position `p`.

For every concrete state `s` that `p` stands for, `s` is solvable exactly when
the bit of `s`'s own king configuration is set in the `subsetTable` expansion of
`v`.  This is the property shared by `solverRecCheckSolvable`'s return value and
by whatever the memo table holds for `p.hash`. -/
def SolvableBits (g : Globals) (p : SolverPosType) (v : UInt16) : Prop :=
  ∀ s : State, StateMatchesSolverPos g s p →
    (Solvable s ↔
      BitSet (subsetAt ((closureInfoOf p).offset.toNat + v.toNat)) (kingConfigOf s p))

/-- Matching reads only the deal arrays, never the memo table. -/
theorem StateMatchesSolverPos.hashmap_iff {g : Globals} {s : State} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) :
    StateMatchesSolverPos { g with hashmap := hm } s p ↔ StateMatchesSolverPos g s p := by
  constructor <;> intro h <;>
    exact { cards_count := h.cards_count, depth_lt6 := h.depth_lt6,
            depth_match := h.depth_match, flute_match := h.flute_match,
            king_pile := h.king_pile, aces_match := h.aces_match }

/-- Consequently a memo-table write cannot invalidate a `SolvableBits` fact. -/
theorem SolvableBits.set_hashmap {g : Globals} {p : SolverPosType} {v : UInt16}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SolvableBits g p v) :
    SolvableBits { g with hashmap := hm } p v :=
  fun s hs => h s ((StateMatchesSolverPos.hashmap_iff hm).1 hs)

/-- **Each hash identifies at most one canonical position.**  This is what makes
`HashmapCorrect` well posed: a slot keyed by `p.hash` can only ever be about `p`.
Composition of the two theorems already in `SolverInvariant`. -/
theorem IsCanonicalPos_of_hash_eq (g : Globals) (p q : SolverPosType)
    (hwf : WellFormedLayout g) (hp : IsCanonicalPos g p) (hq : IsCanonicalPos g q)
    (h : p.hash = q.hash) : p = q :=
  IsCanonicalPos_unique g p q hwf hp hq (IsCanonicalPos_hash_inj g p q hp hq h)

/-- **Memo table correctness.**  Every slot either reads back as `FREESLOT` — the
table is allowed to forget, since collisions silently evict — or holds the
correct bitmask for the unique canonical position with that hash. -/
def HashmapCorrect (g : Globals) : Prop :=
  ∀ (p : SolverPosType), IsCanonicalPos g p →
    ∀ v : UInt8, EStateM.run (getSlot p.hash) g = .ok v g →
      v = UInt8.ofNat FREESLOT ∨ SolvableBits g p v.toUInt16

/-! ## The two statements to discharge

Written as named `Prop`s rather than `sorry`d theorems, so that the eventual
proofs read `theorem … : RecCheckSolvableSpec := …` and nothing here is
unproved. -/

/-- What `solverRecCheckSolvable` must satisfy.  To be proved by well-founded
induction on the pile depths (equivalently on `hash`, which strictly decreases
on every child — see `IsCanonicalPos_hash_inj`).  Note it must also *carry the
memo invariant forward*, since the function writes to the table. -/
def RecCheckSolvableSpec : Prop :=
  ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
    WellFormedLayout g → IsCanonicalPos g p → HashmapCorrect g →
    EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
    SolvableBits g p v ∧ HashmapCorrect g' ∧ g'.pos2card = g.pos2card

/-- What the whole `solve` entry point must satisfy: it answers `SUCCESS` exactly
for solvable positions.  `pk` carries the pile depths and, in slot 10, the
king mask in the *external* convention (`pk[10] = internal ^^^ 0xf`, so bit
`su` set means suit `su` *does* have a pile). -/
def SolveSpec : Prop :=
  ∀ (g g' : Globals) (s : State) (p : SolverPosType) (pk : Vector UInt8 11) (r : UInt8),
    WellFormedLayout g → HashmapCorrect g →
    StateMatchesSolverPos g s p → IsCanonicalPos g p →
    (pk.get 10) = (kingBitmapOf s p).val.toUInt8 ^^^ 0xf →
    EStateM.run (solve pk) g = .ok r g' →
    (r = UInt8.ofNat SUCCESS ↔ Solvable s)
