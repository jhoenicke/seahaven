import Seahaven.RecLoopSound

/-!
# Soundness of `solverRecCheckSolvable` itself

`RecLoopSound` handles the pile loop; this file handles the function around it —
the `hash == 0` leaf, the memo read and write, and the recursion.

## The soundness-only spec layer

`SolvableBits`/`HashmapCorrect`/`RecCheckSolvableSpec` (in `SolvableBits.lean`) are
stated as *equivalences*, i.e. soundness **and** completeness.  Completeness needs a
genuinely separate development (`foundationMove_preserves_Solvable`, the
strategy-stealing lemmas, and the fact that the recursion never runs out of
progress), so rather than `sorry` half of an `↔` this file mirrors the three
statements with `SoundBits` in place of `SolvableBits`: `HashmapSound`,
`RecCheckSolvableSound`.  Nothing here is unproved on that account.

## The recursion

`solverRecCheckSolvable` is defined by `partial_fixpoint`, so `recCheck_eq` unfolds
it one level.  The recursion is then discharged the way the `busyAces` drain loop is
(`SolverSpec.drainBody_run`): the *theorem* carries a `Nat` bounding `DepthSum game`
and inducts on it, instantiated at `DepthSum game + 1`.  The measure decrease is
`move_merged`'s third conjunct, applied where `WellFormedLayout`/`IsCanonicalPos`
are hypotheses — which is exactly why the definition site stays free of it.

## What is left

Nothing syntactic: both side conditions of the induction are discharged here
(`prologueRuns`, `recBodyStep`), so `recCheck_sound_of_semantics` reduces the
recursion's soundness to the two *semantic* hypotheses `SubsetSound` and
`MoveSimulated`.
-/

open Lean Lean.Order

/-! ## The `hash == 0` leaf

`hash = 0` means every pile is solver-empty, so every card counts as freed.  A
canonical position has `busyAces = 0`, and `foundation_maximal_weak` then forces
every foundation to the king: the only reasons a foundation may lag are "the next
card is not free" (impossible here) and "the drain is still pending" (excluded by
canonicity).  All four foundations at the king *is* the goal state, so the position
is not merely solvable — it is already solved. -/

/-- With every pile at depth `0`, every card is free: `isFreeCard` compares the
card's original depth against its pile's current depth, and the latter is `0`. -/
theorem isFreeCard_of_depths_zero {g : Globals} {p : SolverPosType}
    (hd : ∀ i : Fin 10, p.pileDepth.get i = 0) (c : UInt8) : isFreeCard g p c := by
  unfold isFreeCard
  simp only []
  by_cases h10 : (if h64 : c.toNat < 64 then g.card2pile.get ⟨c.toNat, h64⟩ else 0).toNat < 10
  · rw [dif_pos h10, hd ⟨_, h10⟩]
    exact Nat.zero_le _
  · rw [dif_neg h10]
    exact Nat.zero_le _

/-- **`hash = 0` forces every pile empty.**  The hash is the base-6 dot product
`Σ 6^i · pileDepth[i]` with digits `≤ 5` and no `UInt32` wraparound
(`6^10 - 1 < 2^32`), so it vanishes only at the all-zero digit vector.  Same
arithmetic core as `IsCanonicalPos_hash_inj`, instantiated against zero. -/
theorem pileDepth_eq_zero_of_hash_zero {g : Globals} {p : SolverPosType}
    (h : SolverInvBase g p) (hz : p.hash = 0) (i : Fin 10) : p.pileDepth.get i = 0 := by
  have hfoldl :
      (List.finRange 10).foldl
        (fun acc j => acc + pileHashes.get j * (p.pileDepth.get j).toNat.toUInt32) 0 = 0 :=
    h.hash_def.symm.trans hz
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
             pileHashes, Vector.get, Vector.getElem_toArray, Fin.isValue, Fin.val_cast,
             Fin.val_zero, Fin.val_succ, Nat.reduceAdd, List.getElem_toArray,
             List.getElem_cons_succ, List.getElem_cons_zero] at hfoldl
  have hb : ∀ k : Nat, ∀ hk : k < 10, (p.pileDepth[k]'hk : UInt8).toNat ≤ 5 :=
    fun k hk => h.pileDepth_bound ⟨k, hk⟩
  have key := hash_dot_inj _ _ _ _ _ _ _ _ _ _ 0 0 0 0 0 0 0 0 0 0
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega)) (hb 4 (by omega))
    (hb 5 (by omega)) (hb 6 (by omega)) (hb 7 (by omega)) (hb 8 (by omega)) (hb 9 (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hfoldl]; decide)
  clear hfoldl
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := key
  refine UInt8.toNat_inj.mp ?_
  show (p.pileDepth.get i).toNat = (0 : UInt8).toNat
  simp only [show ((0 : UInt8).toNat = 0) from rfl]
  obtain ⟨iv, hiv⟩ := i
  show (p.pileDepth[iv]'hiv : UInt8).toNat = 0
  interval_cases iv <;> assumption

/-- **Every foundation is complete at `hash = 0`.**  `busyAces = 0` kills
`foundation_maximal_weak`'s drain-pending disjunct and every card is free
(`isFreeCard_of_depths_zero`), so its "next card not free" disjunct is impossible
too. -/
theorem aces_king_of_hash_zero {g : Globals} {p : SolverPosType}
    (h : IsCanonicalPos g p) (hz : p.hash = 0) (s : Fin 4) :
    (VALUE (p.aces.get s)).toNat = 13 := by
  have hd := pileDepth_eq_zero_of_hash_zero h.toSolverInvBase hz
  rcases h.foundation_maximal_weak s with hk | hnf | hbusy
  · exact hk
  · exact absurd (isFreeCard_of_depths_zero hd _) hnf
  · rw [h.busyAces_zero] at hbusy
    simp at hbusy

/-- **The leaf is solved, not merely solvable.**  Every matching state has all four
foundations at the king, which is `isGoal`. -/
theorem solvable_of_hash_zero {g : Globals} {s : State} {p : SolverPosType}
    (hcan : IsCanonicalPos g p) (hm : StateMatchesSolverPos g s p) (hz : p.hash = 0) :
    Solvable s := by
  refine Solvable.done ?_
  have hf : ∀ su : Suit, s.foundations su = some Rank.king := by
    intro su
    have := (hm.foundation_value su).symm.trans (aces_king_of_hash_zero hcan hz (finOfSuit su))
    rw [← rankToNatToRank (s.foundations su), this]
    rfl
  simp only [isGoal, List.all_cons, List.all_nil, hf, Bool.and_true]
  decide

/-- The soundness half of the leaf's return value, `1`: every state the position
stands for is solvable, whatever the configuration and whatever the expansion
says. -/
theorem soundBits_of_hash_zero {g : Globals} {p : SolverPosType}
    (hcan : IsCanonicalPos g p) (hz : p.hash = 0) (v : UInt16) : SoundBits g p v :=
  fun _ _ hs _ => solvable_of_hash_zero hcan hs.toMatches hz

/-! ## The memo write is a frame

`setSlot` writes `hashmap` and nothing else, and every predicate the soundness
argument threads — `WellFormedLayout`, the `IsCanonicalPos` tower, `SoundBits`
through `StateMatchesKingConfig` — reads only `pos2card`/`card2pile`/`card2depth`.
Each clause's *statement* is therefore definitionally unchanged by the write;
what is not automatic is the transport of the structures themselves, since
`IsCanonicalPos g p` and `IsCanonicalPos { g with hashmap := hm } p` are
applications of an indexed family to different terms.  Hence one two-line
transport per layer of the tower. -/

theorem PileBase.set_hashmap {g : Globals} {p : SolverPosType} {i : Fin 10}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : PileBase g p i) :
    PileBase { g with hashmap := hm } p i := by
  cases h; constructor <;> assumption

theorem PileMerged.set_hashmap {g : Globals} {p : SolverPosType} {i : Fin 10}
    {hb : (p.pileDepth.get i).toNat ≤ 5}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : PileMerged g p i hb) :
    PileMerged { g with hashmap := hm } p i hb := by
  cases h; constructor <;> assumption

theorem SuitClean.set_hashmap {g : Globals} {p : SolverPosType} {s : Fin 4}
    {hb : ∀ i : Fin 10, (p.pileDepth.get i).toNat ≤ 5}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SuitClean g p s hb) :
    SuitClean { g with hashmap := hm } p s hb := by
  cases h; constructor <;> assumption

theorem SolverInvBase.set_hashmap {g : Globals} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SolverInvBase g p) :
    SolverInvBase { g with hashmap := hm } p where
  pileBase i := (h.pileBase i).set_hashmap hm
  suitClean s := (h.suitClean s).set_hashmap hm
  hash_def := h.hash_def
  usedSpace_def := h.usedSpace_def
  busyAces_lt16 := h.busyAces_lt16

theorem SolverInvMerged.set_hashmap {g : Globals} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SolverInvMerged g p) :
    SolverInvMerged { g with hashmap := hm } p where
  toSolverInvBase := h.toSolverInvBase.set_hashmap hm
  pileMerged i := (h.pileMerged i).set_hashmap hm
  freePiles_def := h.freePiles_def

theorem IsCanonicalPos.set_hashmap {g : Globals} {p : SolverPosType}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : IsCanonicalPos g p) :
    IsCanonicalPos { g with hashmap := hm } p where
  toSolverInvMerged := h.toSolverInvMerged.set_hashmap hm
  busyAces_zero := h.busyAces_zero

theorem WellFormedLayout.set_hashmap {g : Globals}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : WellFormedLayout g) :
    WellFormedLayout { g with hashmap := hm } := by
  cases h; constructor <;> assumption

/-- `SoundBits` reads only the deal arrays, exactly as `SolvableBits` does. -/
theorem SoundBits.set_hashmap {g : Globals} {p : SolverPosType} {v : UInt16}
    (hm : Vector UInt16 BIG_HASH_SIZE) (h : SoundBits g p v) :
    SoundBits { g with hashmap := hm } p v :=
  fun s k hs => h s k ((StateMatchesKingConfig.hashmap_iff hm).1 hs)

/-- The reverse transport, for free: `{ { g with hashmap := hm } with hashmap := g.hashmap }`
*is* `g` by structure eta. -/
theorem IsCanonicalPos.of_set_hashmap {g : Globals} {hm : Vector UInt16 BIG_HASH_SIZE}
    {p : SolverPosType} (h : IsCanonicalPos { g with hashmap := hm } p) : IsCanonicalPos g p :=
  h.set_hashmap g.hashmap

theorem WellFormedLayout.of_set_hashmap {g : Globals} {hm : Vector UInt16 BIG_HASH_SIZE}
    (h : WellFormedLayout { g with hashmap := hm }) : WellFormedLayout g :=
  h.set_hashmap g.hashmap

theorem SoundBits.of_set_hashmap {g : Globals} {hm : Vector UInt16 BIG_HASH_SIZE}
    {p : SolverPosType} {v : UInt16} (h : SoundBits { g with hashmap := hm } p v) :
    SoundBits g p v :=
  h.set_hashmap g.hashmap

/-! ## The soundness-only spec layer

`HashmapSound` and `RecCheckSolvableSound` mirror `HashmapCorrect` and
`RecCheckSolvableSpec` (`SolvableBits.lean`) with `SoundBits` in place of the
`↔`-flavoured `SolvableBits`.

`WFGlobals` is the answer to "should the well-formedness of the globals carry the
memo table too": yes, but note the asymmetry it hides.  `layout` is *unchanged* by
everything the solver does after `initcard`; `memo` is an invariant that has to be
*re-established* at every `setSlot`.  Bundling them buys one hypothesis in and one
out, not a uniform proof obligation. -/

/-- **Memo-table soundness.**  Every slot either reads back as `FREESLOT` — the
table may forget, since colliding keys silently evict — or holds a *sound* mask
for the unique canonical position with that hash.  `LocalMask` rides along because
consumers feed the stored value to `subsetTable`, which is only meaningful
in-block, and `getSlot` by itself can return up to 7 bits. -/
def HashmapSound (g : Globals) : Prop :=
  ∀ (p : SolverPosType), IsCanonicalPos g p →
    ∀ v : UInt8, EStateM.run (getSlot p.hash) g = .ok v g →
      v = UInt8.ofNat FREESLOT ∨ (SoundBits g p v.toUInt16 ∧ LocalMask p v.toUInt16)

/-- The globals are well formed: fixed deal layout, plus a sound memo table. -/
structure WFGlobals (g : Globals) : Prop where
  layout : WellFormedLayout g
  memo : HashmapSound g

/-- **What `solverRecCheckSolvable` must satisfy, soundness half.**  The returned
mask is sound and in-block, the memo invariant is carried forward, and the only
thing the call touched is the memo table — the frame every caller needs, and the
strongest one available since `setSlot` is the function's only write. -/
def RecCheckSolvableSound : Prop :=
  ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
    WFGlobals g → IsCanonicalPos g p →
    EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
    (SoundBits g p v ∧ LocalMask p v) ∧ HashmapSound g' ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm }

/-! ## The hash is small

`hash = Σ 6^i · pileDepth[i]` with digits `≤ 5`, so `hash ≤ 6^10 - 1 = 60466175`.
This is what makes the memo table's 9-bit `high` tag lossless — `high = hash /
2^20 + 1 ≤ 58 < 512` — and hence what rules out one canonical position reading
another's slot value. -/
/-- Arithmetic core, over plain `Nat`s so that applying it unifies whatever spelling
the depth terms happen to carry (`omega` treats `p.pileDepth[0]'h₁` and
`p.pileDepth[0]'h₂` as distinct atoms). -/
private theorem dot_toUInt32_lt (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : Nat)
    (h0 : d0 ≤ 5) (h1 : d1 ≤ 5) (h2 : d2 ≤ 5) (h3 : d3 ≤ 5) (h4 : d4 ≤ 5)
    (h5 : d5 ≤ 5) (h6 : d6 ≤ 5) (h7 : d7 ≤ 5) (h8 : d8 ≤ 5) (h9 : d9 ≤ 5) :
    (1 * d0 + 6 * d1 + 36 * d2 + 216 * d3 + 1296 * d4 + 7776 * d5 + 46656 * d6
      + 279936 * d7 + 1679616 * d8 + 10077696 * d9).toUInt32.toNat < 60466176 := by
  have hlt : 1 * d0 + 6 * d1 + 36 * d2 + 216 * d3 + 1296 * d4 + 7776 * d5 + 46656 * d6
      + 279936 * d7 + 1679616 * d8 + 10077696 * d9 < 4294967296 := by omega
  simp only [show ∀ x : Nat, x.toUInt32 = UInt32.ofNat x from fun _ => rfl,
             UInt32.toNat_ofNat', Nat.reducePow]
  rw [Nat.mod_eq_of_lt hlt]
  omega

theorem hash_lt {g : Globals} {p : SolverPosType} (h : SolverInvBase g p) :
    p.hash.toNat < 60466176 := by
  have hfoldl := h.hash_def
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
             pileHashes, Vector.get, Vector.getElem_toArray, Fin.isValue, Fin.val_cast,
             Fin.val_zero, Fin.val_succ, Nat.reduceAdd, List.getElem_toArray,
             List.getElem_cons_succ, List.getElem_cons_zero] at hfoldl
  have hb : ∀ k : Nat, ∀ hk : k < 10, (p.pileDepth[k]'hk : UInt8).toNat ≤ 5 :=
    fun k hk => h.pileDepth_bound ⟨k, hk⟩
  -- Rewrite the `UInt32` dot product as `(Nat dot product).toUInt32`, whose `toNat`
  -- is the `Nat` sum itself because that sum is `< 2^32`.
  have hdot : p.hash = (1 * (p.pileDepth[0]'(by omega) : UInt8).toNat
      + 6 * (p.pileDepth[1]'(by omega) : UInt8).toNat
      + 36 * (p.pileDepth[2]'(by omega) : UInt8).toNat
      + 216 * (p.pileDepth[3]'(by omega) : UInt8).toNat
      + 1296 * (p.pileDepth[4]'(by omega) : UInt8).toNat
      + 7776 * (p.pileDepth[5]'(by omega) : UInt8).toNat
      + 46656 * (p.pileDepth[6]'(by omega) : UInt8).toNat
      + 279936 * (p.pileDepth[7]'(by omega) : UInt8).toNat
      + 1679616 * (p.pileDepth[8]'(by omega) : UInt8).toNat
      + 10077696 * (p.pileDepth[9]'(by omega) : UInt8).toNat).toUInt32 := by
    rw [hfoldl]
    simp only [show ∀ x : Nat, x.toUInt32 = UInt32.ofNat x from fun _ => rfl,
               UInt32.ofNat_add, UInt32.ofNat_mul, UInt32.reduceOfNat, UInt32.zero_add]
  rw [hdot]
  exact dot_toUInt32_lt _ _ _ _ _ _ _ _ _ _
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega)) (hb 4 (by omega))
    (hb 5 (by omega)) (hb 6 (by omega)) (hb 7 (by omega)) (hb 8 (by omega)) (hb 9 (by omega))

/-! ## The memo table's slot arithmetic

`getSlot`/`setSlot` (`Solver.lean:253-266`) implement an open-addressed table with
no collision resolution: a key's slot is `slotEntry`, and the slot carries a 9-bit
`slotHigh` tag so that a *foreign* key's value reads back as `FREESLOT` instead of
being mistaken for one's own.  What has to be proved is that the tag really
separates keys — for the hashes canonical positions produce, `(entry, tag)`
determines the key. -/

/-- The key's high part, `key / BIG_HASH_SIZE + 1`; its low 9 bits are the slot tag. -/
def slotHigh (key : UInt32) : UInt32 := key / (UInt32.ofNat BIG_HASH_SIZE) + 1

/-- The slot a key hashes to. -/
def slotEntry (key : UInt32) : UInt32 :=
  ((slotHigh key * (UInt32.ofNat 0x10001)) ^^^ key) &&& (UInt32.ofNat (BIG_HASH_SIZE - 1))

theorem slotEntry_lt (key : UInt32) : (slotEntry key).toNat < BIG_HASH_SIZE := by
  have hle : (slotEntry key).toNat ≤ 1048575 := by
    rw [slotEntry, UInt32.toNat_and]
    refine le_trans Nat.and_le_right ?_
    simp only [UInt32.toNat_ofNat']
    norm_num
  -- `omega` treats the `BIG_HASH_SIZE` abbrev as an atom, so spell the literal out.
  show (slotEntry key).toNat < 1048576
  omega

/-- The raw 16-bit word in `key`'s slot: 7 bits of payload above 9 bits of tag. -/
def slotWord (g : Globals) (key : UInt32) : UInt16 :=
  g.hashmap[(slotEntry key).toNat]'(slotEntry_lt key)

/-- What `getSlot` returns, as a pure function. -/
def slotRead (g : Globals) (key : UInt32) : UInt8 :=
  if ((slotWord g key).toUInt32 ^^^ slotHigh key) &&& 0x1ff != 0 then UInt8.ofNat FREESLOT
  else ((slotWord g key) >>> 9).toUInt8

/-- The globals after `setSlot`, as a pure function.  Note it touches only `hashmap`. -/
def slotWrite (g : Globals) (key : UInt32) (v : UInt16) : Globals :=
  let hm := g.hashmap.set (slotEntry key).toNat
      ((v <<< 9) ||| ((slotHigh key).toUInt16 &&& 0x1ff)) (slotEntry_lt key)
  { g with hashmap := hm }

set_option linter.unusedSimpArgs false in
theorem getSlot_run (g : Globals) (key : UInt32) :
    EStateM.run (getSlot key) g = .ok (slotRead g key) g := by
  -- The bound, respelled in the *raw* form the unfolded code uses, so that
  -- `getElem?_pos`'s side condition is discharged syntactically.
  have hlt := slotEntry_lt key
  unfold slotEntry slotHigh at hlt
  unfold getSlot
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, Vector.getE, getElem?_pos, hlt, slotRead, slotWord, slotHigh, slotEntry,
    apply_ite (fun f : EStateM Error Globals UInt8 => f g)]
  -- the last gap is `if c then .ok A g else .ok B g` vs `.ok (if c then A else B) g`
  split <;> rfl

set_option linter.unusedSimpArgs false in
theorem setSlot_run (g : Globals) (key : UInt32) (v : UInt16) :
    EStateM.run (setSlot key v) g = .ok () (slotWrite g key v) := by
  have hlt := slotEntry_lt key
  unfold slotEntry slotHigh at hlt
  unfold setSlot
  simp only [EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, EStateM.set, pure, EStateM.pure, Vector.setE, slotWrite, slotHigh, slotEntry]
  rw [dif_pos hlt]
  rfl

/-! ### The tag separates keys

The slot holds `key`'s 9-bit tag `slotHigh key &&& 0x1ff` below the 7-bit payload.
Two keys sharing a slot *and* a tag are equal: the tag pins `key / 2^20` (both
`slotHigh`s are `≤ 58`, so the 9 bits lose nothing), and once the `slotHigh`s agree
the `slotEntry` computation differs only by `^^^ key`, which the mask makes into
`key % 2^20`. -/

/-- Arithmetic core: with the xor-ed prefix `X` shared, agreeing on the low 20 bits
and on the quotient by `2^20` forces equality. -/
private theorem key_eq_of_bits {k₁ k₂ X : Nat}
    (hq : k₁ / 1048576 = k₂ / 1048576)
    (hentry : (X ^^^ k₁) &&& 1048575 = (X ^^^ k₂) &&& 1048575) : k₁ = k₂ := by
  have hc : k₁ &&& 1048575 = k₂ &&& 1048575 := by
    rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_right] at hentry
    have h := congrArg (fun t => (X &&& 1048575) ^^^ t) hentry
    simpa [← Nat.xor_assoc, Nat.xor_self] using h
  rw [show (1048575 : Nat) = 2 ^ 20 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod] at hc
  norm_num at hc
  omega

/-- `slotHigh` in `Nat` terms; no wraparound, since `key / 2^20 + 1 ≤ 4096`. -/
theorem slotHigh_toNat (key : UInt32) : (slotHigh key).toNat = key.toNat / 1048576 + 1 := by
  have hkey : key.toNat < 4294967296 := key.toNat_lt_size
  rw [slotHigh, UInt32.toNat_add, UInt32.toNat_div]
  have h1 : (UInt32.ofNat BIG_HASH_SIZE).toNat = 1048576 := by
    simp only [UInt32.toNat_ofNat']; norm_num
  have h2 : (1 : UInt32).toNat = 1 := rfl
  rw [h1, h2]
  omega

/-- For a solver hash the tag loses nothing: `slotHigh key ≤ 58 < 512`. -/
theorem slotHigh_lt_512 {key : UInt32} (h : key.toNat < 60466176) :
    (slotHigh key).toNat < 512 := by
  rw [slotHigh_toNat]
  omega

/-- **Same slot, same tag ⟹ same key** (for the hashes canonical positions produce). -/
theorem key_eq_of_slot_agree {k₁ k₂ : UInt32}
    (hhigh : slotHigh k₁ = slotHigh k₂) (hentry : slotEntry k₁ = slotEntry k₂) : k₁ = k₂ := by
  have hq : k₁.toNat / 1048576 = k₂.toNat / 1048576 := by
    have := congrArg UInt32.toNat hhigh
    rw [slotHigh_toNat, slotHigh_toNat] at this
    omega
  refine UInt32.toNat_inj.1 (key_eq_of_bits (X := (slotHigh k₂ * UInt32.ofNat 0x10001).toNat) hq ?_)
  have h := congrArg UInt32.toNat hentry
  rw [slotEntry, slotEntry, hhigh] at h
  rw [UInt32.toNat_and, UInt32.toNat_and, UInt32.toNat_xor, UInt32.toNat_xor] at h
  have hm : (UInt32.ofNat (BIG_HASH_SIZE - 1)).toNat = 1048575 := by
    simp only [UInt32.toNat_ofNat']; norm_num
  rw [hm] at h
  exact h

/-! ### Packing: 7-bit payload above the 9-bit tag -/

/-- The word `setSlot` writes into the slot. -/
def slotPacked (key : UInt32) (v : UInt16) : UInt16 :=
  (v <<< 9) ||| ((slotHigh key).toUInt16 &&& 0x1ff)

private theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have h' := congrArg (fun t => t ^^^ b) h
  simpa [Nat.xor_assoc, Nat.xor_self] using h'

private theorem and_511 (a : Nat) : a &&& 511 = a % 512 := by
  rw [show (511 : Nat) = 2 ^ 9 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

private theorem shift_or_low (a b : Nat) : (((a * 512) % 65536) ||| b) &&& 511 = b % 512 := by
  rw [Nat.and_or_distrib_right, and_511, and_511, show ((a * 512) % 65536) % 512 = 0 by omega,
    Nat.zero_or]

private theorem shift_or_high (a b : Nat) (ha : a < 128) (hb : b < 512) :
    (((a * 512) % 65536) ||| b) >>> 9 = a := by
  rw [Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  norm_num
  rw [show ((a * 512) % 65536) / 512 = a by omega, show b / 512 = 0 by omega, Nat.or_zero]

/-- The packed word's `toNat`, split into the two ranges. -/
private theorem slotPacked_toNat (key : UInt32) (v : UInt16) :
    (slotPacked key v).toNat = ((v.toNat * 512) % 65536) ||| ((slotHigh key).toNat % 512) := by
  -- `.toNat` of a `UIntN` numeral does not reduce by `norm_num`; feed the `rfl`s in.
  simp only [slotPacked, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt16.toNat_and,
    UInt32.toNat_toUInt16, Nat.shiftLeft_eq,
    show (9 : UInt16).toNat = 9 from rfl, show (511 : UInt16).toNat = 511 from rfl]
  norm_num [and_511]

/-- **The tag survives the packing**: the word's low 9 bits are the key's tag. -/
theorem slotPacked_low (key : UInt32) (v : UInt16) :
    (slotPacked key v).toNat &&& 511 = (slotHigh key).toNat % 512 := by
  rw [slotPacked_toNat, shift_or_low]
  omega

/-- **The payload survives the packing**, provided it fits in 7 bits — which
`LocalMask` guarantees, no block being wider than 6 bits. -/
theorem slotPacked_payload {v : UInt16} (key : UInt32) (hv : v.toNat < 128) :
    slotPacked key v >>> 9 = v := by
  refine UInt16.toNat_inj.1 ?_
  rw [UInt16.toNat_shiftRight, slotPacked_toNat, show (9 : UInt16).toNat % 16 = 9 from rfl]
  exact shift_or_high _ _ hv (Nat.mod_lt _ (by omega))

/-- **Same slot, matching tag ⟹ same `slotHigh`.** -/
theorem slotHigh_eq_of_test {k₁ k₂ : UInt32} {v : UInt16}
    (h₁ : (slotHigh k₁).toNat < 512) (h₂ : (slotHigh k₂).toNat < 512)
    (htest : ((slotPacked k₁ v).toUInt32 ^^^ slotHigh k₂) &&& 0x1ff = 0) :
    slotHigh k₁ = slotHigh k₂ := by
  have h := congrArg UInt32.toNat htest
  rw [UInt32.toNat_and, UInt32.toNat_xor, UInt16.toNat_toUInt32,
    show (511 : UInt32).toNat = 511 from rfl] at h
  rw [Nat.and_xor_distrib_right, slotPacked_low, and_511] at h
  have hkey := eq_of_xor_eq_zero h
  refine UInt32.toNat_inj.1 ?_
  omega

/-! ### Reading a slot after a write

Three outcomes, and they are exactly the three disjuncts `HashmapSound` needs: a
different slot is untouched, the same key reads its own value back, and any other
key sharing the slot has been evicted and reads `FREESLOT`. -/

theorem slotWord_write_of_entry_eq (g : Globals) (k₁ k₂ : UInt32) (v : UInt16)
    (he : (slotEntry k₂).toNat = (slotEntry k₁).toNat) :
    slotWord (slotWrite g k₁ v) k₂ = slotPacked k₁ v := by
  show (g.hashmap.set (slotEntry k₁).toNat _ (slotEntry_lt k₁))[(slotEntry k₂).toNat]'_ = _
  rw [Vector.getElem_set (slotEntry_lt k₁) (slotEntry_lt k₂), if_pos he.symm]
  rfl

theorem slotWord_write_of_ne (g : Globals) (k₁ k₂ : UInt32) (v : UInt16)
    (hne : (slotEntry k₂).toNat ≠ (slotEntry k₁).toNat) :
    slotWord (slotWrite g k₁ v) k₂ = slotWord g k₂ := by
  show (g.hashmap.set (slotEntry k₁).toNat _ (slotEntry_lt k₁))[(slotEntry k₂).toNat]'_ = _
  rw [Vector.getElem_set (slotEntry_lt k₁) (slotEntry_lt k₂), if_neg (Ne.symm hne)]
  rfl

/-- A 7-bit payload survives the `UInt16`/`UInt8` narrowing the memo table imposes. -/
theorem toUInt8_toUInt16 {v : UInt16} (hv : v.toNat < 256) : v.toUInt8.toUInt16 = v := by
  refine UInt16.toNat_inj.1 ?_
  rw [UInt8.toNat_toUInt16, UInt16.toNat_toUInt8]
  omega

/-- **Read after write.** -/
theorem slotRead_write (g : Globals) (k₁ k₂ : UInt32) (v : UInt16)
    (hb₁ : k₁.toNat < 60466176) (hb₂ : k₂.toNat < 60466176) (hv : v.toNat < 128) :
    slotRead (slotWrite g k₁ v) k₂ = slotRead g k₂
    ∨ (k₂ = k₁ ∧ slotRead (slotWrite g k₁ v) k₂ = v.toUInt8)
    ∨ slotRead (slotWrite g k₁ v) k₂ = UInt8.ofNat FREESLOT := by
  by_cases he : (slotEntry k₂).toNat = (slotEntry k₁).toNat
  · rw [slotRead, slotWord_write_of_entry_eq g k₁ k₂ v he]
    by_cases ht : ((slotPacked k₁ v).toUInt32 ^^^ slotHigh k₂) &&& 0x1ff = 0
    · -- the tag matches, so the keys agree and the payload comes back intact
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · exact key_eq_of_slot_agree
          (slotHigh_eq_of_test (slotHigh_lt_512 hb₁) (slotHigh_lt_512 hb₂) ht).symm
          (UInt32.toNat_inj.1 he)
      · rw [if_neg (by simpa using ht), slotPacked_payload k₁ hv]
    · exact Or.inr (Or.inr (by rw [if_pos (by simpa using ht)]))
  · exact Or.inl (by rw [slotRead, slotRead, slotWord_write_of_ne g k₁ k₂ v he])

/-! ## The memo write preserves memo soundness -/

/-- Every block is at most 6 bits wide, so an in-block mask fits the memo table's
7-bit payload. -/
theorem localMask_lt_128 {p : SolverPosType} {v : UInt16} (h : LocalMask p v) : v.toNat < 128 := by
  have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
    unfold closureInfoOf
    have : ∀ i : Fin 11, (closureInfos.get i).numBits.toNat ≤ 6 := by decide
    exact this _
  have := h
  unfold LocalMask at this
  calc v.toNat < 2 ^ (closureInfoOf p).numBits.toNat := this
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hnb
    _ = 64 := by norm_num
    _ < 128 := by norm_num

/-- **`setSlot` preserves `HashmapSound`.**  The written key's own slot now holds a
sound mask; every other key either sees an untouched slot or has been evicted and
reads `FREESLOT`. -/
theorem hashmapSound_slotWrite {g : Globals} {p : SolverPosType} {v : UInt16}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hms : HashmapSound g)
    (hsound : SoundBits g p v) (hloc : LocalMask p v) :
    HashmapSound (slotWrite g p.hash v) := by
  have hv : v.toNat < 128 := localMask_lt_128 hloc
  intro q hqcan' w hw
  have hqcan : IsCanonicalPos g q := hqcan'.of_set_hashmap
  rw [getSlot_run] at hw
  have hwval : w = slotRead (slotWrite g p.hash v) q.hash := (EStateM.Result.ok.inj hw).1.symm
  rcases slotRead_write g p.hash q.hash v (hash_lt hcan.toSolverInvBase)
      (hash_lt hqcan.toSolverInvBase) hv with hkeep | ⟨hkey, hval⟩ | hfree
  · -- untouched slot: the old memo invariant answers
    rcases hms q hqcan w (by rw [getSlot_run, hwval, hkeep]) with hfs | ⟨hs, hl⟩
    · exact Or.inl hfs
    · exact Or.inr ⟨hs.set_hashmap _, hl⟩
  · -- the written key: `q` is `p`, and the payload came back intact
    have hpq : q = p := IsCanonicalPos_of_hash_eq g q p hwf hqcan hcan hkey
    subst hpq
    rw [hwval, hval, toUInt8_toUInt16 (by omega)]
    exact Or.inr ⟨hsound.set_hashmap _, hloc⟩
  · exact Or.inl (hwval.trans hfree)

/-! ## Reducing the function's own steps

Each step before the pile loop reads a table or the memo and leaves `Globals`
alone, so the three branches of `recCheck_eq` can be read off one at a time.
The `_apply` spellings are the same facts with `EStateM.run` unfolded (it is
definitionally application), which is the form the reduced goals present. -/

theorem freePiles_index (p : SolverPosType) :
    (p.freePiles.toInt32.toUInt32).toNat = p.freePiles.toNat := rfl

set_option linter.unusedSimpArgs false in
theorem closureInfos_getE_apply (g : Globals) (p : SolverPosType) (h : p.freePiles.toNat ≤ 10) :
    (closureInfos.getE p.freePiles.toInt32.toUInt32 :
        EStateM Error Globals ClosureInfo) g = .ok (closureInfoOf p) g := by
  have hidx : (p.freePiles.toInt32.toUInt32).toNat < 11 := by rw [freePiles_index]; omega
  simp only [Vector.getE, bind, EStateM.bind, pure, EStateM.pure, getElem?_pos, hidx]
  congr 1
  unfold closureInfoOf
  congr 1
  rw [freePiles_index]
  show p.freePiles.toNat = min p.freePiles.toNat 10
  omega

theorem getSlot_apply (g : Globals) (key : UInt32) :
    getSlot key g = .ok (slotRead g key) g := getSlot_run g key

theorem setSlot_apply (g : Globals) (key : UInt32) (v : UInt16) :
    setSlot key v g = .ok () (slotWrite g key v) := setSlot_run g key v

set_option linter.unusedSimpArgs false in
/-- **The `hash == 0` leaf returns `1` and touches nothing.** -/
theorem recCheck_run_hash_zero (g : Globals) (p : SolverPosType) (hz : p.hash = 0) :
    EStateM.run (solverRecCheckSolvable p) g = .ok 1 g := by
  rw [recCheck_eq]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hz, BEq.rfl, if_pos]

set_option linter.unusedSimpArgs false in
/-- **A memo hit returns the cached value and touches nothing.** -/
theorem recCheck_run_cached (g : Globals) (p : SolverPosType) (hfp : p.freePiles.toNat ≤ 10)
    (hz : p.hash ≠ 0) (hne : slotRead g p.hash ≠ UInt8.ofNat FREESLOT) :
    EStateM.run (solverRecCheckSolvable p) g = .ok (slotRead g p.hash).toUInt16 g := by
  -- `FREESLOT` is an abbrev, so `UInt8.ofNat FREESLOT` and the literal `255` are
  -- different terms; bridge by `rfl`.
  have hne' : ((slotRead g p.hash) != 255) = true := by
    simp only [bne_iff_ne, ne_eq]
    exact fun h => hne (h.trans rfl)
  rw [recCheck_eq]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    show (p.hash == 0) = false from beq_eq_false_iff_ne.mpr hz,
    Bool.false_eq_true, reduceIte, closureInfos_getE_apply g p hfp, getSlot_apply,
    hne', reduceIte]

set_option linter.unusedSimpArgs false in
theorem possibleKings_getE_apply (ki : KingInfo) (g : Globals) :
    (ki.possibleKings.getE 0 : EStateM Error Globals UInt8) g
      = .ok (ki.possibleKings.get 0) g := by
  simp only [Vector.getE, bind, EStateM.bind, pure, EStateM.pure, getElem?_pos,
    show ((0 : UInt32).toNat < 6) from by decide]
  rfl

set_option linter.unusedSimpArgs false in
/-- **The loop branch, forward.**  Given what the prologue computes and what the
pile loop returns, this is the whole run — memo write included.  Stated forward
rather than by inverting the run, so it needs no separate "the prologue succeeds"
argument: `EStateM` is deterministic, so the caller reads its own `v`/`g'` off
this equation. -/
theorem recCheck_run_loop (g gl : Globals) (p : SolverPosType) (ki : KingInfo)
    (comp : UInt8) (v : UInt16)
    (hfp : p.freePiles.toNat ≤ 10) (hz : p.hash ≠ 0)
    (hfree : slotRead g p.hash = UInt8.ofNat FREESLOT)
    (hki : EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
      (closureInfoOf p).numBits p) g = .ok ki g)
    (hcomp : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hloop : forIn (List.range 10) (0 : UInt16)
      (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16
        (ki.possibleKings.get 0).toUInt16) g = .ok v gl) :
    EStateM.run (solverRecCheckSolvable p) g = .ok v (slotWrite gl p.hash v) := by
  have hfree' : ((slotRead g p.hash) != 255) = false := by
    simp only [bne_eq_false_iff_eq]
    exact hfree.trans rfl
  -- applied spellings (`EStateM.run f g` is `f g` by definition, but `simp` needs the
  -- shape the reduced goal presents)
  have hki' : computeKingSpaces (closureInfoOf p).shiftValue (closureInfoOf p).numBits p g
      = .ok ki g := hki
  have hcomp' : computeComponentKingBits p g = .ok comp g := hcomp
  rw [recCheck_eq]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    show (p.hash == 0) = false from beq_eq_false_iff_ne.mpr hz,
    Bool.false_eq_true, reduceIte, closureInfos_getE_apply g p hfp, getSlot_apply,
    hfree', possibleKings_getE_apply, hki', hcomp', hloop, setSlot_apply]

set_option linter.unusedSimpArgs false in
/-- **The loop branch, inverted.**  From the whole run, read off the pile loop's own
run and the memo write.  (`EStateM` being deterministic, this is `recCheck_run_loop`
run backwards; it is stated separately because the caller has the outer run, not the
loop's.) -/
theorem recCheck_run_loop_inv (g g' : Globals) (p : SolverPosType) (ki : KingInfo)
    (comp : UInt8) (v : UInt16)
    (hfp : p.freePiles.toNat ≤ 10) (hz : p.hash ≠ 0)
    (hfree : slotRead g p.hash = UInt8.ofNat FREESLOT)
    (hki : EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
      (closureInfoOf p).numBits p) g = .ok ki g)
    (hcomp : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    (hrun : EStateM.run (solverRecCheckSolvable p) g = .ok v g') :
    ∃ gl : Globals,
      forIn (List.range 10) (0 : UInt16)
        (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16
          (ki.possibleKings.get 0).toUInt16) g = .ok v gl ∧
      g' = slotWrite gl p.hash v := by
  cases hl : forIn (List.range 10) (0 : UInt16)
      (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16
        (ki.possibleKings.get 0).toUInt16) g with
  | error e t =>
    -- an erroring loop makes the whole run error
    have hfree' : ((slotRead g p.hash) != 255) = false := by
      simp only [bne_eq_false_iff_eq]; exact hfree.trans rfl
    have hki' : computeKingSpaces (closureInfoOf p).shiftValue (closureInfoOf p).numBits p g
        = .ok ki g := hki
    have hcomp' : computeComponentKingBits p g = .ok comp g := hcomp
    rw [recCheck_eq] at hrun
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      show (p.hash == 0) = false from beq_eq_false_iff_ne.mpr hz,
      Bool.false_eq_true, reduceIte, closureInfos_getE_apply g p hfp, getSlot_apply,
      hfree', possibleKings_getE_apply, hki', hcomp', hl] at hrun
    exact absurd hrun (by simp)
  | ok a t =>
    refine ⟨t, ?_, ?_⟩ <;>
      [skip; skip] <;>
      · have heq := recCheck_run_loop g t p ki comp a hfp hz hfree hki hcomp hl
        rw [heq] at hrun
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
        first
        | exact hl
        | rfl

/-! ## The induction's two side conditions

Both are proved further down — `PrologueRuns` as `prologueRuns`, `RecBodyStep` as
`recBodyStep` — so nothing in this file is left open. -/

/-- `computeKingSpaces` returns masks that fit the position's own block. -/
def PossibleKingsLocal (p : SolverPosType) (ki : KingInfo) : Prop :=
  ∀ c : Fin 6, (ki.possibleKings.get c).toNat < 2 ^ (closureInfoOf p).numBits.toNat

/-- **The prologue's two computations succeed without touching `Globals`.**  Both are
read-only loops (`outerLoop_ok`, `compLoop_run` give the loop halves with the state
unchanged); the one real side condition is `-1 ≤ blockSpace`, i.e.
`usedSpace ≥ kingRefund`.  **Discharged below** as `prologueRuns`, on the back of
`kingRefund_le_usedSpace`. -/
def PrologueRuns : Prop :=
  ∀ (g : Globals) (p : SolverPosType), WellFormedLayout g → IsCanonicalPos g p →
    (∃ ki : KingInfo, EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
        (closureInfoOf p).numBits p) g = .ok ki g ∧ PossibleKingsLocal p ki ∧
        KingInfoCorrect p ki) ∧
    (∃ comp : UInt8, EStateM.run (computeComponentKingBits p) g = .ok comp g)

/-! ### The memo invariant is a parameter

Everything from here to the pile loop treats the memo invariant as an opaque token:
the body hands it to the recursive call and hands back whatever the call returns, and
the loop threads it.  Nothing inspects a slot.  So the memo slot is a parameter
`H : Globals → Prop`, and the same lemmas serve the soundness recursion
(`H := HashmapSound`, below) and the two-sided one (`H := HashmapCorrect`, in
`RecCheckSpec`).  Only the *bit* half of the child's answer — `SoundBits` here — is
direction-specific. -/

/-- What the recursive call is known to satisfy — the induction hypothesis, guarded
by the measure `move_merged` makes drop.  `H` is the memo invariant the recursion
carries; see the note above. -/
def ChildSpec (H : Globals → Prop) (p : SolverPosType) : Prop :=
  ∀ (child : SolverPosType) (g₁ g₂ : Globals) (w : UInt16),
    SolverSpec.DepthSum child < SolverSpec.DepthSum p → WellFormedLayout g₁ → IsCanonicalPos g₁ child →
    H g₁ → EStateM.run (solverRecCheckSolvable child) g₁ = .ok w g₂ →
    (SoundBits g₁ child w ∧ LocalMask child w) ∧ H g₂ ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g₂ = { g₁ with hashmap := hm }

/-- **Reading the loop body off the code.**  `Contributes` is `RecLoopSound`'s record
of one iteration; the two extra conjuncts say the iteration only writes the memo
table, which is what lets the entry globals be recovered at the end.  Proved as
`recBodyStep` at the end of this file, on the back of the five run lemmas listed in
`RecLoopSound` plus the `getDest_spec` → `MoveValid`/`DestValid` bridge that lets
`move_merged` apply. -/
def RecBodyStep (H : Globals → Prop) : Prop :=
  ∀ (p : SolverPosType) (ki : KingInfo) (comp : UInt8) (allkings : UInt16)
    (g₁ g₂ : Globals) (pile : Nat) (w : UInt16) (r : ForInStep UInt16),
    pile < 10 → WellFormedLayout g₁ → IsCanonicalPos g₁ p → H g₁ →
    PossibleKingsLocal p ki → ChildSpec H p →
    recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16 allkings pile w g₁
      = .ok r g₂ →
    Contributes p ki comp w g₁ r.value g₂ ∧ H g₂ ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g₂ = { g₁ with hashmap := hm }

/-! ## The pile loop, with the memo invariant and the frame carried along

`recLoop_body_sound` carries `LoopInv`; the recursion additionally needs the memo
invariant `H` and "only the memo table changed" threaded through the same loop, so
the three travel together in one `forIn_inv`. -/

theorem recLoop_all {H : Globals → Prop} (hSS : SubsetSound) (hMS : MoveSimulated)
    (hRB : RecBodyStep H)
    {g : Globals} {p : SolverPosType} {ki : KingInfo} {comp : UInt8} {allkings : UInt16}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hms : H g)
    (hkiloc : PossibleKingsLocal p ki) (hkic : KingInfoCorrect p ki) (hchild : ChildSpec H p)
    (hcomprun : EStateM.run (computeComponentKingBits p) g = .ok comp g)
    {v : UInt16} {gl : Globals}
    (hloop : forIn (List.range 10) (0 : UInt16)
      (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16 allkings) g
      = .ok v gl) :
    SoundBits gl p v ∧ LocalMask p v ∧ H gl ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, gl = { g with hashmap := hm } := by
  have hcomploc : LocalMask p comp.toUInt16 := localMask_component hcomprun
  have key := forIn_inv
    (fun (w : UInt16) (g₁ : Globals) => LoopInv p comp w g₁ ∧ H g₁ ∧
      ∃ hm : Vector UInt16 BIG_HASH_SIZE, g₁ = { g with hashmap := hm })
    (recBody solverRecCheckSolvable p (closureInfoOf p) ki comp.toUInt16 allkings)
    (List.range 10)
    (fun a ha b g₁ r g₂ hP hbody => by
      obtain ⟨hinv, hms₁, hm₁, rfl⟩ := hP
      obtain ⟨hcontrib, hms₂, hm₂, rfl⟩ :=
        hRB p ki comp allkings _ g₂ a b r (by simpa using ha) hinv.wf hinv.canon hms₁ hkiloc
          hchild hbody
      exact ⟨hinv.step hSS hMS hcomploc hkic hcontrib, hms₂, hm₂, rfl⟩)
    0 g v gl ⟨LoopInv.zero hwf hcan hcomprun, hms, g.hashmap, rfl⟩ hloop
  exact ⟨key.1.sound, key.1.isLocal, key.2.1, key.2.2⟩

/-! ## Soundness of `solverRecCheckSolvable` -/

/-- Every block is at least one bit wide, so the leaf's `1` is in-block. -/
theorem localMask_one (p : SolverPosType) : LocalMask p 1 := by
  have hnb : 1 ≤ (closureInfoOf p).numBits.toNat := by
    unfold closureInfoOf
    have h : ∀ f : Fin 11, 1 ≤ (closureInfos.get f).numBits.toNat := by decide
    exact h _
  show (1 : UInt16).toNat < _
  simp only [show ((1 : UInt16).toNat = 1) from rfl]
  calc 1 < 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (closureInfoOf p).numBits.toNat := Nat.pow_le_pow_right (by omega) hnb

/-- **`solverRecCheckSolvable` is sound**, modulo the two obligations above (both
discharged below) and the two semantic ones (`SubsetSound`, `MoveSimulated`).

The recursion is the `busyAces`-drain recipe: a `Nat` bounding `DepthSum p` in the
*theorem*, `induction` on it, `recCheck_eq` unfolding one level per step.  The three
branches are the `hash == 0` leaf, the memo hit, and the pile loop followed by the
memo write. -/
theorem recCheck_sound (hSS : SubsetSound) (hMS : MoveSimulated)
    (hPro : PrologueRuns) (hRB : RecBodyStep HashmapSound) : RecCheckSolvableSound := by
  suffices H : ∀ n : Nat, ∀ (g g' : Globals) (p : SolverPosType) (v : UInt16),
      SolverSpec.DepthSum p < n → WFGlobals g → IsCanonicalPos g p →
      EStateM.run (solverRecCheckSolvable p) g = .ok v g' →
      (SoundBits g p v ∧ LocalMask p v) ∧ HashmapSound g' ∧
        ∃ hm : Vector UInt16 BIG_HASH_SIZE, g' = { g with hashmap := hm } by
    intro g g' p v hwfg hcan hrun
    exact H (SolverSpec.DepthSum p + 1) g g' p v (by omega) hwfg hcan hrun
  intro n
  induction n with
  | zero => intro g g' p v hmeas; omega
  | succ n ih =>
    intro g g' p v hmeas hwfg hcan hrun
    have hfp : p.freePiles.toNat ≤ 10 := by
      have h := freePiles_bound hcan.toSolverInvMerged
      have : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
      omega
    by_cases hz : p.hash = 0
    · -- the leaf: already solved
      rw [recCheck_run_hash_zero g p hz] at hrun
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
      exact ⟨⟨soundBits_of_hash_zero hcan hz 1, localMask_one p⟩, hwfg.memo, g.hashmap, rfl⟩
    · by_cases hfree : slotRead g p.hash = UInt8.ofNat FREESLOT
      · -- the pile loop, then the memo write
        obtain ⟨⟨ki, hki, hkiloc, hkic⟩, ⟨comp, hcomp⟩⟩ := hPro g p hwfg.layout hcan
        obtain ⟨gl, hloop, rfl⟩ :=
          recCheck_run_loop_inv g g' p ki comp v hfp hz hfree hki hcomp hrun
        have hchild : ChildSpec HashmapSound p := fun child g₁ g₂ w hlt hwf₁ hcan₁ hms₁ hrun₁ =>
          ih g₁ g₂ child w (by omega) ⟨hwf₁, hms₁⟩ hcan₁ hrun₁
        obtain ⟨hsound, hlocal, hms', hm, rfl⟩ :=
          recLoop_all hSS hMS hRB hwfg.layout hcan hwfg.memo hkiloc hkic hchild hcomp hloop
        refine ⟨⟨hsound.of_set_hashmap, hlocal⟩, ?_, ?_⟩
        · exact hashmapSound_slotWrite (hwfg.layout.set_hashmap hm) (hcan.set_hashmap hm)
            hms' hsound hlocal
        · exact ⟨_, rfl⟩
      · -- a memo hit
        rw [recCheck_run_cached g p hfp hz hfree] at hrun
        obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
        rcases hwfg.memo p hcan (slotRead g p.hash) (getSlot_run g p.hash) with hfs | ⟨hs, hl⟩
        · exact absurd hfs hfree
        · exact ⟨⟨hs, hl⟩, hwfg.memo, g.hashmap, rfl⟩

/-! ## `usedSpace ≥ kingRefund`

`PrologueRuns`' only real content: the loop in `computeKingSpaces` writes
`possibleKings[4 - usedSpace']`, so it needs `-1 ≤ usedSpace'` where
`usedSpace' = usedSpace - kingRefund`.  The reason it holds is a counting argument:
for *any* set of suits, the freed king runs of those suits are free cards, distinct,
above their foundations, and never part of a flute — so they all sit in the cells or
on king piles, which is exactly what `usedSpace` counts. -/

/-- The counting bound in `Finset` form: `Finset.equivFin` supplies the injective
`Fin _`-family `usedSpace_ge_of_free_above` wants, and duplicate-freeness is free. -/
theorem usedSpace_ge_of_finset {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) (S : Finset UInt8)
    (hreal : ∀ c ∈ S, IsRealCard c)
    (hfree : ∀ c ∈ S, isFreeCard g p c)
    (haces : ∀ c ∈ S, ∀ hs : (SUIT c).toNat < 4, p.aces.get ⟨(SUIT c).toNat, hs⟩ < c)
    (hflute : ∀ c ∈ S, ∀ (j : Fin 10), 0 < (p.pileDepth.get j).toNat →
      ∀ m : Nat, 1 ≤ m → m < (p.pileFlute.get j).toNat →
      (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1,
          by have := h.pileDepth_bound j; omega⟩ - UInt8.ofNat m ≠ c) :
    (S.card : Int) ≤ p.usedSpace.toInt := by
  have hmem : ∀ i : Fin S.card, ((S.equivFin.symm i : {x // x ∈ S}) : UInt8) ∈ S :=
    fun i => (S.equivFin.symm i).2
  refine usedSpace_ge_of_free_above hwf h
    (fun i => ((S.equivFin.symm i : {x // x ∈ S}) : UInt8)) ?_ ?_ ?_ ?_ ?_
  · exact fun a b hab => S.equivFin.symm.injective (Subtype.ext hab)
  · exact fun i => hreal _ (hmem i)
  · exact fun i => hfree _ (hmem i)
  · exact fun i hs => haces _ (hmem i) hs
  · exact fun i j hdj m hm1 hm2 => hflute _ (hmem i) j hdj m hm1 hm2

private theorem add_ofNat_toNat (x : UInt8) (n : Nat) (h : x.toNat + n < 256) :
    (x + UInt8.ofNat n).toNat = x.toNat + n := by
  rw [UInt8.toNat_add, UInt8.toNat_ofNat']
  omega

/-- The freed king run of suit `su`: every card above `kings[su]`. -/
def kingRunSet (p : SolverPosType) (su : Suit) : Finset UInt8 :=
  (Finset.range (13 - (VALUE (p.kings.get (finOfSuit su))).toNat)).image
    (fun i => p.kings.get (finOfSuit su) + UInt8.ofNat (i + 1))

/-- The runs of all the suits a configuration puts on piles — the cards it refunds. -/
def kingRunsSet (p : SolverPosType) (k : Fin 16) : Finset UInt8 :=
  (piledSet k).biUnion (kingRunSet p)

/-- Members of `kingRunSet` in closed form. -/
theorem mem_kingRunSet {p : SolverPosType} {su : Suit} {c : UInt8} :
    c ∈ kingRunSet p su ↔ ∃ i : Nat, i < 13 - (VALUE (p.kings.get (finOfSuit su))).toNat ∧
      c = p.kings.get (finOfSuit su) + UInt8.ofNat (i + 1) := by
  simp only [kingRunSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- The suit's own card codes: `kings[su] + j` for `j ≤ 13 - VALUE kings[su]` never
carries out of the value nibble. -/
theorem kings_toNat_bound {g : Globals} {p : SolverPosType} (h : SolverInvBase g p) (su : Fin 4) :
    (p.kings.get su).toNat = su.val * 16 + (VALUE (p.kings.get su)).toNat
      ∧ (VALUE (p.kings.get su)).toNat ≤ 13 := by
  obtain ⟨-, -, hs, hv, -⟩ := h.aces_kings_valid su
  refine ⟨?_, hv⟩
  have h1 := SUIT_toNat (p.kings.get su)
  have h2 := VALUE_toNat (p.kings.get su)
  have h3 : (su.val.toUInt8).toNat = su.val := by
    rw [UInt8.toNat_ofNat']; have := su.isLt; omega
  have h4 := congrArg UInt8.toNat hs
  rw [h3] at h4
  omega

/-- Each run has exactly the length the refund charges. -/
theorem card_kingRunSet {g : Globals} {p : SolverPosType} (h : SolverInvBase g p) (su : Suit) :
    (kingRunSet p su).card = 13 - (VALUE (p.kings.get (finOfSuit su))).toNat := by
  obtain ⟨hk, hv⟩ := kings_toNat_bound h (finOfSuit su)
  have hsu4 := (finOfSuit su).isLt
  rw [kingRunSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have hta := add_ofNat_toNat (p.kings.get (finOfSuit su)) (a + 1) (by omega)
  have htb := add_ofNat_toNat (p.kings.get (finOfSuit su)) (b + 1) (by omega)
  -- ascribe the beta-reduced form: `congrArg` produces unreduced applications, which
  -- `omega` would treat as fresh atoms
  have heq : (p.kings.get (finOfSuit su) + UInt8.ofNat (a + 1)).toNat
      = (p.kings.get (finOfSuit su) + UInt8.ofNat (b + 1)).toNat := congrArg UInt8.toNat hab
  omega

/-- Everything the counting argument needs about a run member, in `Nat` form. -/
theorem kingRunSet_spec {g : Globals} {p : SolverPosType} (h : SolverInvBase g p)
    {su : Suit} {c : UInt8} (hc : c ∈ kingRunSet p su) :
    (SUIT c).toNat = (finOfSuit su).val
    ∧ (VALUE (p.kings.get (finOfSuit su))).toNat < (VALUE c).toNat
    ∧ 1 ≤ (VALUE c).toNat ∧ (VALUE c).toNat ≤ 13
    ∧ (p.kings.get (finOfSuit su)).toNat < c.toNat := by
  obtain ⟨i, hi, rfl⟩ := mem_kingRunSet.1 hc
  obtain ⟨hk, hv⟩ := kings_toNat_bound h (finOfSuit su)
  have hsu4 := (finOfSuit su).isLt
  have ht := add_ofNat_toNat (p.kings.get (finOfSuit su)) (i + 1) (by omega)
  have hs := SUIT_toNat (p.kings.get (finOfSuit su) + UInt8.ofNat (i + 1))
  have hvv := VALUE_toNat (p.kings.get (finOfSuit su) + UInt8.ofNat (i + 1))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Runs of different suits are disjoint — they differ in `SUIT`. -/
theorem kingRunSet_disjoint {g : Globals} {p : SolverPosType} (h : SolverInvBase g p)
    {su su' : Suit} (hne : su ≠ su') : Disjoint (kingRunSet p su) (kingRunSet p su') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  have h1 := (kingRunSet_spec h hc).1
  have h2 := (kingRunSet_spec h hc').1
  have : (finOfSuit su).val = (finOfSuit su').val := by omega
  exact hne (by revert this; cases su <;> cases su' <;> simp [finOfSuit])

theorem card_kingRunsSet {g : Globals} {p : SolverPosType} (h : SolverInvBase g p) (k : Fin 16) :
    (kingRunsSet p k).card
      = ∑ su ∈ piledSet k, (13 - (VALUE (p.kings.get (finOfSuit su))).toNat) := by
  rw [kingRunsSet, Finset.card_biUnion (fun su _ su' _ hne => kingRunSet_disjoint h hne)]
  exact Finset.sum_congr rfl (fun su _ => card_kingRunSet h su)

/-- **`usedSpace` covers any configuration's refund.**  The refunded cards are the
freed king runs of the piled suits: free (`king_frontier`), pairwise distinct,
strictly above their foundations, and never inside a flute — a flute card of the same
suit would force that pile's boundary to lie in the run too, hence to be free, which
`boundary_not_free` forbids. -/
theorem kingRefund_le_usedSpace {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) (k : Fin 16) :
    kingRefund p k ≤ p.usedSpace.toInt := by
  have hcard := usedSpace_ge_of_finset hwf h (kingRunsSet p k) ?_ ?_ ?_ ?_
  · -- the card of the run set *is* the refund
    rw [kingRefund_eq_sum]
    refine le_trans (le_of_eq ?_) hcard
    rw [card_kingRunsSet h k, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun su _ => ?_)
    have hv := (kings_toNat_bound h (finOfSuit su)).2
    rw [runLen]
    omega
  all_goals
    intro c hc
    rw [kingRunsSet, Finset.mem_biUnion] at hc
    obtain ⟨su, hsu, hcsu⟩ := hc
    obtain ⟨hs, hvgt, hv1, hv13, hklt⟩ := kingRunSet_spec h hcsu
    have hsu4 := (finOfSuit su).isLt
    have hsuit : SUIT c = (finOfSuit su).val.toUInt8 := by
      refine UInt8.toNat_inj.1 ?_
      rw [hs, UInt8.toNat_ofNat']
      omega
  · -- real
    exact ⟨by omega, hv1, hv13⟩
  · -- free: exactly `king_frontier`'s upper clause
    exact (h.king_frontier (finOfSuit su)).2 c hsuit hvgt hv13
  · -- strictly above the foundation
    intro hs4
    have hfin : (⟨(SUIT c).toNat, hs4⟩ : Fin 4) = finOfSuit su := Fin.ext hs
    rw [hfin]
    refine UInt8.lt_iff_toNat_lt.2 ?_
    have hak := (h.aces_kings_valid (finOfSuit su)).2.2.2.2
    have := UInt8.le_iff_toNat_le.1 hak
    omega
  · -- never inside a flute
    intro j hdj m hm1 hm2 heq
    have hb5 : (p.pileDepth.get j).toNat - 1 < 5 := by have := h.pileDepth_bound j; omega
    have hBreal : IsRealCard ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩) :=
      hwf.pos2card_real j ⟨_, hb5⟩
    have hfl := h.flute_le_value hwf j hdj
    have hBv := VALUE_toNat ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩)
    have hBs := SUIT_toNat ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩)
    -- `m < flute ≤ VALUE B`, so the subtraction stays inside the value nibble
    have hmle : (UInt8.ofNat m) ≤ (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩ := by
      refine UInt8.le_iff_toNat_le.2 ?_
      rw [UInt8.toNat_ofNat']
      omega
    have hsub := UInt8.toNat_sub_of_le _ _ hmle
    rw [UInt8.toNat_ofNat'] at hsub
    have hceq := congrArg UInt8.toNat heq
    rw [hsub] at hceq
    -- so `B` has `c`'s suit and a strictly larger value: `B` is in the run, hence free
    have hBsuit : SUIT ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩)
        = (finOfSuit su).val.toUInt8 := by
      refine UInt8.toNat_inj.1 ?_
      rw [UInt8.toNat_ofNat']
      have hcs := SUIT_toNat c
      have hcv := VALUE_toNat c
      omega
    have hBvgt : (VALUE (p.kings.get (finOfSuit su))).toNat
        < (VALUE ((g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩)).toNat := by
      have hcv := VALUE_toNat c
      omega
    exact boundary_not_free hwf h j hdj
      ((h.king_frontier (finOfSuit su)).2 _ hBsuit hBvgt hBreal.2.2)

/-! ## `PrologueRuns`

With `usedSpace ≥ kingRefund` in hand, `outerLoop_ok`'s last side condition
(`-1 ≤ blockSpace`) is discharged and both prologue computations are known to
succeed; neither writes the state. -/

set_option linter.unusedSimpArgs false in
theorem kingSpaces_run_exists_local {g : Globals} {p : SolverPosType}
    (hwf : WellFormedLayout g) (h : SolverInvBase g p) :
    ∃ ki : KingInfo, EStateM.run (computeKingSpaces (closureInfoOf p).shiftValue
      (closureInfoOf p).numBits p) g = .ok ki g ∧ PossibleKingsLocal p ki := by
  have hfits : (closureInfoOf p).shiftValue.toNat + (closureInfoOf p).numBits.toNat ≤ 16 := by
    unfold closureInfoOf; exact closureInfo_shift_add_numBits _
  have hnb : (closureInfoOf p).numBits.toNat ≤ 6 := by
    unfold closureInfoOf
    have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
    exact hh _
  obtain ⟨res, hres, hchar⟩ := outerLoop_ok (closureInfoOf p).shiftValue p g
    (List.range (closureInfoOf p).numBits.toNat) { possibleKings := mkVector 6 0 }
    (fun i hi => by
      rw [List.mem_range] at hi
      rw [cfgIdx_eq _ _ (by omega)]
      omega)
    (fun i hi => by rw [List.mem_range] at hi; omega)
    (fun i hi => by
      rw [List.mem_range] at hi
      rw [blockSpace_toInt_eq p h _ i (by omega)]
      have := kingRefund_le_usedSpace hwf h
        ⟨min ((closureInfoOf p).shiftValue.toNat + i) 15, by omega⟩
      omega)
  refine ⟨res, ?_, ?_⟩
  · rw [kingSpaces_eq_explicit]
    simp only [kingSpacesExplicit, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hres]
  · intro c
    refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
    by_cases h8 : i < 8
    · by_contra hcon
      rw [Bool.not_eq_false, hchar c i h8] at hcon
      rcases hcon with hz | ⟨hmem, -⟩
      · rw [show ((mkVector 6 (0 : UInt8)).get c = 0) from by fin_cases c <;> rfl,
          show ((0 : UInt8).toNat = 0) from rfl, Nat.zero_testBit] at hz
        exact absurd hz (by simp)
      · rw [List.mem_range] at hmem
        omega
    · have h256 : (res.possibleKings.get c).toNat < 256 :=
        (res.possibleKings.get c).toNat_lt_size
      exact Nat.testBit_lt_two_pow (by
        calc (res.possibleKings.get c).toNat < 256 := h256
          _ = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))

theorem localMask_of_possibleKings {p : SolverPosType} {ki : KingInfo}
    (hloc : PossibleKingsLocal p ki) (c : Fin 6) :
    LocalMask p (ki.possibleKings.get c).toUInt16 := by
  show ((ki.possibleKings.get c).toUInt16).toNat < _
  rw [UInt8.toNat_toUInt16]
  exact hloc c

set_option linter.unusedSimpArgs false in
theorem component_run_exists {g : Globals} {p : SolverPosType} (h : SolverInvMerged g p) :
    ∃ comp : UInt8, EStateM.run (computeComponentKingBits p) g = .ok comp g := by
  have hfpb := freePiles_bound h
  have hfpn : p.freePiles.toInt = (p.freePiles.toNat : Int) := rfl
  by_cases hfp : 1 ≤ p.freePiles.toNat ∧ p.freePiles.toNat ≤ 3
  · -- the enumerating branch: block index, loop, table lookup
    have hg1 : ((1 : UInt8) ≤ p.freePiles) := by
      rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega
    have hg3 : (p.freePiles ≤ (3 : UInt8)) := by
      rw [UInt8.le_iff_toNat_le, show ((3 : UInt8).toNat = 3) from rfl]; omega
    have hidx : (p.freePiles - 1).toUInt32.toNat = p.freePiles.toNat - 1 := by
      rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _
        (by rw [UInt8.le_iff_toNat_le]; show 1 ≤ _; omega)]
      rfl
    have hidx11 : (p.freePiles - 1).toUInt32.toNat < 11 := by rw [hidx]; omega
    have hinfo : closureInfos[(p.freePiles - 1).toUInt32.toNat]? = some (prevInfo p) := by
      rw [getElem?_pos closureInfos ((p.freePiles - 1).toUInt32.toNat) hidx11]
      exact congrArg some (congrArg closureInfos.get
        (Fin.ext (show (p.freePiles - 1).toUInt32.toNat
          = min (p.freePiles.toNat - 1) 10 from by rw [hidx]; omega)))
    have hfitsp : (prevInfo p).shiftValue.toNat + (prevInfo p).numBits.toNat ≤ 16 := by
      unfold prevInfo; exact closureInfo_shift_add_numBits _
    have hnbp : (prevInfo p).numBits.toNat ≤ 6 := by
      unfold prevInfo
      have hh : ∀ f : Fin 11, (closureInfos.get f).numBits.toNat ≤ 6 := by decide
      exact hh _
    have hoffp : (prevInfo p).offset.toNat + 2 ^ (prevInfo p).numBits.toNat ≤ 100 := by
      unfold prevInfo
      have hh : ∀ f : Fin 11,
          (closureInfos.get f).offset.toNat + 2 ^ (closureInfos.get f).numBits.toNat ≤ 100 := by
        decide
      exact hh _
    obtain ⟨result, hres, hchar⟩ := compLoop_run (prevInfo p) p g
      (List.range (prevInfo p).numBits.toNat) 0
      (fun i hi => by
        rw [List.mem_range] at hi
        rw [cfgIdx_eq _ _ (by omega)]
        omega)
      (fun i hi => by rw [List.mem_range] at hi; omega)
    -- the loop only sets bits below `numBits`, so the table index is in range
    have hbound : result.toNat < 2 ^ (prevInfo p).numBits.toNat := by
      refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
      by_cases h16 : i < 16
      · by_contra hcon
        rw [Bool.not_eq_false] at hcon
        rw [hchar i h16] at hcon
        simp only [show ((0 : UInt16).toNat = 0) from rfl, Nat.zero_testBit, Bool.false_eq_true,
          false_or, List.mem_range] at hcon
        omega
      · have h65536 : result.toNat < 65536 := result.toNat_lt_size
        exact Nat.testBit_lt_two_pow (by
          calc result.toNat < 65536 := h65536
            _ = 2 ^ 16 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega))
    have hidxsum : ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat
        = (prevInfo p).offset.toNat + result.toNat := by
      rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
      have h2 : (2 : Nat) ^ (prevInfo p).numBits.toNat ≤ 64 := by
        calc (2 : Nat) ^ (prevInfo p).numBits.toNat ≤ 2 ^ 6 :=
              Nat.pow_le_pow_right (by omega) hnbp
          _ = 64 := by norm_num
      omega
    have hlt100 : ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat < 100 := by
      rw [hidxsum]; omega
    have hct : componentTable[((prevInfo p).offset.toUInt32 + result.toUInt32).toNat]?
        = some (componentAt ((prevInfo p).offset.toNat + result.toNat)) := by
      rw [getElem?_pos componentTable _ hlt100]
      exact congrArg some (congrArg componentTable.get
        (Fin.ext (show ((prevInfo p).offset.toUInt32 + result.toUInt32).toNat
          = min ((prevInfo p).offset.toNat + result.toNat) 99 from by rw [hidxsum]; omega)))
    refine ⟨componentAt ((prevInfo p).offset.toNat + result.toNat), ?_⟩
    rw [component_eq_explicit]
    simp only [componentExplicit, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      Vector.getE, hg1, hg3, decide_true, Bool.and_self, reduceIte, hinfo, hres, hct]
  · -- the guard fails and the function returns `0`
    have hguard : ((1 : UInt8) ≤ p.freePiles && p.freePiles ≤ (3 : UInt8))
        = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.le_iff_toNat_le,
        show ((1 : UInt8).toNat = 1) from rfl, show ((3 : UInt8).toNat = 3) from rfl]
      omega
    refine ⟨0, ?_⟩
    simp only [EStateM.run, computeComponentKingBits, hguard, Bool.false_eq_true,
      reduceIte, pure, EStateM.pure]

/-- **Obligation 1, discharged.** -/
theorem prologueRuns : PrologueRuns := fun g p hwf hcan => by
  obtain ⟨ki, hki, hkiloc⟩ := kingSpaces_run_exists_local hwf hcan.toSolverInvBase
  exact ⟨⟨ki, hki, hkiloc, (kingSpaces_spec g p ki hcan.toSolverInvBase hki).1⟩,
    component_run_exists hcan.toSolverInvMerged⟩

/-- **Soundness of `solverRecCheckSolvable`, with the prologue discharged.**  The
body step is discharged too, at the end of this file; `recCheck_sound_of_semantics`
is the version with both in place. -/
theorem recCheck_sound_of_body (hSS : SubsetSound) (hMS : MoveSimulated)
    (hRB : RecBodyStep HashmapSound) : RecCheckSolvableSound :=
  recCheck_sound hSS hMS prologueRuns hRB

/-! ## From `solverGetDestination` to `move_merged`'s preconditions

`getDest_spec` says what the destination walk returns; `move_merged` wants that
repackaged as `MoveValid`/`DestValid`.  The only non-bookkeeping step is the
`toPile = EXTRA` case: "no pile's boundary is `B + n`" follows from
`round_trip_inv` — a card sits in exactly one slot, so if it were some pile's
boundary then `pftVal` would have been `1` and the walk would have named that
pile. -/

/-- A card is some pile's current boundary exactly when its `pftVal` is `1`. -/
theorem boundary_pftVal_one {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (h : SolverInvBase g p) (c : UInt8)
    (j : Fin 10) (hdj : 0 < (p.pileDepth.get j).toNat)
    (hb5 : (p.pileDepth.get j).toNat - 1 < 5)
    (hbnd : (g.pos2card.get j).get ⟨(p.pileDepth.get j).toNat - 1, hb5⟩ = c) :
    pftVal g p c = 1 := by
  obtain ⟨hpj, hdj'⟩ := hwf.round_trip_inv j ⟨(p.pileDepth.get j).toNat - 1, hb5⟩
  rw [hbnd] at hpj hdj'
  -- `Fin.val` of a literal `⟨…⟩` is an `omega` atom; ascribe the reduced form
  have hdepth : (cardDepth g c).toNat = (p.pileDepth.get j).toNat - 1 := hdj'
  have hpile : (cardPile g c).toNat = j.val := hpj
  clear hdj' hpj
  have hp10 : (cardPile g c).toNat < 10 := by have := j.isLt; omega
  have hjeq : (⟨(cardPile g c).toNat, hp10⟩ : Fin 10) = j := Fin.ext hpile
  have hbound := h.pileDepth_bound j
  have hda : ((p.pileDepth.get j).toInt32).toInt = ((p.pileDepth.get j).toNat : Int) :=
    uint8_toInt32_toInt _
  have hdb : ((cardDepth g c).toUInt32.toInt32).toInt = ((cardDepth g c).toNat : Int) :=
    uint8_toInt32_toInt _
  rw [pftVal_eq g p c hp10, hjeq]
  refine Int32.toInt_inj.mp ?_
  rw [int32_toInt_sub _ _ (by rw [hda, hdb]; omega) (by rw [hda, hdb]; omega), hda, hdb,
    show ((1 : Int32)).toInt = 1 from by decide]
  omega

/-- Converse of `boundary_pftVal_one`: `pftVal = 1` puts the card at its pile's
current boundary. -/
theorem pftVal_one_depth {g : Globals} {p : SolverPosType} (c : UInt8)
    (hp10 : (cardPile g c).toNat < 10) (hcd : (cardDepth g c).toNat ≤ 5)
    (h1 : pftVal g p c = 1) :
    (cardDepth g c).toNat + 1 = (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat := by
  have hda : ((p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toInt32).toInt
      = ((p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat : Int) := uint8_toInt32_toInt _
  have hdb : ((cardDepth g c).toUInt32.toInt32).toInt = ((cardDepth g c).toNat : Int) :=
    uint8_toInt32_toInt _
  have h255 : (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat < 256 :=
    (p.pileDepth.get ⟨(cardPile g c).toNat, hp10⟩).toNat_lt_size
  have := congrArg Int32.toInt (h1.symm.trans (pftVal_eq g p c hp10))
  rw [show ((1 : Int32)).toInt = 1 from by decide,
    int32_toInt_sub _ _ (by rw [hda, hdb]; omega) (by rw [hda, hdb]; omega), hda, hdb] at this
  omega

/-- `getDest_spec` restated in the `.toNat` spelling `move_merged` uses (the two are
definitionally equal, but `omega` treats `x.toNat` and `x.toNat` as unrelated
atoms — see the note in `lean-proof-gotchas`). -/
theorem getDest_spec' {g : Globals} {p : SolverPosType} {pile : UInt32}
    (hwf : WellFormedLayout g) (hcan : IsCanonicalPos g p) (hp : pile.toNat < 10)
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat)
    (hb5 : (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1 < 5) :
    let B := (g.pos2card.get ⟨pile.toNat, hp⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩
    (B = (p.kings.get ⟨(SUIT B).toNat,
            (hwf.pos2card_real ⟨pile.toNat, hp⟩ ⟨_, hb5⟩).1⟩) ∧
        solverGetDestination p pile g = .ok (10 + SUIT B) g)
    ∨ (∃ n : Nat, 1 ≤ n ∧ (VALUE B).toNat + n ≤ 13 ∧
        (∀ j, 1 ≤ j → j < n → isFreeCard g p (B + UInt8.ofNat j)) ∧
        ¬ isFreeCard g p (B + UInt8.ofNat n) ∧
        solverGetDestination p pile g
          = .ok (if (pftVal g p (B + UInt8.ofNat n) == 1) = true
                 then cardPile g (B + UInt8.ofNat n) else 14) g) :=
  getDest_spec g p pile hwf hcan hp hd

set_option maxHeartbeats 1000000 in
/-- **`solverGetDestination` establishes `move_merged`'s destination
preconditions.** -/
theorem destValid_of_getDest {g : Globals} {p : SolverPosType} (hwf : WellFormedLayout g)
    (hcan : IsCanonicalPos g p) {pile : UInt32} (hp : pile.toNat < 10)
    (hd : 0 < (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat)
    (hb5 : (p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1 < 5)
    {toPile : UInt8}
    (hrun : EStateM.run (solverGetDestination p pile) g = .ok toPile g) :
    SolverSpec.MoveValid g p pile toPile ∧
      SolverSpec.DestValid g p ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩) toPile := by
  have hbase := hcan.toSolverInvBase
  have hreal : IsRealCard ((g.pos2card.get ⟨pile.toNat, hp⟩).get
      ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩) := hwf.pos2card_real _ _
  have hmv10 : (⟨pile.toNat % 10, by omega⟩ : Fin 10) = ⟨pile.toNat, hp⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hp)
  have hdmv : 0 < (p.pileDepth.get ⟨pile.toNat % 10, by omega⟩).toNat := by rw [hmv10]; exact hd
  rcases getDest_spec' hwf hcan hp hd hb5 with ⟨hkeq, hrun'⟩ | ⟨n, hn1, hnle, hfree, hnf, hrun'⟩
  · -- king pile
    have htp := (EStateM.Result.ok.inj (hrun.symm.trans hrun')).1
    subst htp
    have hs4 : (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat < 4 := hreal.1
    have htpn : (10 + SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat
        = 10 + (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
          ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat := by
      rw [UInt8.toNat_add, show ((10 : UInt8).toNat = 10) from rfl]
      omega
    exact ⟨⟨hp, by omega, hdmv⟩, Or.inl ⟨⟨_, hs4⟩, rfl, hkeq.symm, htpn⟩⟩
  · -- the walk
    have hs4 : (SUIT ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩)).toNat < 4 := hreal.1
    obtain ⟨hsn, hvn⟩ := card_walk_suit_value _ n (by omega)
    have h64 : ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n).toNat < 64 :=
      card_walk_lt64 _ hs4 n (by omega)
    have hcreal : IsRealCard ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n) :=
      ⟨by rw [hsn]; exact hs4, by omega, by omega⟩
    have hcp10 := cardPile_lt10 g hwf _ h64
    have hcd5 := hwf.depth_le _ hcreal
    have htp := (EStateM.Result.ok.inj (hrun.symm.trans hrun')).1
    by_cases hpft : (pftVal g p ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n) == 1) = true
    · -- the card is at its own pile's boundary: that pile is the destination
      rw [if_pos hpft] at htp
      subst htp
      have hdep := pftVal_one_depth _ hcp10 hcd5 (beq_iff_eq.1 hpft)
      have hdb := hbase.pileDepth_bound ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
        ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩
      refine ⟨⟨hp, by omega, hdmv⟩,
        Or.inr ⟨n, hn1, hnle, hfree, hnf, Or.inl ⟨hcp10, by omega, by omega, ?_⟩⟩⟩
      have hidx : (⟨(p.pileDepth.get ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩).toNat - 1, by omega⟩ : Fin 5)
          = ⟨(cardDepth g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, by omega⟩ := by
        refine Fin.ext ?_
        show (p.pileDepth.get ⟨(cardPile g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat, hcp10⟩).toNat - 1
          = (cardDepth g ((g.pos2card.get ⟨pile.toNat, hp⟩).get
            ⟨(p.pileDepth.get ⟨pile.toNat, hp⟩).toNat - 1, hb5⟩ + UInt8.ofNat n)).toNat
        omega
      rw [hidx]
      exact hwf.round_trip _ hcreal (by omega)
    · -- at no pile's boundary: the destination is EXTRA
      rw [if_neg hpft] at htp
      subst htp
      refine ⟨⟨hp, by decide, hdmv⟩, Or.inr ⟨n, hn1, hnle, hfree, hnf, Or.inr ⟨by rfl, ?_⟩⟩⟩
      intro j hidx hdj heq
      exact hpft (by
        rw [beq_iff_eq]
        exact boundary_pftVal_one hwf hbase _ j hdj hidx heq)

/-! ## `solverGetMovable`: the run and its locality

`Contributes` wants the mask `solverGetMovable` returned *and* `LocalMask p` for it.
Locality is not part of `KingSpacesSpec` (whose bit characterization is stated only
below `numBits`), but `outerLoop_ok` gives it: the loop only ever sets bits in
`List.range numBits`. -/

set_option linter.unusedSimpArgs false in
/-- **`solverGetMovable`'s run, with locality.**  `fluteLen ≥ 1` (from `flute_pos`) is
what keeps the `fluteLen - 1` index inside `possibleKings`. -/
theorem getMovable_run {g : Globals} {p : SolverPosType} (ki : KingInfo)
    (fluteLen toPile : UInt8) (h1 : 1 ≤ fluteLen.toNat) (hloc : PossibleKingsLocal p ki) :
    ∃ mv : UInt16, EStateM.run (solverGetMovable ki (closureInfoOf p).shiftValue fluteLen toPile) g
      = .ok mv g ∧ LocalMask p mv := by
  have hzero : LocalMask p 0 := by
    show (0 : UInt16).toNat < _
    simp only [show ((0 : UInt16).toNat = 0) from rfl]
    exact Nat.two_pow_pos _
  by_cases hfl : (5 : UInt8) < fluteLen
  · refine ⟨0, ?_, hzero⟩
    simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
      show ((5 : UInt8) < fluteLen) = true from by simpa using hfl, reduceIte]
  · -- `fluteLen ≤ 5`, so both `possibleKings` indices are in range
    have hfl5 : fluteLen.toNat ≤ 5 := by
      by_contra hcon
      exact hfl (UInt8.lt_iff_toNat_lt.2 (by
        simp only [show ((5 : UInt8).toNat = 5) from rfl]; omega))
    have hi1 : ((fluteLen - 1).toUInt32).toNat < 6 := by
      rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ (by
        refine UInt8.le_iff_toNat_le.2 ?_
        simpa using h1)]
      simp only [show ((1 : UInt8).toNat = 1) from rfl]
      omega
    have hi0 : (fluteLen.toUInt32).toNat < 6 := by rw [UInt8.toNat_toUInt32]; omega
    have hg1 : ((5 : UInt8) < fluteLen) = false := by simpa using hfl
    by_cases htp10 : toPile < 10
    · refine ⟨(ki.possibleKings.get ⟨_, hi1⟩).toUInt16, ?_,
        localMask_of_possibleKings hloc ⟨_, hi1⟩⟩
      simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
        hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi1,
        show (toPile < 10) = true from by simpa using htp10]
      rfl
    · by_cases htp14 : toPile < 14
      · -- king pile: the `&&&` only shrinks, the `|||` stays in the block
        have hk4 : ((toPile - 10).toUInt32).toNat < 4 := by
          have h10n : 10 ≤ toPile.toNat := by
            by_contra hcon
            exact htp10 (UInt8.lt_iff_toNat_lt.2 (by
              simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega))
          have h10 : (10 : UInt8) ≤ toPile := UInt8.le_iff_toNat_le.2 (by
            simp only [show ((10 : UInt8).toNat = 10) from rfl]; omega)
          have h14 : toPile.toNat < 14 := by
            have h := UInt8.lt_iff_toNat_lt.1 htp14
            simp only [show ((14 : UInt8).toNat = 14) from rfl] at h
            omega
          rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ h10]
          simp only [show ((10 : UInt8).toNat = 10) from rfl]
          omega
        refine ⟨(ki.possibleKings.get ⟨_, hi0⟩).toUInt16 |||
            ((ki.possibleKings.get ⟨_, hi1⟩).toUInt16 &&&
              ((kingOnPileMap.get ⟨_, hk4⟩) >>> (closureInfoOf p).shiftValue.toUInt16)), ?_, ?_⟩
        · simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
            hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0, hi1, hk4,
            show (toPile < 10) = false from by simpa using htp10,
            show (toPile < 14) = true from by simpa using htp14]
          rfl
        · exact localMask_or (localMask_of_possibleKings hloc ⟨_, hi0⟩)
            (LocalMask.and_left _ (localMask_of_possibleKings hloc ⟨_, hi1⟩))
      · refine ⟨(ki.possibleKings.get ⟨_, hi0⟩).toUInt16, ?_,
          localMask_of_possibleKings hloc ⟨_, hi0⟩⟩
        simp only [EStateM.run, solverGetMovable, bind, EStateM.bind, pure, EStateM.pure,
          hg1, Bool.false_eq_true, reduceIte, Vector.getE, getElem?_pos, hi0,
          show (toPile < 10) = false from by simpa using htp10,
          show (toPile < 14) = false from by simpa using htp14]
        rfl

/-! ## Reading the pile-loop body off the code

`RecBodyStep` is discharged below.  The inversion is mechanical — every step of
`recBody` before the recursive call either reads a table or leaves `Globals` alone
— so the work is entirely in naming each step's run:

* `vector_getE_apply` / `vector_getE_error` for the four `getE`s (`pileDepth`,
  `pileFlute`, `closureInfos`, `subsetTable`);
* `getDest_spec'` for the destination walk and `destValid_of_getDest` for the
  `MoveValid`/`DestValid` it feeds `move_merged`;
* `getMovable_run` for the mask, `move_merged` for the move (which returns the
  *entry* globals, so the whole iteration writes only what the child writes);
* `ChildSpec` for the recursive call.

The only non-bookkeeping ingredient is `component_indep`: `LoopFrame` asks that
`computeComponentKingBits` still return `comp` after the child's memo write, and
that holds because the computation never reads `Globals` at all.
-/

/-! ## Monadic bookkeeping -/

theorem bind_ok {α β : Type} {x : EStateM Error Globals α} {f : α → EStateM Error Globals β}
    {g g' : Globals} {a : α} (h : x g = .ok a g') : (x >>= f) g = f a g' := by
  simp only [bind, EStateM.bind, h]

theorem bind_error {α β : Type} {x : EStateM Error Globals α} {f : α → EStateM Error Globals β}
    {g g' : Globals} {e : Error} (h : x g = .error e g') : (x >>= f) g = .error e g' := by
  simp only [bind, EStateM.bind, h]

theorem vector_getE_apply {α : Type} {n : Nat} (v : Vector α n) (i : UInt32) (g : Globals)
    (h : i.toNat < n) :
    (v.getE i : EStateM Error Globals α) g = .ok (v.get ⟨i.toNat, h⟩) g := by
  simp only [Vector.getE, pure, getElem?_pos v i.toNat h]
  rfl

theorem vector_getE_error {α : Type} {n : Nat} (v : Vector α n) (i : UInt32) (g : Globals)
    (h : ¬ i.toNat < n) :
    (v.getE i : EStateM Error Globals α) g = .error Error.ArrayOutOfBounds g := by
  simp only [Vector.getE, getElem?_neg v i.toNat h]
  rfl

/-- The code's `movable''` is `movableComp`: the two only differ in how the guard is
spelled (`!= 0` as a `Bool`, `≠ 0` as a `Prop`). -/
theorem movableComp_eq (x y : UInt16) :
    (if (x &&& y != 0) = true then x ||| y else x) = movableComp x y := by
  unfold movableComp
  by_cases hz : x &&& y = 0
  · rw [if_neg (by simp [hz]), if_neg (by simp [hz])]
  · rw [if_pos (by simpa using hz), if_pos hz]

/-- The body's tail: whichever way the `break` test goes, the iteration's value is the
accumulated `sol` and the state is untouched. -/
theorem tail_run {A allkings : UInt16} {g g' : Globals} {r : ForInStep UInt16}
    (h : (if (A == allkings) = true then (pure (.done A) : EStateM Error Globals (ForInStep UInt16))
        else pure (.yield A)) g = .ok r g') : r.value = A ∧ g' = g := by
  by_cases hb : (A == allkings) = true
  · rw [if_pos hb] at h
    simp only [pure, EStateM.pure] at h
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj h
    exact ⟨rfl, rfl⟩
  · rw [if_neg hb] at h
    simp only [pure, EStateM.pure] at h
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj h
    exact ⟨rfl, rfl⟩

theorem ofNat_pile_toNat {pile : Nat} (h : pile < 10) : (UInt32.ofNat pile).toNat = pile := by
  simp only [UInt32.toNat_ofNat']
  omega

/-! ## `computeComponentKingBits` does not read `Globals` -/

/-- The per-configuration loop threads the state untouched and its result does not
depend on it (`compBody_run` is an *explicit* run, uniform in the state). -/
theorem compLoop_indep (info : ClosureInfo) (game : SolverPosType) :
    ∀ (l : List Nat) (r res : UInt16) (s t : Globals),
      (∀ i ∈ l, cfgIdx info.shiftValue i < 16) →
      forIn l r (compBody info game) s = .ok res s →
      forIn l r (compBody info game) t = .ok res t := by
  intro l
  induction l with
  | nil =>
    intro r res s t _ h
    rw [List.forIn_nil] at h ⊢
    simp only [pure, EStateM.pure] at h ⊢
    exact congrArg (fun x => EStateM.Result.ok x t) (EStateM.Result.ok.inj h).1
  | cons i l ih =>
    intro r res s t hcfg h
    rw [List.forIn_cons] at h ⊢
    simp only [bind, EStateM.bind, compBody_run info game s i r (hcfg i (by simp))] at h
    simp only [bind, EStateM.bind, compBody_run info game t i r (hcfg i (by simp))]
    exact ih _ _ s t (fun j hj => hcfg j (by simp [hj])) h

/-- **`computeComponentKingBits` is state-independent**: it reads only `game` and the
static tables, so its run transports to any other `Globals`.  This is the clause of
`LoopFrame` the recursive call's memo write has to survive. -/
theorem component_indep {p : SolverPosType} {comp : UInt8} {s t : Globals}
    (h : EStateM.run (computeComponentKingBits p) s = .ok comp s) :
    EStateM.run (computeComponentKingBits p) t = .ok comp t := by
  rw [EStateM.run, component_eq_explicit, componentExplicit] at h ⊢
  by_cases hguard : ((1 : UInt8) ≤ p.freePiles && p.freePiles ≤ (3 : UInt8)) = true
  · rw [if_pos hguard] at h ⊢
    by_cases hi11 : (p.freePiles - 1).toUInt32.toNat < 11
    · rw [bind_ok (vector_getE_apply closureInfos _ s hi11)] at h
      rw [bind_ok (vector_getE_apply closureInfos _ t hi11)]
      set info := closureInfos.get ⟨(p.freePiles - 1).toUInt32.toNat, hi11⟩ with hinfo
      have hfits : info.shiftValue.toNat + info.numBits.toNat ≤ 16 := by
        rw [hinfo]; exact closureInfo_shift_add_numBits _
      have hcfg : ∀ i ∈ List.range info.numBits.toNat, cfgIdx info.shiftValue i < 16 := by
        intro i hi
        rw [List.mem_range] at hi
        rw [cfgIdx_eq _ _ (by omega)]
        omega
      obtain ⟨result, hres, -⟩ := compLoop_run info p s (List.range info.numBits.toNat) 0 hcfg
        (fun i hi => by rw [List.mem_range] at hi; omega)
      rw [bind_ok hres] at h
      rw [bind_ok (compLoop_indep info p _ 0 result s t hcfg hres)]
      by_cases h100 : (info.offset.toUInt32 + result.toUInt32).toNat < 100
      · rw [bind_ok (vector_getE_apply componentTable _ s h100)] at h
        rw [bind_ok (vector_getE_apply componentTable _ t h100)]
        simp only [pure, EStateM.pure] at h ⊢
        exact congrArg (fun x => EStateM.Result.ok x t) (EStateM.Result.ok.inj h).1
      · rw [bind_error (vector_getE_error componentTable _ s h100)] at h
        exact absurd h (by simp)
    · rw [bind_error (vector_getE_error closureInfos _ s hi11)] at h
      exact absurd h (by simp)
  · rw [if_neg hguard] at h ⊢
    simp only [pure, EStateM.pure] at h ⊢
    exact congrArg (fun x => EStateM.Result.ok x t) (EStateM.Result.ok.inj h).1

theorem recBodyStep (H : Globals → Prop) : RecBodyStep H := by
  intro p ki comp allkings g₁ g₂ pile w r hpile hwf hcan hms hkiloc hchild hrun
  have hidx : (UInt32.ofNat pile).toNat < 10 := by
    rw [ofNat_pile_toNat hpile]; exact hpile
  rw [recBody, bind_ok (vector_getE_apply p.pileDepth (UInt32.ofNat pile) g₁ hidx)] at hrun
  by_cases hdz : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩ == 0) = true
  · -- the pile is empty: nothing happens
    rw [if_pos hdz] at hrun
    replace hrun : EStateM.Result.ok (ForInStep.yield w) g₁ = .ok r g₂ := hrun
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
    exact ⟨Or.inl ⟨rfl, rfl⟩, hms, g₁.hashmap, rfl⟩
  · rw [if_neg hdz,
      bind_ok (show (pure PUnit.unit : EStateM Error Globals PUnit) g₁ = .ok PUnit.unit g₁ from rfl)]
      at hrun
    dsimp only at hrun
    rw [bind_ok (vector_getE_apply p.pileFlute (UInt32.ofNat pile) g₁ hidx)] at hrun
    -- the pile is non-empty, so the destination walk and the move both make sense
    have hd : 0 < (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat := by
      rcases Nat.eq_zero_or_pos (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat with h | h
      · exact absurd (by simpa using UInt8.toNat_inj.1 (h.trans rfl.symm)) hdz
      · exact h
    have hb5 : (p.pileDepth.get ⟨(UInt32.ofNat pile).toNat, hidx⟩).toNat - 1 < 5 := by
      have := hcan.toSolverInvBase.pileDepth_bound ⟨(UInt32.ofNat pile).toNat, hidx⟩
      omega
    obtain ⟨toPile, hgd⟩ : ∃ tp : UInt8,
        solverGetDestination p (UInt32.ofNat pile) g₁ = .ok tp g₁ := by
      rcases getDest_spec' hwf hcan hidx hd hb5 with ⟨-, h⟩ | ⟨n, -, -, -, -, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    rw [bind_ok hgd] at hrun
    obtain ⟨mv, hmvrun, hmvloc⟩ := getMovable_run (g := g₁) ki
      (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile
      (hcan.toSolverInvBase.flute_pos ⟨(UInt32.ofNat pile).toNat, hidx⟩) hkiloc
    have hmvapp : solverGetMovable ki (closureInfoOf p).shiftValue
        (p.pileFlute.get ⟨(UInt32.ofNat pile).toNat, hidx⟩) toPile g₁ = .ok mv g₁ := hmvrun
    rw [bind_ok hmvapp] at hrun
    by_cases hnew : (mv &&& ~~~w != 0) = true
    · rw [if_pos hnew, bind_ok (show (get : EStateM Error Globals Globals) g₁ = .ok g₁ g₁ from rfl)]
        at hrun
      obtain ⟨hvalid, hdv⟩ := destValid_of_getDest hwf hcan hidx hd hb5 hgd
      obtain ⟨fk, p', hmove, hcan', hmeas⟩ :=
        SolverSpec.move_merged g₁ p (UInt32.ofNat pile) toPile hwf hcan hvalid hidx hb5 _ rfl hdv
      rw [hmove] at hrun
      dsimp only at hrun
      rw [bind_ok (show (set g₁ : EStateM Error Globals PUnit) g₁ = .ok PUnit.unit g₁ from rfl)]
        at hrun
      have hfp' : p'.freePiles.toNat ≤ 10 := by
        have h := freePiles_bound hcan'.toSolverInvMerged
        have : p'.freePiles.toInt = (p'.freePiles.toNat : Int) := rfl
        omega
      rw [bind_ok (closureInfos_getE_apply g₁ p' hfp')] at hrun
      -- the recursive call
      cases hcs : solverRecCheckSolvable p' g₁ with
      | error e s => rw [bind_error hcs] at hrun; exact absurd hrun (by simp)
      | ok cs g₃ =>
        rw [bind_ok hcs] at hrun
        obtain ⟨⟨hcssound, hcsloc⟩, hms₃, hm₃, rfl⟩ := hchild p' g₁ g₃ cs hmeas hwf hcan' hms hcs
        -- the `subsetTable` lookup: the child's answer stays inside the child's block,
        -- and every block fits below `100`
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
        have h64 : (2 : Nat) ^ (closureInfoOf p').numBits.toNat ≤ 64 :=
          calc (2 : Nat) ^ (closureInfoOf p').numBits.toNat ≤ 2 ^ 6 :=
                Nat.pow_le_pow_right (by omega) hnb'
            _ = 64 := by norm_num
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
        obtain ⟨hrval, rfl⟩ := tail_run hrun
        have hfin : (⟨(UInt32.ofNat pile).toNat % 10, by omega⟩ : Fin 10)
            = ⟨(UInt32.ofNat pile).toNat, hidx⟩ := Fin.ext (Nat.mod_eq_of_lt hidx)
        refine ⟨Or.inr ⟨p', UInt32.ofNat pile, toPile, mv, cs, fk, hmvloc, hidx, ?_, hgd, ?_,
          hmove, hcsloc, hcssound, ⟨_, hcs⟩, ?_, ?_⟩, hms₃, hm₃, rfl⟩
        · rw [hfin]; exact hd
        · rw [hfin]; exact hmvrun
        · rw [hrval, movableComp_eq, movablePrime]
        · exact ⟨fun h => h.set_hashmap hm₃, fun h => h.set_hashmap hm₃,
            fun h => component_indep h, fun _ h => h.set_hashmap hm₃⟩
    · rw [if_neg hnew] at hrun
      replace hrun : EStateM.Result.ok (ForInStep.yield w) g₁ = .ok r g₂ := hrun
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hrun
      exact ⟨Or.inl ⟨rfl, rfl⟩, hms, g₁.hashmap, rfl⟩

/-- **Soundness of `solverRecCheckSolvable`, with both syntactic obligations
discharged.**  What remains are only the two *semantic* hypotheses: `SubsetSound`
(the `subsetTable` expansion really is reachable) and `MoveSimulated` (the solver's
move simulates a real move). -/
theorem recCheck_sound_of_semantics (hSS : SubsetSound) (hMS : MoveSimulated) :
    RecCheckSolvableSound :=
  recCheck_sound hSS hMS prologueRuns (recBodyStep HashmapSound)
