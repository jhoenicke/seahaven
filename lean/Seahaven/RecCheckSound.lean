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
  refine UInt8_eq_of_toNat_eq (h.pileDepth_nonneg i) (by decide) ?_
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
