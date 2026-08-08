import Seahaven.RecCheckSound

/-!
# `initcard` establishes the global invariants

`initcard` is the solver's one-time setup: it zeroes the memo table and deals the
52 shuffled cards column-by-column into the ten piles, recording for every card
its pile (`card2pile`), its depth in that pile (`card2depth`), and — for the 50
cards that actually land in a pile — the inverse map `pos2card`.

Two things have to come out of it:

* **`WellFormedLayout`** — the deal arrays are mutually consistent.  This needs
  the shuffle to be a genuine permutation of the 52 card codes `1…52`
  (`IsDeal`): injectivity keeps a later card from overwriting an earlier one's
  `card2pile`/`card2depth` entry, and surjectivity (derived from injectivity by
  pigeonhole) is what makes every real card appear in `pos2card`.
* **`HashmapCorrect` / `HashmapSound`** — trivial: `SolverInit` zeroes the table,
  and a zero word never matches a key's 9-bit tag (which is `≥ 1`), so every
  slot reads back as `FREESLOT`.
-/

/-! ## The loop body, mirrored -/

/-- The body of `initcard`'s deal loop, mirrored as a standalone definition
(join point spelled out, as the `do` elaborator produces it). -/
def initBody (cardshuffle : Vector UInt8 52) (i : Nat) (_r : PUnit) :
    EStateM Error Globals (ForInStep PUnit) := do
  let ci ← cardshuffle.getE (UInt32.ofNat i)
  have suit : UInt8 := (ci - 1) / 13
  have card : UInt8 := CARD suit (ci - 13 * suit)
  let g ← get
  let __do_lift ← g.card2pile.setE card.toUInt32 (UInt8.ofNat (i % 10))
  have g : Globals := { g with card2pile := __do_lift }
  let __do_lift ← g.card2depth.setE card.toUInt32 (UInt8.ofNat (i / 10))
  have g : Globals := { g with card2depth := __do_lift }
  have __do_jp : Globals → PUnit → EStateM Error Globals (ForInStep PUnit) := fun g _y => do
    set g
    pure (ForInStep.yield PUnit.unit)
  if i < 50 then do
      let innerVec ← g.pos2card.getE (UInt32.ofNat (i % 10))
      let innerVec ← innerVec.setE (UInt32.ofNat (i / 10)) card
      let __do_lift ← g.pos2card.setE (UInt32.ofNat (i % 10)) innerVec
      have g : Globals := { g with pos2card := __do_lift }
      let _y ← pure PUnit.unit
      __do_jp g _y
    else do
      let _y ← pure PUnit.unit
      __do_jp g _y

set_option maxHeartbeats 1000000 in
/-- The `rfl`-twin: `initcard` with its `for` loop presented as `forIn … initBody`. -/
theorem initcard_eq (sh : Vector UInt8 52) :
    initcard sh = (do SolverInit; forIn (List.range 52) PUnit.unit (initBody sh); pure PUnit.unit) :=
  rfl

/-! ## Decoding a shuffle entry

The four facts below are pure `UInt8` arithmetic over the 256 possible shuffle
entries, so `decide` settles them; they are the only place the packing
`suit*16 + value` vs `suit*13 + value` is unfolded. -/

set_option maxRecDepth 10000

/-- The card code the solver derives from shuffle entry `ci ∈ 1…52`:
suit `(ci-1)/13`, value `ci - 13·suit`, packed as `suit*16 + value`. -/
def decodeShuffle (ci : UInt8) : UInt8 :=
  CARD ((ci - 1) / 13) (ci - 13 * ((ci - 1) / 13))

/-- The card dealt at deal position `i` (`0` outside the deal, never used). -/
def dealCard (sh : Vector UInt8 52) (i : Nat) : UInt8 :=
  if h : i < 52 then decodeShuffle (sh[i]'h) else 0

/-- The inverse of `decodeShuffle` on real cards: `suit*13 + value`. -/
def encodeShuffle (c : UInt8) : UInt8 := 13 * (SUIT c) + VALUE c

/-- `decodeShuffle` lands in the real cards. -/
theorem decodeShuffle_real {ci : UInt8} (h1 : 1 ≤ ci.toNat) (h2 : ci.toNat ≤ 52) :
    IsRealCard (decodeShuffle ci) := by
  revert h1 h2
  revert ci
  decide

/-- `decodeShuffle` codes are valid `card2*` indices. -/
theorem decodeShuffle_lt {ci : UInt8} (h1 : 1 ≤ ci.toNat) (h2 : ci.toNat ≤ 52) :
    (decodeShuffle ci).toNat < 64 := by
  revert h1 h2
  revert ci
  decide

/-- `encodeShuffle` undoes `decodeShuffle` — hence `decodeShuffle` is injective
on `1…52`. -/
theorem encodeShuffle_decodeShuffle {ci : UInt8} (h1 : 1 ≤ ci.toNat) (h2 : ci.toNat ≤ 52) :
    encodeShuffle (decodeShuffle ci) = ci := by
  revert h1 h2
  revert ci
  decide

/-- Every real card is `decodeShuffle` of its own code, and that code is in range. -/
theorem decodeShuffle_encodeShuffle {c : UInt8} (h : IsRealCard c) :
    decodeShuffle (encodeShuffle c) = c ∧ 1 ≤ (encodeShuffle c).toNat ∧
      (encodeShuffle c).toNat ≤ 52 := by
  revert h
  revert c
  decide

/-! ## One step of the deal loop -/

/-- Pure model of one `initBody` step: record card `c`'s pile and depth, and —
for the 50 cards that land in a pile — its `pos2card` slot. -/
def initStep (g : Globals) (c : UInt8) (hc : c.toNat < 64) (i : Nat) : Globals :=
  let g1 : Globals := { g with
    card2pile  := g.card2pile.set c.toNat (UInt8.ofNat (i % 10)) hc,
    card2depth := g.card2depth.set c.toNat (UInt8.ofNat (i / 10)) hc }
  if h : i < 50 then
    let inner := (g1.pos2card[i % 10]'(by omega)).set (i / 10) c (by omega)
    { g1 with pos2card := g1.pos2card.set (i % 10) inner (by omega) }
  else g1

set_option linter.unusedSimpArgs false in
/-- Exact symbolic run of one loop iteration. -/
theorem initBody_run (sh : Vector UInt8 52) (i : Nat) (hi : i < 52) (g : Globals)
    (hc : (dealCard sh i).toNat < 64) :
    initBody sh i PUnit.unit g
      = .ok (ForInStep.yield PUnit.unit) (initStep g (dealCard sh i) hc i) := by
  have htu : ∀ x : UInt8, x.toUInt32.toNat = x.toNat := fun _ => rfl
  have hidx : (UInt32.ofNat i).toNat = i := by rw [UInt32.toNat_ofNat']; omega
  have hmod : (UInt32.ofNat (i % 10)).toNat = i % 10 := by rw [UInt32.toNat_ofNat']; omega
  have hdiv : (UInt32.ofNat (i / 10)).toNat = i / 10 := by rw [UInt32.toNat_ofNat']; omega
  have hcard : dealCard sh i = CARD ((sh[i]'hi - 1) / 13) (sh[i]'hi - 13 * ((sh[i]'hi - 1) / 13)) := by
    simp only [dealCard, dif_pos hi, decodeShuffle]
  -- index bounds, in the raw spelling the unfolded code produces
  have hc' : (dealCard sh i).toNat < 64 := hc
  rw [hcard] at hc'
  have hp : i % 10 < 10 := by omega
  by_cases h50 : i < 50
  · have hd : i / 10 < 5 := by omega
    unfold initBody
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
      pure, EStateM.pure, Vector.getE, Vector.setE, getElem?_pos, hidx, hi, htu, hmod, hdiv,
      hc', hp, hd, dif_pos trivial, dif_pos h50, if_pos h50, initStep, hcard]
  · unfold initBody
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
      pure, EStateM.pure, Vector.getE, Vector.setE, getElem?_pos, hidx, hi, htu,
      dif_pos hc', if_neg h50, dif_neg h50, initStep, hcard]

/-! ## The shuffle is a permutation -/

/-- The input to `initcard` is a genuine deal: every entry is a card code in
`1…52` and no code repeats.  (Surjectivity onto the 52 codes then follows —
`IsDeal.surj` below.) -/
structure IsDeal (sh : Vector UInt8 52) : Prop where
  mem : ∀ (i : Nat) (h : i < 52), 1 ≤ (sh[i]'h).toNat ∧ (sh[i]'h).toNat ≤ 52
  inj : ∀ (i j : Nat) (hi : i < 52) (hj : j < 52), (sh[i]'hi) = (sh[j]'hj) → i = j

namespace IsDeal

theorem card_real {sh : Vector UInt8 52} (hd : IsDeal sh) {i : Nat} (h : i < 52) :
    IsRealCard (dealCard sh i) := by
  rw [dealCard, dif_pos h]
  exact decodeShuffle_real (hd.mem i h).1 (hd.mem i h).2

theorem card_lt {sh : Vector UInt8 52} (hd : IsDeal sh) {i : Nat} (h : i < 52) :
    (dealCard sh i).toNat < 64 := by
  rw [dealCard, dif_pos h]
  exact decodeShuffle_lt (hd.mem i h).1 (hd.mem i h).2

/-- Distinct deal positions hold distinct cards — `encodeShuffle` inverts the
decoding, so a repeated card would be a repeated shuffle entry. -/
theorem card_inj {sh : Vector UInt8 52} (hd : IsDeal sh) {i j : Nat} (hi : i < 52) (hj : j < 52)
    (h : dealCard sh i = dealCard sh j) : i = j := by
  rw [dealCard, dif_pos hi] at h
  rw [dealCard, dif_pos hj] at h
  refine hd.inj i j hi hj ?_
  have h1 := encodeShuffle_decodeShuffle (hd.mem i hi).1 (hd.mem i hi).2
  have h2 := encodeShuffle_decodeShuffle (hd.mem j hj).1 (hd.mem j hj).2
  rw [← h1, ← h2, h]

/-- Every real card is dealt somewhere: injectivity on the finite type `Fin 52`
is surjectivity. -/
theorem surj {sh : Vector UInt8 52} (hd : IsDeal sh) {c : UInt8} (hc : IsRealCard c) :
    ∃ i, ∃ _h : i < 52, dealCard sh i = c := by
  -- The shuffle, read as a map `Fin 52 → Fin 52` on codes shifted down by one.
  let f : Fin 52 → Fin 52 := fun i =>
    ⟨(sh[i.val]'i.isLt).toNat - 1, by have := hd.mem i.val i.isLt; omega⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 := hd.mem a.val a.isLt
    have h2 := hd.mem b.val b.isLt
    have heq : (sh[a.val]'a.isLt).toNat = (sh[b.val]'b.isLt).toNat := by
      have hv := congrArg Fin.val hab
      simp only [f] at hv
      omega
    exact Fin.ext (hd.inj a.val b.val a.isLt b.isLt (UInt8.toNat_inj.1 heq))
  obtain ⟨hdec, hlo, hhi⟩ := decodeShuffle_encodeShuffle hc
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hfinj)
    ⟨(encodeShuffle c).toNat - 1, by omega⟩
  refine ⟨i.val, i.isLt, ?_⟩
  have hval := congrArg Fin.val hi
  simp only [f] at hval
  have hmem := hd.mem i.val i.isLt
  have hsh : (sh[i.val]'i.isLt) = encodeShuffle c := UInt8.toNat_inj.1 (by omega)
  rw [dealCard, dif_pos i.isLt, hsh, hdec]

end IsDeal

/-! ## The loop invariant -/

theorem cardPile_eq {g : Globals} {c : UInt8} (h : c.toNat < 64) :
    cardPile g c = g.card2pile[c.toNat]'h := by
  rw [cardPile, dif_pos h]; rfl

theorem cardDepth_eq {g : Globals} {c : UInt8} (h : c.toNat < 64) :
    cardDepth g c = g.card2depth[c.toNat]'h := by
  rw [cardDepth, dif_pos h]; rfl

/-- What holds of the globals after the first `k` deal positions have been
processed.  The two global bounds are what `WellFormedLayout` needs at *every*
index (including the twelve non-card codes, which the loop never writes); the
two positional clauses record where the first `k` cards went. -/
structure InitInv (sh : Vector UInt8 52) (k : Nat) (g : Globals) : Prop where
  pile_lt : ∀ (n : Nat) (h : n < 64), (g.card2pile[n]'h).toNat < 10
  depth_le : ∀ (n : Nat) (h : n < 64), (g.card2depth[n]'h).toNat ≤ 5
  located : ∀ (j : Nat), j < k → j < 52 →
      cardPile g (dealCard sh j) = UInt8.ofNat (j % 10) ∧
      cardDepth g (dealCard sh j) = UInt8.ofNat (j / 10)
  placed : ∀ (p d : Nat) (hp : p < 10) (hd : d < 5), d * 10 + p < k →
      (g.pos2card[p]'hp)[d]'hd = dealCard sh (d * 10 + p)
  memo_zero : ∀ (n : Nat) (h : n < BIG_HASH_SIZE), g.hashmap[n]'h = 0

/-! ### One step preserves the invariant -/

theorem initStep_card2pile (g : Globals) (c : UInt8) (hc : c.toNat < 64) (i : Nat) :
    (initStep g c hc i).card2pile = g.card2pile.set c.toNat (UInt8.ofNat (i % 10)) hc := by
  unfold initStep; split <;> rfl

theorem initStep_card2depth (g : Globals) (c : UInt8) (hc : c.toNat < 64) (i : Nat) :
    (initStep g c hc i).card2depth = g.card2depth.set c.toNat (UInt8.ofNat (i / 10)) hc := by
  unfold initStep; split <;> rfl

theorem initStep_pos2card_lt (g : Globals) (c : UInt8) (hc : c.toNat < 64) {i : Nat}
    (h : i < 50) :
    (initStep g c hc i).pos2card = g.pos2card.set (i % 10)
      ((g.pos2card[i % 10]'(by omega)).set (i / 10) c (by omega)) (by omega) := by
  unfold initStep; rw [dif_pos h]

theorem initStep_pos2card_ge (g : Globals) (c : UInt8) (hc : c.toNat < 64) {i : Nat}
    (h : ¬ i < 50) : (initStep g c hc i).pos2card = g.pos2card := by
  unfold initStep; rw [dif_neg h]

theorem initInv_step {sh : Vector UInt8 52} (hdeal : IsDeal sh) {k : Nat} (hk : k < 52)
    {g : Globals} (hinv : InitInv sh k g) :
    InitInv sh (k + 1) (initStep g (dealCard sh k) (hdeal.card_lt hk) k) where
  pile_lt n hn := by
    rw [initStep_card2pile, Vector.getElem_set]
    split
    · rw [UInt8.toNat_ofNat']; omega
    · exact hinv.pile_lt n hn
  depth_le n hn := by
    rw [initStep_card2depth, Vector.getElem_set]
    split
    · rw [UInt8.toNat_ofNat']; omega
    · exact hinv.depth_le n hn
  located j hjk hj := by
    have hcj : (dealCard sh j).toNat < 64 := hdeal.card_lt hj
    have hck : (dealCard sh k).toNat < 64 := hdeal.card_lt hk
    rw [cardPile_eq hcj, cardDepth_eq hcj, initStep_card2pile, initStep_card2depth,
      Vector.getElem_set, Vector.getElem_set]
    rcases Nat.lt_or_ge j k with hlt | hge
    · -- an earlier card: a different index, so untouched
      have hne : (dealCard sh k).toNat ≠ (dealCard sh j).toNat := by
        intro he
        exact absurd (hdeal.card_inj hk hj (UInt8.toNat_inj.1 he)) (by omega)
      rw [if_neg hne, if_neg hne]
      have := hinv.located j hlt hj
      rw [cardPile_eq hcj, cardDepth_eq hcj] at this
      exact this
    · -- the card just written
      have hjk' : j = k := by omega
      subst hjk'
      rw [if_pos rfl, if_pos rfl]
      exact ⟨rfl, rfl⟩
  memo_zero n hn := by
    have : (initStep g (dealCard sh k) (hdeal.card_lt hk) k).hashmap = g.hashmap := by
      unfold initStep; split <;> rfl
    rw [this]; exact hinv.memo_zero n hn
  placed p d hp hd hpk := by
    have hck : (dealCard sh k).toNat < 64 := hdeal.card_lt hk
    rcases Nat.lt_or_ge (d * 10 + p) k with hlt | hge
    · -- an earlier slot
      by_cases h50 : k < 50
      · by_cases hpe : k % 10 = p
        · subst hpe
          rw [initStep_pos2card_lt _ _ _ h50, Vector.getElem_set, if_pos rfl,
            Vector.getElem_set, if_neg (by omega)]
          exact hinv.placed _ d hp hd hlt
        · rw [initStep_pos2card_lt _ _ _ h50, Vector.getElem_set, if_neg hpe]
          exact hinv.placed p d hp hd hlt
      · rw [initStep_pos2card_ge _ _ _ h50]
        exact hinv.placed p d hp hd hlt
    · -- the slot just written
      have heq : d * 10 + p = k := by omega
      have h50 : k < 50 := by omega
      have hpe : k % 10 = p := by omega
      subst hpe
      have hde : k / 10 = d := by omega
      subst hde
      rw [initStep_pos2card_lt _ _ _ h50, Vector.getElem_set, if_pos rfl,
        Vector.getElem_set, if_pos rfl, heq]

/-! ### The deal loop -/

theorem initLoop_ok {sh : Vector UInt8 52} (hdeal : IsDeal sh) :
    ∀ (n k : Nat) (g : Globals), k + n = 52 → InitInv sh k g →
      ∃ g', forIn (List.range' k n) PUnit.unit (initBody sh) g = .ok PUnit.unit g'
        ∧ InitInv sh 52 g' := by
  intro n
  induction n with
  | zero =>
    intro k g hk hinv
    refine ⟨g, rfl, ?_⟩
    have : k = 52 := by omega
    subst this
    exact hinv
  | succ n ih =>
    intro k g hk hinv
    have hklt : k < 52 := by omega
    obtain ⟨g'', hrun, hinv''⟩ :=
      ih (k + 1) (initStep g (dealCard sh k) (hdeal.card_lt hklt) k) (by omega)
        (initInv_step hdeal hklt hinv)
    refine ⟨g'', ?_, hinv''⟩
    rw [List.range'_succ, List.forIn_cons]
    show (initBody sh k PUnit.unit >>= _) g = _
    simp only [bind, EStateM.bind, initBody_run sh k hklt g (hdeal.card_lt hklt)]
    exact hrun

/-! ## What `initcard` establishes -/

theorem isRealCard_lt {c : UInt8} (h : IsRealCard c) : c.toNat < 64 := by
  revert h; revert c; decide

/-- Index congruence for the doubly-indexed `pos2card` reads (the `getElem`
bound proofs are irrelevant, but `rw` cannot see that). -/
theorem pos2card_congr {n m : Nat} (v : Vector (Vector UInt8 m) n) {a a' b b' : Nat}
    (ha : a = a') (hb : b = b') (h1 : a < n) (h2 : b < m) (h1' : a' < n) (h2' : b' < m) :
    (v[a]'h1)[b]'h2 = (v[a']'h1')[b']'h2' := by
  subst ha; subst hb; rfl

/-- The end state of the deal loop is a well-formed layout. -/
theorem wellFormedLayout_of_initInv {sh : Vector UInt8 52} (hdeal : IsDeal sh) {g : Globals}
    (hinv : InitInv sh 52 g) : WellFormedLayout g where
  pile_lt c hc := by
    rw [cardPile_eq (isRealCard_lt hc)]
    exact hinv.pile_lt _ _
  card2pile_lt i h := hinv.pile_lt i h
  depth_le c hc := by
    rw [cardDepth_eq (isRealCard_lt hc)]
    exact hinv.depth_le _ _
  round_trip c hc hdlt := by
    obtain ⟨j, hj, hcj⟩ := hdeal.surj hc
    obtain ⟨hp, hd⟩ := hinv.located j hj hj
    rw [hcj] at hp hd
    have hpn : (cardPile g c).toNat = j % 10 := by rw [hp, UInt8.toNat_ofNat']; omega
    have hdn : (cardDepth g c).toNat = j / 10 := by rw [hd, UInt8.toNat_ofNat']; omega
    have hj50 : j < 50 := by rw [hdn] at hdlt; omega
    have hplaced := hinv.placed (j % 10) (j / 10) (by omega) (by omega) (by omega)
    show (g.pos2card[(cardPile g c).toNat]'_)[(cardDepth g c).toNat]'_ = c
    rw [pos2card_congr g.pos2card hpn hdn _ _ (by omega) (by omega), hplaced,
      show j / 10 * 10 + j % 10 = j by omega, hcj]
  pos2card_real pile d := by
    show IsRealCard ((g.pos2card[pile.val]'pile.isLt)[d.val]'d.isLt)
    rw [hinv.placed pile.val d.val pile.isLt d.isLt (by omega)]
    exact hdeal.card_real (by omega)
  round_trip_inv pile d := by
    have hslot : (g.pos2card[pile.val]'pile.isLt)[d.val]'d.isLt
        = dealCard sh (d.val * 10 + pile.val) :=
      hinv.placed pile.val d.val pile.isLt d.isLt (by omega)
    obtain ⟨hp, hd⟩ := hinv.located (d.val * 10 + pile.val) (by omega) (by omega)
    show (cardPile g ((g.pos2card[pile.val]'pile.isLt)[d.val]'d.isLt)).toNat = pile.val ∧
      (cardDepth g ((g.pos2card[pile.val]'pile.isLt)[d.val]'d.isLt)).toNat = d.val
    rw [hslot, hp, hd]
    refine ⟨?_, ?_⟩
    · rw [UInt8.toNat_ofNat']; omega
    · rw [UInt8.toNat_ofNat']; omega

/-! ## The memo table starts empty

A zero word carries the tag `0`, and a key's tag is `key / 2^20 + 1 ≥ 1`, so no
slot ever matches and `getSlot` answers `FREESLOT` everywhere.  Both memo
invariants — the soundness-only `HashmapSound` and the two-sided
`HashmapCorrect` — are then their left disjunct. -/

theorem slotRead_of_zero {g : Globals}
    (hz : ∀ (n : Nat) (h : n < BIG_HASH_SIZE), g.hashmap[n]'h = 0)
    {key : UInt32} (hkey : key.toNat < 60466176) :
    slotRead g key = UInt8.ofNat FREESLOT := by
  have hw : slotWord g key = 0 := hz _ (slotEntry_lt key)
  have hne : (((0 : UInt16).toUInt32 ^^^ slotHigh key) &&& (0x1ff : UInt32)) ≠ 0 := by
    intro h
    have h0 := congrArg UInt32.toNat h
    rw [UInt32.toNat_and, UInt32.toNat_xor, show ((0 : UInt16).toUInt32).toNat = 0 from rfl,
      Nat.zero_xor, show ((0x1ff : UInt32)).toNat = 511 from rfl,
      show (511 : Nat) = 2 ^ 9 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      slotHigh_toNat, show ((0 : UInt32)).toNat = 0 from rfl] at h0
    omega
  have hcond : ((((0 : UInt16).toUInt32 ^^^ slotHigh key) &&& (0x1ff : UInt32)) != 0) = true := by
    simpa [bne_iff_ne] using hne
  rw [slotRead, hw, if_pos hcond]

theorem hashmapSound_of_zero {g : Globals}
    (hz : ∀ (n : Nat) (h : n < BIG_HASH_SIZE), g.hashmap[n]'h = 0) : HashmapSound g := by
  intro p hcan v hrun
  left
  rw [getSlot_run] at hrun
  injection hrun with hv _
  rw [← hv]
  exact slotRead_of_zero hz (hash_lt hcan.toSolverInvMerged.toSolverInvBase)

theorem hashmapCorrect_of_zero {g : Globals}
    (hz : ∀ (n : Nat) (h : n < BIG_HASH_SIZE), g.hashmap[n]'h = 0) : HashmapCorrect g := by
  intro p hcan v hrun
  left
  rw [getSlot_run] at hrun
  injection hrun with hv _
  rw [← hv]
  exact slotRead_of_zero hz (hash_lt hcan.toSolverInvMerged.toSolverInvBase)

/-! ## The top-level statement -/

theorem mkVector_getElem {α : Type} (n : Nat) (x : α) (i : Nat) (h : i < n) :
    (mkVector n x)[i]'h = x := by
  simp [mkVector]

theorem solverInit_run (g : Globals) :
    SolverInit g = .ok () { g with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) } := rfl

/-- **`initcard` establishes the global invariants.**  On a genuine deal it
succeeds, and the globals it produces are a well-formed layout with an empty —
hence both sound and correct — memo table.

The only requirement on the incoming globals is that the twelve `card2pile` /
`card2depth` entries at non-card codes (which the deal never writes) are already
in range; a zero-initialized `Globals` satisfies this. -/
theorem initcard_ok {sh : Vector UInt8 52} (hdeal : IsDeal sh) (g : Globals)
    (hpile : ∀ (n : Nat) (h : n < 64), (g.card2pile[n]'h).toNat < 10)
    (hdepth : ∀ (n : Nat) (h : n < 64), (g.card2depth[n]'h).toNat ≤ 5) :
    ∃ g', EStateM.run (initcard sh) g = .ok () g' ∧
      WellFormedLayout g' ∧ HashmapCorrect g' ∧ HashmapSound g' := by
  have hinv0 : InitInv sh 0 { g with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) } :=
    { pile_lt := fun n hn => hpile n hn
      depth_le := fun n hn => hdepth n hn
      located := fun _ hj _ => absurd hj (by omega)
      placed := fun _ _ _ _ h => absurd h (by omega)
      memo_zero := fun n hn => mkVector_getElem _ _ n hn }
  obtain ⟨g', hrun, hinv⟩ :=
    initLoop_ok hdeal 52 0 { g with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) } rfl hinv0
  refine ⟨g', ?_, wellFormedLayout_of_initInv hdeal hinv,
    hashmapCorrect_of_zero hinv.memo_zero, hashmapSound_of_zero hinv.memo_zero⟩
  rw [initcard_eq]
  show (SolverInit >>= fun _ =>
    forIn (List.range 52) PUnit.unit (initBody sh) >>= fun _ => pure PUnit.unit) g = _
  simp only [bind, EStateM.bind, solverInit_run, List.range_eq_range', hrun, pure, EStateM.pure]

/-- Same, but also exporting the loop invariant — `placed` (where each dealt card
sits in `pos2card`) and `located` (its recorded pile/depth) are what a `Rules`-side
deal has to be matched against. -/
theorem initcard_ok' {sh : Vector UInt8 52} (hdeal : IsDeal sh) (g : Globals)
    (hpile : ∀ (n : Nat) (h : n < 64), (g.card2pile[n]'h).toNat < 10)
    (hdepth : ∀ (n : Nat) (h : n < 64), (g.card2depth[n]'h).toNat ≤ 5) :
    ∃ g', EStateM.run (initcard sh) g = .ok () g' ∧
      WellFormedLayout g' ∧ HashmapCorrect g' ∧ HashmapSound g' ∧ InitInv sh 52 g' := by
  have hinv0 : InitInv sh 0 { g with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) } :=
    { pile_lt := fun n hn => hpile n hn
      depth_le := fun n hn => hdepth n hn
      located := fun _ hj _ => absurd hj (by omega)
      placed := fun _ _ _ _ h => absurd h (by omega)
      memo_zero := fun n hn => mkVector_getElem _ _ n hn }
  obtain ⟨g', hrun, hinv⟩ :=
    initLoop_ok hdeal 52 0 { g with hashmap := mkVector BIG_HASH_SIZE (UInt16.ofNat 0) } rfl hinv0
  refine ⟨g', ?_, wellFormedLayout_of_initInv hdeal hinv,
    hashmapCorrect_of_zero hinv.memo_zero, hashmapSound_of_zero hinv.memo_zero, hinv⟩
  rw [initcard_eq]
  show (SolverInit >>= fun _ =>
    forIn (List.range 52) PUnit.unit (initBody sh) >>= fun _ => pure PUnit.unit) g = _
  simp only [bind, EStateM.bind, solverInit_run, List.range_eq_range', hrun, pure, EStateM.pure]

/-- Packaged as `WFGlobals`. -/
theorem initcard_wfGlobals {sh : Vector UInt8 52} (hdeal : IsDeal sh) (g : Globals)
    (hpile : ∀ (n : Nat) (h : n < 64), (g.card2pile[n]'h).toNat < 10)
    (hdepth : ∀ (n : Nat) (h : n < 64), (g.card2depth[n]'h).toNat ≤ 5) :
    ∃ g', EStateM.run (initcard sh) g = .ok () g' ∧ WFGlobals g' ∧ HashmapCorrect g' := by
  obtain ⟨g', hrun, hwf, hcorr, hsound⟩ := initcard_ok hdeal g hpile hdepth
  exact ⟨g', hrun, ⟨hwf, hsound⟩, hcorr⟩
