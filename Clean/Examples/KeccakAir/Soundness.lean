/-
Soundness of a window of the Keccak-f AIR: if its constraints hold, it computes a round of
Keccak-f. The limbs of a lane are read as bits, the bits of θ, ρ, π and χ as the bits of
`Specs.Keccak256.Lanes`, which agree with `Specs.Keccak256`.
-/
module

public import Clean.Examples.KeccakAir.Spec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace KeccakAir
open Specs.Keccak256 Air.Flat

variable {p : ℕ}

lemma laneValue_lt {limb : Fin 4 → F p} (h : ∀ l, (limb l).val < 2 ^ 16) :
    laneValue limb < 2 ^ 64 := by
  have := h 0; have := h 1; have := h 2; have := h 3
  simp only [laneValue]
  omega

/-- The lane as a bit vector. -/
def laneBits (limb : Fin 4 → F p) : BitVec 64 := BitVec.ofNat 64 (laneValue limb)

/-- The lanes held as limbs `limb y x`. -/
def lanesOf (limb : Fin 5 → Fin 5 → Fin 4 → F p) : Lanes := fun x y => laneBits (limb y x)

lemma stateOf_eq_toState {limb : Fin 5 → Fin 5 → Fin 4 → F p}
    (h : ∀ y x l, (limb y x l).val < 2 ^ 16) : stateOf limb = Lanes.toState (lanesOf limb) := by
  ext i hi
  simp only [stateOf, Lanes.toState, lanesOf, laneBits, Vector.getElem_ofFn, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (laneValue_lt (h _ _))]

variable [Fact p.Prime]

/-- A field element that is 0 or 1. -/
def IsBit (v : F p) : Prop := v = 0 ∨ v = 1

/-- The bit a field element `0` or `1` stands for. -/
def bitOf (v : F p) : Bool := decide (v = 1)

section Bits

lemma isBit_of_boolCheck {v : F p} (h : boolCheck v = 0) : IsBit v := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

lemma bitOf_zero : bitOf (0 : F p) = false := by
  simp [bitOf]

lemma bitOf_one : bitOf (1 : F p) = true := by
  simp [bitOf]

lemma isBit_xor {x y : F p} (hx : IsBit x) (hy : IsBit y) :
    IsBit (xor x y) ∧ bitOf (xor x y) = (bitOf x ^^ bitOf y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [IsBit, xor, bitOf_zero, bitOf_one]

lemma isBit_andn {x y : F p} (hx : IsBit x) (hy : IsBit y) :
    IsBit (andn x y) ∧ bitOf (andn x y) = (!bitOf x && bitOf y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [IsBit, andn, bitOf_zero, bitOf_one]

lemma val_of_isBit {v : F p} (h : IsBit v) : v.val = (bitOf v).toNat := by
  rcases h with rfl | rfl
  · simp [bitOf_zero]
  · simp [bitOf_one, ZMod.val_one]

lemma natCast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : F p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd hn h) (by omega)

/-- `diff (diff - 2) (diff - 4) = 0` for `diff = a0 + ... + a4 - c` makes `c` the parity of the bits
`a0, ..., a4`. -/
lemma parity {a0 a1 a2 a3 a4 c : F p} (hp : 15 < p) (h0 : IsBit a0) (h1 : IsBit a1)
    (h2 : IsBit a2) (h3 : IsBit a3) (h4 : IsBit a4) (hc : IsBit c)
    (h : let diff := a0 + a1 + a2 + a3 + a4 - c; diff * (diff - 2) * (diff - 4) = 0) :
    bitOf c = (bitOf a0 ^^ bitOf a1 ^^ bitOf a2 ^^ bitOf a3 ^^ bitOf a4) := by
  have three : (3 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 3) (by omega) (by omega)
  have fifteen : (15 : F p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (n := 15) (by omega) (by omega)
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> rcases h4 with rfl | rfl <;> rcases hc with rfl | rfl <;>
    revert h <;> norm_num [bitOf_zero, bitOf_one, three, fifteen]

end Bits

section Limbs

/-- Blocks of `w` bits, summed with their place values, keep their bits. -/
lemma testBit_sum_blocks (w : ℕ) (hw : 0 < w) (f : ℕ → ℕ) (n : ℕ)
    (hf : ∀ l < n, f l < 2 ^ w) :
    ∑ l ∈ Finset.range n, 2 ^ (w * l) * f l < 2 ^ (w * n) ∧
      ∀ i, (∑ l ∈ Finset.range n, 2 ^ (w * l) * f l).testBit i =
        (decide (i < w * n) && (f (i / w)).testBit (i % w)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hlt, htest⟩ := ih fun l hl => hf l (by omega)
    have hfn := hf n (by omega)
    rw [Finset.sum_range_succ, add_comm]
    constructor
    · have : 2 ^ (w * n) * f n ≤ 2 ^ (w * n) * (2 ^ w - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hpow : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * 2 ^ w := by
        rw [Nat.mul_succ, pow_add]
      have : 2 ^ (w * n) * (2 ^ w - 1) + 2 ^ (w * n) = 2 ^ (w * n) * 2 ^ w := by
        have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
        rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ this)]
      omega
    · intro i
      rw [Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hi : i < w * n
      · simp only [hi, ↓reduceIte, htest i]
        simp [show i < w * (n + 1) by nlinarith]
      · simp only [hi, ↓reduceIte]
        by_cases hi' : i < w * (n + 1)
        · have hdiv : i / w = n := by
            apply Nat.div_eq_of_lt_le <;> [rw [mul_comm]; rw [mul_comm, Nat.succ_mul] at *] <;>
              linarith [Nat.mul_succ w n]
          have hmod : i % w = i - w * n := by
            rw [Nat.mod_eq_sub_mul_div, hdiv, mul_comm]
          simp [hi', hdiv, hmod]
        · have : f n < 2 ^ (i - w * n) :=
            lt_of_lt_of_le hfn
              (Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ] at hi'; omega))
          simp [hi', Nat.testBit_lt_two_pow this]

/-- Horner's rule computes the place-value sum of the limb's bits. -/
lemma horner_eq (bit : Fin 16 → F p) (n : ℕ) (hn : n ≤ 15) :
    horner bit n = ∑ j ∈ Finset.range (n + 1), 2 ^ j * bit (Fin.ofNat 16 (15 - n + j)) := by
  induction n with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, ih (by omega), Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ, show 15 - (n + 1) + (j + 1) = 15 - n + j by omega]
      ring
    · simp [show 15 - (n + 1) = 14 - n by omega]

/-- The bits `z` of a lane, `bit z` standing for the `z`-th place value. -/
def bitValue (bits : Fin 64 → F p) (limb : Fin 4) (j : ℕ) : ℕ :=
  (bitOf (bits (limbBit limb (Fin.ofNat 16 j)))).toNat

lemma limbOf_eq_natCast (bits : Fin 64 → F p) (hbits : ∀ z, IsBit (bits z)) (limb : Fin 4) :
    limbOf bits limb =
      ((∑ j ∈ Finset.range 16, 2 ^ (1 * j) * bitValue bits limb j : ℕ) : F p) := by
  rw [limbOf, horner_eq _ 15 le_rfl]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [one_mul, bitValue, ← val_of_isBit (hbits _), ZMod.natCast_zmod_val, zero_add]

lemma bitValue_lt (bits : Fin 64 → F p) (limb : Fin 4) (j : ℕ) : bitValue bits limb j < 2 ^ 1 := by
  simp only [bitValue, pow_one]
  exact Bool.toNat_lt _

lemma limbOf_val (hp : 2 ^ 16 < p) (bits : Fin 64 → F p) (hbits : ∀ z, IsBit (bits z))
    (limb : Fin 4) :
    (limbOf bits limb).val < 2 ^ 16 ∧ ∀ k < 16,
      (limbOf bits limb).val.testBit k = bitOf (bits (limbBit limb (Fin.ofNat 16 k))) := by
  obtain ⟨hlt, htest⟩ := testBit_sum_blocks 1 one_pos (bitValue bits limb) 16
    fun j _ => bitValue_lt bits limb j
  rw [limbOf_eq_natCast bits hbits, ZMod.val_natCast_of_lt (by omega)]
  refine ⟨hlt, fun k hk => ?_⟩
  rw [htest k]
  simp only [one_mul, Nat.div_one, Nat.mod_one, hk, decide_true, Bool.true_and, bitValue]
  cases bitOf (bits (limbBit limb (Fin.ofNat 16 k))) <;> rfl

/-- The limbs of a lane that are the place-value sums of bits are 16-bit, and the lane's bits are
those bits. -/
theorem lane_testBit (hp : 2 ^ 16 < p) (bits : Fin 64 → F p) (hbits : ∀ z, IsBit (bits z))
    (limb : Fin 4 → F p) (hlimb : ∀ l, limb l = limbOf bits l) :
    (∀ l, (limb l).val < 2 ^ 16) ∧ laneValue limb < 2 ^ 64 ∧
      ∀ z : Fin 64, (laneValue limb).testBit z = bitOf (bits z) := by
  have hval l := limbOf_val hp bits hbits l
  have hlimbs : ∀ l, (limb l).val < 2 ^ 16 := fun l => hlimb l ▸ (hval l).left
  let value (l : ℕ) : ℕ := if h : l < 4 then (limb ⟨l, h⟩).val else 0
  have hsum : laneValue limb = ∑ l ∈ Finset.range 4, 2 ^ (16 * l) * value l := by
    simp [laneValue, Finset.sum_range_succ, value, mul_comm]
  obtain ⟨hlt, htest⟩ := testBit_sum_blocks 16 (by norm_num) value 4 fun l hl => by
    simp only [value, hl, ↓reduceDIte]
    exact hlimbs _
  refine ⟨hlimbs, hsum ▸ hlt, fun z => ?_⟩
  have hz := z.isLt
  rw [hsum, htest]
  have hl : z.val / 16 < 4 := by omega
  simp only [show z.val < 16 * 4 by omega, decide_true, Bool.true_and, value, hl, ↓reduceDIte,
    hlimb, (hval _).right _ (Nat.mod_lt _ (by norm_num))]
  congr 2
  ext
  simp only [limbBit, Fin.val_ofNat]
  omega

theorem laneBits_getLsbD (hp : 2 ^ 16 < p) (bits : Fin 64 → F p) (hbits : ∀ z, IsBit (bits z))
    (limb : Fin 4 → F p) (hlimb : ∀ l, limb l = limbOf bits l) (z : Fin 64) :
    (laneBits limb).getLsbD z = bitOf (bits z) := by
  rw [laneBits, BitVec.getLsbD_ofNat, (lane_testBit hp bits hbits limb hlimb).2.2 z]
  simp

end Limbs

section Round

lemma getLsbD_rotateLeft (lane : BitVec 64) (offset z : Fin 64) :
    (lane.rotateLeft offset).getLsbD z = lane.getLsbD ((z - offset : Fin 64) : ℕ) := by
  rw [BitVec.getLsbD_rotateLeft, Fin.val_sub]
  obtain ⟨z, hz⟩ := z
  obtain ⟨k, hk⟩ := offset
  simp only [Nat.mod_eq_of_lt hk]
  split_ifs with h
  · congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [hz, decide_true, Bool.true_and]
    congr 1
    omega

lemma foldl_oneHot (r : Fin 24) (rounds : List (Fin 24)) (hrounds : rounds.Nodup) (sum : F p) :
    rounds.foldl (fun sum r' => sum + (oneHot r)[r']) sum = sum + if r ∈ rounds then 1 else 0 := by
  induction rounds generalizing sum with
  | nil => simp
  | cons r' rounds ih =>
    rw [List.nodup_cons] at hrounds
    rw [List.foldl_cons, ih hrounds.right]
    by_cases h : r' = r
    · subst h
      simp [oneHot, hrounds.left]
    · simp [oneHot, h, Ne.symm h]

lemma iotaBit_oneHot {r : Fin 24} {bit : F p} (hbit : IsBit bit) (z : Fin 64) :
    IsBit (iotaBit (oneHot r) bit z) ∧
      bitOf (iotaBit (oneHot r) bit z) = (roundConstantBit r z ^^ bitOf bit) := by
  have hmem : r ∈ (List.finRange 24).filter (roundConstantBit · z) ↔ roundConstantBit r z := by
    simp
  have hnodup : ((List.finRange 24).filter (roundConstantBit · z)).Nodup :=
    (List.nodup_finRange 24).filter _
  unfold iotaBit
  split
  · rename_i hnil
    rw [hnil] at hmem
    simp only [List.not_mem_nil, false_iff] at hmem
    simp [hbit, hmem]
  · rename_i r0 rs hcons
    rw [hcons] at hmem hnodup
    have hsum : rs.foldl (fun sum r' => sum + (oneHot r)[r']) (oneHot r)[r0] =
        if roundConstantBit r z then (1 : F p) else 0 := by
      have := foldl_oneHot r (r0 :: rs) hnodup (0 : F p)
      rw [List.foldl_cons, zero_add, zero_add] at this
      rw [this]
      simp only [hmem]
    have hsumBit : IsBit (if roundConstantBit r z then (1 : F p) else 0) := by
      split <;> simp [IsBit]
    rw [hsum]
    refine ⟨(isBit_xor hsumBit hbit).left, ?_⟩
    rw [(isBit_xor hsumBit hbit).right]
    cases roundConstantBit r z <;> simp [bitOf_zero, bitOf_one]

/-- θ's column parities: the bits `c` that make `A' = A ^ C ^ C'` of parity `C'` are the column
parities of `A`. -/
lemma columnParity_bool (s0 s1 s2 s3 s4 a0 a1 a2 a3 a4 c c' : Bool)
    (h0 : s0 = (a0 ^^ (c ^^ c'))) (h1 : s1 = (a1 ^^ (c ^^ c'))) (h2 : s2 = (a2 ^^ (c ^^ c')))
    (h3 : s3 = (a3 ^^ (c ^^ c'))) (h4 : s4 = (a4 ^^ (c ^^ c')))
    (hparity : c' = (a0 ^^ a1 ^^ a2 ^^ a3 ^^ a4)) :
    c = (s0 ^^ s1 ^^ s2 ^^ s3 ^^ s4) := by
  subst h0 h1 h2 h3 h4 hparity
  revert a0 a1 a2 a3 a4 c
  decide

lemma getLsbD_rotateLeft_one (lane : BitVec 64) (z : Fin 64) :
    (lane.rotateLeft 1).getLsbD z = lane.getLsbD ((z - 1 : Fin 64) : ℕ) :=
  getLsbD_rotateLeft lane 1 z

lemma theta_bool (a c c' c4 c1 : Bool) (hc' : c' = (c ^^ c4 ^^ c1)) :
    a = ((a ^^ (c ^^ c')) ^^ (c4 ^^ c1)) := by
  subst hc'
  revert a c c4 c1
  decide

/-- A row whose bit-level constraints hold computes a round of Keccak-f on its lanes. -/
theorem round_of_bits (hp : 2 ^ 16 < p) (row : Row (F p)) (r : Fin 24)
    (hflags : row.stepFlags = oneHot r)
    (hc : ∀ x z, IsBit (row.cBit x z))
    (hcPrime : ∀ x z, row.cPrimeBit x z =
      xor (xor (row.cBit x z) (row.cBit (x + 4) z)) (row.cBit (x + 1) (z - 1)))
    (haPrime : ∀ y x z, IsBit (row.aPrimeBit y x z))
    (ha : ∀ y x l, row.aLimb y x l =
      limbOf (fun z => xor (row.aPrimeBit y x z) (xor (row.cBit x z) (row.cPrimeBit x z))) l)
    (hparity : ∀ x z,
      let diff := row.aPrimeBit 0 x z + row.aPrimeBit 1 x z + row.aPrimeBit 2 x z +
        row.aPrimeBit 3 x z + row.aPrimeBit 4 x z - row.cPrimeBit x z
      diff * (diff - 2) * (diff - 4) = 0)
    (hchi : ∀ y x l, row.aPrimePrimeLimb y x l = limbOf (fun z =>
      xor (andn (row.b (x + 1) y z) (row.b (x + 2) y z)) (row.b x y z)) l)
    (hbits : ∀ z : Fin 64, IsBit row.aPrimePrime00Bits[z])
    (h00 : ∀ l, row.aPrimePrimeLimb 0 0 l = limbOf (fun z => row.aPrimePrime00Bits[z]) l)
    (hiota : ∀ l, row.aPrimePrimePrime00Limbs[l] =
      limbOf (fun z => iotaBit row.stepFlags row.aPrimePrime00Bits[z] z) l) :
    (∀ y x l, (row.aLimb y x l).val < 2 ^ 16) ∧
      (∀ y x l, (row.aPrimePrimePrimeLimb y x l).val < 2 ^ 16) ∧
      lanesOf row.aPrimePrimePrimeLimb = Lanes.round (lanesOf row.aLimb) roundConstants[r] := by
  -- the bits of `C'`
  have hcPrimeBit (x : Fin 5) (z : Fin 64) : IsBit (row.cPrimeBit x z) ∧ bitOf (row.cPrimeBit x z) =
      (bitOf (row.cBit x z) ^^ bitOf (row.cBit (x + 4) z) ^^ bitOf (row.cBit (x + 1) (z - 1))) := by
    obtain ⟨h1, h2⟩ := isBit_xor (hc x z) (hc (x + 4) z)
    obtain ⟨h3, h4⟩ := isBit_xor h1 (hc (x + 1) (z - 1))
    rw [hcPrime]
    exact ⟨h3, by rw [h4, h2]⟩
  -- the bits of `A`
  have hthetaBit (y x : Fin 5) (z : Fin 64) :
      IsBit (xor (row.aPrimeBit y x z) (xor (row.cBit x z) (row.cPrimeBit x z)))
      ∧ bitOf (xor (row.aPrimeBit y x z) (xor (row.cBit x z) (row.cPrimeBit x z))) =
        (bitOf (row.aPrimeBit y x z) ^^ (bitOf (row.cBit x z) ^^ bitOf (row.cPrimeBit x z))) := by
    obtain ⟨h1, h2⟩ := isBit_xor (hc x z) (hcPrimeBit x z).left
    obtain ⟨h3, h4⟩ := isBit_xor (haPrime y x z) h1
    exact ⟨h3, by rw [h4, h2]⟩
  set state := lanesOf row.aLimb with hstate
  have hstateBit (x y : Fin 5) (z : Fin 64) : (state x y).getLsbD z =
      (bitOf (row.aPrimeBit y x z) ^^ (bitOf (row.cBit x z) ^^ bitOf (row.cPrimeBit x z))) := by
    rw [hstate, lanesOf, laneBits_getLsbD hp _ (fun z => (hthetaBit y x z).left) _ (ha y x),
      (hthetaBit y x z).right]
  -- θ: `C` are the column parities, and `A'` is θ's output
  have hcolumn (x : Fin 5) (z : Fin 64) :
      bitOf (row.cBit x z) = (Lanes.columnParity state x).getLsbD z := by
    simp only [Lanes.columnParity, BitVec.getLsbD_xor, hstateBit]
    exact columnParity_bool _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
      (parity (by omega) (haPrime 0 x z) (haPrime 1 x z) (haPrime 2 x z) (haPrime 3 x z)
        (haPrime 4 x z) (hcPrimeBit x z).left (hparity x z))
  have htheta (y x : Fin 5) (z : Fin 64) :
      bitOf (row.aPrimeBit y x z) = (Lanes.theta state x y).getLsbD z := by
    simp only [Lanes.theta, BitVec.getLsbD_xor, getLsbD_rotateLeft_one, hstateBit]
    rw [← hcolumn, ← hcolumn]
    exact theta_bool _ _ _ _ _ (hcPrimeBit x z).right
  -- ρ and π
  have hrhoPi (x y : Fin 5) (z : Fin 64) :
      bitOf (row.b x y z) = (Lanes.rhoPi (Lanes.theta state) x y).getLsbD z := by
    simp only [Row.b, Lanes.rhoPi, getLsbD_rotateLeft, htheta]
  have hbBit (x y : Fin 5) (z : Fin 64) : IsBit (row.b x y z) := haPrime _ _ _
  -- χ
  have hchiBit (y x : Fin 5) (z : Fin 64) :
      IsBit (xor (andn (row.b (x + 1) y z) (row.b (x + 2) y z)) (row.b x y z)) ∧
      bitOf (xor (andn (row.b (x + 1) y z) (row.b (x + 2) y z)) (row.b x y z)) =
        (Lanes.chi (Lanes.rhoPi (Lanes.theta state)) x y).getLsbD z := by
    obtain ⟨h1, h2⟩ := isBit_andn (hbBit (x + 1) y z) (hbBit (x + 2) y z)
    obtain ⟨h3, h4⟩ := isBit_xor h1 (hbBit x y z)
    refine ⟨h3, ?_⟩
    simp only [h4, h2, hrhoPi, Lanes.chi, BitVec.getLsbD_xor, BitVec.getLsbD_and,
      BitVec.getLsbD_not, z.isLt, decide_true, Bool.true_and]
    exact Bool.xor_comm _ _
  -- the bounds
  have haBound (y x : Fin 5) (l : Fin 4) : (row.aLimb y x l).val < 2 ^ 16 :=
    (lane_testBit hp _ (fun z => (hthetaBit y x z).left) _ (ha y x)).left l
  have hchiBound (y x : Fin 5) (l : Fin 4) : (row.aPrimePrimeLimb y x l).val < 2 ^ 16 :=
    (lane_testBit hp _ (fun z => (hchiBit y x z).left) _ (hchi y x)).left l
  have hiotaBit (z : Fin 64) := iotaBit_oneHot (r := r) (hbits z) z
  have hiotaLimbs : ∀ l, row.aPrimePrimePrime00Limbs[l] =
      limbOf (fun z => iotaBit (oneHot r) row.aPrimePrime00Bits[z] z) l := by
    intro l
    rw [hiota, hflags]
  have hiotaBound (l : Fin 4) : row.aPrimePrimePrime00Limbs[l].val < 2 ^ 16 :=
    (lane_testBit hp _ (fun z => (hiotaBit z).left) _ hiotaLimbs).left l
  refine ⟨haBound, fun y x l => ?_, ?_⟩
  · simp only [Row.aPrimePrimePrimeLimb]
    split
    · exact hiotaBound l
    · exact hchiBound y x l
  -- ι
  funext x y
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hchiLane : (laneBits (row.aPrimePrimeLimb y x)).getLsbD i =
      (Lanes.chi (Lanes.rhoPi (Lanes.theta state)) x y).getLsbD i := by
    rw [laneBits_getLsbD hp _ (fun z => (hchiBit y x z).left) _ (hchi y x) ⟨i, hi⟩,
      (hchiBit y x ⟨i, hi⟩).right]
  simp only [Lanes.round, Lanes.iota]
  by_cases hzero : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    have hlane : row.aPrimePrimePrimeLimb 0 0 = fun l => row.aPrimePrimePrime00Limbs[l] := by
      funext l
      simp [Row.aPrimePrimePrimeLimb]
    have h00Bit : bitOf row.aPrimePrime00Bits[(⟨i, hi⟩ : Fin 64)] =
        (Lanes.chi (Lanes.rhoPi (Lanes.theta state)) 0 0).getLsbD i := by
      rw [← hchiLane, laneBits_getLsbD hp _ hbits _ h00 ⟨i, hi⟩]
    simp only [lanesOf, hlane, and_self, ↓reduceIte, BitVec.getLsbD_xor]
    rw [laneBits_getLsbD hp _ (fun z => (hiotaBit z).left) _ hiotaLimbs ⟨i, hi⟩,
      (hiotaBit ⟨i, hi⟩).right, h00Bit, Bool.xor_comm]
    rw [roundConstantBit]
    congr 1
  · have hlane : row.aPrimePrimePrimeLimb y x = row.aPrimePrimeLimb y x := by
      funext l
      simp only [Row.aPrimePrimePrimeLimb, show ¬(y = 0 ∧ x = 0) by tauto, ↓reduceIte]
    simp only [lanesOf, hlane, hzero, ↓reduceIte, hchiLane]

end Round

end KeccakAir

namespace KeccakAir
open Specs.Keccak256 Air.Flat

variable {p : ℕ} [Fact p.Prime]

section Window

lemma oneHot_getElem (r i : Fin 24) : (oneHot r : Vector (F p) 24)[i] = if i = r then 1 else 0 := by
  simp [oneHot]

lemma limbIndex_surjective (i : Fin 100) : ∃ y x limb, limbIndex y x limb = i :=
  ⟨⟨i.val / 20, by omega⟩, ⟨i.val / 4 % 5, by omega⟩, ⟨i.val % 4, by omega⟩, by
    ext
    simp only [limbIndex]
    omega⟩

lemma limbs_ext {α : Type} {u v : Vector α 100}
    (h : ∀ y x limb, u[limbIndex y x limb] = v[limbIndex y x limb]) : u = v := by
  ext i hi
  obtain ⟨y, x, limb, hindex⟩ := limbIndex_surjective ⟨i, hi⟩
  have := h y x limb
  simp only [hindex] at this
  exact this

lemma getElem_ofFn_fin {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  simp

lemma rounds_zero (state : Vector ℕ 25) : rounds 0 state = state := rfl

lemma rounds_succ (r : Fin 24) (state : Vector ℕ 25) :
    rounds (r.val + 1) state = keccakRound (rounds r state) roundConstants[r] := by
  simp only [rounds, List.take_add_one, List.foldl_append]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

/-- The flags of the first row are those of round 0. -/
lemma oneHot_zero_of_first {flags : Vector (F p) 24} (h0 : flags[0] - 1 = 0)
    (hrest : ∀ j : Fin 23, flags[j.succ] = 0) : flags = oneHot 0 := by
  ext i hi
  rw [show (oneHot 0 : Vector (F p) 24)[i] = (oneHot 0 : Vector (F p) 24)[(⟨i, hi⟩ : Fin 24)] from
    rfl, oneHot_getElem]
  cases i with
  | zero => simpa [sub_eq_zero] using h0
  | succ j =>
    have := hrest ⟨j, by omega⟩
    simp only [Fin.succ_mk] at this
    simp only [Fin.ext_iff, Fin.val_zero, Nat.add_one_ne_zero, ↓reduceIte]
    exact this

/-- Flags that move by one round on a transition. -/
lemma oneHot_succ {flags next : Vector (F p) 24} {r : Fin 24} (hflags : flags = oneHot r)
    (h : ∀ j : Fin 24, flags[j] - next[j + 1] = 0) : next = oneHot (r + 1) := by
  ext i hi
  have := h (⟨i, hi⟩ - 1)
  simp only [sub_add_cancel, hflags, oneHot_getElem, sub_eq_zero] at this
  change next[(⟨i, hi⟩ : Fin 24)] = (oneHot (r + 1) : Vector (F p) 24)[(⟨i, hi⟩ : Fin 24)]
  rw [oneHot_getElem]
  simp only [Fin.getElem_fin] at this ⊢
  rw [← this]
  simp only [sub_eq_iff_eq_add]

/-- If the constraints of a window hold, and the window is the first row or carries the invariant,
then it computes a round of its preimage. -/
theorem windowSpec_of_constraints (hp : 2 ^ 16 < p) (window : Window Row (F p))
    (hconstraints : ∀ e ∈ constraints window, e = 0)
    (hassumption : window.isFirstRow = 1 ∨ Carried window.current) :
    WindowSpec window := by
  simp only [constraints, List.forall_mem_append] at hconstraints
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hflags, hpreimage⟩, hexport⟩, hcolumn⟩, htheta⟩, hparity⟩, hchi⟩, hiota⟩,
    houtput⟩ := hconstraints
  simp only [roundFlagConstraints, preimageConstraints, exportConstraints,
    thetaColumnConstraints, thetaConstraints, parityConstraints, chiConstraints, iotaConstraints,
    outputConstraints, List.forall_mem_cons, List.forall_mem_flatMap, List.forall_mem_append,
    List.forall_mem_map, List.mem_finRange, forall_const, forall_and, getElem_ofFn_fin] at *
  set current := window.current with hcurrent
  -- the round of the row
  obtain ⟨r, hr, hcarried⟩ : ∃ r : Fin 24, current.stepFlags = oneHot r ∧
      (r ≠ 0 → current.PreimageNormalized ∧
        current.inputState = rounds r current.preimageState) := by
    rcases hassumption with hfirst | ⟨r, hr, hcarried⟩
    · refine ⟨0, oneHot_zero_of_first ?_ ?_, fun h => absurd rfl h⟩
      · simpa [hfirst] using hflags.left.left
      · intro j
        simpa [hfirst] using hflags.left.right j
    · exact ⟨r, hr, hcarried⟩
  -- the round's bits
  obtain ⟨hinputBound, houtputBound, hround⟩ := round_of_bits hp current r hr
    (fun x z => isBit_of_boolCheck (hcolumn.left x z))
    (fun x z => sub_eq_zero.mp (hcolumn.right x z))
    (fun y x z => isBit_of_boolCheck (htheta.left x y z))
    (fun y x l => (sub_eq_zero.mp (htheta.right x y l)).symm)
    hparity
    (fun y x l => (sub_eq_zero.mp (hchi y x l)).symm)
    (fun z => isBit_of_boolCheck (hiota.left.left z))
    (fun l => (sub_eq_zero.mp (hiota.left.right l)).symm)
    (fun l => (sub_eq_zero.mp (hiota.right l)).symm)
  have hflag (i : ℕ) (hi : i < 24) : current.stepFlags[i] = if i = r.val then 1 else 0 := by
    have := oneHot_getElem (p := p) r ⟨i, hi⟩
    simp only [Fin.getElem_fin, Fin.ext_iff] at this
    rw [hr, this]
  -- the row's preimage and input
  have hinput : current.PreimageNormalized ∧
      current.inputState = rounds r current.preimageState := by
    by_cases hr0 : r = 0
    · subst hr0
      have hsame y x l : current.preimageLimb y x l = current.aLimb y x l := by
        have := hpreimage.left y x l
        rw [hflag 0 (by omega)] at this
        simp only [Fin.val_zero, ↓reduceIte, one_mul, sub_eq_zero] at this
        exact this
      refine ⟨fun y x l => hsame y x l ▸ hinputBound y x l, ?_⟩
      simp only [Row.inputState, Row.preimageState, rounds_zero, Fin.val_zero]
      congr 1
      funext y x l
      exact (hsame y x l).symm
    · exact hcarried hr0
  have houtputState : current.outputState = rounds (r.val + 1) current.preimageState := by
    rw [rounds_succ, ← hinput.right, Row.outputState, Row.inputState,
      stateOf_eq_toState houtputBound, stateOf_eq_toState hinputBound, hround,
      Lanes.keccakRound_toState]
  refine ⟨r, hr, hinput.left, hinput.right, houtputState, ?_, ?_⟩
  -- only the last round exports
  · intro hexported
    have := hexport.right.left
    rw [hexported, mul_one, sub_eq_zero, hflag 23 (by omega)] at this
    by_contra hne
    simp only [show ¬(23 = r.val) from fun h => hne (Fin.ext h.symm), ↓reduceIte] at this
    exact one_ne_zero this
  -- transitions
  · intro htransition
    refine ⟨oneHot_succ hr fun j => by simpa [htransition] using hflags.right j, fun hlast => ?_⟩
    have hsame : transitionInPermutation window = 1 := by
      rw [transitionInPermutation, htransition, ← hcurrent, hflag 23 (by omega)]
      simp only [show ¬(23 = r.val) from fun h => hlast (Fin.ext h.symm), ↓reduceIte]
      ring
    constructor
    · apply limbs_ext
      intro y x l
      have := hpreimage.right y x l
      rw [hsame, one_mul, sub_eq_zero] at this
      exact this.symm
    · simp only [Row.inputState, Row.outputState]
      congr 1
      funext y x l
      have := houtput x y l
      rw [hsame, one_mul, sub_eq_zero] at this
      exact this.symm

end Window

end KeccakAir

namespace KeccakAir
open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- A window that computes a round establishes the invariant of the next row on a transition. -/
theorem carried_of_windowSpec {window : Window Row (F p)} (hspec : WindowSpec window)
    (htransition : window.isTransition = 1) : Carried window.next := by
  obtain ⟨r, -, hnormalized, -, houtput, -, hnext⟩ := hspec
  obtain ⟨hflags, hsame⟩ := hnext htransition
  refine ⟨r + 1, hflags, fun hne => ?_⟩
  have hlast : r ≠ 23 := by
    rintro rfl
    exact hne rfl
  have hval : (r + 1).val = r.val + 1 := by
    have : r.val ≠ 23 := fun h => hlast (Fin.ext h)
    rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hpreimage, hinput⟩ := hsame hlast
  have hstate : window.next.preimageState = window.current.preimageState := by
    simp only [Row.preimageState]
    congr 1
    funext y x l
    simp only [Row.preimageLimb, hpreimage]
  refine ⟨fun y x l => ?_, ?_⟩
  · simpa only [Row.preimageLimb, hpreimage] using hnormalized y x l
  · rw [hinput, houtput, hstate, hval]

end KeccakAir
