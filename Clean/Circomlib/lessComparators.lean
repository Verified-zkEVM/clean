/- import Std.Data.Vector.Basic -/
import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/comparators.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]


namespace LessThan
/-
template LessThan(n) {
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1 << n) - in[1];

    out <== 1-n2b.out[n];
}
-/
structure Input (p : ℕ) [Fact p.Prime] [Fact (p > 2)] where
  a : F p
  b : F p

structure Bounds 
  (p n : ℕ) [Fact p.Prime] [Fact (p > 2)] 
  (a b : F p)
  where
  ha : ZMod.val a < 2 ^ n
  hb : ZMod.val b < 2 ^ n
  hp : 2 ^ (n + 1) < p
  hp' : 2 ^ n < p

/-- From `2^(n+1) < p` get `2^n < p`. -/
lemma pow_lt_of_succ {n p : ℕ} (hn : 2^(n+1) < p) : 2^n < p := by
  exact lt_trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)) hn

/-- `testBit` is insensitive to rewriting `x - y` as `x + -y`. -/
lemma testBit_sub_eq_addNeg (x y : ZMod p) (k : ℕ) :
    (ZMod.val (x - y)).testBit k = (ZMod.val (x + -y)).testBit k := by
  simp [sub_eq_add_neg]

lemma testBit_sum_sub_eq_sum_addNeg 
  {p : ℕ} [Fact p.Prime] [Fact (p > 2)] 
  (a b : ZMod p) (n k : ℕ) :
    (ZMod.val (a + 2^n - b)).testBit k
  = (ZMod.val (a + 2^n + -b)).testBit k := by
  simp [sub_eq_add_neg, add_comm, add_left_comm]
  /- using -/
  /-   (testBit_sub_eq_addNeg (a + 2^n) b k) -/

/-- Pack the repeated bounds (`ha hb hp hp'`) into your structure in one shot. -/
def Bounds.of_assumptions
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : ZMod p}
    (ha : a.val < 2^n) (hb : b.val < 2^n)
    (hp_succ : 2^(n+1) < p) : Bounds p n a b :=
  ⟨ha, hb, hp_succ, pow_lt_of_succ hp_succ⟩

lemma add_two_pow_sub_eq_add_diff {n a b : ℕ} (h : b ≤ a) :
    a + 2 ^ n - b = 2 ^ n + (a - b) := by
  calc
    a + 2 ^ n - b
      = (2 ^ n + a) - b := by ac_rfl
    _ = (2 ^ n + a) - (b + 0) := by rfl
    _ = 2 ^ n + (a - b) := by
      simp only [Nat.add_zero, Nat.add_sub_assoc h]

lemma add_two_pow_sub_eq_sub_diff {n a b : ℕ} (h : a < b) :
    a + 2 ^ n - b = 2 ^ n - (b - a) := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le (Nat.le_of_lt h)).symm
  calc
    a + 2 ^ n - b
        = a + 2 ^ n - (a + (b - a)) := by rw [hb]; simp only [Nat.add_sub_cancel_left]
    _ = (2 ^ n + a) - ((b - a) + a) := by ac_rfl
    _ = 2 ^ n - (b - a) := by simp only [Nat.add_sub_add_right]

lemma add_two_pow_sub_lt_pow_succ {n a b : ℕ} (ha : a < 2 ^ n) :
    a + 2 ^ n - b < 2 ^ (n + 1) := by
  calc
    a + 2 ^ n - b ≤ a + 2 ^ n := Nat.sub_le _ _
    _ < 2 ^ n + 2 ^ n := Nat.add_lt_add_right ha _
    _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_two]

lemma ZMod.val_add_two_pow_sub_rel
    {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a b : F p) :

    if ZMod.val a < ZMod.val b then
      ZMod.val a + 2 ^ n - ZMod.val b < 2 ^ n
    else
      ZMod.val a + 2 ^ n - ZMod.val b ≥ 2 ^ n := by

  split_ifs with h_lt
  · rw [add_two_pow_sub_eq_sub_diff h_lt]
    have h_pos : 0 < ZMod.val b - ZMod.val a := Nat.sub_pos_of_lt h_lt
    simp_all [tsub_lt_self_iff, pow_pos]
  · rw [add_two_pow_sub_eq_add_diff (le_of_not_gt h_lt)]
    exact Nat.le_add_right _ _

lemma ZMod.val_two_pow_of_lt {p n : ℕ} [NeZero p] [Fact p.Prime] (h : 2 ^ n < p) (hp : p > 2):
    (2 ^ n : ZMod p).val = 2 ^ n := by

  have p_ne_zero := NeZero.ne p
  rw [ZMod.val_pow] at *
  rw [← Nat.cast_ofNat]
  rw [ZMod.val_natCast]
  . -- (2 % p) ^ n = 2 ^ n
    have h_mod := Nat.mod_eq_iff_lt (m := 2) (n := p) p_ne_zero

    have h_mod' : 2 % p = 2 := by
      simp_all only [gt_iff_lt, ne_eq, iff_true]

    rw [h_mod']
    
  . 
    rw [← Nat.cast_ofNat]
    rw [ZMod.val_natCast]

    have h_mod := Nat.mod_eq_iff_lt (m := 2) (n := p) p_ne_zero
    have h_mod' : 2 % p = 2 := by
      simp_all only [gt_iff_lt, ne_eq, iff_true]
    rw [h_mod']
    exact h

-- Helper: no wrap on a + 2^n
/- omit [Fact (p > 2)] -/
private lemma add_two_pow_no_wrap_val {p : ℕ} [Fact (p > 2)] [Fact p.Prime] (a : ZMod p) (n : ℕ)
  (ha : a.val < 2 ^ n) (hp : 2 ^ n < p) (hp' : 2 ^ (n+1) < p) :
  (a + 2 ^ n).val = a.val + 2 ^ n := by

  have hp2 := Fact.out (p := p > 2)

  have h2n : (2^n: ZMod p).val = 2^n := by
    exact ZMod.val_two_pow_of_lt hp hp2

  have hlt : a.val + 2 ^ n < p := lt_trans
    (by
      have : a.val + 2 ^ n < 2 ^ n + 2 ^ n := Nat.add_lt_add_right ha _
      simp [pow_succ]
      rw [Nat.mul_two]
      exact this
    )
    hp'
  have hlt' : a.val + (2^n : ZMod p).val < p := by
    simp_all only

  rw [ZMod.val_add_of_lt hlt']
  rw [h2n]

 -- Helper: no wrap on (a + 2^n) - b because b.val ≤ a.val + 2^n
private lemma ZMod.val_sub_add_two_pow_of_no_wrap (n : ℕ) (a b : ZMod p)
  (ha : a.val < 2 ^ n) (hb : b.val < 2 ^ n) (hp : 2^n < p) (hp' : 2 ^ (n+1) < p) :
  ((a + 2 ^ n) - b).val = (a.val + 2 ^ n) - b.val := by
  -- First compute (a + 2^n).val without wrap
  have hadd : (a + 2 ^ n).val = a.val + 2 ^ n :=
    add_two_pow_no_wrap_val (n:=n) a ha hp hp'
  -- b.val ≤ 2^n ≤ 2^n + a.val = (a + 2^n).val
  have hb_le_twoPow : b.val ≤ 2 ^ n := Nat.le_of_lt hb
  have twoPow_le_sum : 2 ^ n ≤ (a.val + 2 ^ n) := by
    simp [Nat.add_comm]
  have hble : b.val ≤ (a.val + 2 ^ n) := le_trans hb_le_twoPow twoPow_le_sum
  -- For subtraction in ZMod: if x.val ≥ y.val then (x - y).val = x.val - y.val
  -- Rewrite x.val using hadd, then finish.
  have hres : ((a + 2 ^ n) - b).val = (a + (2 ^ n : ℕ)).val - b.val := by
    rw [ZMod.val_sub]
    simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pow, Nat.cast_ofNat]
    rw [hadd]
    exact hble

  rw [hres]
  simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pow, Nat.cast_ofNat]

lemma ZMod.val_sub_add_two_pow_rel {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p}
    (R : ℕ → ℕ → Prop) (threshold : ℕ)
    (h_bounds : Bounds p n a b)
    (h_val : R (ZMod.val a + 2 ^ n - ZMod.val b) threshold) :
    R (ZMod.val (a + 2 ^ n - b)) threshold := by

  have hp' : 2 ^ n < p := pow_lt_of_succ h_bounds.hp

  rw [ZMod.val_sub_add_two_pow_of_no_wrap n a b h_bounds.ha h_bounds.hb h_bounds.hp' h_bounds.hp]
  exact h_val

lemma ZMod.val_sub_add_two_pow_lt {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p} : 
    (Bounds p n a b) -> 
    (ZMod.val a + 2 ^ n - ZMod.val b) < (2 ^ n) -> 
    (ZMod.val (a + 2 ^ n - b)) < (2 ^ n) := 
    ZMod.val_sub_add_two_pow_rel (· < ·) (2 ^ n)

lemma ZMod.val_sub_add_two_pow_ge {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p} :
    (Bounds p n a b) -> 
    (ZMod.val a + 2 ^ n - ZMod.val b) ≥ (2 ^ n) -> 
    (ZMod.val (a + 2 ^ n - b)) ≥ (2 ^ n) :=
    ZMod.val_sub_add_two_pow_rel (· ≥ ·) (2 ^ n)

lemma ZMod.val_sub_add_two_pow_no_wrap {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p} : 
    (Bounds p n a b) -> 
    (ZMod.val a + 2 ^ n - ZMod.val b) < (2 ^ (n+1)) -> 
    (ZMod.val (a + 2 ^ n - b)) < (2 ^ (n+1)) := 
    ZMod.val_sub_add_two_pow_rel (· < ·) (2 ^ (n+1))
  
lemma bit_is_clear {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a : ZMod p)
    (hlt : ZMod.val a < 2^n) :
    (ZMod.val a).testBit n = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  -- ⊢ decide (a.val / 2 ^ n % 2 = 1) = false
  have hbpos : 0 < 2^n := pow_pos (by decide) n
  have hdiv : ZMod.val a / 2^n = 0 :=
    Nat.div_eq_of_lt hlt
  rw [hdiv, Nat.zero_mod]
  -- ⊢ decide (0 = 1) = false
  simp only [zero_ne_one, decide_false]

lemma bit_is_set {p : ℕ} [Fact p.Prime]
  /- (n : ℕ) (a b : ℕ)  -/
  (n : ℕ) (x : F p)
  (hlt: ZMod.val x < 2^(n+1))
  (hge: ZMod.val x ≥ 2^n) :
    (ZMod.val x).testBit n = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq ]

      simp only [decide_eq_true_eq]
      /- ⊢ ZMod.val a / 2 ^ n % 2 = 1 -/
      set x := ZMod.val x
      have hbpos : 0 < 2^n := pow_pos (by decide) n

        -- lower bound: 1 ≤ x / 2^n
      have h1 : 1 ≤ x / 2^n := by
        simp only [Nat.le_div_iff_mul_le hbpos, one_mul]
        exact hge

        -- upper bound: x / 2^n < 2
      have h2 : x / 2^n < 2 := by
        rw [Nat.div_lt_iff_lt_mul hbpos]

        rw [← Nat.pow_add_one']
        exact hlt

      rw [le_antisymm (Nat.lt_succ_iff.mp h2) h1]

-- The nth bit of (a + 2^n - b) is 0 iff a.val < b.val, otherwise 1.
lemma testBit_n_of_add_two_pow_sub
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p}
    (hB : Bounds p n a b)
    (h_sum_lt : ZMod.val (a + (2 ^ n : F p) - b) < 2 ^ (n + 1)) :
    (ZMod.val (a + (2 ^ n : F p) - b)).testBit n
      = (if ZMod.val a < ZMod.val b then false else true) := by
  -- relational split for a.val vs b.val
  have h_rel := ZMod.val_add_two_pow_sub_rel n a b
  -- branch on (a.val < b.val)
  by_cases hlt : ZMod.val a < ZMod.val b
  · -- then sum < 2^n, bit is 0
    have h_lt : ZMod.val a + 2 ^ n - ZMod.val b < 2 ^ n := by
      simpa [hlt] using h_rel
    have hx_lt : ZMod.val (a + (2 ^ n : F p) - b) < 2 ^ n :=
      ZMod.val_sub_add_two_pow_lt hB h_lt
    have h_clear : (ZMod.val (a + (2 ^ n : F p) - b)).testBit n = false :=
      bit_is_clear n (a + (2 ^ n : F p) - b) hx_lt
    simpa [hlt, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_clear
  · -- else sum ≥ 2^n, bit is 1
    have h_ge : ZMod.val a + 2 ^ n - ZMod.val b ≥ 2 ^ n := by
      simpa [hlt] using h_rel
    have hx_ge : ZMod.val (a + (2 ^ n : F p) - b) ≥ 2 ^ n :=
      ZMod.val_sub_add_two_pow_ge hB h_ge
    have h_set : (ZMod.val (a + (2 ^ n : F p) - b)).testBit n = true :=
      bit_is_set n (a + (2 ^ n : F p) - b) h_sum_lt hx_ge
    simpa [hlt, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_set


def main (n : ℕ) (hn : 2^(n+1) < p) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← Num2Bits.circuit (n + 1) hn diff
  let out <== 1 - bits[n]
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := main n hn
  localLength _ := n + 2
  localLength_eq := by simp [circuit_norm, main, Num2Bits.circuit]
  output _ i := var ⟨ i + n + 1 ⟩
  output_eq := by simp +arith [circuit_norm, main, Num2Bits.circuit]

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n -- TODO: ∧ n <= 252

  Spec := fun (x, y) output =>
    output = (if x.val < y.val then 1 else 0)

  soundness := by
    intro i₀ env input_var input h_input h_assumptions h_holds
    unfold main at *
    simp only [circuit_norm, Num2Bits.circuit] at h_holds
    simp only [circuit_norm] at *
--
    rw [← h_input]


    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]
    set a := input.1
    set b := input.2
    set hp := hn
    
    have hp' : 2 ^ n < p := pow_lt_of_succ hp

    have h_bounds : Bounds p n a b := Bounds.of_assumptions h_assumptions.left h_assumptions.right hp 


    rw [h1, h2] at h_holds
    rw [h1, h2]
    simp only [id_eq]
    set summation := ((ZMod.val a : ℤ) + 2 ^ n + -(ZMod.val b : ℤ))
    rw [← Nat.add_assoc] at h_holds
    rw [h_holds.right]
    obtain ⟨⟨h_holds1, h_holds2⟩, h_holds3⟩ := h_holds
    simp only [Vector.ext_iff] at h_holds2

    specialize h_holds2 n (Nat.lt_succ_self n)

    rw [Vector.getElem_map, Vector.getElem_mapRange] at h_holds2
    simp only [circuit_norm] at h_holds2
    simp only [fieldToBits, toBits] at h_holds2
    rw [Vector.getElem_map, Vector.getElem_mapRange] at h_holds2
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h_holds2
    rw [h_holds2]
    by_cases hab : ZMod.val a < ZMod.val b
    .
      -- sum is < 2^n, so nth bit is 0
      have h_rel := ZMod.val_add_two_pow_sub_rel n a b
      simp [hab] at h_rel
      have h_lt := h_rel

      have h_val_lt : ZMod.val (a + (2 ^ n : F p) - b) < 2 ^ n := by
        exact ZMod.val_sub_add_two_pow_lt h_bounds h_lt
      have h_bit_clear : (ZMod.val (a + (2 ^ n : F p) - b)).testBit n = false :=
        bit_is_clear n (a + (2 ^ n : F p) - b) h_val_lt
      have h_bit_clear' : (ZMod.val (a + 2 ^ n + -b)).testBit n = false := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_bit_clear
      simp [h_bit_clear', hab]
    .
      -- sum is ≥ 2^n, so nth bit is 1

      have hab' : ZMod.val a ≥ ZMod.val b := by
        simp_all only [not_lt, ge_iff_le]
      have h_holds1' : ZMod.val (a + 2 ^ n - b) < 2 ^ (n + 1) := by
        rw [← sub_eq_add_neg] at h_holds1
        exact h_holds1

      have h_rel := ZMod.val_add_two_pow_sub_rel n a b
      simp [hab] at h_rel
      have h_ge := h_rel
      have h_val_ge : ZMod.val (a + (2 ^ n : F p) - b) ≥ 2 ^ n := by
        exact ZMod.val_sub_add_two_pow_ge h_bounds h_ge
      have h_bit_set : (ZMod.val (a + (2 ^ n : F p) - b)).testBit n = true :=
        bit_is_set n (a + (2 ^ n : F p) - b) h_holds1' h_val_ge
      have h_bit_set' : (ZMod.val (a + 2 ^ n + -b)).testBit n = true := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_bit_set
        
      simp [h_bit_set', hab]

  completeness := by
    circuit_proof_start
    simp only [Num2Bits.circuit] at *
    simp only [circuit_norm] at *
    simp_all only [gt_iff_lt, true_and, id_eq, and_true]

    obtain ⟨h_envl, h_envr⟩ := h_env
    obtain ⟨ha, hb⟩ := h_assumptions

    set hp := hn

    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]

    set a := input.1
    set b := input.2
    rw [h1, h2]
    rw [h1, h2] at h_envl

    rw [← sub_eq_add_neg (a:=(a+ 2 ^ n))]

    have hp' : 2 ^ n < p := pow_lt_of_succ hp

    have h_bounds : Bounds p n a b := Bounds.of_assumptions ha hb hp 
    have h_comp := ZMod.val_sub_add_two_pow_no_wrap h_bounds 

    have h_sum_lt_2n1 : ZMod.val a + 2 ^ n - ZMod.val b < 2 ^ (n + 1) := 
      add_two_pow_sub_lt_pow_succ ha

    exact h_comp h_sum_lt_2n1

end LessThan
