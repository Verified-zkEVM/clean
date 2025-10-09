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
  (bounds: Bounds p n a b) :
  ((a + 2 ^ n) - b).val = (a.val + 2 ^ n) - b.val := by
  -- First compute (a + 2^n).val without wrap
  have hadd : (a + 2 ^ n).val = a.val + 2 ^ n :=
    add_two_pow_no_wrap_val (n:=n) a bounds.ha bounds.hp' bounds.hp
  -- b.val ≤ 2^n ≤ 2^n + a.val = (a + 2^n).val
  have hb_le_twoPow : b.val ≤ 2 ^ n := Nat.le_of_lt bounds.hb
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
    (bounds : Bounds p n a b)
    (h_val : R (ZMod.val a + 2 ^ n - ZMod.val b) threshold) :
    R (ZMod.val (a + 2 ^ n - b)) threshold := by

  have hp' : 2 ^ n < p := pow_lt_of_succ bounds.hp

  rw [ZMod.val_sub_add_two_pow_of_no_wrap n a b bounds]
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

/-- From `<` on naturals to `<` on `.val (a + 2^n - b)` using `Bounds`. -/
lemma zval_lt_of_nat_lt
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : ZMod p}
    (bounds : Bounds p n a b)
    (h : a.val + 2^n - b.val < 2^n) :
    (a + 2^n - b).val < 2^n :=
  ZMod.val_sub_add_two_pow_lt bounds h

/-- From `≥` on naturals to `≥` on `.val (a + 2^n - b)` using `Bounds`. -/
lemma zval_ge_of_nat_ge
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : ZMod p}
    (bounds : Bounds p n a b)
    (h : a.val + 2^n - b.val ≥ 2^n) :
    (a + 2^n - b).val ≥ 2^n :=
  ZMod.val_sub_add_two_pow_ge bounds h
  
/-- If `a.val < b.val`, the nth bit of `ZMod.val (a + 2^n - b)` is `false`. -/
lemma nth_bit_clear_of_val_lt
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p}
    (bounds : Bounds p n a b)
    (hab : a.val < b.val) :
    (ZMod.val (a + 2^n - b)).testBit n = false := by
  -- nat-level bound
  have hnlt := ZMod.val_add_two_pow_sub_rel n a b
  simp [hab] at hnlt
  have h_lt := hnlt
  -- lift through no-wrap
  have hzlt := zval_lt_of_nat_lt bounds hnlt
  exact bit_is_clear n (a + 2^n - b) hzlt

/-- If `a.val ≥ b.val` and the sum is `< 2^(n+1)`, the nth bit is `true`. -/
lemma nth_bit_set_of_val_ge
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p}
    (bounds : Bounds p n a b)
    (h_sum_lt : (a + 2^n - b).val < 2^(n+1))
    /- (hab : a.val ≥ b.val) : -/
    (hab : ¬(a.val < b.val)) :
    (ZMod.val (a + 2^n - b)).testBit n = true := by
  -- nat-level bound
  have h_rel := ZMod.val_add_two_pow_sub_rel n a b
  simp [hab] at h_rel
  have h_ge := h_rel
  -- lift through no-wrap
  have hzge := zval_ge_of_nat_ge bounds h_ge
  exact bit_is_set n (a + 2^n - b) h_sum_lt hzge

lemma num2bits_bit_eq_testBit
    {p n i₀ : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {env : Environment (F p)}
    {a b : F p}
    (h_holds :
      Vector.map (Expression.eval env)
        (Vector.mapRange (n + 1) (fun i ↦ var { index := i₀ + i }))
      = fieldToBits (n + 1) (a + 2 ^ n + -b)) :
    (Vector.map (Expression.eval env)
       (Vector.mapRange (n + 1) (fun i ↦ var { index := i₀ + i })))[n]'(Nat.lt_succ_self n)
      =
    (if (ZMod.val (a + 2 ^ n + -b)).testBit n then (1 : F p) else 0) := by
  simp only [Vector.ext_iff] at h_holds
  specialize h_holds n (Nat.lt_succ_self n)
  simp only [Vector.getElem_map, Vector.getElem_mapRange,
        fieldToBits, toBits, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h_holds

  simp only [Vector.getElem_map, Vector.getElem_mapRange]
  exact h_holds

lemma nth_bit_from_val
    {p n : ℕ} [Fact p.Prime] [Fact (p > 2)]
    {a b : F p}
    (bounds : Bounds p n a b)
    (h_holds1 : ZMod.val (a + 2 ^ n - b) < 2 ^ (n + 1))
    : (ZMod.val (a + 2 ^ n + -b)).testBit n
      = decide (¬ (ZMod.val a < ZMod.val b)) := by
  by_cases hab : ZMod.val a < ZMod.val b
  · -- Case 1: a < b → bit n is 0
    have h_bit_clear :
        (ZMod.val (a + 2 ^ n + -b)).testBit n = false := by
      have h_bit := nth_bit_clear_of_val_lt (p := p) (n := n) (a := a) (b := b) bounds hab
      rw [sub_eq_add_neg] at h_bit
      exact h_bit
    simp [h_bit_clear, hab]
  · -- Case 2: a ≥ b → bit n is 1
    have h_bit_set :
        (ZMod.val (a + 2 ^ n + -b)).testBit n = true := by
      have h_ge : ZMod.val a ≥ ZMod.val b := by simpa [not_lt, ge_iff_le] using hab
      have h_bit := nth_bit_set_of_val_ge (p := p) (n := n) (a := a) (b := b)
                        bounds h_holds1 hab
      rw [sub_eq_add_neg] at h_bit
      exact h_bit
    simp [h_bit_set, hab]

/-- In any field, `1 - [y ≤ x] = [x < y]` where brackets mean 1/0-as-a-field. -/
lemma one_sub_if_le_eq_if_lt {F} [Field F] {x y : ℕ} :
    (1 : F) + - (if y ≤ x then 1 else 0)
  = (if x < y then 1 else 0) := by
  by_cases h : y ≤ x
  · -- then `¬ (x < y)`
    have hxlt : ¬ x < y := not_lt.mpr h
    simp [h, hxlt]
  · -- so `x < y`
    have hxlt : x < y := lt_of_not_ge h
    simp [h, hxlt]

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

    -- ① evaluate inputs
    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]
    set a := input.1
    set b := input.2
    set hp := hn
    rw [h1, h2] at h_holds
    rw [h1, h2]
    simp only [id_eq]
    
    -- ② prepare bounds
    have hp' : 2 ^ n < p := pow_lt_of_succ hp

    have bounds := Bounds.of_assumptions h_assumptions.left h_assumptions.right hp 

    -- ③ extract nth bit
    rw [← Nat.add_assoc] at h_holds
    obtain ⟨⟨h_holds1, h_holds2⟩, h_holds3⟩ := h_holds

    rw [h_holds3]

    have h_nbit := num2bits_bit_eq_testBit h_holds2
    simp only [circuit_norm] at h_nbit
    rw [h_nbit]
    
    -- ④ core logic: bit is set iff a ≥ b
    rw [← sub_eq_add_neg] at h_holds1
    have h_bit := nth_bit_from_val bounds h_holds1
    simp only [h_bit, circuit_norm]
    simp only [not_lt, decide_eq_true_eq]
    simpa using (one_sub_if_le_eq_if_lt (F := F p) (x := ZMod.val a) (y := ZMod.val b))

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

    have bounds := Bounds.of_assumptions ha hb hp 

    have h_sum_lt_2n1 : ZMod.val a + 2 ^ n - ZMod.val b < 2 ^ (n + 1) := 
      add_two_pow_sub_lt_pow_succ ha

    exact ZMod.val_sub_add_two_pow_no_wrap bounds h_sum_lt_2n1

end LessThan
