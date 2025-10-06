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

lemma a_lt_b_eq_sum_lt_2n {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a b : F p) (hn : ZMod.val a < ZMod.val b) :
    (ZMod.val a : ℤ) + 2^n - (ZMod.val b : ℤ) < 2^n := by
  rw [Int.add_sub_assoc, Int.add_comm]

  linarith [Int.ofNat_lt.mpr hn]

lemma val_pow_of_lt {p n : ℕ} [NeZero p] (h : 2^n < p) :
    ((2^n : ℕ): ZMod p).val = 2^n := by
  rw [ZMod.val_natCast_of_lt (a := 2^n) (n := p)]
  exact h

lemma test_lemma {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a b : F p) (hab : ZMod.val a < ZMod.val b)
    (ha : ZMod.val a < 2^n)
    (hb : ZMod.val b < 2^n)
    (hp : 2^n < p)
    (hp' : 2^(n+1) < p)
    (h_val: (ZMod.val a + 2^n - ZMod.val b) < 2^n) :
    (a + 2 ^ n - b).val < 2 ^ n := by

      have h2n : ((2^n : ℕ) : ZMod p).val = 2^n := by
        change (((2^n : ℕ) : ZMod p).val) = 2^n
        simp only [ZMod.val_natCast]
        simp only [Nat.mod_eq_of_lt hp]

      have h_int : (a.val : ℤ) + 2^n - (b.val : ℤ) < 2^n := by
        linarith

      have h_aa : ZMod.val a = a := by
        have hap : a.val < p := by
          linarith

        sorry
        /- rw [ZMod.val_natCast p (a.val: ℕ)] -/
        /- rw [FieldUtils.natToField a hap] -/
        /- simp only [instFieldFOfFactPrime.congr_simp] -/
        /- apply FieldUtils.val_lt_p -/
        /- linarith -/


      have h_a2n : (a.val : ℕ) + 2^n < p + 0 := by
        have hap : a.val < p := by
          linarith

        sorry
        /- rw [ZMod.val_cast_of_lt hap] -/
        /- simp_all only [Nat.add_lt_add_of_le_of_lt (a := a.val) (b := p) (c := 2^n) (d := 0) hap ] -/
        /- linarith -/
        
      /- ring_nf at h_int -/
      /- ring_nf -/
      /- simp_all only [Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val] -/
      simp_all only [Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val]
      /- simp_all only [ZMod.val_sub, ZMod.cast_sub, Int.cast_sub] -/
      sorry

lemma zmod_def {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    x.val = ZMod.val x := rfl

lemma bit_is_clear {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a : ZMod p)
    (hlt : ZMod.val a < 2^n) :
    (ZMod.val a).testBit n = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hbpos : 0 < 2^n := pow_pos (by decide) n
  have hdiv : ZMod.val a / 2^n = 0 :=
    Nat.div_eq_of_lt hlt
  rw [hdiv, Nat.zero_mod]
  simp only [zero_ne_one, decide_false]

lemma bit_is_set {p : ℕ} [Fact p.Prime] 
  /- (n : ℕ) (a b : ℕ)  -/
  (n : ℕ) (x : F p) 
  (hlt: ZMod.val x < 2^(n+1)) 
  (hge: ZMod.val x > 2^n) :
    (ZMod.val x).testBit n = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq ]

      /- ⊢ ZMod.val a / 2 ^ n % 2 = 1 -/
      simp only [decide_eq_true_eq]
      set x := ZMod.val x
        -- lower bound: 1 ≤ x / 2^n
      have hbpos : 0 < 2^n := pow_pos (by decide) n
      have h1 : 1 ≤ x / 2^n := by
        simp only [Nat.le_div_iff_mul_le hbpos, one_mul]
        apply Nat.le_of_lt at hge
        exact hge

        -- upper bound: x / 2^n < 2
      have h2 : x / 2^n < 2 := by
        rw [Nat.div_lt_iff_lt_mul hbpos]

        rw [← Nat.pow_add_one']
        exact hlt

      rw [le_antisymm (Nat.lt_succ_iff.mp h2) h1]

def main (n : ℕ) (hn : 2^(n+1) < p) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← Num2Bits.circuit (n + 1) hn diff
  let out <==1 - bits[n]
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
--   
    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]
    set a := input.1
    set b := input.2
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
      have h_assumptions_a' : ZMod.val a < 2 ^ (n+1) :=
        lt_trans h_assumptions.left (Nat.pow_lt_pow_succ (a:=2) (by decide : 1 < 2) )

      have hn := a_lt_b_eq_sum_lt_2n n a b hab
      
      simp only at hn
      /- change (a + 2^n - b).val = 2^n -/
      repeat rw [Mathlib.Tactic.RingNF.add_neg]

      have hb := bit_is_clear n (a + 2 ^ n - b) hn 

      rw [← zmod_def] at hb

      have hc : (ZMod.val (a + 2 ^ n - b)).testBit n = false := by 
        exact hb


      rw [hc]
      simp 
      exact hab

    . 
      
      have h_assumptions_b' : ZMod.val b < 2 ^ (n+1) :=
        lt_trans h_assumptions.right (Nat.pow_lt_pow_succ (a:=2) (by decide : 1 < 2) )
      have hn := a_lt_b_eq_sum_lt_2n n a b hab

      sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry

end LessThan
