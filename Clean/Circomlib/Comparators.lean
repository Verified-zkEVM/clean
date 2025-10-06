import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Mathlib.Data.Int.Basic
/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/comparators.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace IsZero
/-
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}
-/
def main (input : Expression (F p)) := do
  let inv ← witness fun env =>
    let x := input.eval env
    if x ≠ 0 then x⁻¹ else 0

  let out <== -input * inv + 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 2

  Assumptions _ := True

  Spec input output :=
    output = (if input = 0 then 1 else 0)

  soundness := by
    circuit_proof_start
    simp only [id_eq, h_holds]
    split_ifs with h_ifs
    . simp only [h_ifs, zero_mul, neg_zero, zero_add]
    . rw [neg_add_eq_zero]
      have h1 := h_holds.left
      have h2 := h_holds.right
      rw [h1] at h2
      simp only [id_eq, mul_eq_zero] at h2
      cases h2
      case neg.inl hl => contradiction
      case neg.inr hr =>
        rw [neg_add_eq_zero] at hr
        exact hr

  completeness := by
    circuit_proof_start
    cases h_env with
    | intro left right =>
      simp only [left, ne_eq, id_eq, ite_not, mul_ite, mul_zero] at right
      simp only [id_eq, right, left, ne_eq, ite_not, mul_ite, mul_zero, mul_eq_zero, true_and]
      split_ifs <;> aesop

end IsZero

namespace IsEqual
/-
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 - input.2
  let out ← IsZero.circuit diff
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 2

  Assumptions _ := True

  Spec input output :=
    output = (if input.1 = input.2 then 1 else 0)

  completeness := by
    simp only [circuit_norm, main, IsZero.circuit]

  soundness := by
    circuit_proof_start
    rw [← h_input]
    simp only [id_eq]

    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]

    rw [h1, h2] at h_holds
    simp only [IsZero.circuit] at h_holds ⊢

    rw [h_holds, h1, h2]

    apply ite_congr
    . ring_nf
      simp [sub_eq_zero]

    . intro h_eq
      rfl
    . intro h_eq
      rfl

    trivial

end IsEqual

namespace ForceEqualIfEnabled
/-
template ForceEqualIfEnabled() {
    signal input enabled;
    signal input in[2];

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    (1 - isz.out)*enabled === 0;
}
-/
structure Inputs (F : Type) where
  enabled : F
  inp : fieldPair F

instance : ProvableStruct Inputs where
  components := [field, fieldPair]
  toComponents := fun { enabled, inp } => .cons enabled (.cons inp .nil)
  fromComponents := fun (.cons enabled (.cons inp .nil)) => { enabled, inp }

def main (inputs : Var Inputs (F p)) := do
  let { enabled, inp } := inputs
  let isz ← IsZero.circuit (inp.2 - inp.1)
  enabled * (1 - isz) === 0

def circuit : FormalAssertion (F p) Inputs where
  main
  localLength _ := 2

  Assumptions := fun { enabled, inp } =>
    enabled = 0 ∨ enabled = 1

  Spec := fun { enabled, inp } =>
    enabled = 1 → inp.1 = inp.2

  soundness := by
    circuit_proof_start
    intro h_ie
    simp_all only [gt_iff_lt, one_ne_zero, or_true, id_eq, one_mul]
    cases h_input with
    | intro h_enabled h_inp =>
      rw [← h_inp]
      simp only
      cases h_holds with
      | intro h1 h2 =>
        rw [h1] at h2
        rw [add_comm] at h2
        simp only [id_eq] at h2
        split_ifs at h2 with h_ifs
        . simp_all only [neg_add_cancel]
          rw [add_comm, neg_add_eq_zero] at h_ifs
          exact h_ifs
        . simp_all only [neg_zero, zero_add, one_ne_zero]
        rw [add_comm, neg_add_eq_zero] at h2
        rw [h2] at h1
        trivial

  completeness := by
    circuit_proof_start
    simp_all only [gt_iff_lt, id_eq]
    constructor
    trivial
    rw [mul_eq_zero, add_comm, neg_add_eq_zero]
    cases h_assumptions with
    | inl h_enabled_l => apply Or.inl h_enabled_l
    | inr h_enabled_r =>
      simp_all only [forall_const, one_ne_zero, false_or]
      have h_spec := h_spec.symm
      rw [← sub_eq_zero, ← h_input.right] at h_spec
      rw [← sub_eq_add_neg] at h_env
      rw [h_env]
      simp only [id_eq, h_spec, ↓reduceIte]
      trivial

end ForceEqualIfEnabled

namespace LessThan
/-
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1 << n) - in[1];

    out <== 1-n2b.out[n];
}
-/
def main (n : ℕ) (hn : 2^(n+1) < p) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← Num2Bits.circuit (n + 1) hn diff
  let out <== 1 - bits[n]
  return out

-- set_option pp.all true
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := main n hn
  localLength _ := n + 2
  localLength_eq := by simp [circuit_norm, main, Num2Bits.circuit]
  output _ i := var ⟨ i + n + 1 ⟩
  output_eq := by simp +arith [circuit_norm, main, Num2Bits.circuit]

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n

  Spec := fun (x, y) output =>
    output = (if x.val < y.val then 1 else 0)


  soundness := by
    circuit_proof_start
    simp only [circuit_norm, Num2Bits.circuit] at h_holds ⊢
    rcases h_assumptions with ⟨hx, hy⟩
    have hx_eval : Expression.eval env input_var.1 = input.1 := by
      simpa using congrArg Prod.fst h_input
    have hy_eval : Expression.eval env input_var.2 = input.2 := by
      simpa using congrArg Prod.snd h_input

    simp [hx_eval, hy_eval] at h_holds

    set out := env.get (i₀ + n + 1) with hout
    have two_exp_n_small : 2 ^ n < p := by
      have : 2 ^ n ≤ 2 ^ (n + 1) := by gcongr; repeat linarith
      exact lt_of_le_of_lt this hn

    have heq: ZMod.val ((2: F p) ^ n) = 2 ^ n := by
      rw [ZMod.val_pow]
      rw [ZMod.val_ofNat_of_lt]
      · simp_all
        exact Fact.out
      convert two_exp_n_small
      rw [ZMod.val_ofNat_of_lt]
      simp_all
      exact Fact.out

    by_cases hlt : ZMod.val input.1 < ZMod.val input.2

    -- CASE input.1 < input.2
    simp [hlt]

    have hdiff_lt : ZMod.val (input.1 + 2 ^ n - input.2) < 2^n := by
      rw[ZMod.val_sub]
      · rw[ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2 ^ n - ZMod.val input.2 <  ZMod.val input.2 + 2 ^ n - ZMod.val input.2 := by omega
            _ = 2 ^ n := by omega
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega
      · rw[ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega

    -- split h_holds to h1 h2 h3
    have h3 := h_holds.right
    have h2 := h_holds.left.right
    have h1 := h_holds.left.left

    rw[add_assoc] at hout
    rw[← hout] at h3
    rw[h3]
    --simp the goal basic math


    unfold fieldToBits at h2
    unfold toBits at h2
    --now I need to use that On Nat, shift is equivalent to a / 2 ^ b.

    apply congrArg (fun v => v[n]) at h2
    simp only [Vector.getElem_map, Vector.getElem_mapRange,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, circuit_norm] at h2


    simp only [← sub_eq_add_neg, Nat.testBit_eq_false_of_lt hdiff_lt, Bool.false_eq_true,
      ↓reduceIte] at h2
    rw[h2]
    simp only [neg_zero, add_zero]

    -- CASE input.1 >= input.2
    simp [hlt]
    have hdiff_ge : ZMod.val (input.1 + 2 ^ n - input.2) >= 2^n := by
      rw[ZMod.val_sub]
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2 ^ n - ZMod.val input.2 ≥ ZMod.val input.1 + 2 ^ n - ZMod.val input.1 := by omega
            _ = 2 ^ n := by omega
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega
      · rw[ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega

    -- split h_holds to h1 h2 h3
    have h3 := h_holds.right
    have h2 := h_holds.left.right
    have h1 := h_holds.left.left

    rw[add_assoc] at hout
    rw[← hout] at h3
    rw[h3]
    --simp the goal basic math
    unfold fieldToBits at h2
    unfold toBits at h2
    --now I need to use that On Nat, shift is equivalent to a / 2 ^ b.

    apply congrArg (fun v => v[n]) at h2
    simp only [Vector.getElem_map, Vector.getElem_mapRange,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, circuit_norm] at h2

    have hf: (ZMod.val (input.1 + 2 ^ n + -input.2)).testBit n = true := by
      have hpos : 0 < 2 ^ n := pow_pos (by decide) n
      have hlt2 : (ZMod.val (input.1 + 2 ^ n + -input.2)) / 2 ^ n < 2 := by
        have : (ZMod.val (input.1 + 2 ^ n + -input.2)) < 2 ^ n * 2 := by simpa [pow_succ, two_mul, mul_two] using h1
        exact Nat.div_lt_of_lt_mul this

      have hge1 : 1 ≤ (ZMod.val (input.1 + 2 ^ n + -input.2)) / 2 ^ n :=
        (Nat.le_div_iff_mul_le hpos).mpr (by simpa [one_mul, sub_eq_add_neg] using hdiff_ge)

      have hxdiv : (ZMod.val (input.1 + 2 ^ n + -input.2)) / 2 ^ n = 1 :=
        le_antisymm (Nat.lt_succ_iff.mp hlt2) hge1

      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hxdiv]



    simp only [hf, ↓reduceIte] at h2
    simp only [h2, add_neg_cancel]



  completeness := by
    circuit_proof_start
    simp only [circuit_norm, Num2Bits.circuit] at *
    rcases h_assumptions with ⟨hx, hy⟩
    have hx_eval : Expression.eval env input_var.1 = input.1 := by
      simpa using congrArg Prod.fst h_input
    have hy_eval : Expression.eval env input_var.2 = input.2 := by
      simpa using congrArg Prod.snd h_input
    simp [hx_eval, hy_eval] at *
    set out := env.get (i₀ + n + 1) with hout
    have two_exp_n_small : 2 ^ n < p := by
      have : 2 ^ n ≤ 2 ^ (n + 1) := by gcongr; repeat linarith
      exact lt_of_le_of_lt this hn

    have heq: ZMod.val ((2: F p) ^ n) = 2 ^ n := by
      rw [ZMod.val_pow]
      rw [ZMod.val_ofNat_of_lt]
      · simp_all
        exact Fact.out
      convert two_exp_n_small
      rw [ZMod.val_ofNat_of_lt]
      simp_all
      exact Fact.out

    have hdiff_lt_basic : ZMod.val (input.1 + 2 ^ n - input.2) < 2^ (n+1) := by
      rw[ZMod.val_sub]
      · rw[ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2 ^ n - ZMod.val input.2 <  2^n + 2 ^ n := by omega
            _ = 2 ^ (n + 1) := by rw[pow_succ, mul_two]
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega
      · rw[ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2 ^ n = 2 ^ (n + 1) := by
            rw[pow_succ, two_mul]
            omega
          omega

    have h2 := h_env.right
    refine And.intro ?_ ?_
    · simpa [sub_eq_add_neg] using hdiff_lt_basic
    · exact h2

end LessThan

namespace LessEqThan
/-
template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (x, y + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val <= y.val then 1 else 0)

  soundness := by
    intro i env input (x, y) h_input assumptions h_holds
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]
    have : 2^n < 2^(n+1) := by gcongr; repeat linarith
    have hy : y.val + (1 : F p).val < p := by
      simp only [ZMod.val_one]; linarith
    rw [ZMod.val_add_of_lt hy, ZMod.val_one] at h_holds
    by_cases hy : y.val + 1 = 2^n
    case neg =>
      specialize h_holds (by omega)
      simp_all [Nat.lt_add_one_iff]
    -- TODO the spec of LessThan is not strong enough to handle this case
    sorry

  completeness := by
    intro i env input h_env (x, y) h_input assumptions
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]
    -- TODO impossible to prove
    sorry
end LessEqThan

namespace GreaterThan
/-
template GreaterThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n

  Spec := fun (x, y) output =>
    output = (if x.val > y.val then 1 else 0)

  soundness := by
    simp_all [circuit_norm, LessThan.circuit]

  completeness := by
    simp_all [circuit_norm, LessThan.circuit]
end GreaterThan

namespace GreaterEqThan
/-
template GreaterEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0]+1;
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val >= y.val then 1 else 0)

  soundness := by
    simp only [circuit_norm]
    sorry

  completeness := by
    simp only [circuit_norm]
    sorry
end GreaterEqThan

end Circomlib
