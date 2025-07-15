import Clean.Circuit
import Clean.Circuit.Expression
import Clean.Utils.Bits
import Clean.Utils.Fin
import Clean.Utils.Vector
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Circomlib.Bitify

namespace Circomlib
open Utils.Bits Expression
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

-- Define a 2D vector type for BinSum inputs
-- Represents ops operands, each with n bits
-- This is a vector of ops elements, where each element is a vector of n field elements
@[reducible]
def BinSumInput (n ops : ℕ) := ProvableVector (fields n) ops

-- Instance for NonEmptyProvableType for fields when n > 0
instance {n : ℕ} [hn : NeZero n] : NonEmptyProvableType (fields n) where
  nonempty := Nat.pos_of_ne_zero hn.out

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/binsum.circom

The BinSum template takes multiple binary numbers as input and outputs their sum in binary form.
Note that the input bits must be guaranteed to be binary (0 or 1) by the caller.
The circuit ensures that:
1. All output bits are binary (0 or 1)
2. The sum of inputs equals the sum represented by output bits
-/

def nbits (a : ℕ) : ℕ :=
  if a = 0 then 1 else Nat.log2 a + 1

-- Lemma: The sum of ops n-bit numbers fits in nbits((2^n - 1) * ops) bits
omit [Fact (p > 2)] in
lemma sum_bound_of_binary_inputs {n ops : ℕ} [hn : NeZero n] (hops : 0 < ops)
    (hnout : 2^(nbits ((2^n - 1) * ops)) < p)
    (inputs : BinSumInput n ops (F p))
    (h_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool inputs[j][k])
    (h_sum : F p)
    (h_sum_eq : h_sum = Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0) :
    h_sum.val < 2^(nbits ((2^n - 1) * ops)) := by
  -- Each input[j] is n-bit binary, so fieldFromBits inputs[j] ≤ 2^n - 1
  -- The sum of ops such numbers is at most ops * (2^n - 1)
  -- We need to show this is < 2^(nbits(ops * (2^n - 1)))

  -- First, bound each individual fieldFromBits
  have h_individual_bound : ∀ j (hj : j < ops), (fieldFromBits inputs[j]).val ≤ 2^n - 1 := by
    intro j hj
    -- Apply the bound theorem for binary inputs
    have h_binary_j : ∀ k (hk : k < n), IsBool inputs[j][k] := fun k hk => h_binary j k hj hk
    have h_binary_alt : ∀ k (hk : k < n), inputs[j][k] = 0 ∨ inputs[j][k] = 1 := by
      intro k hk
      cases h_binary_j k hk with
      | inl h => left; exact h
      | inr h => right; exact h
    -- Use the fieldFromBits bound
    have h_lt := fieldFromBits_lt inputs[j] h_binary_alt
    -- We have fieldFromBits inputs[j] < 2^n, so its value is ≤ 2^n - 1
    omega

  -- Now bound the sum using h_sum_eq
  rw [h_sum_eq]
  -- The sum is bounded by ops * (2^n - 1)
  have h_sum_bound : (Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0).val ≤ ops * (2^n - 1) := by
    -- Apply our general lemma about foldl sum bounds
    apply Fin.foldl_sum_val_bound (fun j => fieldFromBits inputs[j]) (2^n - 1)
    · -- Prove each element is bounded
      intro j
      exact h_individual_bound j j.isLt
    · -- Prove no overflow: ops * (2^n - 1) < p
      -- This follows from hnout and the definition of nbits
      rw [mul_comm]
      apply Nat.lt_trans _ hnout
      simp only [nbits]
      split_ifs with h
      · -- Case (2^n - 1) * ops = 0, but this contradicts our assumptions
        have pos_prod : 0 < (2^n - 1) * ops := by
          apply Nat.mul_pos
          · have : 1 < 2^n := by
              apply Nat.one_lt_pow
              · exact NeZero.ne n
              · norm_num
            omega
          · exact hops
        omega
      · -- Case (2^n - 1) * ops ≠ 0
        exact Nat.lt_log2_self

  -- Apply the bound we just proved
  apply Nat.lt_of_le_of_lt h_sum_bound
  -- We need to apply the nbits property to (2^n - 1) * ops
  rw [mul_comm]
  -- The goal is (2^n - 1) * ops < 2^(nbits ((2^n - 1) * ops))
  -- This follows from the definition of nbits
  simp only [nbits]
  split_ifs with h
  · -- Case (2^n - 1) * ops = 0, contradicts our assumptions
    have pos_prod : 0 < (2^n - 1) * ops := by
      apply Nat.mul_pos
      · have : 1 < 2^n := by
          apply Nat.one_lt_pow
          · exact NeZero.ne n
          · norm_num
        omega
      · exact hops
    omega
  · -- Case (2^n - 1) * ops ≠ 0
    exact Nat.lt_log2_self
namespace BinSum

/-
Circuit that computes the linear sum of multiple binary numbers.
Takes n-bit binary numbers and computes their weighted sum.
-/
namespace InputLinearSum

-- Compute the linear sum of input bits weighted by powers of 2
def main (n ops : ℕ) (inp : BinSumInput n ops (Expression (F p))) : Expression (F p) :=
  -- Calculate input linear sum
  Fin.foldl n (fun lin k =>
    Fin.foldl ops (fun lin j => lin + inp[j][k] * (2^k.val : F p)) lin) 0

-- Lemma 1: The circuit evaluation computes the nested sum Σ_k 2^k * (Σ_j offset[j][k])
omit [Fact (p > 2)] in
lemma eval_nested_sum {n ops : ℕ}
    (env : Environment (F p))
    (offset : Var (BinSumInput n ops) (F p)) :
    Expression.eval env (main n ops offset) =
    Fin.foldl n (fun acc k => acc + (2^k.val : F p) *
      Fin.foldl ops (fun acc' j => acc' + Expression.eval env offset[j][k]) 0) 0 := by
  -- The main function uses nested Fin.foldl
  simp only [main, circuit_norm, eval_foldl]
  congr 1
  ext acc k
  have h := Fin.foldl_factor_const (fun i => Expression.eval env offset[↑i][↑k]) (2 ^ k.val) acc
  -- The lemma gives us exactly what we need after recognizing that ↑k = k.val
  convert h

-- Lemma showing that evaluating the main circuit computes the correct sum
omit [Fact (p > 2)] in
lemma main_eval_eq_sum {n ops : ℕ} [hn : NeZero n]
    (env : Environment (F p))
    (input : Var (BinSumInput n ops) (F p))
    (input_val : BinSumInput n ops (F p))
    (h_eval : eval env input = input_val) :
    Expression.eval env (main n ops input) =
    Fin.foldl ops (fun acc j => acc + fieldFromBits input_val[j]) 0 := by
  -- The main function uses input[j][k] which evaluates to input_val[j][k]
  -- We need to show the nested sum equals the sum of fieldFromBits

  -- Step 1: Apply eval_nested_sum to show how the circuit evaluates
  rw [eval_nested_sum env input]

  -- Step 2: Replace Expression.eval env input[j][k] with input_val[j][k]
  simp only [Fin.getElem_fin, ProvableType.getElem_eval_fields, getElem_eval_vector, h_eval]

  rw [Fin.sum_interchange]
  simp only [fieldFromBits_as_sum]
end InputLinearSum

/-
template BinSum(n, ops) {
    var nout = nbits((2**n - 1)*ops);
    signal input in[ops][n];
    signal output out[nout];

    var lin = 0;
    var lout = 0;

    var k;
    var j;
    var e2;

    // Calculate input linear sum
    e2 = 1;
    for (k=0; k < n; k++) {
        for (j=0; j < ops; j++) {
            lin += in[j][k] * e2;
        }
        e2 = e2 + e2;
    }

    // Calculate output bits
    e2 = 1;
    for (k=0; k < nout; k++) {
        out[k] <-- (lin >> k) & 1;

        // Ensure out is binary
        out[k] * (out[k] - 1) === 0;

        lout += out[k] * e2;

        e2 = e2+e2;
    }

    // Ensure the sum is correct
    lin === lout;
}
-/
-- n: number of bits per operand
-- ops: number of operands to sum
def main (n ops : ℕ)
    (inp : BinSumInput n ops (Expression (F p))) : Circuit (F p) (Vector (Expression (F p)) (nbits ((2^n - 1) * ops))) := do
  let nout := nbits ((2^n - 1) * ops)

  -- Use InputLinearSum subcircuit to calculate the sum
  let lin := InputLinearSum.main n ops inp

  -- Use Num2Bits subcircuit to decompose into bits
  let out ← Num2Bits.arbitraryBitLengthCircuit nout lin

  return out

-- n: number of bits per operand
-- ops: number of operands to sum
def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p) :
    FormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main n ops input

  localLength _ := nbits ((2^n - 1) * ops)
  localLength_eq := by
    intros
    simp only [circuit_norm, main, Num2Bits.arbitraryBitLengthCircuit]

  output _ i := varFromOffset (fields (nbits ((2^n - 1) * ops))) i

  output_eq := by
    intros input offset
    simp only [circuit_norm, main, subcircuit]
    -- The output of the main circuit is the output of Num2Bits
    simp only [Num2Bits.arbitraryBitLengthCircuit]
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ j k (hj : j < ops) (hk : k < n), IsBool input[j][k]

  Spec input output :=
    let nout := nbits ((2^n - 1) * ops)
    -- All outputs are binary
    (∀ i (hi : i < nout), IsBool output[i])
    -- Sum of inputs equals the value represented by output bits
    ∧ fieldFromBits output =
        Fin.foldl ops (fun sum (j : Fin ops) =>
          sum + fieldFromBits input[j]) (0 : F p)

  soundness := by
    intros offset env input_var input h_input_eval h_assumptions h_constraints_hold
    -- h_circuit_constraints contains our assumptions about the input (they are binary)
    -- h_constraints_hold contains the fact that circuit constraints hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main, subcircuit, subcircuit_norm] at h_constraints_hold
    -- Unfold the subcircuit definitions to access their specs
    simp only [Num2Bits.arbitraryBitLengthCircuit] at h_constraints_hold

    -- Now we can see the constraints from both subcircuits
    -- The constraints are:
    -- 1. From InputLinearSum: none (it just computes)
    -- 2. From Num2Bits: binary constraints and sum constraint

    -- If the subcircuits were sound, we would have:
    -- - InputLinearSum.Spec: its output equals the sum of inputs
    -- - Num2Bits.Spec: outputs are binary and represent the input

    -- Extract the two parts of the constraint
    obtain ⟨h_sum_bound, h_output_decomp⟩ := h_constraints_hold

    -- We need to prove the output specification
    constructor
    · -- First: all outputs are binary
      intro i hi
      -- The output is varFromOffset at position offset + input
      simp only [varFromOffset, ProvableType.eval, fromVars, fromElements, toVars, fields, size]
      -- Apply the binary constraint from Num2Bits
      have h_binary := h_output_decomp.1 i hi
      simp only [varFromOffset] at h_binary
      exact h_binary

    · -- Second: the sum property
      -- We know inputs are binary from h_circuit_constraints
      have h_inputs_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval env input_var)[j][k] := by
        intro j k hj hk
        rw [h_input_eval]
        exact h_assumptions j k hj hk

      -- Apply InputLinearSum spec with binary inputs
      have h_lin_sum := InputLinearSum.main_eval_eq_sum env input_var input h_input_eval

      -- Apply Num2Bits spec
      have h_output_sum := h_output_decomp.2

      -- Chain the equalities
      -- The goal is about ElaboratedCircuit.output which is varFromOffset
      simp only [ElaboratedCircuit.output]
      -- Now we need to connect this with our hypotheses
      -- h_output_sum tells us about fieldFromBits of the output
      have h_output_eq : fieldFromBits (eval env (varFromOffset (fields (nbits ((2^n - 1) * ops))) offset)) =
                         fieldFromBits (Vector.map (Expression.eval env)
                           (varFromOffset (fields (nbits ((2^n - 1) * ops))) offset)) := by
        congr 1
      rw [h_output_eq, h_output_sum, h_lin_sum]

  completeness := by
    intros witness_offset env inputs_var h_witness_extends inputs h_inputs_eval h_inputs_binary
    simp only [circuit_norm, main, subcircuit, subcircuit_norm, Num2Bits.arbitraryBitLengthCircuit]
    apply sum_bound_of_binary_inputs hops hnout inputs h_inputs_binary
    exact InputLinearSum.main_eval_eq_sum _ _ _ h_inputs_eval

end BinSum

end Circomlib
