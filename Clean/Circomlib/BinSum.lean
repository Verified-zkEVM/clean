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
lemma sum_bound_of_binary_inputs {n ops : ℕ}
  (hnout : 2^(nbits ((2^n - 1) * ops)) < p) (inputs : BinSumInput n ops (F p))
  (h_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool inputs[j][k]) :
    (Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0).val < 2^(nbits ((2^n - 1) * ops)) := by
  -- Each input[j] is n-bit binary, so fieldFromBits inputs[j] ≤ 2^n - 1
  -- The sum of ops such numbers is at most ops * (2^n - 1)
  -- We need to show this is < 2^(nbits(ops * (2^n - 1)))

  -- First, bound each individual fieldFromBits
  have h_individual_bound : ∀ j (hj : j < ops), (fieldFromBits inputs[j]).val ≤ 2^n - 1 := by
    intro j hj
    -- Use the fieldFromBits bound
    have h_lt := fieldFromBits_lt inputs[j] (h_binary j · hj)
    -- We have fieldFromBits inputs[j] < 2^n, so its value is ≤ 2^n - 1
    omega

  have h_log_bound (n : ℕ) : ops * (2 ^ n - 1) < 2 ^ nbits ((2 ^ n - 1) * ops) := by
    simp only [nbits]
    rw [mul_comm]
    split_ifs with h <;> simp [h, Nat.lt_log2_self]

  -- The sum is bounded by ops * (2^n - 1)
  have h_sum_bound : (Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0).val ≤ ops * (2^n - 1) := by
    -- Apply our general lemma about foldl sum bounds
    apply Fin.foldl_sum_val_bound (fun j => fieldFromBits inputs[j]) (2^n - 1)
    · -- Prove each element is bounded
      intro j
      exact h_individual_bound j j.isLt
    · -- Prove no overflow: ops * (2^n - 1) < p
      -- This follows from hnout and the definition of nbits
      apply Nat.lt_trans (h_log_bound _) hnout

  -- Apply the bound we just proved
  apply Nat.lt_of_le_of_lt h_sum_bound (h_log_bound n)
namespace BinSum

-- Compute the linear sum of input bits weighted by powers of 2
def inputLinearSum (n ops : ℕ) (inp : BinSumInput n ops (Expression (F p))) : Expression (F p) :=
  -- Calculate input linear sum
  Fin.foldl n (fun lin k =>
    Fin.foldl ops (fun lin j => lin + inp[j][k] * (2^k.val : F p)) lin) 0

-- Lemma showing that evaluating the main circuit computes the correct sum
omit [Fact (p > 2)] in
lemma inputLinearSum_eval_eq_sum {n ops : ℕ} [hn : NeZero n]
  (env : Environment (F p))
  (input : Var (BinSumInput n ops) (F p))
  (input_val : BinSumInput n ops (F p))
  (h_eval : eval env input = input_val) :
    Expression.eval env (inputLinearSum n ops input) =
    Fin.foldl ops (fun acc j => acc + fieldFromBits input_val[j.val]) 0 := by
  -- The main function uses input[j][k] which evaluates to input_val[j][k]
  -- We need to show the nested sum equals the sum of fieldFromBits

  -- Step 1: The circuit evaluation computes the nested sum Σ_k 2^k * (Σ_j offset[j][k])
  simp only [inputLinearSum, circuit_norm, eval_foldl, Fin.foldl_factor_const]

  -- Step 2: Replace Expression.eval env input[j][k] with input_val[j][k]
  simp only [ProvableType.getElem_eval_fields, getElem_eval_vector, h_eval]

  rw [Fin.sum_interchange]
  simp only [fieldFromBits_as_sum]

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
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (n ops : ℕ)
    (inp : BinSumInput n ops (Expression (F p))) : Circuit sentences (Vector (Expression (F p)) (nbits ((2^n - 1) * ops))) := do
  let nout := nbits ((2^n - 1) * ops)

  -- Use InputLinearSum subcircuit to calculate the sum
  let lin := inputLinearSum n ops inp

  -- Use Num2Bits subcircuit to decompose into bits
  let out ← Num2Bits.arbitraryBitLengthCircuit order nout lin

  return out

-- n: number of bits per operand
-- ops: number of operands to sum
def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (n ops : ℕ) [hn : NeZero n] (hnout : 2^(nbits ((2^n - 1) * ops)) < p) :
    FormalCircuit (F p) sentences order (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main order n ops input

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

  Spec _ input output :=
    let nout := nbits ((2^n - 1) * ops)
    -- All outputs are binary
    (∀ i (hi : i < nout), IsBool output[i])
    -- Sum of inputs equals the value represented by output bits
    ∧ fieldFromBits output =
        Fin.foldl ops (fun sum (j : Fin ops) =>
          sum + fieldFromBits input[j]) (0 : F p)

  soundness := by
    intros offset env yields checked input_var input h_input_eval h_assumptions h_constraints_hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main, subcircuit,
      Num2Bits.arbitraryBitLengthCircuit] at *

    -- Extract the two parts of the constraint
    obtain ⟨_, h_output_binary, h_output_sum ⟩ := h_constraints_hold
    use h_output_binary
    rw [h_output_sum]

    -- Apply inputLinearSum lemma
    rw [inputLinearSum_eval_eq_sum _ _ _ h_input_eval]

  completeness := by
    intros witness_offset env yields inputs_var h_witness_extends inputs h_inputs_eval h_inputs_binary
    simp only [circuit_norm, main, subcircuit, Num2Bits.arbitraryBitLengthCircuit]
    convert sum_bound_of_binary_inputs hnout inputs h_inputs_binary
    exact inputLinearSum_eval_eq_sum _ _ _ h_inputs_eval

  spec_monotonic := by
    intros checked₁ checked₂ input output _ h; exact h

end BinSum

end Circomlib
