import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean


namespace Circomlib
open Utils.Bits
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

namespace BinSum
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
    for (k=0; k<n; k++) {
        for (j=0; j<ops; j++) {
            lin += in[j][k] * e2;
        }
        e2 = e2 + e2;
    }

    // Calculate output bits
    e2 = 1;
    for (k=0; k<nout; k++) {
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
def main (n ops : ℕ) (inp : BinSumInput n ops (Expression (F p))) := do
  let nout := nbits ((2^n - 1) * ops)

  -- Calculate input linear sum
  let lin ← Circuit.foldlRange n (0 : Expression (F p)) fun lin k => do
    let e2 : Expression (F p) := (2^k.val : F p)
    Circuit.foldlRange ops lin fun lin j => do
      return lin + inp[j][k] * e2

  -- Witness output bits
  let out ← witnessVector nout fun env =>
    fieldToBits nout (lin.eval env)

  -- Calculate output linear sum and constrain bits
  let (lout, _) ← Circuit.foldlRange nout ((0 : Expression (F p)), (1 : Expression (F p))) fun (lout, e2) k => do
    -- Ensure out[k] is binary
    out[k] * (out[k] - (1 : Expression (F p))) === (0 : Expression (F p))
    let lout := lout + out[k] * e2
    return (lout, e2 + e2)

  -- Ensure the sum is correct
  lin === lout

  return out

-- n: number of bits per operand
-- ops: number of operands to sum
def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p) :
    GeneralFormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main n ops input

  localLength _ := nbits ((2^n - 1) * ops)
  localLength_eq := by simp [circuit_norm, main]

  output _ i := varFromOffset (fields (nbits ((2^n - 1) * ops))) i

  output_eq := by
    intros
    simp +arith [circuit_norm, main]

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
    simp only [GeneralFormalCircuit.Soundness]
    intros offset env input_var input h_input_eval h_constraints
    simp only [circuit_norm, main] at h_constraints
    -- Need to prove the spec holds
    constructor
    · -- Prove all outputs are binary
      intro i hi
      -- The constraint says out[i] * (out[i] - 1) = 0, which means IsBool out[i]
      have h_bit_constraint := h_constraints.1 ⟨i, hi⟩
      -- The offset calculation simplifies because ops * 0 = 0
      have h_offset : offset + (if h : n > 0 then n * (if h : ops > 0 then ops * 0 else 0) else 0) + i = offset + i := by
        simp only [mul_zero]
        split_ifs <;> simp
      rw [h_offset] at h_bit_constraint
      simp only [varFromOffset, circuit_norm, eval, fromVars, Vector.getElem_mapRange, size, fields]
      -- Use the characterization of IsBool
      rw [IsBool.iff_mul_sub_one, sub_eq_add_neg]
      exact h_bit_constraint
    · -- Prove the sum property
      -- This requires proving that the sum constraint in the circuit
      -- correctly enforces that the output bits represent the sum of inputs
      sorry

  completeness := by
    simp only [GeneralFormalCircuit.Completeness]
    intro offset env input_var h_witnesses input h_input h_assumptions
    -- We need to prove ConstraintsHold.Completeness
    simp only [circuit_norm, main, Circuit.ConstraintsHold.Completeness]
    -- The constraints are: binary constraints on outputs and sum constraint
    apply And.intro
    · -- Binary constraints: out[i] * (out[i] - 1) = 0 for each output bit
      intro i
      -- The witnesses should satisfy this because they come from fieldToBits
      -- First, simplify the offset
      have h_offset : offset + (if h : n > 0 then n * (if h : ops > 0 then ops * 0 else 0) else 0) + ↑i = offset + ↑i := by
        simp only [mul_zero]
        split_ifs <;> simp
      rw [h_offset]
      simp only [circuit_norm, main, subcircuit] at h_witnesses
      -- Now we need to show that the witnessed value at offset + i is binary
      -- This follows from the fact that witnessVector uses fieldToBits
      -- The key insight is that fieldToBits produces binary values
      -- because toBits produces 0 or 1, which are then cast to field elements
      -- We need to use h_witnesses which tells us about the witness generation
      sorry -- This requires reasoning about witnessVector and fieldToBits
    · -- Sum constraint: lin = lout
      -- The witness generation ensures this by construction
      sorry

end BinSum

end Circomlib
