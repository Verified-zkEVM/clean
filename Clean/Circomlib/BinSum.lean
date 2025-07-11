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
Circuit that computes the linear sum of multiple binary numbers.
Takes n-bit binary numbers and computes their weighted sum.
-/
namespace InputLinearSum

-- Compute the linear sum of input bits weighted by powers of 2
def main (n ops : ℕ) (inp : BinSumInput n ops (Expression (F p))) : Circuit (F p) (Expression (F p)) := do
  -- Calculate input linear sum
  let lin ← Circuit.foldlRange n (0 : Expression (F p)) fun lin k => do
    let e2 : Expression (F p) := (2^k.val : F p)
    Circuit.foldlRange ops lin fun lin j => do
      return lin + inp[j][k] * e2
  return lin

-- Lemma showing that evaluating the main circuit computes the correct sum
lemma main_eval_eq_sum {n ops : ℕ} [hn : NeZero n] (hops : 0 < ops)
    (env : Environment (F p))
    (offset : Var (BinSumInput n ops) (F p))
    (input_val : BinSumInput n ops (F p))
    (h_eval : eval env offset = input_val)
    (input_offset : ℕ) :
    Expression.eval env ((main n ops offset input_offset).1) =
    Fin.foldl ops (fun acc j => acc + fieldFromBits input_val[j]) 0 := by
  -- The main function uses offset[j][k] which evaluates to input_val[j][k]
  -- We need to show the nested sum equals the sum of fieldFromBits

  -- The proof strategy:
  -- 1. Show that the circuit computes Σ_k 2^k * (Σ_j offset[j][k])
  -- 2. Use interchange of summation to get Σ_j (Σ_k 2^k * offset[j][k])
  -- 3. Show that Σ_k 2^k * offset[j][k] = fieldFromBits(input_val[j])

  -- For now, we leave this as a key lemma to prove
  sorry

def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) :
    FormalCircuit (F p) (BinSumInput n ops) field where
  main input := main n ops input

  localLength _ := 0
  localLength_eq := by
    simp only [circuit_norm, main]
    -- Need to show that the conditional expression equals 0
    simp only [mul_zero]
    -- Both branches of the if-then-else evaluate to 0
    split_ifs <;> simp

  output input offset := Circuit.output (main n ops input) offset
  output_eq := by
    intros
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ j k (hj : j < ops) (hk : k < n), IsBool input[j][k]

  Spec input output :=
    -- Output equals the sum of all input bits interpreted as numbers
    output = Fin.foldl ops (fun sum (j : Fin ops) =>
      sum + fieldFromBits input[j]) (0 : F p)

  soundness := by
    intros input h_assumptions offset env h_input_eval h_constraints
    intro h_constraints_hold
    -- InputLinearSum has no internal constraints, just computes the sum
    -- The soundness proof shows that the output equals the weighted sum of inputs

    -- The circuit output is the result of the nested foldl computation
    simp only [ElaboratedCircuit.output, circuit_norm]

    -- We need to show that the output equals the sum of fieldFromBits
    -- The main function computes: sum over k of (2^k * sum over j of inp[j][k])
    -- This is equivalent to: sum over j of (sum over k of (2^k * inp[j][k]))
    -- Which equals: sum over j of fieldFromBits(inp[j])

    -- The circuit has no constraints, so h_constraints_hold is trivial
    -- We just need to show the computation is correct
    simp only [main]

    -- The output is the evaluation of the circuit's output expression
    -- We need to show it equals the sum of fieldFromBits of the inputs

    -- Apply our lemma to show the circuit computes the correct sum
    exact main_eval_eq_sum hops h_assumptions offset env h_input_eval input

  completeness := by
    intros input_var h_uses_local_witnesses input_val h_input_eval h_assumptions
    -- InputLinearSum has no constraints, so it's always satisfiable
    -- The circuit just computes a value, no constraints to satisfy
    simp only [circuit_norm, main]
    -- The constraints are empty (True), so they're trivially satisfied

end InputLinearSum

/-
Circuit that computes the weighted sum of binary values: Σ_i bits[i] * 2^i
Assumes the inputs are binary (0 or 1).
-/
namespace BinaryWeightedSum

-- Compute Σ_i bits[i] * 2^i and verify each bit is binary
def main (n : ℕ) (bits : Vector (Expression (F p)) n) : Circuit (F p) (Expression (F p)) := do
  let (sum, _) ← Circuit.foldlRange n ((0 : Expression (F p)), (1 : Expression (F p))) fun (sum, e2) i => do
    -- Ensure bits[i] is binary
    bits[i] * (bits[i] - (1 : Expression (F p))) === (0 : Expression (F p))
    let sum := sum + bits[i] * e2
    return (sum, e2 + e2)
  return sum

def circuit (n : ℕ) : GeneralFormalCircuit (F p) (fields n) field where
  main input := main n input

  localLength _ := 0
  localLength_eq := by
    simp only [circuit_norm, main]
    split_ifs <;> simp

  output input offset := Circuit.output (main n input) offset
  output_eq := by
    intros
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ i (hi : i < n), IsBool input[i]

  Spec input output :=
    -- All inputs are binary (enforced by constraints)
    (∀ i (hi : i < n), IsBool input[i])
    -- Output equals the weighted sum of bits
    ∧ output = fieldFromBits input

  soundness := by
    simp only [GeneralFormalCircuit.Soundness]
    intros offset env input_var input h_input_eval h_constraints
    -- No constraints, just computation
    -- We need to show the foldl computes fieldFromBits
    sorry

  completeness := by
    sorry

end BinaryWeightedSum

/-
Circuit that decomposes a number into binary representation and verifies each bit.
-/
namespace OutputBitsDecomposition

-- Witness output bits and verify they are binary
def main (nout : ℕ) (lin : Expression (F p)) : Circuit (F p) (Vector (Expression (F p)) nout) := do
  -- Witness output bits
  let out ← witnessVector nout fun env =>
    fieldToBits nout (lin.eval env)

  -- Use BinaryWeightedSum subcircuit to compute the sum and verify bits are binary
  let lout ← BinaryWeightedSum.circuit nout out

  -- Ensure the sum is correct
  lin === lout

  return out

def circuit (nout : ℕ) (hnout : 2^nout < p) :
    FormalCircuit (F p) field (fields nout) where
  main input := main nout input

  localLength _ := nout
  localLength_eq := by
    intro offset
    simp only [circuit_norm, main]
    simp only [BinaryWeightedSum.circuit]
    simp

  output _ i := varFromOffset (fields nout) i
  output_eq := by simp +arith [circuit_norm, main]

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := True

  Spec input output :=
    -- All outputs are binary
    (∀ i (hi : i < nout), IsBool output[i])
    -- Output bits represent the input value
    ∧ fieldFromBits output = input

  soundness := by
    intros input h_assumptions offset env h_input_eval h_constraints
    intro h_constraints_hold
    -- OutputBitsDecomposition enforces:
    -- 1. Each output bit is binary (0 or 1)
    -- 2. The sum of output bits equals the input

    -- Extract the constraints from h_constraints_hold
    simp only [circuit_norm, main, BinaryWeightedSum.circuit, subcircuit_norm, Gadgets.Equality.circuit] at h_constraints_hold

    -- The constraints now come from BinaryWeightedSum subcircuit:
    -- 1. For each i: out[i] * (out[i] - 1) = 0 (binary constraint)
    -- 2. Plus our assertEq: lin = lout (sum constraint)

    constructor
    · -- First: prove all outputs are binary
      intro i hi
      -- BinaryWeightedSum enforces out[i] * (out[i] - 1) = 0 which means IsBool
      -- The output is varFromOffset which maps to the witnessed variables
      simp only [ElaboratedCircuit.output]
      simp only [varFromOffset, eval, fromVars, fromElements, toVars]
      simp only [toElements, size, fields]
      simp only [Vector.getElem_map, Vector.getElem_mapRange]
      -- The constraint tells us the witnessed variables are binary
      have h_binary_all := h_constraints_hold.1.1
      exact h_binary_all i hi

    · -- Second: prove fieldFromBits output = input
      -- BinaryWeightedSum.Spec says: lout = fieldFromBits out
      -- We have the constraint: lin = lout
      -- Therefore: fieldFromBits output = lout = lin = input

      -- First, simplify the output
      simp only [ElaboratedCircuit.output]
      simp only [varFromOffset, eval, fromVars, fromElements, toVars]

      -- From h_constraints_hold, we have:
      -- 1. All bits are binary (h_constraints_hold.1)
      -- 2. BinaryWeightedSum output = fieldFromBits of the bits (h_constraints_hold.2.1)
      -- 3. input = BinaryWeightedSum output (h_constraints_hold.2.2)

      -- Extract the parts of the constraint
      have ⟨h_binary_and_sum, h_eq⟩ := h_constraints_hold
      have ⟨h_binary, h_sum⟩ := h_binary_and_sum

      -- First simplify the goal
      simp only [toElements, size, fields]
      -- Now we need to show: fieldFromBits(...) = env
      -- We have the chain: fieldFromBits(...) = BinaryWeightedSum output = offset = env
      -- Work backwards from the goal
      rw [← h_sum]
      -- Now we need: BinaryWeightedSum output = env
      rw [← h_eq]
      -- Now we need: Expression.eval h_assumptions offset = env
      -- h_input_eval gives us this (after expanding eval)
      simp only [eval, fromVars, fromElements, toVars] at h_input_eval
      -- For field type, this should be the identity
      exact h_input_eval

  completeness := by
    intros witness_offset env lin_var h_witness_extends lin_value h_lin_eval
    -- We can always witness the binary decomposition of the input
    -- The circuit witnesses out = fieldToBits(input)
    -- This satisfies all constraints:
    -- 1. Binary constraints: fieldToBits produces binary values
    -- 2. Sum constraint: fieldFromBits(fieldToBits(x)) = x (when x < 2^nout)
    simp only [circuit_norm, main, BinaryWeightedSum.circuit, subcircuit_norm, Gadgets.Equality.circuit]

    -- The witnessing uses fieldToBits which:
    -- 1. Produces binary values
    -- 2. Has the property fieldFromBits(fieldToBits(x)) = x

    -- This proof requires showing that:
    -- 1. fieldToBits produces binary values (for BinaryWeightedSum constraints)
    -- 2. fieldFromBits(fieldToBits(input)) = input (for the assertEq)
    
    constructor
    · -- First: show the witnessed bits are binary
      intro i hi
      -- The circuit witnesses out[i] = fieldToBits(lin_value)[i]
      -- We need to show this is binary
      -- The key property is that fieldToBits produces values in {0, 1}
      
      -- h_witness_extends tells us that the environment extends the witness vector at offset witness_offset
      -- The witness vector is fieldToBits nout (lin.eval env) from the main function
      have h_witness : env.get (witness_offset + i) = 
                       (fieldToBits nout (Expression.eval env lin_var))[i] := by
        -- h_witness_extends contains ExtendsVector for the witness operation
        simp only [Environment.UsesLocalWitnessesCompleteness] at h_witness_extends
        have ⟨h_extends, _⟩ := h_witness_extends
        simp only [Environment.ExtendsVector] at h_extends
        exact h_extends ⟨i, hi⟩
      
      rw [h_witness]
      -- Now apply the theorem about fieldToBits producing binary values
      have h_binary := fieldToBits_bits (i := i) hi (x := Expression.eval env lin_var)
      cases h_binary with
      | inl h => left; exact h
      | inr h => right; exact h
      
    · -- Second: show input = BinaryWeightedSum output
      -- BinaryWeightedSum computes fieldFromBits of the witnessed bits
      -- The witnessed bits are fieldToBits(input)
      -- So we need: input = fieldFromBits(fieldToBits(input))
      
      -- The BinaryWeightedSum main function evaluates to fieldFromBits of its input vector
      -- Its input vector is Vector.mapRange nout (fun i => var ⟨witness_offset + i⟩)
      -- When evaluated, this gives us the witness values
      
      -- First, let's understand what BinaryWeightedSum.main computes
      -- It computes Σ_i bits[i] * 2^i = fieldFromBits bits
      
      -- The expression we need to prove equal to lin_var is:
      -- BinaryWeightedSum.main nout (Vector.mapRange nout fun i ↦ var { index := witness_offset + i })
      
      -- When evaluated, the var expressions give us the witness values
      have h_witness_vec : Vector.map (Expression.eval env) 
                           (Vector.mapRange nout fun i ↦ var { index := witness_offset + i }) = 
                           fieldToBits nout (Expression.eval env lin_var) := by
        rw [Vector.ext_iff]
        intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange]
        -- Use h_witness_extends to get the witness value
        simp only [Environment.UsesLocalWitnessesCompleteness] at h_witness_extends
        have ⟨h_extends, _⟩ := h_witness_extends
        simp only [Environment.ExtendsVector] at h_extends
        simp only [Expression.eval]
        exact h_extends ⟨i, hi⟩
      
      -- Now we need to prove that the evaluation of lin_var equals the evaluation of BinaryWeightedSum output
      -- The LHS is Expression.eval env lin_var = lin_value
      -- The RHS is the output of BinaryWeightedSum.main applied to the witness vector
      
      -- Let's think about what BinaryWeightedSum.main computes:
      -- It takes a vector of bits and computes Σ_i bits[i] * 2^i
      -- When applied to fieldToBits(lin_value), it should return lin_value
      
      -- First, let's use h_lin_eval to replace the LHS
      have h_lhs : Expression.eval env lin_var = lin_value := h_lin_eval
      rw [h_lhs]
      
      -- Now we need to show that the RHS also equals lin_value
      -- The RHS is the evaluation of BinaryWeightedSum.main on the witness vector
      -- The witness vector evaluates to fieldToBits nout lin_value (by h_witness_vec)
      
      -- To proceed, we need a lemma about what BinaryWeightedSum.main computes
      -- It should compute fieldFromBits of its input vector
      -- For now, let's leave this as a sorry
      sorry

end OutputBitsDecomposition

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
def main (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p)
    (inp : BinSumInput n ops (Expression (F p))) : Circuit (F p) (Vector (Expression (F p)) (nbits ((2^n - 1) * ops))) := do
  let nout := nbits ((2^n - 1) * ops)

  -- Use InputLinearSum subcircuit to calculate the sum
  let lin ← subcircuit (InputLinearSum.circuit n ops hops) inp

  -- Use OutputBitsDecomposition subcircuit to decompose into bits
  let out ← subcircuit (OutputBitsDecomposition.circuit nout hnout) lin

  return out

-- n: number of bits per operand
-- ops: number of operands to sum
def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p) :
    FormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main n ops hops hnout input

  localLength _ := nbits ((2^n - 1) * ops)
  localLength_eq := by
    intros
    simp only [circuit_norm, main, subcircuit]
    -- The localLength of InputLinearSum is 0
    -- The localLength of OutputBitsDecomposition is nout
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit]
    simp only [zero_add]

  output _ i := varFromOffset (fields (nbits ((2^n - 1) * ops))) i

  output_eq := by
    intros input offset
    simp only [circuit_norm, main, subcircuit]
    -- The output of the main circuit is the output of OutputBitsDecomposition
    simp only [OutputBitsDecomposition.circuit]
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
    intros input h_assumptions offset env h_input_eval h_circuit_constraints
    -- Extract what h_circuit_constraints says
    intro h_constraints_hold
    -- h_circuit_constraints contains our assumptions about the input (they are binary)
    -- h_constraints_hold contains the fact that circuit constraints hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main, subcircuit, subcircuit_norm] at h_constraints_hold
    -- Unfold the subcircuit definitions to access their specs
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit] at h_constraints_hold

    -- Now we can see the constraints from both subcircuits
    -- The constraints are:
    -- 1. From InputLinearSum: none (it just computes)
    -- 2. From OutputBitsDecomposition: binary constraints and sum constraint

    -- If the subcircuits were sound, we would have:
    -- - InputLinearSum.Spec: its output equals the sum of inputs
    -- - OutputBitsDecomposition.Spec: outputs are binary and represent the input

    -- Extract the two parts of the constraint
    obtain ⟨h_input_sum, h_output_decomp⟩ := h_constraints_hold

    -- We need to prove the output specification
    constructor
    · -- First: all outputs are binary
      intro i hi
      -- The output is varFromOffset at position offset + input
      simp only [varFromOffset, eval, fromVars, fromElements, toVars, fields, size]
      -- Apply the binary constraint from OutputBitsDecomposition
      have h_binary := (h_output_decomp trivial).1 i hi
      simp only [varFromOffset] at h_binary
      exact h_binary

    · -- Second: the sum property
      -- We know inputs are binary from h_circuit_constraints
      have h_inputs_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval h_assumptions offset)[j][k] := by
        intro j k hj hk
        rw [h_input_eval]
        exact h_circuit_constraints j k hj hk

      -- Apply InputLinearSum spec with binary inputs
      have h_lin_sum := h_input_sum h_inputs_binary

      -- Apply OutputBitsDecomposition spec
      have h_output_sum := (h_output_decomp trivial).2

      -- Chain the equalities
      -- The goal is about ElaboratedCircuit.output which is varFromOffset
      simp only [ElaboratedCircuit.output]
      -- Now we need to connect this with our hypotheses
      -- h_output_sum tells us about fieldFromBits of the output
      have h_output_eq : fieldFromBits (eval h_assumptions (varFromOffset (fields (nbits ((2^n - 1) * ops))) input)) =
                         fieldFromBits (Vector.map (Expression.eval h_assumptions)
                           (varFromOffset (fields (nbits ((2^n - 1) * ops))) (input + 0))) := by
        congr 1
      rw [h_output_eq, h_output_sum, h_lin_sum, h_input_eval]

  completeness := by
    intros input_var h_uses_local_witnesses input_val h_input_eval h_assumptions
    -- We need to show that when inputs are binary, the circuit constraints can be satisfied
    -- The completeness follows from:
    -- 1. InputLinearSum has no constraints, so it's trivially complete
    -- 2. OutputBitsDecomposition witnesses the correct binary decomposition

    -- The circuit constraints come from the subcircuits
    simp only [circuit_norm, main, subcircuit, subcircuit_norm]
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit]

    -- We have implications to handle
    intro h_eq h_binary
    -- Now we need to prove the conjunction
    constructor
    · -- First part: inputs remain binary after evaluation
      intro j k hj hk
      rw [h_eq]
      exact h_binary j k hj hk

    · -- Second part: OutputBitsDecomposition completeness (True)
      trivial

end BinSum

end Circomlib
