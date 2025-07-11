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
Circuit that decomposes a number into binary representation and verifies each bit.
-/
namespace OutputBitsDecomposition

-- Witness output bits and verify they are binary
def main (nout : ℕ) (lin : Expression (F p)) : Circuit (F p) (Vector (Expression (F p)) nout) := do
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

def circuit (nout : ℕ) (hnout : 2^nout < p) :
    FormalCircuit (F p) field (fields nout) where
  main input := main nout input

  localLength _ := nout
  localLength_eq := by
    simp only [circuit_norm, main]
    simp only [mul_zero, add_zero]
    split_ifs <;> simp

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
    
    -- The circuit main function:
    -- 1. Witnesses output bits using fieldToBits
    -- 2. Constrains each bit to be binary: out[k] * (out[k] - 1) = 0
    -- 3. Constrains the sum: lin = Σ_k out[k] * 2^k
    
    constructor
    · -- First: prove all outputs are binary
      intro i hi
      -- The constraint out[i] * (out[i] - 1) = 0 enforces IsBool
      sorry
      
    · -- Second: prove fieldFromBits output = input
      -- This follows from the constraint lin = lout
      sorry

  completeness := by
    intros input_var h_uses_local_witnesses input_val h_input_eval h_assumptions
    -- We can always witness the binary decomposition of the input
    -- The circuit witnesses out = fieldToBits(input)
    -- This satisfies all constraints:
    -- 1. Binary constraints: fieldToBits produces binary values
    -- 2. Sum constraint: fieldFromBits(fieldToBits(x)) = x (when x < 2^nout)
    simp only [circuit_norm, main]
    -- We need to handle the implication
    intro h_eq
    -- The goal has two parts: binary constraints and sum constraint
    constructor
    · -- Binary constraints: out[i] * (out[i] - 1) = 0
      intro i
      -- The witnessing uses fieldToBits which produces binary values
      -- This ensures the constraint is satisfied
      sorry
    · -- Sum constraint: input = Σ_i out[i] * 2^i
      -- This follows from fieldFromBits(fieldToBits(x)) = x
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
