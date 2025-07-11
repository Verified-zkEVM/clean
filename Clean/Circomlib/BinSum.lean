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
    sorry
  
  completeness := by
    sorry

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
    sorry
  
  completeness := by
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
    GeneralFormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
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
    simp only [GeneralFormalCircuit.Soundness]
    intros offset env input_var input h_input_eval h_constraints
    simp only [circuit_norm, main] at h_constraints
    -- The modular structure means we can use the subcircuits' soundness
    -- But for now, let's use the original proof approach
    sorry

  completeness := by
    -- The modular structure means we can leverage the subcircuits' completeness
    sorry

end BinSum

end Circomlib
