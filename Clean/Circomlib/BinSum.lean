import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

-- Define a 2D vector type for BinSum inputs
-- Represents ops operands, each with n bits
-- This is a vector of ops elements, where each element is a vector of n field elements
@[reducible]
def BinSumInput (n ops : ℕ) := ProvableVector (fields n) ops

-- Instance for NonEmptyProvableType for fields when n > 0
instance {n : ℕ} [hn : Fact (0 < n)] : NonEmptyProvableType (fields n) where
  size := n
  toElements := id
  fromElements := id
  nonempty := hn.out

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/binsum.circom

The BinSum template takes multiple binary numbers as input and outputs their sum in binary form.
It ensures that:
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
def circuit (n ops : ℕ) [hn : Fact (0 < n)] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p) : 
  GeneralFormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main n ops input
  
  localLength _ := nbits ((2^n - 1) * ops)
  localLength_eq := by simp [circuit_norm, main]
  
  output _ i := varFromOffset (fields (nbits ((2^n - 1) * ops))) i
  
  output_eq := by 
    intros
    simp only [main, Circuit.output]
    sorry  -- The proof that output is correct
  
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  
  Assumptions input := 
    -- All inputs are binary
    ∀ j k (hj : j < ops) (hk : k < n), input[j][k] = 0 ∨ input[j][k] = 1
  
  Spec input output := 
    let nout := nbits ((2^n - 1) * ops)
    -- All inputs are binary
    (∀ j k (hj : j < ops) (hk : k < n), input[j][k] = 0 ∨ input[j][k] = 1)
    -- All outputs are binary
    ∧ (∀ i (hi : i < nout), output[i] = 0 ∨ output[i] = 1)
    -- Sum of inputs equals the value represented by output bits
    ∧ fieldFromBits output = 
        Fin.foldl n (fun sum (k : Fin n) => 
          sum + Fin.foldl ops (fun sum' (j : Fin ops) => 
            sum' + input[j][k] * (2^k.val : F p)) (0 : F p)) (0 : F p)
  
  soundness := by
    sorry
  
  completeness := by
    sorry

end BinSum

end Circomlib