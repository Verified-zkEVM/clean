import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean



namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

-- Instance to show that 2 > 0
instance : Fact (0 < 2) := ⟨by norm_num⟩

-- Define a 2D vector type for BinSub inputs
-- Represents 2 operands, each with n bits
-- This is a vector of 2 elements, where each element is a vector of n field elements
@[reducible]
def BinSubInput (n : ℕ) := ProvableVector (fields n) 2

-- Define output type for BinSub
-- Represents n output bits plus 1 aux bit
@[reducible]
def BinSubOutput (n : ℕ) := fields (n + 1)

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/binsub.circom

The BinSub template takes two binary numbers as input and outputs their difference in binary form.
The circuit computes: (in[0] + 2^n) - in[1] = out + aux*2^n
where aux is the borrow bit.
Note that the input bits must be guaranteed to be binary (0 or 1) by the caller.
The circuit ensures that:
1. All output bits are binary (0 or 1)
2. The aux bit is binary (0 or 1)
3. The equation (in[0] + 2^n) - in[1] = out + aux*2^n holds
-/

namespace BinSub
/-
template BinSub(n) {
    signal input in[2][n];
    signal output out[n];

    signal aux;

    var lin = 2**n;
    var lout = 0;

    var i;

    for (i=0; i<n; i++) {
        lin = lin + in[0][i]*(2**i);
        lin = lin - in[1][i]*(2**i);
    }

    for (i=0; i<n; i++) {
        out[i] <-- (lin >> i) & 1;

        // Ensure out is binary
        out[i] * (out[i] - 1) === 0;

        lout = lout + out[i]*(2**i);
    }

    aux <-- (lin >> n) & 1;
    aux*(aux-1) === 0;
    lout = lout + aux*(2**n);

    // Ensure the sum
    lin === lout;
}
-/
-- n: number of bits per operand
def main (n : ℕ) [NeZero n] (inp : BinSubInput n (Expression (F p))) := do
  -- Calculate input linear sum: lin = 2^n + in[0] - in[1]
  let lin ← Circuit.foldlRange n ((2^n : F p) : Expression (F p)) fun lin i => do
    let e2 : Expression (F p) := (2^i.val : F p)
    return lin + inp[0][i] * e2 - inp[1][i] * e2
  
  -- Witness output bits
  let out ← witnessVector n fun env => 
    fieldToBits n (lin.eval env)
  
  -- Witness aux bit
  let aux ← witness fun env =>
    let lin_val := lin.eval env
    -- Extract the nth bit (borrow bit)
    if (lin_val.val / (2^n)) % 2 = 1 then (1 : F p) else (0 : F p)
  
  -- Calculate output linear sum and constrain bits
  let (lout, _) ← Circuit.foldlRange n ((0 : Expression (F p)), (1 : Expression (F p))) fun (lout, e2) i => do
    -- Ensure out[i] is binary
    out[i] * (out[i] - (1 : Expression (F p))) === (0 : Expression (F p))
    let lout := lout + out[i] * e2
    return (lout, e2 + e2)
  
  -- Ensure aux is binary
  aux * (aux - (1 : Expression (F p))) === (0 : Expression (F p))
  
  -- Add aux contribution to lout
  let lout := lout + aux * ((2^n : F p) : Expression (F p))
  
  -- Ensure the equation holds
  lin === lout
  
  -- Create the final output vector with n bits for out and 1 bit for aux
  let result ← witnessVector (n + 1) fun env => 
    Vector.ofFn fun i : Fin (n + 1) =>
      if h : i.val < n then
        have hi : i.val < n := h
        out[i.val]'hi |>.eval env
      else
        aux.eval env
      
  return result

-- n: number of bits per operand
def circuit (n : ℕ) [hn : NeZero n] [NonEmptyProvableType (fields n)] (hnout : 2^(n+1) < p) : 
    GeneralFormalCircuit (F p) (BinSubInput n) (BinSubOutput n) where
  main input := main n input
  
  localLength _ := n + 1
  localLength_eq := by sorry
  
  output _ i := varFromOffset (BinSubOutput n) i
  
  output_eq := by sorry
  
  subcircuitsConsistent := by sorry
  
  Assumptions input := 
    -- All inputs are binary
    ∀ j i (hj : j < 2) (hi : i < n), IsBool input[j][i]
  
  Spec input output := 
    -- All inputs are binary
    (∀ j i (hj : j < 2) (hi : i < n), IsBool input[j][i])
    -- All output bits are binary (first n bits)
    ∧ (∀ i (hi : i < n), IsBool output[i])
    -- aux bit is binary (the n-th bit)
    ∧ IsBool output[n]
    -- The equation (in[0] + 2^n) - in[1] = out + aux*2^n holds
    ∧ let out_bits : Vector (F p) n := ⟨Array.mk (List.ofFn fun i : Fin n => output[i.val]), by simp⟩
      fieldFromBits input[0] + (2^n : F p) - fieldFromBits input[1] = 
        fieldFromBits out_bits + output[n] * (2^n : F p)
  
  soundness := by
    sorry
  
  completeness := by
    sorry

end BinSub

end Circomlib