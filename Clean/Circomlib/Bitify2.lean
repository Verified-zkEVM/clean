import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Clean.Circomlib.AliasCheck
import Clean.Circomlib.Comparators

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/bitify.circom

This file contains the templates from bitify.circom that couldn't be included in Bitify.lean
due to cyclic import dependencies with AliasCheck.
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace Num2Bits_strict
/-
template Num2Bits_strict() {
    signal input in;
    signal output out[254];

    component aliasCheck = AliasCheck();
    component n2b = Num2Bits(254);
    in ==> n2b.in;

    for (var i=0; i<254; i++) {
        n2b.out[i] ==> out[i];
        n2b.out[i] ==> aliasCheck.in[i];
    }
}
-/
def main (input : Expression (F p)) := do
  -- Convert input to 254 bits
  -- TODO the requirement 2^254 < p is too strong here, need more precise version of Num2Bits
  let bits ← Num2Bits.circuit 254 sorry input

  -- Check that the bits represent a value less than p
  AliasCheck.circuit bits

  return bits

def circuit : FormalCircuit (F p) field (fields 254) where
  main
  localLength _ := 254 + 127 + 1 + 135 + 1 -- Num2Bits + AliasCheck

  Spec input output := output = fieldToBits 254 input

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Num2Bits_strict

namespace Bits2Num_strict
/-
template Bits2Num_strict() {
    signal input in[254];
    signal output out;

    component aliasCheck = AliasCheck();
    component b2n = Bits2Num(254);

    for (var i=0; i<254; i++) {
        in[i] ==> b2n.in[i];
        in[i] ==> aliasCheck.in[i];
    }

    b2n.out ==> out;
}
-/
def main (input : Vector (Expression (F p)) 254) := do
  -- Check that the bits represent a value less than p
  AliasCheck.circuit input

  -- Convert bits to number
  let out ← Bits2Num.circuit 254 sorry input

  return out

def circuit : FormalCircuit (F p) (fields 254) field where
  main
  localLength _ := (127 + 1 + 135 + 1) + 1  -- AliasCheck + Bits2Num

  Assumptions input := ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

  Spec input output :=
    output.val = fromBits (input.map ZMod.val)

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Bits2Num_strict

namespace Num2BitsNeg
/-
template Num2BitsNeg(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    component isZero;

    isZero = IsZero();

    var neg = n == 0 ? 0 : 2**n - in;

    for (var i = 0; i < n; i++) {
        out[i] <-- (neg >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * 2**i;
    }

    in ==> isZero.in;

    lc1 + isZero.out * 2**n === 2**n - in;
}
-/
def main (n : ℕ) (input : Expression (F p)) := do
  -- Witness the bits of 2^n - input (when n > 0)
  let out ← witnessVector n fun env =>
    fieldToBits n (if n = 0 then 0 else (2^n : F p) - input.eval env)

  -- Constrain each bit to be 0 or 1 and compute linear combination
  let lc1 ← Circuit.foldlRange n 0 fun lc1 i => do
    out[i] * (out[i] - 1) === 0
    return lc1 + out[i] * (2^i.val : F p)

  -- Check if input is zero
  let isZero_out ← IsZero.circuit input

  -- Main constraint: lc1 + isZero.out * 2^n === 2^n - in
  lc1 + isZero_out * (2^n : F p) === (2^n : F p) - input

  return out

def circuit (n : ℕ) (hn : 2^n < p) : FormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := 2 + n + n  -- IsZero + witness + foldlRange constraints
  localLength_eq := by simp [circuit_norm, main, IsZero.circuit]; sorry
  subcircuitsConsistent := sorry

  Assumptions input := True

  Spec input output :=
    output = fieldToBits n (if n = 0 then 0 else 2^n - input.val : F p)

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Num2BitsNeg

end Circomlib
