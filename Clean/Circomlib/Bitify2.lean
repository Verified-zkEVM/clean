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
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Expression (F p)) : Circuit sentences (Vector (Expression (F p)) 254) := do
  -- Convert input to 254 bits
  let bits ← Num2Bits.main order 254 input

  -- Check that the bits represent a value less than p
  AliasCheck.circuit order bits

  return bits

set_option linter.constructorNameAsVariable false

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order field (fields 254) where
  main := main order
  localLength _ := 254 + 127 + 1 + 135 + 1 -- Num2Bits + AliasCheck
  localLength_eq _ _ := by simp +arith [circuit_norm, main,
    Num2Bits.main, AliasCheck.circuit]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main,
    Num2Bits.main, AliasCheck.circuit]

  Assumptions _ := True

  Spec _ input bits :=
    bits = fieldToBits 254 input

  soundness := by
    intro i0 env yields checked input_var input h_input assumptions h_holds
    simp only [circuit_norm, main, Num2Bits.main] at h_holds ⊢
    simp_all only [circuit_norm, AliasCheck.circuit,
      Vector.map_mapRange, Vector.map_map, Function.comp_apply]
    simp only [Num2Bits.lc_eq, Fin.forall_iff,
      id_eq, mul_eq_zero, add_neg_eq_zero] at h_holds
    obtain ⟨ h_bits, h_eq, h_alias ⟩ := h_holds
    specialize h_alias h_bits
    rw [← h_eq, fieldToBits, fieldFromBits,
      ZMod.val_natCast, Vector.map_mapRange]
    rw [Nat.mod_eq_of_lt h_alias, toBits_fromBits, Vector.ext_iff]
    simp only [circuit_norm]
    intro i hi
    rw [ZMod.natCast_zmod_val]
    intro i hi; specialize h_bits i hi
    simp only [circuit_norm]
    rcases h_bits with h_bits | h_bits
      <;> simp [h_bits, ZMod.val_one]

  completeness := by
    intro i0 env yields input_var h_env input h_input assumptions
    simp only [circuit_norm, main, Num2Bits.main] at h_env h_input ⊢
    dsimp only [circuit_norm, AliasCheck.circuit] at h_env ⊢
    simp only [h_input, circuit_norm] at h_env ⊢
    simp only [Num2Bits.lc_eq, Fin.forall_iff,
      id_eq, mul_eq_zero, add_neg_eq_zero] at h_env ⊢
    rw [Vector.map_mapRange]
    simp only [Expression.eval]
    have h_bits i (hi : i < 254) : env.get (i0 + i) = 0 ∨ env.get (i0 + i) = 1 := by
      simp [h_env i hi, fieldToBits_bits]
    set bits := Vector.mapRange 254 fun i => env.get (i0 + i)
    have h_eq : bits = fieldToBits 254 input := by
      ext i hi; simp [bits, circuit_norm, h_env i hi]
    have input_lt : input.val < 2^254 := by
      linarith [‹Fact (p < 2^254)›.elim, ZMod.val_lt input]
    use h_bits
    simp_rw [h_eq, fieldFromBits_fieldToBits input_lt,
      fieldToBits, Vector.map_map, val_natCast_toBits,
      fromBits_toBits input_lt, ZMod.val_lt]
    use trivial, h_bits
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
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Vector (Expression (F p)) 254) : Circuit sentences (Expression (F p)) := do
  -- Check that the bits represent a value less than p
  AliasCheck.circuit order input

  -- Convert bits to number
  Bits2Num.main order 254 input

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order (fields 254) field where
  main := main order
  localLength _ := (127 + 1 + 135 + 1) + 1  -- AliasCheck + Bits2Num
  localLength_eq _ _ := by simp +arith [circuit_norm, main,
    Bits2Num.main, AliasCheck.circuit]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main,
    Bits2Num.main, AliasCheck.circuit]

  Assumptions input := ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

  Spec _ input output :=
    output.val = fromBits (input.map ZMod.val)

  soundness := by
    simp only [circuit_norm, main, Bits2Num.main]
    sorry

  completeness := by
    simp only [circuit_norm, main, Bits2Num.main]
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
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (n : ℕ) (input : Expression (F p)) : Circuit sentences (Vector (Expression (F p)) n) := do
  -- Witness the bits of 2^n - input (when n > 0)
  let out ← witnessVector n fun env =>
    fieldToBits n (if n = 0 then 0 else (2^n : F p) - input.eval env)

  -- Constrain each bit to be 0 or 1 and compute linear combination
  let lc1 ← Circuit.foldlRange n 0 fun lc1 i => do
    assertBool order out[i]
    return lc1 + out[i] * (2^i.val : F p)

  -- Check if input is zero
  let isZero_out ← IsZero.circuit order input

  -- Main constraint: lc1 + isZero.out * 2^n === 2^n - in
  lc1 + isZero_out * (2^n : F p) ===[order] (2^n : F p) - input

  return out

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (n : ℕ) (hn : 2^n < p) : FormalCircuit order field (fields n) where
  main := main order n
  localLength _ := n + 2 -- witness + IsZero
  localLength_eq := by simp [circuit_norm, main, IsZero.circuit]
  subcircuitsConsistent := by
    simp +arith only [circuit_norm, main, IsZero.circuit]

  Spec _ input output :=
    output = fieldToBits n (if n = 0 then 0 else 2^n - input.val : F p)

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end Num2BitsNeg

end Circomlib
