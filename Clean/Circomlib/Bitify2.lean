import Clean.Circuit
import Clean.Utils.Bits
import Clean.Utils.Fin
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
  let bits ← Num2Bits.main 254 input

  -- Check that the bits represent a value less than p
  AliasCheck.circuit bits

  return bits

set_option linter.constructorNameAsVariable false

def circuit : FormalCircuit (F p) field (fields 254) where
  main
  localLength _ := 254 + 127 + 1 + 135 + 1 -- Num2Bits + AliasCheck
  localLength_eq := by simp +arith [circuit_norm, main,
    Num2Bits.main, AliasCheck.circuit]
  localAdds_eq input env offset := by
    have h : (main input |>.operations offset).collectAdds env = 0 := by
      simp only [main, Num2Bits.main, circuit_norm, Operations.collectAdds]
      simp only [List.append_nil]
      apply Circuit.collectAdds_foldlRange'
      intro (lc1, e2) i k
      simp only [circuit_norm, Operations.collectAdds, List.append_nil]
    simp only [h, InteractionDelta.toFinsupp_zero]
  subcircuitsConsistent := by simp +arith [circuit_norm, main,
    Num2Bits.main, AliasCheck.circuit]

  Spec input bits :=
    bits = fieldToBits 254 input

  soundness := by
    intro i0 env input_var input h_input assumptions h_holds
    simp only [circuit_norm, main, Num2Bits.main] at h_holds ⊢
    simp_all only [circuit_norm, AliasCheck.circuit,
      Vector.map_mapRange]
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
    intro i0 env input_var h_env input h_input assumptions
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
def main (input : Vector (Expression (F p)) 254) := do
  -- Check that the bits represent a value less than p
  AliasCheck.circuit input

  -- Convert bits to number
  Bits2Num.main 254 input

set_option linter.constructorNameAsVariable false

def circuit : GeneralFormalCircuit (F p) (fields 254) field where
  main
  localLength _ := (127 + 1 + 135 + 1) + 1  -- AliasCheck + Bits2Num
  localLength_eq := by simp +arith [circuit_norm, main,
    Bits2Num.main, AliasCheck.circuit]
  localAdds_eq _ _ _ := by
    simp only [main, circuit_norm, Operations.collectAdds, Bits2Num.main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main,
    Bits2Num.main, AliasCheck.circuit]

  Assumptions input _ := (∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1) ∧ fromBits (input.map ZMod.val) < p

  Spec input output _ :=
    (∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1) → output.val = fromBits (input.map ZMod.val)

  soundness := by
    intro i0 env input_var input h_input assumptions output h_binary
    simp only [ElaboratedCircuit.main, main] at assumptions output ⊢
    simp only [circuit_norm, Bits2Num.main, AliasCheck.circuit] at h_input assumptions output ⊢
    have : (∀ (i : ℕ) (x : i < 254), Expression.eval env input_var[i] = input[i]) := by
      intro i hi
      rw [← h_input]
      simp only [Vector.getElem_map]
    have : (∀ (i : ℕ) (x : i < 254), Expression.eval env input_var[i] = 0 ∨ Expression.eval env input_var[i] = 1) := by
      intro i hi
      rw [this]
      apply h_binary
    simp_all only [implies_true, forall_const]
    obtain ⟨ h_bits, h_eq ⟩ := assumptions
    rw [← ZMod.val_natCast_of_lt h_bits]
    rw [← Vector.mapFinRange_eq_map]
    rw [← fieldFromBits_eq_mapFinRange_cast]
    conv =>
          rhs
          congr
          congr
          congr
          ext i
          rw [← h_input]
          simp only [Fin.getElem_fin, Vector.getElem_map]
          rw [← Fin.getElem_fin]
    rw [← Bits2Num.lc_eq]
    simp only [output, circuit_norm, main, AliasCheck.circuit, Bits2Num.main]
    rw [h_eq]

  completeness := by
    simp only [circuit_norm, main]
    intro i0 env input_var h_env input h_input assumptions
    simp only [circuit_norm, Bits2Num.main] at h_env h_input ⊢
    simp only [h_input, circuit_norm] at h_env ⊢
    obtain ⟨assumption₁, assumption₂⟩ := assumptions
    simp only [circuit_norm, AliasCheck.circuit, assumption₁, assumption₂] at ⊢
    rw [← h_env]
    rfl
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
    assertBool out[i]
    return lc1 + out[i] * (2^i.val : F p)

  -- Check if input is zero
  let isZero_out ← IsZero.circuit input

  -- Main constraint: lc1 + isZero.out * 2^n === 2^n - in
  lc1 + isZero_out * (2^n : F p) === (2^n : F p) - input

  return out

def circuit (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := n + 2 -- witness + IsZero
  localLength_eq := by simp [circuit_norm, main, IsZero.circuit]
  localAdds_eq input env offset := by
    have h : (main n input |>.operations offset).collectAdds env = 0 := by
      simp only [main, circuit_norm, Operations.collectAdds]
      simp only [List.append_nil]
      apply Circuit.collectAdds_foldlRange'
      intro lc1 i k
      simp only [circuit_norm, Operations.collectAdds, List.append_nil]
    simp only [h, InteractionDelta.toFinsupp_zero]
  subcircuitsConsistent := by
    simp +arith only [circuit_norm, main, IsZero.circuit]

  Assumptions input _ := input.val < 2^n

  Spec input output _ :=
    output = fieldToBits n (if n = 0 then 0 else 2^n - input.val : F p)

  soundness := by
    intro i0 env input_var input h_input h_holds
    simp only [circuit_norm, main, IsZero.circuit, IsZero.main] at h_holds ⊢
    obtain ⟨ h_bits, h_iszero, h_eq ⟩ := h_holds

    by_cases h_n : n = 0
    · rw [h_n] at h_eq h_iszero ⊢
      simp_all only [Nat.reducePow, gt_iff_lt, pow_zero, id_eq, add_zero, lt_self_iff_false,
        ↓reduceDIte, Fin.foldl_zero, mul_one, ↓reduceIte]
      unfold Vector.mapRange
      simp only [Vector.map_mk, List.map_toArray, List.map_nil, Vector.mk_eq, Array.empty_eq,
        Vector.toArray_eq_empty_iff]
    · set bits := Vector.map (Expression.eval env) (Vector.mapRange n fun i => var { index := i0 + i })
      have h_bits' : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1 := by
        intro i hi
        simp only [bits, Vector.getElem_map, Vector.getElem_mapRange]
        apply h_bits ⟨i, hi⟩

      set bits_vars := Vector.mapRange n fun i => var (F := F p) { index := i0 + i }
      have h_fold : (Fin.foldl n (fun acc i ↦ acc + var { index := i0 + ↑i } * Expression.const (2 ^ (Fin.val i))) 0)
          = fieldFromBitsExpr bits_vars := by
        simp [fieldFromBitsExpr, bits_vars, Vector.getElem_mapRange]

      by_cases h_input_zero : input = 0
      · simp_rw [h_input_zero] at h_input ⊢
        have : Expression.eval env input_var = 0 := by
          simp only [eval, fromElements, toVars, toElements] at h_input
          convert h_input
          simp
        rw [this] at h_eq
        simp only [id_eq, mul_zero, dite_eq_ite, ite_self, add_zero, neg_zero, ZMod.val_zero,
          Nat.cast_zero, sub_zero] at h_eq ⊢
        rw [← h_eq]
        have h_f := fieldToBits_fieldFromBits hn bits h_bits'
        simp_all only [Nat.reducePow, gt_iff_lt, id_eq, mul_zero, dite_eq_ite, ite_self, add_zero,
          ↓reduceIte, one_mul, add_eq_right, zero_add]
        ext i hi
        simp only [fieldToBits, toBits, Vector.getElem_mapRange, Vector.getElem_map]
        rw [← Nat.cast_two, ← Nat.cast_pow, ZMod.val_natCast_of_lt hn, Nat.testBit_two_pow]
        have : n ≠ i := ne_of_gt hi
        simp only [this]
        rw [← fieldToBits_fieldFromBits hn bits h_bits']
        have h_val_zero : fieldFromBits bits = 0 := by
          simp only [fieldFromBits_eval] at h_eq
          have h_bits_eq : Vector.map (Expression.eval env) bits_vars = bits := by
            simp only [bits, bits_vars]
          rw [h_bits_eq] at h_eq
          exact h_eq
        rw [h_val_zero]
        simp [fieldToBits, toBits, Vector.getElem_mapRange]
      · have : Expression.eval env input_var = input := by
          rw [← h_input]
          simp [circuit_norm]
        rw [this] at h_eq
        simp_all only [Nat.reducePow, gt_iff_lt, id_eq, mul_zero, dite_eq_ite, ite_self, add_zero,
          ↓reduceIte, zero_mul, ZMod.natCast_val]
        have : (2 ^ n - ZMod.cast input) = fieldFromBits bits := by
          rw [sub_eq_add_neg, ZMod.cast_id, ← h_eq]
          let bits_vars := Vector.mapRange n fun i => var (F := F p) { index := i0 + i }
          have h_expr_fold : (Fin.foldl n (fun acc i ↦ acc + var { index := i0 + ↑i } * Expression.const (2 ^ (Fin.val i))) 0)
              = fieldFromBitsExpr bits_vars := by
            simp only [fieldFromBitsExpr, bits_vars, Vector.getElem_mapRange]
          rw [← fieldFromBits_eval]
        rw [this]
        symm
        apply fieldToBits_fieldFromBits hn
        exact h_bits'

  completeness := by
    simp only [circuit_norm, main]
    intro i0 env input_var h_env input h_input assumption
    simp only [circuit_norm, IsZero.circuit, IsZero.main] at h_env h_input ⊢
    simp only [h_input, circuit_norm] at h_env ⊢
    by_cases h_n : n = 0
    · rw [h_n] at h_env ⊢
      simp_all only [Nat.reducePow, gt_iff_lt, pow_zero, ↓reduceIte, IsEmpty.forall_iff, id_eq,
        add_zero, lt_self_iff_false, ↓reduceDIte, true_and, Fin.foldl_zero, mul_one]
      by_cases h_input_zero : input = 0
      · rw [h_input_zero]
        simp only [Expression.eval, ↓reduceIte, neg_zero, add_zero, add_eq_right]
      · simp_all only [id_eq, ↓reduceIte, add_zero]
        simp only [Expression.eval]
        rw [← h_env]
        rw [← h_input]
        simp_all
    · obtain ⟨h_bits, h_eq⟩ := h_env
      constructor
      · intro i
        rw [h_bits]
        simp only [IsBool]
        apply fieldToBits_bits
      · rw [h_eq]
        simp_all only [Nat.reducePow, gt_iff_lt, ↓reduceIte, id_eq, mul_zero, dite_eq_ite, ite_self,
          add_zero, ite_mul, one_mul, zero_mul]
        let bits_vars := Vector.mapRange n fun i => var (F := F p) { index := i0 + i }

        have h_expr_fold : (Fin.foldl n (fun acc i ↦ acc + var { index := i0 + ↑i } * Expression.const (2 ^ (Fin.val i))) 0)
            = fieldFromBitsExpr bits_vars := by
          simp only [fieldFromBitsExpr, bits_vars, Vector.getElem_mapRange]
        rw [h_expr_fold]

        have : ∀ (i: Fin n), Expression.eval env bits_vars[i]! = env.get (i0 + i) := by
          unfold bits_vars
          simp_all only [not_false_eq_true, Fin.is_lt, getElem!_pos, Fin.getElem_fin]
          intro i
          rw [← h_bits]
          simp only [Vector.getElem_mapRange, Expression.eval]

        simp_all only [not_false_eq_true, Fin.is_lt, getElem!_pos, Fin.getElem_fin]
        simp only [fieldFromBits_eval]

        by_cases h_iz: input = 0
        · have h : (ZMod.val (2 ^ n: ZMod p)) = 2 ^ n := by
            rw [← ZMod.val_natCast_of_lt hn]
            simp only [Nat.cast_pow, Nat.cast_ofNat]

          simp_all only [sub_zero, ↓reduceIte, id_eq, neg_zero, add_zero, add_eq_right]
          simp only [fieldToBits, toBits, Vector.getElem_map] at this
          simp_all only [ZMod.val_zero, Nat.ofNat_pos, pow_pos]
          simp only [Nat.testBit_two_pow, Vector.getElem_mapRange] at this

          have h : ∀ (i : Fin n), n ≠ i.val := by
            intro i
            symm
            exact ne_of_lt i.isLt
          simp only [h] at this

          rw [fieldFromBits_as_sum]
          simp only [Vector.getElem_map]
          conv =>
            lhs
            congr
            ext acc k
            rw [this k]
            simp only [decide_false, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_mul,
              add_zero]
          apply Fin.fin_foldl_const
        · have h_field_eq : ((2 ^ n - input.val : ℕ) : F p) = (2 ^ n : F p) - (ZMod.cast input : F p) := by
            rw [Nat.cast_sub (Nat.le_of_lt assumption)]
            simp only [Nat.cast_pow, Nat.cast_ofNat]
            congr
            simp only [ZMod.natCast_val]

          have h_1: fieldFromBits ((fieldToBits n ((2 ^ n) - input.val).cast)) = ((fieldFromBits (Vector.map (fun x ↦ Expression.eval env x) bits_vars))) := by
            apply fieldFromBits_eq
            intro i
            simp only [Fin.getElem_fin, Vector.getElem_map]
            rw [this, h_field_eq]
            rw [ZMod.cast_id]

          simp_all only [↓reduceIte, id_eq, add_zero]
          rw [← h_1]
          rw [ZMod.cast_id]
          rw [fieldFromBits_fieldToBits]
          simp only [sub_eq_add_neg]

          have hnowrap : 2 ^ n - ZMod.val input < p :=
            lt_of_le_of_lt (Nat.sub_le _ _) hn

          have h_val_eq : HSub.hSub (2^n : F p) ↑input = ↑(2 ^ n - ZMod.val input) := by
            rw [Nat.cast_sub (Nat.le_of_lt assumption)]
            simp only [Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val, sub_right_inj]
            rw [ZMod.cast_id]

          rw [h_val_eq]
          simp only [ZMod.val_natCast_of_lt hnowrap]
          simp only [tsub_lt_self_iff, Nat.ofNat_pos, pow_pos, ZMod.val_pos, ne_eq, true_and]
          exact h_iz
end Num2BitsNeg

end Circomlib
