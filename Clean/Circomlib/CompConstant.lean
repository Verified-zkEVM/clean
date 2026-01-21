import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Clean.Circomlib.CompConstantLemmas

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/compconstant.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace CompConstant
def main (ct : ℕ) (input : Vector (Expression (F p)) 254) := do
  let parts : fields 127 (Expression (F p)) <== Vector.ofFn fun i =>
    let clsb := (ct >>> (i.val * 2)) &&& 1
    let cmsb := (ct >>> (i.val * 2 + 1)) &&& 1
    let slsb := input[i.val * 2]
    let smsb := input[i.val * 2 + 1]

    -- Compute b, a values for this iteration
    let b_val : ℤ := 2^128 - 2^i.val
    let a_val : ℤ := 2^i.val

    if cmsb == 0 && clsb == 0 then
      -(b_val : F p) * smsb * slsb + (b_val : F p) * smsb + (b_val : F p) * slsb
    else if cmsb == 0 && clsb == 1 then
      (a_val : F p) * smsb * slsb - (a_val : F p) * slsb + (b_val : F p) * smsb - (a_val : F p) * smsb + (a_val : F p)
    else if cmsb == 1 && clsb == 0 then
      (b_val : F p) * smsb * slsb - (a_val : F p) * smsb + (a_val : F p)
    else
      -(a_val : F p) * smsb * slsb + (a_val : F p)

  -- Compute sum
  let sout <== parts.sum

  -- Convert sum to bits
  have hp : p > 2^135 := by linarith [‹Fact (p > 2^253)›.elim]
  let bits ← Num2Bits.circuit 135 hp sout

  let out <== bits[127]
  return out

set_option maxRecDepth 2000 in
def circuit (c : ℕ) (h_c : c < 2^254) : FormalCircuit (F p) (fields 254) field where
  main := main c
  localLength _ := 127 + 1 + 135 + 1  -- parts witness + sout witness + Num2Bits + out witness
  localLength_eq := by simp only [circuit_norm, main, Num2Bits.circuit]
  subcircuitsConsistent input n := by
    simp only [circuit_norm, main, Num2Bits.circuit]
    and_intros <;> ac_rfl

  Assumptions input :=
    (∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)

  Spec bits output :=
    output = if fromBits (bits.map ZMod.val) > c then 1 else 0

  soundness := by
    circuit_proof_start [Num2Bits.circuit]
    rcases h_holds with ⟨h_parts, h_holds⟩
    rcases h_holds with ⟨h_sout, h_holds⟩
    rcases h_holds with ⟨h_num2bits, h_out⟩
    rcases h_num2bits with ⟨h_sout_range, h_bits_valid⟩

    let parts : Vector (F p) 127 := Vector.mapRange 127 fun i => env.get (i₀ + i)
    let sout : F p := env.get (i₀ + 127)
    let bits : Vector (F p) 135 := Vector.mapRange 135 fun i => env.get (i₀ + 127 + 1 + i)
    let out : F p := env.get (i₀ + 127 + 1 + 135)
    let input_val : ℕ := fromBits (input.map ZMod.val)

    have h_input_eval : ∀ j : ℕ, (hj : j < 254) → input_var[j].eval env = input[j] := by
      intro j hj
      have := congrArg (fun v => v[j]) h_input
      simp only [Vector.getElem_map] at this
      exact this

    have h_parts' :
        ∀ i : Fin 127,
          parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] c := by
      intro i
      have h_parts_i := congrArg (fun v => v[i]) h_parts
      simp only [circuit_norm, Vector.getElem_ofFn] at h_parts_i
      show (Vector.mapRange 127 fun j => env.get (i₀ + j))[i.val] = _
      simp only [Vector.getElem_mapRange, h_parts_i]
      simp only [apply_ite (Expression.eval env)]
      simp only [circuit_norm]
      have hi2 : (i : ℕ) * 2 < 254 := by omega
      have hi2p1 : (i : ℕ) * 2 + 1 < 254 := by omega
      simp only [h_input_eval _ hi2, h_input_eval _ hi2p1]
      simp only [computePart, bCoeff, aCoeff]
      have h_pow_le : (2 : ℕ)^(i : ℕ) ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega : (i : ℕ) ≤ 128)
      have h_int_eq_nat_sub : ((2^128 - 2^(i : ℕ) : ℤ) : F p) = ((2^128 - 2^(i : ℕ) : ℕ) : F p) := by
        rw [Int.cast_sub, Nat.cast_sub h_pow_le]
        simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      simp_rw [h_int_eq_nat_sub]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub h_pow_le]
      split_ifs <;> ring

    have h_sum_encodes := sum_bit127_encodes_gt c h_c input h_assumptions parts h_parts'

    have h_sout' : parts.sum = sout := by
      show (Vector.mapRange 127 fun i => env.get (i₀ + i)).sum = env.get (i₀ + 127)
      rw [h_sout]
      have h_vec_eq : (Vector.mapRange 127 fun i => env.get (i₀ + i)) =
                      Vector.map (Expression.eval env) (Vector.mapRange 127 fun i => var { index := i₀ + i }) := by
        ext j hj
        simp only [Vector.getElem_mapRange, Vector.getElem_map, circuit_norm]
      rw [h_vec_eq]
      have h_list_sum_eval : ∀ l : List (Expression (F p)),
          (l.map (Expression.eval env)).sum = Expression.eval env l.sum := by
        intro l
        induction l with
        | nil => simp only [List.map_nil, List.sum_nil, circuit_norm]
        | cons x xs ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          simp only [circuit_norm]
      simp only [Vector.sum, Vector.toArray_map]
      conv_lhs => rw [← Array.sum_eq_sum_toList, Array.toList_map]
      conv_rhs => rw [← Array.sum_eq_sum_toList]
      exact h_list_sum_eval _

    have h_sum_encodes' : sout.val.testBit 127 = (input_val > c) := by
      rw [← h_sout']
      exact h_sum_encodes

    have h_bits' : bits = fieldToBits 135 sout := by
      show Vector.mapRange 135 (fun i => env.get (i₀ + 127 + 1 + i)) = fieldToBits 135 (env.get (i₀ + 127))
      have h_bits_valid' := h_bits_valid
      simp only [Vector.map_mapRange, circuit_norm] at h_bits_valid'
      ext j hj
      have h_bits_j := congrArg (fun v => v[j]) h_bits_valid'
      simp only [Vector.getElem_mapRange] at h_bits_j ⊢
      exact h_bits_j

    have h_bits_127 : bits[127] = if input_val > c then 1 else 0 := by
      rw [h_bits']
      rw [fieldToBits_testBit_127 sout 135 (by omega : 127 < 135)]
      simp only [h_sum_encodes']

    have h_out' : out = bits[127] := by
      change env.get (i₀ + 127 + 1 + 135) = (Vector.mapRange 135 fun i => env.get (i₀ + 127 + 1 + i))[127]
      simp only [Vector.getElem_mapRange, h_out]

    have h_out_final : out = if input_val > c then 1 else 0 := by
      calc
        out = bits[127] := h_out'
        _ = if input_val > c then 1 else 0 := h_bits_127
    simpa [out, input_val] using h_out_final

  completeness := by
    circuit_proof_start [Num2Bits.circuit]
    -- no simp needed here
    rcases h_env with ⟨h_parts, h_sout, h_num2bits, h_out⟩

    let parts : Vector (F p) 127 := Vector.mapRange 127 fun i => env.get (i₀ + i)
    let sout : F p := env.get (i₀ + 127)

    have h_input_eval : ∀ j : ℕ, (hj : j < 254) → input_var[j].eval env = input[j] := by
      intro j hj
      have := congrArg (fun v => v[j]) h_input
      simp only [Vector.getElem_map] at this
      exact this

    have h_parts' :
        ∀ i : Fin 127,
          parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] c := by
      intro i
      have h_parts_i := h_parts i
      simp only [circuit_norm, Vector.getElem_ofFn] at h_parts_i
      show (Vector.mapRange 127 fun j => env.get (i₀ + j))[i.val] = _
      simp only [Vector.getElem_mapRange, h_parts_i]
      simp only [apply_ite (Expression.eval env)]
      simp only [circuit_norm]
      have hi2 : (i : ℕ) * 2 < 254 := by omega
      have hi2p1 : (i : ℕ) * 2 + 1 < 254 := by omega
      simp only [h_input_eval _ hi2, h_input_eval _ hi2p1]
      simp only [computePart, bCoeff, aCoeff]
      have h_pow_le : (2 : ℕ)^(i : ℕ) ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega : (i : ℕ) ≤ 128)
      have h_int_eq_nat_sub : ((2^128 - 2^(i : ℕ) : ℤ) : F p) = ((2^128 - 2^(i : ℕ) : ℕ) : F p) := by
        rw [Int.cast_sub, Nat.cast_sub h_pow_le]
        simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      have h_int_eq_nat_pow : ((2^(i : ℕ) : ℤ) : F p) = ((2^(i : ℕ) : ℕ) : F p) := by
        simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
      simp_rw [h_int_eq_nat_sub, h_int_eq_nat_pow]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub h_pow_le]
      split_ifs <;> ring

    have h_sout' : parts.sum = sout := by
      show (Vector.mapRange 127 fun i => env.get (i₀ + i)).sum = env.get (i₀ + 127)
      rw [h_sout]
      have h_vec_eq : (Vector.mapRange 127 fun i => env.get (i₀ + i)) =
                      Vector.map (Expression.eval env) (Vector.mapRange 127 fun i => var { index := i₀ + i }) := by
        ext j hj
        simp only [Vector.getElem_mapRange, Vector.getElem_map, circuit_norm]
      rw [h_vec_eq]
      have h_list_sum_eval : ∀ l : List (Expression (F p)),
          (l.map (Expression.eval env)).sum = Expression.eval env l.sum := by
        intro l
        induction l with
        | nil => simp only [List.map_nil, List.sum_nil, circuit_norm]
        | cons x xs ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          simp only [circuit_norm]
      simp only [Vector.sum, Vector.toArray_map]
      conv_lhs => rw [← Array.sum_eq_sum_toList, Array.toList_map]
      conv_rhs => rw [← Array.sum_eq_sum_toList]
      exact h_list_sum_eval _

    have h_parts_bounded : ∀ i : Fin 127, parts[i].val ≤ 2^128 := by
      intro i
      rw [h_parts' i]
      exact computePart_val_bound' i.val i.isLt _ _
        (h_assumptions (i.val * 2) (by omega)) (h_assumptions (i.val * 2 + 1) (by omega)) c

    have h_sum_bound' : (parts.toList.map ZMod.val).sum ≤ parts.toList.length * 2^128 := by
      apply list_sum_val_bound'
      intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [Vector.getElem_toList]
      rw [Vector.length_toList] at hi
      exact h_parts_bounded ⟨i, hi⟩

    have h_sum_bound : (parts.toList.map ZMod.val).sum ≤ 127 * 2^128 := by
      simpa [Vector.length_toList] using h_sum_bound'

    have h_sum_lt_2_135 : (parts.toList.map ZMod.val).sum < 2^135 := by
      have h_bound : (127 : ℕ) * 2^128 < 2^135 := by native_decide
      exact lt_of_le_of_lt h_sum_bound h_bound

    have h_sum_lt_p : (parts.toList.map ZMod.val).sum < p := by
      have h_2_135_lt_p : 2^135 < p := by
        have h_2_135_lt_2_253 : 2^135 < 2^253 := by native_decide
        linarith [‹Fact (p > 2^253)›.elim, h_2_135_lt_2_253]
      exact lt_trans h_sum_lt_2_135 h_2_135_lt_p

    have h_parts_sum_val : parts.sum.val = (parts.toList.map ZMod.val).sum := by
      have h_vec_sum : parts.sum = parts.toList.sum := vector_sum_eq_list_sum' parts
      rw [h_vec_sum, list_sum_val_eq' h_sum_lt_p]

    have h_parts_sum_lt : parts.sum.val < 2^135 := by
      simpa [h_parts_sum_val] using h_sum_lt_2_135

    have h_sout_lt : sout.val < 2^135 := by
      have h_sout_val : parts.sum.val = sout.val := congrArg ZMod.val h_sout'
      simpa [h_sout_val] using h_parts_sum_lt

    and_intros
    · ext i hi
      have h_parts_i := h_parts ⟨i, hi⟩
      simpa [Vector.getElem_map, Vector.getElem_mapRange] using h_parts_i
    · exact h_sout
    · exact h_sout_lt
    · exact h_out

end CompConstant

end Circomlib
