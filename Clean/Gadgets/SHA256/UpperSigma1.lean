import Clean.Gadgets.SHA256.LowerSigma0
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# Σ₁ (upper sigma 1) for SHA-256

Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)

Single carry-save 3-input XOR (`xor3raw`) = 32 witnesses total.

Mirrors `UpperSigma0` with constants 6, 11, 25 instead of 2, 13, 22.
Reuses the helper lemmas defined in `LowerSigma0`.
-/

/-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x) -/
def upperSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  xor3raw (rotr32 6 x) (rotr32 11 x) (rotr32 25 x)

namespace UpperSigma1

open LowerSigma0 (sum_bool_lt_two_pow testBit_binary_sum bool_finsum_xor_eq
  valueBits_lt_two_pow valueBits_rotr32_eq eval_rotr32)

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma1 x

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) where
  main := main
  localLength _ := 32
  localLength_eq _ _ := by simp [circuit_norm, main, upperSigma1, xor3raw, carrySave]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main, upperSigma1, xor3raw, carrySave]
  channelsLawful := by intro x n; simp [circuit_norm, main, upperSigma1, xor3raw, carrySave]

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma1 (valueBits x) ∧ Normalized z

/-! ## Spec proof factored out to avoid kernel deep recursion -/

private lemma spec_of_constraint
    (input z : fields 32 (F p))
    (hx : Normalized input)
    (h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val])
      + input[(i + 25).val]
      - 2 * (input[(i + 6).val] + input[(i + 11).val] -
              2 * input[(i + 6).val] * input[(i + 11).val])
            * input[(i + 25).val]) :
    valueBits z = Specs.SHA256.upperSigma1 (valueBits input) ∧ Normalized z := by
  have ha_val : ∀ i : Fin 32, (input[i] : F p).val = 0 ∨ (input[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r611_isbool : ∀ i : Fin 32,
      input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] = 0 ∨
      input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] = 1 :=
    fun i => IsBool.xor_is_bool (hx _) (hx _)
  have h_r25_isbool : ∀ i : Fin 32, input[(i + 25).val] = (0 : F p) ∨ input[(i + 25).val] = 1 :=
    fun i => hx _
  have h_z_isbool : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := fun i => by
    rw [h_z i]; exact IsBool.xor_is_bool (h_r611_isbool i) (h_r25_isbool i)
  have h_r611_val : ∀ i : Fin 32,
      ((input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] : F p)).val = 0 ∨
      ((input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] : F p)).val = 1 :=
    fun i => by rcases h_r611_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r25_val : ∀ i : Fin 32, (input[(i + 25).val] : F p).val = 0 ∨
      (input[(i + 25).val] : F p).val = 1 :=
    fun i => ha_val _
  have h_z_xor_val : ∀ i : Fin 32, (z[i] : F p).val =
      (input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] : F p).val ^^^
      (input[(i + 25).val] : F p).val :=
    fun i => by rw [h_z i]; exact IsBool.xor_eq_val_xor (h_r611_isbool i) (h_r25_isbool i)
  have h_r611_xor_val : ∀ i : Fin 32,
      (input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val] : F p).val =
      (input[(i + 6).val] : F p).val ^^^ (input[(i + 11).val] : F p).val :=
    fun i => IsBool.xor_eq_val_xor (hx _) (hx _)
  have key : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
      ((rotRight32 (valueBits input) 6) ^^^ (rotRight32 (valueBits input) 11))
      ^^^ rotRight32 (valueBits input) 25 := by
    have step1 : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
        ∑ i : Fin 32, ((input[(i + 6).val] + input[(i + 11).val] -
            2 * input[(i + 6).val] * input[(i + 11).val] : F p).val ^^^
          (input[(i + 25).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_z_xor_val i]
    rw [step1, bool_finsum_xor_eq 32 _ _ h_r611_val h_r25_val]
    have step2 : ∑ i : Fin 32,
        (input[(i + 6).val] + input[(i + 11).val] -
          2 * input[(i + 6).val] * input[(i + 11).val] : F p).val * 2^i.val =
        ∑ i : Fin 32,
          ((input[(i + 6).val] : F p).val ^^^ (input[(i + 11).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_r611_xor_val i]
    rw [step2, bool_finsum_xor_eq 32
      (fun i : Fin 32 => (input[(i + 6).val] : F p).val)
      (fun i : Fin 32 => (input[(i + 11).val] : F p).val)
      (fun i => ha_val ⟨(i + 6).val, (i + 6).isLt⟩)
      (fun i => ha_val ⟨(i + 11).val, (i + 11).isLt⟩)]
    rw [valueBits_rotr32_eq 6 input hx, valueBits_rotr32_eq 11 input hx,
        valueBits_rotr32_eq 25 input hx]
    rfl
  have sigma_def : ∀ x : ℕ, Specs.SHA256.upperSigma1 x =
      rotRight32 x 6 ^^^ rotRight32 x 11 ^^^ rotRight32 x 25 := fun _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_z_isbool⟩
  rw [sigma_def, h_z_eq]
  exact key

variable [Fact (p > 2^35)]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [upperSigma1, xor3raw, carrySave]
  obtain ⟨h_q_bool, h_par_bool⟩ := h_holds
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r6  : ∀ i : Fin 32, Expression.eval env (rotr32 6 input_var)[i.val]  = input[(i + 6).val]  :=
    fun i => eval_rotr32 env input_var input h_input 6 i
  have h_r11 : ∀ i : Fin 32, Expression.eval env (rotr32 11 input_var)[i.val] = input[(i + 11).val] :=
    fun i => eval_rotr32 env input_var input h_input 11 i
  have h_r25 : ∀ i : Fin 32, Expression.eval env (rotr32 25 input_var)[i.val] = input[(i + 25).val] :=
    fun i => eval_rotr32 env input_var input h_input 25 i
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env)
      (Vector.ofFn fun i : Fin 32 =>
        (rotr32 6 input_var)[i.val] + (rotr32 11 input_var)[i.val] + (rotr32 25 input_var)[i.val]
          - 2 * var { index := i₀ + i.val }) with hz_def
  have hq : ∀ i : Fin 32, IsBool (env.get (i₀ + i.val)) := by
    intro i; rw [IsBool.iff_mul_sub_one]; linear_combination h_q_bool i
  have hpar : ∀ i : Fin 32, IsBool (input[(i + 6).val] + input[(i + 11).val] +
      input[(i + 25).val] - 2 * env.get (i₀ + i.val)) := by
    intro i; rw [IsBool.iff_mul_sub_one]
    have h := h_par_bool i; rw [h_r6 i, h_r11 i, h_r25 i] at h; linear_combination h
  have h_carry : ∀ i : Fin 32, env.get (i₀ + i.val) =
      input[(i + 6).val] * input[(i + 11).val] +
        input[(i + 25).val] *
          (input[(i + 6).val] + input[(i + 11).val] - 2 * (input[(i + 6).val] * input[(i + 11).val])) :=
    fun i => carry_eq_maj (ha (i + 6)) (ha (i + 11)) (ha (i + 25)) (hq i) (hpar i)
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 6).val] + input[(i + 11).val] -
        2 * input[(i + 6).val] * input[(i + 11).val])
      + input[(i + 25).val]
      - 2 * (input[(i + 6).val] + input[(i + 11).val] -
              2 * input[(i + 6).val] * input[(i + 11).val])
            * input[(i + 25).val] := by
    intro i
    simp only [z, Vector.getElem_map, Vector.getElem_ofFn, circuit_norm]
    rw [h_r6 i, h_r11 i, h_r25 i, h_carry i]; ring
  exact spec_of_constraint input z ha h_z

omit [Fact (p > 2^35)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [upperSigma1, xor3raw, carrySave]
  obtain ⟨h_env_q, -⟩ := h_env
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have hr6 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 6 input_var)[i.val] = input[(i + 6).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 6 i
  have hr11 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 11 input_var)[i.val] = input[(i + 11).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 11 i
  have hr25 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 25 input_var)[i.val] = input[(i + 25).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 25 i
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hq := h_env_q i
    simp only [Vector.getElem_ofFn] at hq
    rw [hq, hr6 i, hr11 i, hr25 i]
    have hbool := maj_is_bool (ha (i + 6)) (ha (i + 11)) (ha (i + 25))
    rw [IsBool.iff_mul_sub_one] at hbool; linear_combination hbool
  · have hq := h_env_q i
    simp only [Vector.getElem_ofFn] at hq
    rw [hq, hr6 i, hr11 i, hr25 i]
    have hbool := parity_is_bool (ha (i + 6)) (ha (i + 11)) (ha (i + 25))
    rw [IsBool.iff_mul_sub_one] at hbool; linear_combination hbool

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end UpperSigma1
end Gadgets.SHA256
end
