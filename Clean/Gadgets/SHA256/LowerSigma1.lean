import Clean.Gadgets.SHA256.LowerSigma0
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# σ₁ (lower sigma 1) for SHA-256

σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)

Single-constraint 3-input XOR (`xor3raw`): 32 witnesses, 32 constraints.

Mirrors `LowerSigma0` with constants 17, 19, 10 instead of 7, 18, 3.
Reuses the helper lemmas defined in `LowerSigma0`.
-/

/-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x) -/
def lowerSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  xor3raw (rotr32 17 x) (rotr32 19 x) (shr32 10 x)

namespace LowerSigma1

open LowerSigma0 (sum_bool_lt_two_pow testBit_binary_sum bool_finsum_xor_eq
  valueBits_lt_two_pow valueBits_rotr32_eq valueBits_shr32_eq
  eval_rotr32 eval_shr32 shr_isbool)

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma1 x

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) where
  main := main
  localLength _ := 32
  localLength_eq _ _ := by simp [circuit_norm, main, lowerSigma1, xor3raw]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main, lowerSigma1, xor3raw]
  channelsLawful := by intro x n; simp [circuit_norm, main, lowerSigma1, xor3raw]

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma1 (valueBits x) ∧ Normalized z

/-! ## Spec proof factored out to avoid kernel deep recursion -/

private lemma spec_of_constraint
    (input z : fields 32 (F p))
    (hx : Normalized input)
    (h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val])
      + (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0)
      - 2 * (input[(i + 17).val] + input[(i + 19).val] -
              2 * input[(i + 17).val] * input[(i + 19).val])
            * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0)) :
    valueBits z = Specs.SHA256.lowerSigma1 (valueBits input) ∧ Normalized z := by
  have ha_val : ∀ i : Fin 32, (input[i] : F p).val = 0 ∨ (input[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r19_isbool : ∀ i : Fin 32,
      input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] = 0 ∨
      input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] = 1 :=
    fun i => IsBool.xor_is_bool (hx _) (hx _)
  have h_s10_isbool : ∀ i : Fin 32,
      (if h : i.val + 10 < 32 then input[i.val + 10]'h else (0 : F p)) = 0 ∨
      (if h : i.val + 10 < 32 then input[i.val + 10]'h else (0 : F p)) = 1 :=
    fun i => shr_isbool 10 input hx i
  have h_z_isbool : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := fun i => by
    rw [h_z i]; exact IsBool.xor_is_bool (h_r19_isbool i) (h_s10_isbool i)
  have h_r19_val : ∀ i : Fin 32,
      ((input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] : F p)).val = 0 ∨
      ((input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] : F p)).val = 1 :=
    fun i => by rcases h_r19_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_s10_val : ∀ i : Fin 32,
      ((if h : i.val + 10 < 32 then (input[i.val + 10]'h : F p) else 0) : F p).val = 0 ∨
      ((if h : i.val + 10 < 32 then (input[i.val + 10]'h : F p) else 0) : F p).val = 1 :=
    fun i => by rcases h_s10_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_z_xor_val : ∀ i : Fin 32, (z[i] : F p).val =
      (input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] : F p).val ^^^
      ((if h : i.val + 10 < 32 then (input[i.val + 10]'h : F p) else 0) : F p).val :=
    fun i => by rw [h_z i]; exact IsBool.xor_eq_val_xor (h_r19_isbool i) (h_s10_isbool i)
  have h_r19_xor_val : ∀ i : Fin 32,
      (input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] : F p).val =
      (input[(i + 17).val] : F p).val ^^^ (input[(i + 19).val] : F p).val :=
    fun i => IsBool.xor_eq_val_xor (hx _) (hx _)
  have key : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
      ((rotRight32 (valueBits input) 17) ^^^ (rotRight32 (valueBits input) 19))
      ^^^ (valueBits input / 2^10) := by
    have step1 : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
        ∑ i : Fin 32, ((input[(i + 17).val] + input[(i + 19).val] -
            2 * input[(i + 17).val] * input[(i + 19).val] : F p).val ^^^
          ((if h : i.val + 10 < 32 then (input[i.val + 10]'h : F p) else 0) : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_z_xor_val i]
    rw [step1, bool_finsum_xor_eq 32 _ _ h_r19_val h_s10_val]
    have step2 : ∑ i : Fin 32,
        (input[(i + 17).val] + input[(i + 19).val] -
          2 * input[(i + 17).val] * input[(i + 19).val] : F p).val * 2^i.val =
        ∑ i : Fin 32,
          ((input[(i + 17).val] : F p).val ^^^ (input[(i + 19).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_r19_xor_val i]
    rw [step2, bool_finsum_xor_eq 32
      (fun i : Fin 32 => (input[(i + 17).val] : F p).val)
      (fun i : Fin 32 => (input[(i + 19).val] : F p).val)
      (fun i => ha_val ⟨(i + 17).val, (i + 17).isLt⟩)
      (fun i => ha_val ⟨(i + 19).val, (i + 19).isLt⟩)]
    rw [valueBits_rotr32_eq 17 input hx, valueBits_rotr32_eq 19 input hx]
    show _ ^^^ _ ^^^
      (∑ i : Fin 32, ((if h : i.val + ((10 : Fin 32).val) < 32
        then (input[i.val + ((10 : Fin 32).val)]'h : F p) else 0) : F p).val * 2^i.val) = _
    rw [valueBits_shr32_eq 10 input hx]
    rfl
  have sigma1_def : ∀ x : ℕ, Specs.SHA256.lowerSigma1 x =
      rotRight32 x 17 ^^^ rotRight32 x 19 ^^^ (x / 2^10) := fun _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_z_isbool⟩
  rw [sigma1_def, h_z_eq]
  exact key

variable [Fact (p > 2^35)]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [lowerSigma1, xor3raw]
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r17 : ∀ i : Fin 32, Expression.eval env (rotr32 17 input_var)[i.val] = input[(i + 17).val] :=
    fun i => eval_rotr32 env input_var input h_input 17 i
  have h_r19 : ∀ i : Fin 32, Expression.eval env (rotr32 19 input_var)[i.val] = input[(i + 19).val] :=
    fun i => eval_rotr32 env input_var input h_input 19 i
  have h_s10 : ∀ i : Fin 32, Expression.eval env (shr32 10 input_var)[i.val] =
      if h : i.val + 10 < 32 then input[i.val + 10]'h else 0 :=
    fun i => eval_shr32 env input_var input h_input 10 i
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_zget : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val])
      + (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0)
      - 2 * (input[(i + 17).val] + input[(i + 19).val] -
              2 * input[(i + 17).val] * input[(i + 19).val])
            * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0) := by
    intro i
    have hcon : (env.get (i₀ + i.val) + 2 * input[(i + 17).val] + 2 * input[(i + 19).val]
          + 7 * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0))
          * (input[(i + 17).val] + input[(i + 19).val]
            - 4 * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0) + 1)
          - (6 * input[(i + 17).val] + 6 * input[(i + 19).val]
            - 24 * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0)) = 0 := by
      have h := h_holds i; rw [h_r17 i, h_r19 i, h_s10 i] at h; linear_combination h
    have hxor := xor3_unique (ha (i + 17)) (ha (i + 19)) (shr_isbool 10 input ha i) hcon
    rw [h_zget i]; linear_combination hxor
  exact spec_of_constraint input z ha h_z

omit [Fact (p > 2^35)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [lowerSigma1, xor3raw]
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have hr17 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 17 input_var)[i.val] = input[(i + 17).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 17 i
  have hr19 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 19 input_var)[i.val] = input[(i + 19).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 19 i
  have hs10 : ∀ i : Fin 32, Expression.eval env.toEnvironment (shr32 10 input_var)[i.val] =
      if h : i.val + 10 < 32 then input[i.val + 10]'h else 0 :=
    fun i => eval_shr32 env.toEnvironment input_var input h_input 10 i
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [hr17 i, hr19 i, hs10 i] at henv
  rw [hr17 i, hr19 i, hs10 i, henv]
  linear_combination xor3_complete (ha (i + 17)) (ha (i + 19)) (shr_isbool 10 input ha i)

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  Assumptions := Assumptions; Spec := Spec
  soundness := soundness; completeness := completeness

end LowerSigma1
end Gadgets.SHA256
end
