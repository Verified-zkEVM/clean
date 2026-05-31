import Clean.Gadgets.SHA256.LowerSigma0
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# Σ₀ (upper sigma 0) for SHA-256

Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)

Single-constraint 3-input XOR (`xor3raw`): 32 witnesses, 32 constraints.

Mirrors `LowerSigma0` but with three rotations (no shift) and constants 2, 13, 22.
Reuses the helper lemmas defined in `LowerSigma0`.
-/

/-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x) -/
def upperSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  xor3raw (rotr32 2 x) (rotr32 13 x) (rotr32 22 x)

namespace UpperSigma0

open LowerSigma0 (sum_bool_lt_two_pow testBit_binary_sum bool_finsum_xor_eq
  valueBits_lt_two_pow valueBits_rotr32_eq eval_rotr32)

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma0 x

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) where
  main := main
  localLength _ := 32
  localLength_eq _ _ := by simp [circuit_norm, main, upperSigma0, xor3raw]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main, upperSigma0, xor3raw]
  channelsLawful := by intro x n; simp [circuit_norm, main, upperSigma0, xor3raw]

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma0 (valueBits x) ∧ Normalized z

/-! ## Spec proof factored out to avoid kernel deep recursion -/

private lemma spec_of_constraint
    (input z : fields 32 (F p))
    (hx : Normalized input)
    (h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val])
      + input[(i + 22).val]
      - 2 * (input[(i + 2).val] + input[(i + 13).val] -
              2 * input[(i + 2).val] * input[(i + 13).val])
            * input[(i + 22).val]) :
    valueBits z = Specs.SHA256.upperSigma0 (valueBits input) ∧ Normalized z := by
  have ha_val : ∀ i : Fin 32, (input[i] : F p).val = 0 ∨ (input[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r213_isbool : ∀ i : Fin 32,
      input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] = 0 ∨
      input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] = 1 :=
    fun i => IsBool.xor_is_bool (hx _) (hx _)
  have h_r22_isbool : ∀ i : Fin 32, input[(i + 22).val] = (0 : F p) ∨ input[(i + 22).val] = 1 :=
    fun i => hx _
  have h_z_isbool : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := fun i => by
    rw [h_z i]; exact IsBool.xor_is_bool (h_r213_isbool i) (h_r22_isbool i)
  have h_r213_val : ∀ i : Fin 32,
      ((input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] : F p)).val = 0 ∨
      ((input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] : F p)).val = 1 :=
    fun i => by rcases h_r213_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r22_val : ∀ i : Fin 32, (input[(i + 22).val] : F p).val = 0 ∨
      (input[(i + 22).val] : F p).val = 1 :=
    fun i => ha_val _
  have h_z_xor_val : ∀ i : Fin 32, (z[i] : F p).val =
      (input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] : F p).val ^^^
      (input[(i + 22).val] : F p).val :=
    fun i => by rw [h_z i]; exact IsBool.xor_eq_val_xor (h_r213_isbool i) (h_r22_isbool i)
  have h_r213_xor_val : ∀ i : Fin 32,
      (input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] : F p).val =
      (input[(i + 2).val] : F p).val ^^^ (input[(i + 13).val] : F p).val :=
    fun i => IsBool.xor_eq_val_xor (hx _) (hx _)
  have key : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
      ((rotRight32 (valueBits input) 2) ^^^ (rotRight32 (valueBits input) 13))
      ^^^ rotRight32 (valueBits input) 22 := by
    have step1 : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
        ∑ i : Fin 32, ((input[(i + 2).val] + input[(i + 13).val] -
            2 * input[(i + 2).val] * input[(i + 13).val] : F p).val ^^^
          (input[(i + 22).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_z_xor_val i]
    rw [step1, bool_finsum_xor_eq 32 _ _ h_r213_val h_r22_val]
    have step2 : ∑ i : Fin 32,
        (input[(i + 2).val] + input[(i + 13).val] -
          2 * input[(i + 2).val] * input[(i + 13).val] : F p).val * 2^i.val =
        ∑ i : Fin 32,
          ((input[(i + 2).val] : F p).val ^^^ (input[(i + 13).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_r213_xor_val i]
    rw [step2, bool_finsum_xor_eq 32
      (fun i : Fin 32 => (input[(i + 2).val] : F p).val)
      (fun i : Fin 32 => (input[(i + 13).val] : F p).val)
      (fun i => ha_val ⟨(i + 2).val, (i + 2).isLt⟩)
      (fun i => ha_val ⟨(i + 13).val, (i + 13).isLt⟩)]
    rw [valueBits_rotr32_eq 2 input hx, valueBits_rotr32_eq 13 input hx,
        valueBits_rotr32_eq 22 input hx]
    rfl
  have sigma_def : ∀ x : ℕ, Specs.SHA256.upperSigma0 x =
      rotRight32 x 2 ^^^ rotRight32 x 13 ^^^ rotRight32 x 22 := fun _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_z_isbool⟩
  rw [sigma_def, h_z_eq]
  exact key

variable [Fact (p > 2^35)]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [upperSigma0, xor3raw]
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r2  : ∀ i : Fin 32, Expression.eval env (rotr32 2 input_var)[i.val]  = input[(i + 2).val]  :=
    fun i => eval_rotr32 env input_var input h_input 2 i
  have h_r13 : ∀ i : Fin 32, Expression.eval env (rotr32 13 input_var)[i.val] = input[(i + 13).val] :=
    fun i => eval_rotr32 env input_var input h_input 13 i
  have h_r22 : ∀ i : Fin 32, Expression.eval env (rotr32 22 input_var)[i.val] = input[(i + 22).val] :=
    fun i => eval_rotr32 env input_var input h_input 22 i
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_zget : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val])
      + input[(i + 22).val]
      - 2 * (input[(i + 2).val] + input[(i + 13).val] -
              2 * input[(i + 2).val] * input[(i + 13).val])
            * input[(i + 22).val] := by
    intro i
    -- The single XOR constraint at bit `i`, with the rotations evaluated to input bits.
    have hcon : (env.get (i₀ + i.val) + 2 * input[(i + 2).val] + 2 * input[(i + 13).val]
          + 7 * input[(i + 22).val]) * (input[(i + 2).val] + input[(i + 13).val]
            - 4 * input[(i + 22).val] + 1)
          - (6 * input[(i + 2).val] + 6 * input[(i + 13).val] - 24 * input[(i + 22).val]) = 0 := by
      have h := h_holds i; rw [h_r2 i, h_r13 i, h_r22 i] at h; linear_combination h
    have hxor := xor3_unique (ha (i + 2)) (ha (i + 13)) (ha (i + 22)) hcon
    rw [h_zget i]; linear_combination hxor
  exact spec_of_constraint input z ha h_z

omit [Fact (p > 2^35)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [upperSigma0, xor3raw]
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have hr2 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 2 input_var)[i.val] = input[(i + 2).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 2 i
  have hr13 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 13 input_var)[i.val] = input[(i + 13).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 13 i
  have hr22 : ∀ i : Fin 32, Expression.eval env.toEnvironment (rotr32 22 input_var)[i.val] = input[(i + 22).val] :=
    fun i => eval_rotr32 env.toEnvironment input_var input h_input 22 i
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [hr2 i, hr13 i, hr22 i] at henv
  rw [hr2 i, hr13 i, hr22 i, henv]
  linear_combination xor3_complete (ha (i + 2)) (ha (i + 13)) (ha (i + 22))

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end UpperSigma0
end Gadgets.SHA256
end
