import Clean.Gadgets.SHA256.LowerSigma0

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# Σ₀ (upper sigma 0) for SHA-256

Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)

Two xor32 calls = 64 witnesses total.

Mirrors `LowerSigma0` but with three rotations (no shift) and constants 2, 13, 22.
Reuses the helper lemmas defined in `LowerSigma0`.
-/

/-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x) -/
def upperSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← xor32 (rotr32 2  x) (rotr32 13 x)
  xor32 r1 (rotr32 22 x)

namespace UpperSigma0

open LowerSigma0 (sum_bool_lt_two_pow testBit_binary_sum bool_finsum_xor_eq
  valueBits_lt_two_pow valueBits_rotr32_eq eval_rotr32)

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma0 x

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

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [upperSigma0, xor32]
  obtain ⟨h_holds1, h_holds2⟩ := h_holds
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r2  : ∀ i : Fin 32, Expression.eval env (rotr32 2 input_var)[i.val]  = input[(i + 2).val]  :=
    fun i => eval_rotr32 env input_var input h_input 2 i
  have h_r13 : ∀ i : Fin 32, Expression.eval env (rotr32 13 input_var)[i.val] = input[(i + 13).val] :=
    fun i => eval_rotr32 env input_var input h_input 13 i
  have h_r22 : ∀ i : Fin 32, Expression.eval env (rotr32 22 input_var)[i.val] = input[(i + 22).val] :=
    fun i => eval_rotr32 env input_var input h_input 22 i
  have h_r1 : ∀ i : Fin 32, env.get (i₀ + i.val) =
      input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val] := by
    intro i
    have h := h_holds1 i; rw [h_r2 i, h_r13 i] at h
    have key : env.get (i₀ + i.val) -
        (input[(i + 2).val] + input[(i + 13).val] -
          2 * input[(i + 2).val] * input[(i + 13).val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  have h_z_raw : ∀ i : Fin 32, env.get (i₀ + (32 + 32 * 0) + i.val) =
      env.get (i₀ + i.val) + Expression.eval env (rotr32 22 input_var)[i.val] -
      2 * env.get (i₀ + i.val) * Expression.eval env (rotr32 22 input_var)[i.val] := by
    intro i
    have h := h_holds2 i
    have key : env.get (i₀ + (32 + 32 * 0) + i.val) -
        (env.get (i₀ + i.val) + Expression.eval env (rotr32 22 input_var)[i.val] -
         2 * env.get (i₀ + i.val) * Expression.eval env (rotr32 22 input_var)[i.val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + (32 + 32 * 0) + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + (32 + 32 * 0) + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 2).val] + input[(i + 13).val] -
        2 * input[(i + 2).val] * input[(i + 13).val])
      + input[(i + 22).val]
      - 2 * (input[(i + 2).val] + input[(i + 13).val] -
              2 * input[(i + 2).val] * input[(i + 13).val])
            * input[(i + 22).val] := by
    intro i
    rw [h_z_get i, h_z_raw i, h_r1 i, h_r22 i]
  exact spec_of_constraint input z ha h_z

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [upperSigma0, xor32]
  obtain ⟨h_env1, h_env2, -⟩ := h_env
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hr2 := eval_rotr32 env.toEnvironment input_var input h_input 2 i
    have hr13 := eval_rotr32 env.toEnvironment input_var input h_input 13 i
    have h1 := h_env1 i
    simp only [Vector.getElem_ofFn] at h1
    rw [h1, hr2, hr13]
    have b2 : input[(i + 2).val] = (0 : F p) ∨ input[(i + 2).val] = 1 := h_assumptions (i + 2)
    have b13 : input[(i + 13).val] = (0 : F p) ∨ input[(i + 13).val] = 1 := h_assumptions (i + 13)
    have hc : ((input[(i + 2).val].val ^^^ input[(i + 13).val].val : ℕ) : F p) =
        input[(i + 2).val] + input[(i + 13).val] -
          2 * input[(i + 2).val] * input[(i + 13).val] := by
      rw [← IsBool.xor_eq_val_xor b2 b13, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hc]; ring
  · have hr2 := eval_rotr32 env.toEnvironment input_var input h_input 2 i
    have hr13 := eval_rotr32 env.toEnvironment input_var input h_input 13 i
    have hr22 := eval_rotr32 env.toEnvironment input_var input h_input 22 i
    have h1 := h_env1 i
    have h2 := h_env2 i
    simp only [Vector.getElem_ofFn, mul_zero, zero_add] at h2
    simp only [Vector.getElem_ofFn] at h1
    rw [show (i₀ + (32 + 32 * 0) + ↑i) = i₀ + 32 + ↑i from by ring, h2, h1, hr2, hr13, hr22]
    have b2 : input[(i + 2).val] = (0 : F p) ∨ input[(i + 2).val] = 1 := h_assumptions (i + 2)
    have b13 : input[(i + 13).val] = (0 : F p) ∨ input[(i + 13).val] = 1 := h_assumptions (i + 13)
    have b22 : input[(i + 22).val] = (0 : F p) ∨ input[(i + 22).val] = 1 := h_assumptions (i + 22)
    set r2 : F p := input[(i + 2).val]
    set r13 : F p := input[(i + 13).val]
    set r22 : F p := input[(i + 22).val]
    have hxor1 : ((r2.val ^^^ r13.val : ℕ) : F p) = r2 + r13 - 2 * r2 * r13 := by
      rw [← IsBool.xor_eq_val_xor b2 b13, ZMod.natCast_val]
      exact ZMod.cast_id p _
    have hxor1_bool : IsBool (((r2.val ^^^ r13.val : ℕ) : F p)) := by
      rw [hxor1]; exact IsBool.xor_is_bool b2 b13
    have hxor3 : (((((r2.val ^^^ r13.val : ℕ) : F p).val ^^^ r22.val) : ℕ) : F p) =
        ((r2.val ^^^ r13.val : ℕ) : F p) + r22 -
          2 * ((r2.val ^^^ r13.val : ℕ) : F p) * r22 := by
      rw [← IsBool.xor_eq_val_xor hxor1_bool b22, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hxor3, hxor1]; ring

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end UpperSigma0
end Gadgets.SHA256
end
