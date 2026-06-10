import Clean.Gadgets.SHA256.LowerSigma0

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# σ₁ (lower sigma 1) for SHA-256

σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)

Two xor32 calls = 64 witnesses total.

Mirrors `LowerSigma0` with constants 17, 19, 10 instead of 7, 18, 3.
Reuses the helper lemmas defined in `LowerSigma0`.
-/

/-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x) -/
def lowerSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← xor32 (rotr32 17 x) (rotr32 19 x)
  xor32 r1 (shr32 10 x)

namespace LowerSigma1

open LowerSigma0 (sum_bool_lt_two_pow testBit_binary_sum bool_finsum_xor_eq
  valueBits_lt_two_pow valueBits_rotr32_eq valueBits_shr32_eq
  eval_rotr32 eval_shr32 shr_isbool)

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma1 x

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

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [lowerSigma1, xor32]
  obtain ⟨h_holds1, h_holds2⟩ := h_holds
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r17 : ∀ i : Fin 32, Expression.eval env (rotr32 17 input_var)[i.val] = input[(i + 17).val] :=
    fun i => eval_rotr32 env input_var input h_input 17 i
  have h_r19 : ∀ i : Fin 32, Expression.eval env (rotr32 19 input_var)[i.val] = input[(i + 19).val] :=
    fun i => eval_rotr32 env input_var input h_input 19 i
  have h_s10 : ∀ i : Fin 32, Expression.eval env (shr32 10 input_var)[i.val] =
      if h : i.val + 10 < 32 then input[i.val + 10]'h else 0 :=
    fun i => eval_shr32 env input_var input h_input 10 i
  have h_r1 : ∀ i : Fin 32, env.get (i₀ + i.val) =
      input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val] := by
    intro i
    have h := h_holds1 i; rw [h_r17 i, h_r19 i] at h
    have key : env.get (i₀ + i.val) -
        (input[(i + 17).val] + input[(i + 19).val] -
          2 * input[(i + 17).val] * input[(i + 19).val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  have h_z_raw : ∀ i : Fin 32, env.get (i₀ + (32 + 32 * 0) + i.val) =
      env.get (i₀ + i.val) + Expression.eval env (shr32 10 input_var)[i.val] -
      2 * env.get (i₀ + i.val) * Expression.eval env (shr32 10 input_var)[i.val] := by
    intro i
    have h := h_holds2 i
    have key : env.get (i₀ + (32 + 32 * 0) + i.val) -
        (env.get (i₀ + i.val) + Expression.eval env (shr32 10 input_var)[i.val] -
         2 * env.get (i₀ + i.val) * Expression.eval env (shr32 10 input_var)[i.val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + (32 + 32 * 0) + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + (32 + 32 * 0) + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 17).val] + input[(i + 19).val] -
        2 * input[(i + 17).val] * input[(i + 19).val])
      + (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0)
      - 2 * (input[(i + 17).val] + input[(i + 19).val] -
              2 * input[(i + 17).val] * input[(i + 19).val])
            * (if h : i.val + 10 < 32 then input[i.val + 10]'h else 0) := by
    intro i
    rw [h_z_get i, h_z_raw i, h_r1 i, h_s10 i]
  exact spec_of_constraint input z ha h_z

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [lowerSigma1, xor32]
  obtain ⟨h_env1, h_env2, -⟩ := h_env
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hr17 := eval_rotr32 env.toEnvironment input_var input h_input 17 i
    have hr19 := eval_rotr32 env.toEnvironment input_var input h_input 19 i
    have h1 := h_env1 i
    simp only [circuit_norm, Vector.getElem_ofFn] at h1
    rw [h1, hr17, hr19]
    have b17 : input[(i + 17).val] = (0 : F p) ∨ input[(i + 17).val] = 1 := h_assumptions (i + 17)
    have b19 : input[(i + 19).val] = (0 : F p) ∨ input[(i + 19).val] = 1 := h_assumptions (i + 19)
    have hc : ((input[(i + 17).val].val ^^^ input[(i + 19).val].val : ℕ) : F p) =
        input[(i + 17).val] + input[(i + 19).val] -
          2 * input[(i + 17).val] * input[(i + 19).val] := by
      rw [← IsBool.xor_eq_val_xor b17 b19, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hc]; ring
  · have hr17 := eval_rotr32 env.toEnvironment input_var input h_input 17 i
    have hr19 := eval_rotr32 env.toEnvironment input_var input h_input 19 i
    have hs10 := eval_shr32 env.toEnvironment input_var input h_input 10 i
    have h1 := h_env1 i
    have h2 := h_env2 i
    simp only [circuit_norm, Vector.getElem_ofFn, mul_zero, zero_add] at h2
    simp only [circuit_norm, Vector.getElem_ofFn] at h1
    rw [show (i₀ + (32 + 32 * 0) + ↑i) = i₀ + 32 + ↑i from by ring, h2, h1, hr17, hr19, hs10]
    have b17 : input[(i + 17).val] = (0 : F p) ∨ input[(i + 17).val] = 1 := h_assumptions (i + 17)
    have b19 : input[(i + 19).val] = (0 : F p) ∨ input[(i + 19).val] = 1 := h_assumptions (i + 19)
    have bs10 : (if h : i.val + (10 : Fin 32).val < 32
          then (input[i.val + (10 : Fin 32).val]'h : F p) else 0) = 0 ∨
        (if h : i.val + (10 : Fin 32).val < 32
          then (input[i.val + (10 : Fin 32).val]'h : F p) else 0) = 1 :=
      shr_isbool _ input h_assumptions i
    set r17 : F p := input[(i + 17).val]
    set r19 : F p := input[(i + 19).val]
    set s10 : F p := if h : i.val + (10 : Fin 32).val < 32
      then input[i.val + (10 : Fin 32).val]'h else 0
    have hxor1 : ((r17.val ^^^ r19.val : ℕ) : F p) = r17 + r19 - 2 * r17 * r19 := by
      rw [← IsBool.xor_eq_val_xor b17 b19, ZMod.natCast_val]
      exact ZMod.cast_id p _
    have hxor1_bool : IsBool (((r17.val ^^^ r19.val : ℕ) : F p)) := by
      rw [hxor1]; exact IsBool.xor_is_bool b17 b19
    have hxor3 : (((((r17.val ^^^ r19.val : ℕ) : F p).val ^^^ s10.val) : ℕ) : F p) =
        ((r17.val ^^^ r19.val : ℕ) : F p) + s10 -
          2 * ((r17.val ^^^ r19.val : ℕ) : F p) * s10 := by
      rw [← IsBool.xor_eq_val_xor hxor1_bool bs10, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hxor3, hxor1]; ring

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end LowerSigma1
end Gadgets.SHA256
end
