import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Gadgets.IsZero
import Clean.Utils.Tactics

namespace Gadgets.IsZeroU32

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Main circuit that checks if a U32 is zero.
Returns 1 if all limbs are 0, otherwise returns 0.
Uses the fact that if any limb is non-zero, the product of all "isZero" flags will be 0.
-/
def main (x : Var U32 (F p)) : Circuit (F p) (Var field (F p)) := do
  
  -- For each limb, compute isZero flag (1 if limb = 0, 0 otherwise)
  let isZero0 ← IsZero.circuit x.x0
  let isZero1 ← IsZero.circuit x.x1
  let isZero2 ← IsZero.circuit x.x2
  let isZero3 ← IsZero.circuit x.x3
  
  -- Multiply all flags - result is 1 only if all limbs are 0
  let result ← witness fun env => 
    isZero0.eval env * isZero1.eval env * isZero2.eval env * isZero3.eval env
  
  -- Add constraints to ensure the witness is correct
  result === isZero0 * isZero1 * isZero2 * isZero3
  
  return result

instance elaborated : ElaboratedCircuit (F p) U32 field where
  main := main
  localLength _ := 5  -- 4 isZero witnesses + 1 result witness

def Assumptions (x : U32 (F p)) : Prop :=
  x.Normalized

def Spec (x : U32 (F p)) (output : F p) : Prop :=
  output = if x.value = 0 then 1 else 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro offset env x_var x h_eval h_assumptions h_holds
  simp only [Assumptions] at h_assumptions
  simp only [main, circuit_norm] at h_holds
  obtain ⟨h_isZero0, h_isZero1, h_isZero2, h_isZero3, h_result⟩ := h_holds
  
  -- Extract the isZero constraint facts
  simp only [circuit_norm] at h_isZero0 h_isZero1 h_isZero2 h_isZero3
  
  -- The result constraint
  simp only [h_eval] at h_result
  
  -- Prove the spec
  simp only [Spec]
  
  -- Case split on whether x.value = 0
  by_cases h : x.value = 0
  · -- Case: x.value = 0, so all limbs must be 0
    simp [h]
    have h_limbs : x.x0 = 0 ∧ x.x1 = 0 ∧ x.x2 = 0 ∧ x.x3 = 0 := by
      rw [U32.value_eq_zero_iff] at h
      exact h
    obtain ⟨h0, h1, h2, h3⟩ := h_limbs
    
    -- Each isZero should be 1
    have hz0 : env.get (offset + 0) = 1 := by
      rw [←h_isZero0, h_eval, h0]
      simp [isZero_spec]
    have hz1 : env.get (offset + 1) = 1 := by
      rw [←h_isZero1, h_eval, h1]
      simp [isZero_spec]
    have hz2 : env.get (offset + 1 + 1) = 1 := by
      rw [←h_isZero2, h_eval, h2]
      simp [isZero_spec]
    have hz3 : env.get (offset + 1 + 1 + 1) = 1 := by
      rw [←h_isZero3, h_eval, h3]
      simp [isZero_spec]
    
    -- Therefore result = 1 * 1 * 1 * 1 = 1
    rw [←h_result, hz0, hz1, hz2, hz3]
    simp
    
  · -- Case: x.value ≠ 0, so at least one limb is non-zero
    simp [h]
    have h_limbs : x.x0 ≠ 0 ∨ x.x1 ≠ 0 ∨ x.x2 ≠ 0 ∨ x.x3 ≠ 0 := by
      rw [U32.value_ne_zero_iff] at h
      exact h
    
    -- At least one isZero is 0, so the product is 0
    rw [←h_result]
    cases h_limbs with
    | inl h0 =>
      have hz0 : env.get offset = 0 := by
        rw [←h_isZero0, h_eval]
        simp [isZero_spec, h0]
      simp [hz0]
    | inr h_rest =>
      cases h_rest with
      | inl h1 =>
        have hz1 : env.get (offset + 1) = 0 := by
          rw [←h_isZero1, h_eval]
          simp [isZero_spec, h1]
        simp [hz1]
      | inr h_rest =>
        cases h_rest with
        | inl h2 =>
          have hz2 : env.get (offset + 1 + 1) = 0 := by
            rw [←h_isZero2, h_eval]
            simp [isZero_spec, h2]
          simp [hz2]
        | inr h3 =>
          have hz3 : env.get (offset + 1 + 1 + 1) = 0 := by
            rw [←h_isZero3, h_eval]
            simp [isZero_spec, h3]
          simp [hz3]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env x_var h_env_uses x h_eval h_assumptions
  simp only [Assumptions] at h_assumptions
  simp only [main, circuit_norm]
  
  -- Extract witness values from h_env_uses
  have h_uses : env.UsesLocalWitnessesCompleteness offset (main x_var (offset)).2 := by
    simp only [elaborated, ElaboratedCircuit.main] at h_env_uses
    exact h_env_uses
  simp only [main, circuit_norm] at h_uses
  obtain ⟨h_wit0, h_wit1, h_wit2, h_wit3, h_wit_result⟩ := h_uses
  
  -- The witnesses are exactly what the constraints require
  refine ⟨?_, ?_, ?_, ?_, h_wit_result⟩
  · simp [isZero_equation, h_eval] at h_wit0; exact h_wit0
  · simp [isZero_equation, h_eval] at h_wit1; exact h_wit1
  · simp [isZero_equation, h_eval] at h_wit2; exact h_wit2
  · simp [isZero_equation, h_eval] at h_wit3; exact h_wit3

def circuit : FormalCircuit (F p) U32 field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZeroU32