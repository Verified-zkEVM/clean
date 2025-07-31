import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZero

variable {p : ℕ} [Fact p.Prime]

/--
Main circuit that checks if a field element is zero.
Returns 1 if the input is 0, otherwise returns 0.
-/
def main (x : Var field (F p)) : Circuit (F p) (Var field (F p)) := do
  let isZero ← witness fun env => if x.eval env = 0 then (1 : F p) else 0

  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let x_inv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F p)⁻¹

  isZero * x === 0  -- If isZero = 1, then x must be 0
  isZero * (isZero - 1) === 0  -- isZero must be boolean (0 or 1)

  -- If isZero = 0 (i.e., x ≠ 0), then x * x_inv = 1, so x is non-zero
  (1 - isZero) * x * x_inv === (1 - isZero)

  return isZero

instance elaborated : ElaboratedCircuit (F p) field field where
  main := main
  localLength _ := 2  -- 2 witnesses: isZero and x_inv

def Assumptions (_ : F p) : Prop := True

def Spec (x : F p) (output : F p) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro offset env x_var x h_eval h_assumptions h_holds
  simp only [main, circuit_norm] at h_holds
  obtain ⟨h_constraint1, h_constraint2, h_constraint3⟩ := h_holds

  -- h_constraint1: isZero * x = 0
  -- h_constraint2: isZero * (isZero - 1) = 0
  -- h_constraint3: (1 - isZero) * x * x_inv = (1 - isZero)

  simp only [Spec]

  -- From h_constraint2, we know isZero = 0 or isZero = 1
  have h_bool : env.get offset = 0 ∨ env.get offset = 1 := by
    -- h_constraint2: env.get offset * (env.get offset + -1) = 0
    -- This means env.get offset * (env.get offset - 1) = 0
    have h : env.get offset * (env.get offset - 1) = 0 := by
      convert h_constraint2 using 2
      ring
    -- So either env.get offset = 0 or env.get offset - 1 = 0
    cases' mul_eq_zero.mp h with h h
    · left; exact h
    · right; exact sub_eq_zero.mp h

  -- Case split on whether x = 0
  by_cases hx : x = 0
  · -- Case: x = 0
    cases h_bool with
    | inl h0 =>
      -- If isZero = 0 and x = 0, then from h_constraint3:
      -- (1 - 0) * 0 * x_inv = (1 - 0)
      -- 1 * 0 * x_inv = 1
      -- 0 = 1, which is a contradiction
      exfalso
      rw [h0] at h_constraint3
      simp only [circuit_norm] at h_constraint3 h_eval
      simp only [h_eval, hx] at h_constraint3
      ring_nf at h_constraint3
      simp_all
    | inr h1 =>
      simp [circuit_norm, main, h1, hx]

  · -- Case: x ≠ 0
    simp [hx]
    -- We need to prove that isZero = 0
    cases h_bool with
    | inl h0 => exact h0
    | inr h1 =>
      -- If isZero = 1, then from h_constraint1: 1 * x = 0, so x = 0
      -- But we have x ≠ 0, contradiction
      exfalso
      rw [h1] at h_constraint1
      -- h_constraint1 becomes: 1 * Expression.eval env x_var = 0
      simp only [one_mul] at h_constraint1
      simp only [circuit_norm] at h_constraint1 h_eval
      simp only [h_eval] at h_constraint1
      simp only [h_constraint1] at hx
      trivial

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env x_var h_env_uses x h_eval h_assumptions
  simp only [main, circuit_norm]

  -- Extract witness values from h_env_uses
  have h_uses : env.UsesLocalWitnessesCompleteness offset (main x_var (offset)).2 := by
    simp only [elaborated, ElaboratedCircuit.main] at h_env_uses
    exact h_env_uses
  simp only [main, circuit_norm] at h_uses
  obtain ⟨h_wit_isZero, h_wit_x_inv⟩ := h_uses

  -- The witnesses are exactly as specified
  simp [h_eval] at h_wit_isZero h_wit_x_inv

  refine ⟨?_, ?_, ?_⟩
  · -- First constraint: isZero * x = 0
    rw [h_wit_isZero]
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  · -- Second constraint: isZero * (isZero - 1) = 0
    rw [h_wit_isZero]
    by_cases hx : x = 0
    · simp only [circuit_norm] at h_eval ⊢
      simp only [h_eval]
      simp [hx]
    · simp only [circuit_norm] at h_eval ⊢
      simp only [h_eval]
      simp [hx]
  · -- Third constraint: (1 - isZero) * x * x_inv = (1 - isZero)
    simp only [circuit_norm] at h_eval ⊢
    simp only [h_eval]
    rw [h_wit_isZero, h_wit_x_inv]
    by_cases hx : x = 0
    · simp only [h_eval]
      simp [hx]
    · simp only [h_eval]
      simp [hx]

def circuit : FormalCircuit (F p) field field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZero
