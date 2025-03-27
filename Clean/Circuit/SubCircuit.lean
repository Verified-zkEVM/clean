import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F: Type} [Field F]

namespace FlatOperation
open Circuit (constraints_hold.completeness constraints_hold)

lemma constraints_hold_cons : ∀ {op : FlatOperation F}, ∀ {ops: List (FlatOperation F)}, ∀ {env : Environment F},
  constraints_hold_flat env (op :: ops) ↔ constraints_hold_flat env [op] ∧ constraints_hold_flat env ops := by
  intro op ops env
  constructor <;> (
    rintro h
    dsimp only [constraints_hold_flat] at h
    split at h
    <;> simp_all only [constraints_hold_flat, and_self])

lemma constraints_hold_append : ∀ {a b: List (FlatOperation F)}, ∀ {env : Environment F},
  constraints_hold_flat env (a ++ b) ↔ constraints_hold_flat env a ∧ constraints_hold_flat env b := by
  intro a b env
  induction a with
  | nil => rw [List.nil_append]; tauto
  | cons op ops ih =>
    constructor
    · intro h
      rw [List.cons_append] at h
      obtain ⟨ h_op, h_rest ⟩ := constraints_hold_cons.mp h
      obtain ⟨ h_ops, h_b ⟩ := ih.mp h_rest
      exact ⟨ constraints_hold_cons.mpr ⟨ h_op, h_ops ⟩, h_b ⟩
    · rintro ⟨ h_a, h_b ⟩
      obtain ⟨ h_op, h_ops ⟩ := constraints_hold_cons.mp h_a
      have h_rest := ih.mpr ⟨ h_ops, h_b ⟩
      exact constraints_hold_cons.mpr ⟨ h_op, h_rest ⟩
end FlatOperation

variable {α β: TypeMap} [ProvableType α] [ProvableType β]
variable {elaborated : ElaboratedCircuit F β (Var α F)} {elaborated_assertion : ElaboratedAssertion F β}

namespace Circuit
open FlatOperation (constraints_hold_append)
open Environment (env_extends_of_flat)

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem can_replace_subcircuits {n: ℕ} : ∀ {ops : Operations F n}, ∀ {env : Environment F},
  constraints_hold env ops ↔ constraints_hold_flat env (to_flat_operations ops)
:= by
  intro ops env
  induction ops with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness ops _ ih | assert ops _ ih | lookup ops _ ih | subcircuit ops _ ih =>
    dsimp only [to_flat_operations]
    rw [constraints_hold_append]
    simp_all only [constraints_hold, constraints_hold_flat, and_true]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def formal_circuit_to_subcircuit (n: ℕ)
  (circuit: FormalCircuit F β α elaborated) (b_var : Var β F) : SubCircuit F n :=
  let ops := elaborated.main b_var |>.operations n
  let flat_ops := to_flat_operations ops
  {
    ops := flat_ops,
    soundness := subcircuit_soundness circuit b_var n,
    completeness := subcircuit_completeness circuit b_var,
    local_length := elaborated.local_length b_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env h_holds
      show subcircuit_soundness circuit b_var n env

      let b : β F := eval env b_var
      let a : α F := eval env (elaborated.output b_var n)
      rintro (as : circuit.assumptions b)
      show circuit.spec b a

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: constraints_hold.soundness env ops by
        exact circuit.soundness n env b_var b rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.constraints_hold_flat env flat_ops
      apply can_replace_soundness
      exact can_replace_subcircuits.mpr h_holds

    implied_by_completeness := by
      -- we are given that the assumptions are true
      intro env h_env h_completeness

      let b := eval env b_var
      have as : circuit.assumptions b := h_completeness

      have h_env' : env.uses_local_witnesses ops := by
        guard_hyp h_env : env.extends_vector (FlatOperation.witnesses env flat_ops) n
        have hn : ops.initial_offset = n := by apply elaborated.initial_offset_eq
        rw [←hn] at h_env
        exact env_extends_of_flat h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env b_var h_env' b rfl as

      -- so we just need to go from constraints to flattened constraints
      apply can_replace_subcircuits.mp
      exact can_replace_completeness h_env' h_holds

    local_length_eq := by
      rw [← elaborated.local_length_eq b_var n]
      exact Environment.flat_witness_length_eq |>.symm
  }

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def formal_assertion_to_subcircuit (n: ℕ)
  (circuit: FormalAssertion F β elaborated_assertion) (b_var : Var β F) : SubCircuit F n :=
  let ops := elaborated_assertion.main b_var |>.operations n
  let flat_ops := to_flat_operations ops
  {
    ops := flat_ops,
    soundness := subassertion_soundness circuit b_var,
    completeness := subassertion_completeness circuit b_var,
    local_length := elaborated_assertion.local_length b_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env h_holds
      show subassertion_soundness circuit b_var env

      let b : β F := eval env b_var
      rintro (as : circuit.assumptions b)
      show circuit.spec b

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: constraints_hold.soundness env ops by
        exact circuit.soundness n env b_var b rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.constraints_hold_flat env flat_ops
      apply can_replace_soundness
      exact can_replace_subcircuits.mpr h_holds

    implied_by_completeness := by
      -- we are given that the assumptions and the spec are true
      intro env h_env h_completeness

      let b := eval env b_var
      have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

      have h_env' : env.uses_local_witnesses ops := by
        guard_hyp h_env : env.extends_vector (FlatOperation.witnesses env flat_ops) n
        have hn : ops.initial_offset = n := by apply elaborated_assertion.initial_offset_eq
        rw [←hn] at h_env
        exact env_extends_of_flat h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env b_var h_env' b rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply can_replace_subcircuits.mp
      exact can_replace_completeness h_env' h_holds

    local_length_eq := by
      rw [← elaborated_assertion.local_length_eq b_var n]
      exact Environment.flat_witness_length_eq |>.symm
  }
end Circuit

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit (circuit: FormalCircuit F β α elaborated) (b: Var β F) : Circuit F (Var α F) := do
  modifyGet (fun ops =>
    let a := elaborated.output b ops.offset
    let subcircuit := Circuit.formal_circuit_to_subcircuit ops.offset circuit b
    (a, .subcircuit ops subcircuit)
  )

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion (circuit: FormalAssertion F β elaborated_assertion) (b: Var β F) : Circuit F Unit := do
  modify (fun ops =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ops.offset circuit b
    .subcircuit ops subcircuit
  )

namespace Circuit

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_local_length_eq (circuit: FormalCircuit F β α elaborated) (input: Var β F) (offset: ℕ) :
    (formal_circuit_to_subcircuit offset circuit input).local_length
    = elaborated.local_length input := by rfl

lemma assertion_local_length_eq (circuit: FormalAssertion F β elaborated_assertion) (input: Var β F) (offset: ℕ) :
    (formal_assertion_to_subcircuit offset circuit input).local_length
    = elaborated_assertion.local_length input := by rfl
end Circuit

-- simp set to unfold subcircuits
attribute [subcircuit_norm]
  Circuit.formal_circuit_to_subcircuit Circuit.formal_assertion_to_subcircuit to_flat_operations
  Circuit.subcircuit_soundness Circuit.subcircuit_completeness
  Circuit.subassertion_soundness Circuit.subassertion_completeness

-- to just reduce offsets, it's much better to _not_ use `subcircuit_norm`
-- instead, `circuit_norm` will use these theorems to unfold subcircuits
attribute [circuit_norm]
  Circuit.subcircuit_local_length_eq Circuit.assertion_local_length_eq
