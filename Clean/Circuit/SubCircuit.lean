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
  (circuit: FormalCircuit F β α) (b_var : Var β F) : Var α F × SubCircuit F n :=
  let res := circuit.main b_var |>.run n
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  let ops := res.snd.withLength
  let a_var := res.fst

  have s: SubCircuit F n := by
    open FlatOperation in
    let flat_ops := to_flat_operations ops
    let soundness := subcircuit_soundness circuit b_var a_var
    let completeness := subcircuit_completeness circuit b_var
    let initial_offset_eq := circuit.initial_offset_eq
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β F := eval env b_var
    let a : α F := eval env a_var
    rintro (as : circuit.assumptions b)
    show circuit.spec b a

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: constraints_hold.soundness env ops by
      exact circuit.soundness n env b_var b rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.constraints_hold_flat env flat_ops
    apply can_replace_soundness
    exact can_replace_subcircuits.mpr h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro env h_env h_completeness

    let b := eval env b_var
    have as : circuit.assumptions b := h_completeness

    have h_env' : env.uses_local_witnesses ops := by
      guard_hyp h_env : env.extends_vector (FlatOperation.witnesses env flat_ops) n
      have hn : ops.initial_offset = n := by apply initial_offset_eq
      rw [←hn] at h_env
      exact env_extends_of_flat h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env' b rfl as

    -- so we just need to go from constraints to flattened constraints
    apply can_replace_subcircuits.mp
    exact can_replace_completeness h_env' h_holds

  ⟨ a_var, s ⟩

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def formal_assertion_to_subcircuit (n: ℕ)
  (circuit: FormalAssertion F β) (b_var : Var β F) : SubCircuit F n :=
  let res := circuit.main b_var |>.run n
  let ops := res.snd.withLength

  have s: SubCircuit F n := by
    open FlatOperation in
    let flat_ops := to_flat_operations ops
    let soundness := subassertion_soundness circuit b_var
    let completeness := subassertion_completeness circuit b_var
    let initial_offset_eq := circuit.initial_offset_eq
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

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

    -- `implied_by_completeness`
    -- we are given that the assumptions and the spec are true
    intro env h_env h_completeness

    let b := eval env b_var
    have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

    have h_env' : env.uses_local_witnesses ops := by
      guard_hyp h_env : env.extends_vector (FlatOperation.witnesses env flat_ops) n
      have hn : ops.initial_offset = n := by apply initial_offset_eq
      rw [←hn] at h_env
      exact env_extends_of_flat h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env' b rfl as.left as.right

    -- so we just need to go from constraints to flattened constraints
    apply can_replace_subcircuits.mp
    exact can_replace_completeness h_env' h_holds

  s
end Circuit

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit (circuit: FormalCircuit F β α) (b: Var β F) : Circuit F (Var α F) := do
  modifyGet (fun ops =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ops.offset circuit b
    (a, .subcircuit ops subcircuit)
  )

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion (circuit: FormalAssertion F β) (b: Var β F) : Circuit F Unit := do
  modifyGet (fun ops =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ops.offset circuit b
    ((), .subcircuit ops subcircuit)
  )

-- UNUSED STUFF BELOW

namespace FlatOperation
open Circuit (constraints_hold_from_list.soundness )

def to_flat_operations_from_list (ops: List (Operation F)) : List (FlatOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | .witness m compute => witness m compute :: to_flat_operations_from_list ops
    | .assert e => assert e :: to_flat_operations_from_list ops
    | .lookup l => lookup l :: to_flat_operations_from_list ops
    | .subcircuit circuit => circuit.ops ++ to_flat_operations_from_list ops

@[deprecated "Use `can_replace_subcircuits` instead"]
theorem can_replace_subcircuits_from_list {n: ℕ} : ∀ {ops : Operations F n}, ∀ {env : Environment F},
  constraints_hold_flat env (to_flat_operations_from_list ops.toList) → constraints_hold_from_list.soundness env ops.toList
:= by
  intro ops env h
  generalize ops.toList = ops at *
  -- `to_flat_operations.induct` (functional induction for `to_flat_operations`) is matching on
  -- empty vs non-empty lists, and different cases for the head in the non-empty case, at the same time.
  induction ops using to_flat_operations_from_list.induct with
  | case1 => tauto
  -- we can handle all non-empty cases except `SubCircuit` at once
  | case2 ops _ ih | case3 ops _ ih | case4 ops _ ih =>
    dsimp only [to_flat_operations_from_list] at h
    cases ops
    <;> try dsimp only [constraints_hold_flat, constraints_hold_from_list.soundness] at h; tauto
  | case5 ops _ circuit ih =>
    dsimp only [to_flat_operations_from_list] at h
    have h_subcircuit : constraints_hold_flat env circuit.ops := (constraints_hold_append.mp h).left
    have h_rest : constraints_hold_flat env (to_flat_operations_from_list ops) := (constraints_hold_append.mp h).right
    cases ops
    <;> dsimp only [constraints_hold_from_list.soundness]
    <;> use (circuit.imply_soundness env) h_subcircuit
    use ih h_rest
end FlatOperation
