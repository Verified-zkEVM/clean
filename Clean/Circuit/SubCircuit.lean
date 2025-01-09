import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace PreOperation
-- in the following, we prove equivalence between flattened and nested constraints

def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => PreOperation.Witness compute :: to_flat_operations ops
    | Operation.Assert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.Lookup l => PreOperation.Lookup l :: to_flat_operations ops
    | Operation.Assign (c, v) => PreOperation.Assign (c, v) :: to_flat_operations ops
    | Operation.SubCircuit circuit => circuit.ops ++ to_flat_operations ops

-- TODO super painful, mainly because `cases` doesn't allow rich patterns -- how does this work again?
theorem can_flatten_first : ∀ (env: ℕ → F) (ops: List (Operation F)),
  PreOperation.constraints_hold env (to_flat_operations ops)
  → Circuit.constraints_hold_from_list env ops
:= by
  intro env ops
  induction ops with
  | nil => intro h; exact h
  | cons op ops ih =>
    cases ops with
    | nil =>
      simp at ih
      cases op with
      | SubCircuit c =>
        sorry
      | _ => simp [PreOperation.constraints_hold]
    | cons op' ops' =>
      let ops := op' :: ops'
      cases op with
      | SubCircuit c => sorry
      | Assert e => sorry
      | Witness c =>
        have h_ops : to_flat_operations (Operation.Witness c :: op' :: ops') = PreOperation.Witness c :: to_flat_operations (op' :: ops') := rfl
        rw [h_ops]
        intro h_pre
        have h1 : PreOperation.constraints_hold env (to_flat_operations (op' :: ops')) := by
          rw [PreOperation.constraints_hold] at h_pre
          · exact h_pre
          · sorry
          · simp
          · simp
        have ih1 := ih h1
        simp [ih1]
      | Lookup l => sorry
      | Assign a => sorry

theorem can_flatten : ∀ (ops: List (Operation F)),
  Circuit.constraints_hold_from_list_default ops →
  PreOperation.constraints_hold_default (to_flat_operations ops)
:= by
 sorry
end PreOperation

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

namespace Circuit
def formal_circuit_to_subcircuit (ctx: Context F)
  (circuit: FormalCircuit F β α) (b_var : β.var) : α.var × SubCircuit F :=
  let res := circuit.main b_var ctx
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  -- let ((_, ops), a_var) := res
  let ops := res.1.2
  let a_var := res.2

  have s: SubCircuit F := by
    let flat_ops := PreOperation.to_flat_operations ops
    let soundness := subcircuit_soundness circuit b_var a_var
    let completeness := subcircuit_completeness circuit b_var
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval_env env b_var
    let a : α.value := Provable.eval_env env a_var
    rintro (as : circuit.assumptions b)
    show circuit.spec b a

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: constraints_hold_from_list env ops by
      exact circuit.soundness ctx env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env (PreOperation.to_flat_operations ops)
    exact PreOperation.can_flatten_first env ops h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro h_completeness
    let b := Provable.eval F b_var
    have as : circuit.assumptions b := h_completeness

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds : constraints_hold_from_list_default ops := circuit.completeness ctx b b_var rfl as

    -- so we just need to go from constraints to flattened constraints
    exact PreOperation.can_flatten ops h_holds

  ⟨ a_var, s ⟩
end Circuit

-- run a sub-circuit
@[simp]
def subcircuit (circuit: Circuit.FormalCircuit F β α) (b: β.var) := Circuit.as_circuit (F:=F) (
  fun ctx =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx circuit b
    (Operation.SubCircuit subcircuit, a)
)
