import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace PreOperation

def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => Witness compute :: to_flat_operations ops
    | Operation.Assert e => Assert e :: to_flat_operations ops
    | Operation.Lookup l => Lookup l :: to_flat_operations ops
    | Operation.Assign c => Assign c :: to_flat_operations ops
    | Operation.SubCircuit circuit => circuit.ops ++ to_flat_operations ops

open Circuit (constraints_hold_from_list constraints_hold_from_list_default)

/--
This theorem proves equivalence between flattened and nested constraints.

It thereby justifies relying on the nested variant `Circuit.constraints_hold_from_list`,
where constraints of subcircuits are replaced with higher-level statements
that imply (or are implied by) those constraints.
 -/
theorem can_replace_subcircuits : ∀ ops: List (Operation F), ∀ env : ℕ → F,
  constraints_hold_from_list env ops ↔ constraints_hold env (to_flat_operations ops)
:= by
  intro ops env
  induction ops using to_flat_operations.induct with
  | case1 => dsimp only [to_flat_operations]; tauto
  | case2 ops _ ih | case3 ops _ ih | case4 ops _ ih | case5 ops _ ih =>
    dsimp only [to_flat_operations]
    constructor
    <;> intro h
    <;> cases ops
    <;> generalize to_flat_operations (F:=F) _ = flatops at h ih
    <;> cases flatops
    <;> try dsimp only [constraints_hold, constraints_hold_from_list] at h; tauto
  | case6 ops _ ih =>
    sorry

theorem can_replace_subcircuits_default : ∀ ops: List (Operation F),
  constraints_hold_from_list_default ops ↔ constraints_hold_default (to_flat_operations ops)
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
    exact (PreOperation.can_replace_subcircuits ops env).mpr h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro h_completeness
    let b := Provable.eval F b_var
    have as : circuit.assumptions b := h_completeness

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds : constraints_hold_from_list_default ops := circuit.completeness ctx b b_var rfl as

    -- so we just need to go from constraints to flattened constraints
    exact (PreOperation.can_replace_subcircuits_default ops).mp h_holds

  ⟨ a_var, s ⟩
end Circuit

-- run a sub-circuit
@[simp]
def subcircuit (circuit: FormalCircuit F β α) (b: β.var) := Circuit.as_circuit (F:=F) (
  fun ctx =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx circuit b
    (Operation.SubCircuit subcircuit, a)
)
