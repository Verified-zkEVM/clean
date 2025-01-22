import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace PreOperation

def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => PreOperation.Witness compute :: to_flat_operations ops
    | Operation.Assert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.Lookup l => PreOperation.Lookup l :: to_flat_operations ops
    | Operation.SubCircuit circuit => circuit.ops ++ to_flat_operations ops

open Circuit (constraints_hold_from_list constraints_hold_from_context_default)

lemma constraints_hold_cons : ∀ {op : PreOperation F}, ∀ {ops: List (PreOperation F)}, ∀ {env : ℕ → F},
  constraints_hold env (op :: ops) ↔ constraints_hold env [op] ∧ constraints_hold env ops := by
  intro op ops env
  match ops with
  | [] => tauto
  | op' :: ops =>
    constructor <;> (
      rintro h
      dsimp only [constraints_hold] at h
      split at h
      <;> simp_all only [constraints_hold, and_self])

lemma constraints_hold_append : ∀ {a b: List (PreOperation F)}, ∀ {env : ℕ → F},
  constraints_hold env (a ++ b) ↔ constraints_hold env a ∧ constraints_hold env b := by
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

/--
Main soundness theorem which proves that flattened constraints imply nested constraints.

It thereby justifies relying on the nested version `Circuit.constraints_hold_from_list`,
where constraints of subcircuits are replaced with higher-level statements
that imply (or are implied by) those constraints.
-/
theorem can_replace_subcircuits : ∀ {ops: List (Operation F)}, ∀ {env : ℕ → F},
  constraints_hold env (to_flat_operations ops) → constraints_hold_from_list env ops
:= by
  intro ops env h
  -- `to_flat_operations.induct` (functional induction for `to_flat_operations`) is matching on
  -- empty vs non-empty lists, and different cases for the head in the non-empty case, at the same time.
  induction ops using to_flat_operations.induct with
  | case1 => tauto
  -- we can handle all non-empty cases except `SubCircuit` at once
  | case2 ops _ ih | case3 ops _ ih | case4 ops _ ih =>
    dsimp only [to_flat_operations] at h
    generalize to_flat_operations ops = flatops at h ih
    cases ops
    <;> cases flatops
    <;> try dsimp only [constraints_hold, constraints_hold_from_list] at h; tauto
  | case5 ops _ circuit ih =>
    dsimp only [to_flat_operations] at h
    have h_subcircuit : constraints_hold env circuit.ops := (constraints_hold_append.mp h).left
    have h_rest : constraints_hold env (to_flat_operations ops) := (constraints_hold_append.mp h).right
    cases ops
    <;> dsimp only [constraints_hold_from_list]
    <;> use (circuit.imply_soundness env) h_subcircuit
    use ih h_rest

/--
Main completeness theorem which proves that nested constraints imply flattened constraints
using the default witness generator.

This justifies only proving the nested version `Circuit.constraints_hold_from_list_default`,
where constraints of subcircuits are replaced with higher-level statements
that imply (or are implied by) those constraints.

Note: Ideally, `can_replace_subcircuits` would prove both directions, and this would be just a special
case. See https://github.com/Verified-zkEVM/clean/issues/42
-/
theorem can_replace_subcircuits_default {n: ℕ} : ∀ {ctx : Operations F n},
  constraints_hold_from_context_default ctx →
  constraints_hold ctx.default_env (to_flat_operations ctx.operations)
:= by
  intro ctx h
  -- `to_flat_operations.induct` (functional induction for `to_flat_operations`) is matching on
  -- empty vs non-empty lists, and different cases for the head in the non-empty case, at the same time.
  induction ctx using to_flat_operations.induct with
  | case1 => tauto
  -- we can handle all non-empty cases except `SubCircuit` at once
  | case2 ops _ ih | case3 ops _ ih | case4 ops _ ih =>
    dsimp only [to_flat_operations]
    generalize to_flat_operations ops = flatops at *
    <;> cases flatops
    <;> dsimp only [constraints_hold]
    <;> tauto
    <;> cases ctx
    <;> dsimp only [constraints_hold_from_list_default] at h
    <;> tauto

  | case5 ops circuit ih =>
    dsimp only [to_flat_operations]
    apply constraints_hold_append.mpr
    cases ops
    · dsimp at h
      have h := circuit.implied_by_completeness h
      use h; tauto
    dsimp only [constraints_hold_from_list_default] at h
    exact ⟨ circuit.implied_by_completeness h.left, ih h.right ⟩
end PreOperation

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

namespace Circuit
-- helper lemma: given a witness, there is some context such that the context produces the witness
lemma exists_context_of_witness {n: ℕ} (w: Witness F n) : ∃ (ctx: Operations F n), ctx.witnesses = w := by
  induction' w using Vector.induct_push with n' cs c ih
  · use Operations.empty
    rw [Operations.witnesses, Vector.nil]
  · obtain ⟨ ctx, hc ⟩ := ih
    use Operations.witness ctx c
    rw [Operations.witnesses, hc]

def formal_circuit_to_subcircuit (in_ctx: OperationsList F)
  (circuit: FormalCircuit F β α) (b_var : β.var) : α.var × SubCircuit F in_ctx.offset :=
  let n := in_ctx.offset
  let res := circuit.main b_var in_ctx
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  let out_ctx := res.1.context
  let ops := out_ctx.operations
  let a_var := res.2

  have s: SubCircuit F n := by
    open PreOperation in
    let flat_ops := to_flat_operations out_ctx.operations
    let soundness := subcircuit_soundness circuit b_var a_var
    let completeness := subcircuit_completeness (n:=n) circuit b_var
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
      exact circuit.soundness in_ctx env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env (to_flat_operations ops)
    exact PreOperation.can_replace_subcircuits h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro in_wit h_completeness

    let b := Provable.eval_env in_wit.default_env b_var
    obtain ⟨ in_ctx', h_in_ctx' ⟩ := exists_context_of_witness in_wit
    subst h_in_ctx'
    have as : circuit.assumptions b := h_completeness

    let in_wit := in_ctx'.witnesses
    let out_ctx' := (circuit.main b_var in_ctx').1.context

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness in_ctx' b b_var rfl as
    -- so we just need to go from constraints to flattened constraints
    have h_holds' : PreOperation.constraints_hold out_ctx'.default_env (to_flat_operations out_ctx'.operations)
      := can_replace_subcircuits_default h_holds
    show PreOperation.constraints_hold (in_wit.extend flat_ops).default_env (to_flat_operations out_ctx.operations)
    sorry -- TODO

  ⟨ a_var, s ⟩

def formal_assertion_to_subcircuit (ctx: OperationsList F)
  (circuit: FormalAssertion F β) (b_var : β.var) : SubCircuit F ctx.offset :=
  let res := circuit.main b_var ctx
  let ops := res.1.2

  have s: SubCircuit F ctx.offset := by
    let flat_ops := PreOperation.to_flat_operations ops
    let soundness := subassertion_soundness circuit b_var
    let completeness := subassertion_completeness circuit b_var
    use flat_ops, soundness, completenessInductiveOperations

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval_env env b_var
    rintro (as : circuit.assumptions b)
    show circuit.spec b

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: constraints_hold_from_list env ops by
      exact circuit.soundness ctx env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env (PreOperation.to_flat_operations ops)
    exact PreOperation.can_replace_subcircuits h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions and the spec are true
    intro h_completeness
    let b := Provable.eval F b_var
    have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds : constraints_hold_from_list_default ops := circuit.completeness ctx b b_var rfl as.left as.right

    -- so we just need to go from constraints to flattened constraints
    exact PreOperation.can_replace_subcircuits_default h_holds

  s
end Circuit

-- run a sub-circuit
@[simp]
def subcircuit (circuit: FormalCircuit F β α) (b: β.var) : Circuit F α.var :=
  fun ctx =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx circuit b
    (Operations.subcircuit ctx.context subcircuit, a)

@[simp]
def assertion (circuit: FormalAssertion F β) (b: β.var) : Circuit F Unit :=
  fun ctx =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ctx circuit b
    (Operations.subcircuit ctx.context subcircuit, ())
