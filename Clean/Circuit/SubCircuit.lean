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

open Circuit (constraints_hold_from_list constraints_hold_inductive_completeness)

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
The witness length from flat and nested operations is the same
-/
lemma flat_witness_length_eq_witness_length {n: ℕ} {ops: Operations F n} :
  witness_length (to_flat_operations ops.toList) = ops.locals_length := by
  sorry

lemma flat_witness_length_eq_witness_length' {n: ℕ} {ops: Operations F n} :
  _root_.Witness F (witness_length (to_flat_operations ops.toList)) = _root_.Witness F ops.locals_length := by
  sorry

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {n: ℕ} {ops: Operations F n} :
  cast flat_witness_length_eq_witness_length' (witness (to_flat_operations ops.toList)) = ops.local_witnesses := by
  sorry

/--
Helper lemma: If an environment respects local witnesses, then it also does so in the flattened variant.
-/
lemma env_extends_of_flat {n: ℕ} {ops: Operations F n} {env: Environment F} :
  env.extends_vector (witness (to_flat_operations ops.toList)) ops.initial_offset →
  env.extends ops :=
  sorry

/--
Main completeness theorem which proves that nested constraints imply flattened constraints
using the default witness generator.

This justifies only proving the nested version `Circuit.constraints_hold_from_list_default`,
where constraints of subcircuits are replaced with higher-level statements
that imply (or are implied by) those constraints.

Note: Ideally, `can_replace_subcircuits` would prove both directions, and this would be just a special
case. See https://github.com/Verified-zkEVM/clean/issues/42
-/
theorem can_replace_subcircuits_default {n: ℕ} :
  ∀ {ops : Operations F n}, ∀ {env : Environment F}, env.extends ops →
  constraints_hold_inductive_completeness env ops →
  constraints_hold env (to_flat_operations ops.toList)
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
-- helper lemma: `Operations.initial_offset` is well-defined
lemma initial_offset_eq {α} {n: ℕ} {circuit: Circuit F α} :
  (circuit.from n).initial_offset = n := by sorry

def formal_circuit_to_subcircuit (n: ℕ)
  (circuit: FormalCircuit F β α) (b_var : β.var) : α.var × SubCircuit F n :=
  let res := circuit.main b_var n
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  let ops := res.1.withLength
  let a_var := res.2

  have s: SubCircuit F n := by
    open PreOperation in
    let flat_ops := to_flat_operations ops.toList
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
    suffices h: constraints_hold_from_list env ops.toList by
      exact circuit.soundness n env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env flat_ops
    exact PreOperation.can_replace_subcircuits h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions are true
    intro env h_env h_completeness

    let b := Provable.eval_env env b_var
    have as : circuit.assumptions b := h_completeness

    have h_env' : env.extends ops := by
      guard_hyp h_env : env.extends_vector (PreOperation.witness flat_ops) n
      have hn : ops.initial_offset = n := by apply initial_offset_eq
      rw [←hn] at h_env
      exact PreOperation.env_extends_of_flat h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env' b rfl as

    -- so we just need to go from constraints to flattened constraints
    exact PreOperation.can_replace_subcircuits_default h_env' h_holds

  ⟨ a_var, s ⟩

def formal_assertion_to_subcircuit (n: ℕ)
  (circuit: FormalAssertion F β) (b_var : β.var) : SubCircuit F n :=
  let res := circuit.main b_var n
  let ops := res.1.withLength

  have s: SubCircuit F n := by
    let flat_ops := PreOperation.to_flat_operations ops.toList
    let soundness := subassertion_soundness circuit b_var
    let completeness := subassertion_completeness circuit b_var
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval_env env b_var
    rintro (as : circuit.assumptions b)
    show circuit.spec b

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: constraints_hold_from_list env ops.toList by
      exact circuit.soundness n env b b_var rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : PreOperation.constraints_hold env flat_ops
    exact PreOperation.can_replace_subcircuits h_holds

    -- `implied_by_completeness`
    -- we are given that the assumptions and the spec are true
    intro env h_env h_completeness

    let b := Provable.eval_env env b_var
    have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

    have h_env' : env.extends ops := by
      guard_hyp h_env : env.extends_vector (PreOperation.witness flat_ops) n
      have hn : ops.initial_offset = n := by apply initial_offset_eq
      rw [←hn] at h_env
      exact PreOperation.env_extends_of_flat h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env' b rfl as.left as.right

    -- so we just need to go from constraints to flattened constraints
    exact PreOperation.can_replace_subcircuits_default h_env' h_holds

  s
end Circuit

-- run a sub-circuit
@[simp]
def subcircuit (circuit: FormalCircuit F β α) (b: β.var) : Circuit F α.var :=
  fun ops =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ops.offset circuit b
    (.subcircuit ops subcircuit, a)

@[simp]
def assertion (circuit: FormalAssertion F β) (b: β.var) : Circuit F Unit :=
  fun ops =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ops.offset circuit b
    (.subcircuit ops subcircuit, ())
