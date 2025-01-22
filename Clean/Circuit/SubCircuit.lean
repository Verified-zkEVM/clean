import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace PreOperation

def to_flat_operations (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | .Witness compute => .Witness compute :: to_flat_operations ops
    | .Assert e => .Assert e :: to_flat_operations ops
    | .Lookup l => .Lookup l :: to_flat_operations ops
    | .SubCircuit circuit => circuit.ops ++ to_flat_operations ops

def to_flat_operations_inductive {n: ℕ} : Operations F n → List (PreOperation F)
  | .empty _ => []
  | .witness ops c => to_flat_operations_inductive ops ++ [.Witness c]
  | .assert ops c => to_flat_operations_inductive ops ++ [.Assert c]
  | .lookup ops l => to_flat_operations_inductive ops ++ [.Lookup l]
  | .subcircuit ops circuit => to_flat_operations_inductive ops ++ circuit.ops

def to_flat_operations_eq {n: ℕ} (ops: Operations F n) :
  to_flat_operations_inductive ops = to_flat_operations ops.toList := by
  sorry

open Circuit (constraints_hold_from_list constraints_hold_inductive_completeness constraints_hold_inductive)

lemma constraints_hold_cons : ∀ {op : PreOperation F}, ∀ {ops: List (PreOperation F)}, ∀ {env : Environment F},
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

lemma constraints_hold_append : ∀ {a b: List (PreOperation F)}, ∀ {env : Environment F},
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
theorem can_replace_subcircuits {n: ℕ} : ∀ {ops : Operations F n}, ∀ {env : Environment F},
  constraints_hold env (to_flat_operations ops.toList) → constraints_hold_from_list env ops.toList
:= by
  intro ops env h
  generalize ops.toList = ops at *
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
Same as the above, but for the inductive version and in the other direction
-/
-- TODO unify these, clearly all three statements are equivalent
theorem can_replace_subcircuits_inductive {n: ℕ} : ∀ {ops : Operations F n}, ∀ {env : Environment F},
  constraints_hold_inductive env ops → constraints_hold env (to_flat_operations ops.toList)
:= by
  intro ops env h
  rw [←to_flat_operations_eq ops]
  induction ops with
  | empty => trivial
  -- we can handle all non-empty cases except `SubCircuit` at once
  | witness ops _ ih | assert ops _ ih | lookup ops _ ih =>
    dsimp only [to_flat_operations_inductive]
    generalize to_flat_operations_inductive ops = flatops at *
    apply constraints_hold_append.mpr
    simp_all only [true_implies, constraints_hold, constraints_hold_inductive, and_self]
  | subcircuit ops circuit ih =>
    dsimp only [to_flat_operations_inductive]
    apply constraints_hold_append.mpr
    dsimp only [constraints_hold_inductive] at h
    exact ⟨ ih h.left, h.right ⟩

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

lemma env_extends_witness {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.extends (ops.witness c) → env.extends ops
:= by
  intro h i
  simp_all only [Environment.extends, Operations.locals_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  specialize h i
  simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h
  rw [h]
  simp [List.getElem_append]

lemma env_extends_assert {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.extends (ops.assert c) → env.extends ops := by
  intro h i; simp_all only [Environment.extends, Operations.locals_length, Operations.initial_offset, Operations.local_witnesses]

lemma env_extends_lookup {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.extends (ops.lookup c) → env.extends ops := by
  intro h i; simp_all only [Environment.extends, Operations.locals_length, Operations.initial_offset, Operations.local_witnesses]

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.extends (ops.subcircuit c) → env.extends ops
:= by
  intro h i
  simp_all only [Environment.extends, Operations.locals_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  have : i < ops.locals_length + c.witness_length := by linarith [i.is_lt]
  specialize h ⟨ i, this ⟩
  simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h
  rw [h]
  simp [List.getElem_append]

lemma total_length_eq {n: ℕ} {ops: Operations F n} : ops.initial_offset + ops.locals_length = n := by
  sorry

lemma env_extends_subcircuit_inner {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.extends (ops.subcircuit c) → env.extends_vector (witness c.ops) n
:= by
  intro h i
  simp_all only [Environment.extends, Operations.locals_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  unfold SubCircuit.witness_length at h
  have : ops.locals_length + i < ops.locals_length + witness_length c.ops := by linarith [i.is_lt]
  specialize h ⟨ ops.locals_length + i, this ⟩
  simp only [Vector.get, Vector.append, Fin.cast_mk, List.get_eq_getElem] at h
  rw [←add_assoc, total_length_eq] at h
  rw [h]
  simp [List.getElem_append, Operations.local_witnesses, SubCircuit.witness]
  -- definitely true! TODO finish
  sorry

lemma plain_of_completeness  {n: ℕ} {ops : Operations F n} {env} : env.extends ops →
  constraints_hold_inductive_completeness env ops → constraints_hold_inductive env ops := by
  intro h_env h
  induction ops with
  | empty => trivial
  | witness ops c ih | assert ops c ih | lookup ops c ih =>
    try replace h_env := env_extends_witness h_env
    try replace h_env := env_extends_assert h_env
    try replace h_env := env_extends_lookup h_env
    specialize ih h_env
    cases ops <;> simp_all [constraints_hold_inductive_completeness, constraints_hold_inductive]
  | subcircuit ops circuit ih =>
    specialize ih (env_extends_subcircuit h_env)
    dsimp only [constraints_hold_inductive_completeness] at h
    dsimp only [constraints_hold_inductive]
    split at h
    · use trivial
      exact circuit.implied_by_completeness env (env_extends_subcircuit_inner h_env) h
    · use ih h.left
      exact circuit.implied_by_completeness env (env_extends_subcircuit_inner h_env) h.right

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
  intro ops env h_env h
  exact can_replace_subcircuits_inductive (plain_of_completeness h_env h)
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

@[simp]
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
