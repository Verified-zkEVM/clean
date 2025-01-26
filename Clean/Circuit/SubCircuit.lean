import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace FlatOperation

def to_flat_operations {n: ℕ} : Operations F n → List (FlatOperation F)
  | .empty _ => []
  | .witness ops c => to_flat_operations ops ++ [witness c]
  | .assert ops c => to_flat_operations ops ++ [assert c]
  | .lookup ops l => to_flat_operations ops ++ [lookup l]
  | .subcircuit ops circuit => to_flat_operations ops ++ circuit.ops

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
Soundness theorem which proves that we can replace constraints in subcircuits
with their `soundness` statement.

Together with `can_replace_subcircuits`, it justifies assuming the nested version
`constraints_hold.soundness` when defining soundness for formal circuits,
because it is implied by the flat version.
-/
theorem can_replace_soundness  {n: ℕ} {ops : Operations F n} {env} :
  constraints_hold env ops → constraints_hold.soundness env ops := by
  intro h
  induction ops with
  | empty => trivial
  | witness ops c ih | assert ops c ih | lookup ops c ih =>
    cases ops <;> simp_all [constraints_hold.completeness, constraints_hold]
  | subcircuit ops circuit ih =>
    dsimp only [constraints_hold.soundness]
    dsimp only [constraints_hold] at h
    split
    · exact circuit.imply_soundness env h.right
    · exact ⟨ ih h.left, circuit.imply_soundness env h.right ⟩

/--
The witness length from flat and nested operations is the same
-/
lemma flat_witness_length_eq {n: ℕ} {ops: Operations F n} :
  witness_length (to_flat_operations ops) = ops.local_length := by
  induction ops with
  | empty => trivial
  | witness ops c ih | assert ops c ih | lookup ops c ih | subcircuit ops _ ih =>
    dsimp [to_flat_operations, Operations.local_length]
    generalize to_flat_operations ops = flat_ops at *
    generalize ops.local_length = n at *
    induction flat_ops using witness_length.induct generalizing n with
    | case1 => simp_all only [witness_length, List.nil_append, self_eq_add_left]
    | case2 env ops ih' =>
      dsimp only [witness_length] at *
      specialize ih' (n - 1) (Eq.symm <| Nat.pred_eq_of_eq_succ (Eq.symm ih))
      show witness_length (ops ++ _) + 1 = _
      omega
    | case3 env ops ih' =>
      simp_all only [imp_false, forall_eq', witness_length, List.cons_append]

lemma witnesses_append {F} {a b: List (FlatOperation F)} :
  (witnesses (a ++ b)).val = (witnesses a).val ++ (witnesses b).val := by
  induction a using witnesses.induct with
  | case1 => simp only [List.nil_append, witnesses]
  | case2 _ _ ih | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, List.append_eq, ih]

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {n: ℕ} {ops: Operations F n} :
  (witnesses (to_flat_operations ops)).val = ops.local_witnesses.val := by
  induction ops with
  | empty => trivial
  | witness ops c ih | assert ops c ih | lookup ops c ih | subcircuit ops _ ih =>
    dsimp [to_flat_operations, Operations.local_length]
    rw [←ih, witnesses_append]
    try simp only [witness_length, Nat.reduceAdd, witnesses, List.append_nil]

/--
Helper lemma: If an environment respects local witnesses, then it also does so in the flattened variant.
-/
lemma env_extends_of_flat {n: ℕ} {ops: Operations F n} {env: Environment F} :
  env.extends_vector (witnesses (to_flat_operations ops)) ops.initial_offset →
  env.uses_local_witnesses ops := by
  sorry

lemma env_extends_witness {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses (ops.witness c) → env.uses_local_witnesses ops
:= by
  intro h i
  simp_all only [Environment.uses_local_witnesses, Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  specialize h i
  simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h
  rw [h]
  simp [List.getElem_append]

lemma env_extends_assert {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses (ops.assert c) → env.uses_local_witnesses ops := by
  intro h i; simp_all only [Environment.uses_local_witnesses, Operations.local_length, Operations.initial_offset, Operations.local_witnesses]

lemma env_extends_lookup {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses (ops.lookup c) → env.uses_local_witnesses ops := by
  intro h i; simp_all only [Environment.uses_local_witnesses, Operations.local_length, Operations.initial_offset, Operations.local_witnesses]

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses (ops.subcircuit c) → env.uses_local_witnesses ops
:= by
  intro h i
  simp_all only [Environment.uses_local_witnesses, Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  have : i < ops.local_length + c.witness_length := by linarith [i.is_lt]
  specialize h ⟨ i, this ⟩
  simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h
  rw [h]
  simp [List.getElem_append]

lemma total_length_eq {n: ℕ} {ops: Operations F n} : ops.initial_offset + ops.local_length = n := by
  open Operations (initial_offset local_length) in
  induction ops with
  | empty n => simp only [initial_offset, local_length, add_zero]
  | witness ops _ ih | subcircuit ops s ih =>
    dsimp only [initial_offset, local_length]
    rw [←add_assoc, ih]
  | assert ops _ ih | lookup op _ ih =>
    simp only [initial_offset, local_length, ih]

lemma env_extends_subcircuit_inner {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses (ops.subcircuit c) → env.extends_vector (witnesses c.ops) n
:= by
  intro h i
  simp_all only [Environment.uses_local_witnesses, Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  unfold SubCircuit.witness_length at h
  have : ops.local_length + i < ops.local_length + witness_length c.ops := by linarith [i.is_lt]
  specialize h ⟨ ops.local_length + i, this ⟩
  simp only [Vector.get, Vector.append, Fin.cast_mk, List.get_eq_getElem] at h
  rw [←add_assoc, total_length_eq] at h
  rw [h]
  simp [List.getElem_append, Operations.local_witnesses, SubCircuit.witnesses]
  -- definitely true! TODO finish
  sorry

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness  {n: ℕ} {ops : Operations F n} {env} : env.uses_local_witnesses ops →
  constraints_hold.completeness env ops → constraints_hold env ops := by
  intro h_env h
  induction ops with
  | empty => trivial
  | witness ops c ih | assert ops c ih | lookup ops c ih =>
    try replace h_env := env_extends_witness h_env
    try replace h_env := env_extends_assert h_env
    try replace h_env := env_extends_lookup h_env
    specialize ih h_env
    cases ops <;> simp_all [constraints_hold.completeness, constraints_hold]
  | subcircuit ops circuit ih =>
    specialize ih (env_extends_subcircuit h_env)
    dsimp only [constraints_hold.completeness] at h
    dsimp only [constraints_hold]
    split at h
    · use trivial
      exact circuit.implied_by_completeness env (env_extends_subcircuit_inner h_env) h
    · use ih h.left
      exact circuit.implied_by_completeness env (env_extends_subcircuit_inner h_env) h.right
end FlatOperation

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
    open FlatOperation in
    let flat_ops := to_flat_operations ops
    let soundness := subcircuit_soundness circuit b_var a_var
    let completeness := subcircuit_completeness circuit b_var
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval env b_var
    let a : α.value := Provable.eval env a_var
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

    let b := Provable.eval env b_var
    have as : circuit.assumptions b := h_completeness

    have h_env' : env.uses_local_witnesses ops := by
      guard_hyp h_env : env.extends_vector (FlatOperation.witnesses flat_ops) n
      have hn : ops.initial_offset = n := by apply initial_offset_eq
      rw [←hn] at h_env
      exact env_extends_of_flat h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env b_var h_env' b rfl as

    -- so we just need to go from constraints to flattened constraints
    apply can_replace_subcircuits.mp
    exact can_replace_completeness h_env' h_holds

  ⟨ a_var, s ⟩

@[simp]
def formal_assertion_to_subcircuit (n: ℕ)
  (circuit: FormalAssertion F β) (b_var : β.var) : SubCircuit F n :=
  let res := circuit.main b_var n
  let ops := res.1.withLength

  have s: SubCircuit F n := by
    open FlatOperation in
    let flat_ops := to_flat_operations ops
    let soundness := subassertion_soundness circuit b_var
    let completeness := subassertion_completeness circuit b_var
    use flat_ops, soundness, completeness

    -- `imply_soundness`
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env h_holds
    show soundness env

    let b : β.value := Provable.eval env b_var
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

    let b := Provable.eval env b_var
    have as : circuit.assumptions b ∧ circuit.spec b := h_completeness

    have h_env' : env.uses_local_witnesses ops := by
      guard_hyp h_env : env.extends_vector (FlatOperation.witnesses flat_ops) n
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


-- UNUSED STUFF BELOW

namespace FlatOperation
open Circuit (constraints_hold_from_list.soundness )

def to_flat_operations_from_list (ops: List (Operation F)) : List (FlatOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | .witness compute => witness compute :: to_flat_operations_from_list ops
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
