/-
This file contains theorems that immediately follow from the definitions in `Circuit.Basic`.

For more complicated interconnected theorems, we have separate files,
such as `Circuit.SubCircuit` which focuses on establishing the foundation for subcircuit composition.
-/
import Clean.Circuit.Basic

variable {F: Type} [Field F]

namespace Circuit
/--
Soundness theorem which proves that we can replace constraints in subcircuits
with their `soundness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies assuming the nested version
`constraints_hold.soundness` when defining soundness for formal circuits,
because it is implied by the flat version.
-/
theorem can_replace_soundness  {n: ℕ} {ops : Operations F n} {env} :
  constraints_hold env ops → constraints_hold.soundness env ops := by
  intro h
  induction ops with
  | empty => trivial
  | witness ops _ c ih | assert ops c ih | lookup ops c ih =>
    cases ops <;> simp_all [constraints_hold.completeness, constraints_hold, circuit_norm]
  | subcircuit ops circuit ih =>
    dsimp only [constraints_hold.soundness]
    dsimp only [constraints_hold] at h
    split
    · exact circuit.imply_soundness env h.right
    · exact ⟨ ih h.left, circuit.imply_soundness env h.right ⟩

/--
Initial offset + size of local witnesses = final offset of a circuit
-/
lemma total_length_eq {n: ℕ} {ops: Operations F n} : ops.initial_offset + ops.local_length = n := by
  open Operations (initial_offset local_length) in
  induction ops with
  | empty n => simp only [initial_offset, local_length, add_zero]
  | witness ops _ _ ih | subcircuit ops s ih =>
    dsimp only [initial_offset, local_length]
    rw [←add_assoc, ih]
  | assert ops _ ih | lookup op _ ih =>
    simp only [initial_offset, local_length, ih]

end Circuit

namespace Environment
open FlatOperation (witness_length witnesses)
/-
what follows are relationships between different ways of deriving local witness generators,
and between different versions of `Environment.uses_local_witnesses`
-/

/--
The witness length from flat and nested operations is the same
-/
lemma flat_witness_length_eq {n: ℕ} {ops: Operations F n} :
  witness_length (to_flat_operations ops) = ops.local_length := by
  induction ops with
  | empty => trivial
  | witness ops m c ih | assert ops c ih | lookup ops c ih | subcircuit ops _ ih =>
    dsimp only [to_flat_operations, Operations.local_length]
    generalize to_flat_operations ops = flat_ops at *
    generalize ops.local_length = n at *
    induction flat_ops using FlatOperation.witness_length.induct generalizing n with
    | case1 =>  simp_all only [witness_length, List.nil_append, self_eq_add_left, SubCircuit.local_length_eq]
    | case2 ops m' _ ih' =>
      dsimp only [witness_length] at *
      specialize ih' (n - m') (by rw [←ih]; omega)
      show witness_length (ops ++ _) + m' = _
      omega
    | case3 ops _ ih' | case4 ops _ ih' =>
      simp_all only [forall_eq', witness_length, List.cons_append]

lemma witnesses_append {F} {a b: List (FlatOperation F)} {env} :
  (witnesses env (a ++ b)).toArray = (witnesses env a).toArray ++ (witnesses env b).toArray := by
  induction a using FlatOperation.witness_length.induct with
  | case1 => simp only [List.nil_append, witness_length, witnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, ih, Vector.mk_toArray]

lemma subcircuit_witness_eq {n: ℕ} (sc : SubCircuit F n) {env} :
    (sc.witnesses env).toArray = (FlatOperation.witnesses env sc.ops).toArray := by
  unfold SubCircuit.witnesses
  congr
  exact sc.local_length_eq
  simp only [eqRec_heq_iff_heq, heq_eq_eq]

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {n: ℕ} {ops: Operations F n} {env} :
  (witnesses env (to_flat_operations ops)).toArray = (ops.local_witnesses env).toArray := by
  induction ops with
  | empty => trivial
  | witness ops m c ih | assert ops c ih | lookup ops c ih | subcircuit ops _ ih =>
    simp only [to_flat_operations, Operations.local_length, Operations.local_witnesses, Vector.toArray_append]
    rw [←ih, witnesses_append]
    try simp only [witness_length, witnesses, Vector.toArray_empty, Array.append_empty, subcircuit_witness_eq]

/-- equivalent, non-inductive statement of `Environment.uses_local_witnesses` (that is harder to unfold for a circuit) -/
def uses_local_witnesses' (env: Environment F) {n} (ops: Operations F n) :=
  env.extends_vector (ops.local_witnesses env) ops.initial_offset

/--
Helper lemma: An environment respects local witnesses if it does so in the flattened variant.
-/
lemma env_extends_of_flat {n: ℕ} {ops: Operations F n} {env: Environment F} :
    env.extends_vector (witnesses env (to_flat_operations ops)) ops.initial_offset →
    env.uses_local_witnesses' ops := by
  simp only [uses_local_witnesses', extends_vector, Vector.get, flat_witness_eq_witness]
  intro h i
  exact h ⟨ i, by rw [flat_witness_length_eq]; exact i.is_lt ⟩

lemma env_extends_witness {n: ℕ} {ops: Operations F n} {env: Environment F} {m c} :
    env.uses_local_witnesses' (ops.witness m c) → env.uses_local_witnesses' ops := by
  intro h i
  simp_all only [uses_local_witnesses', Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  specialize h ⟨ i, by omega ⟩
  simp only [Fin.coe_cast, Fin.cast_mk] at h
  rw [h]
  simp [Vector.get, Vector.append, Array.getElem_append]

lemma env_extends_witness_inner {n: ℕ} {ops: Operations F n} {env: Environment F} {m c} :
    env.uses_local_witnesses' (ops.witness m c) → env.extends_vector (c env) n := by
  intro h i
  simp only [uses_local_witnesses', extends_vector, circuit_norm] at h
  specialize h ⟨ ops.local_length + i, by linarith [i.is_lt] ⟩
  simp only at h
  rw [←add_assoc, Circuit.total_length_eq] at h
  rw [h, Vector.getElem_append]
  simp

lemma env_extends_assert {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
    env.uses_local_witnesses' (ops.assert c) → env.uses_local_witnesses' ops := by
  intro h i; simp_all only [uses_local_witnesses', extends_vector, circuit_norm]

lemma env_extends_lookup {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
    env.uses_local_witnesses' (ops.lookup c) → env.uses_local_witnesses' ops := by
  intro h i; simp_all only [uses_local_witnesses', extends_vector, circuit_norm]

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
    env.uses_local_witnesses' (ops.subcircuit c) → env.uses_local_witnesses' ops := by
  intro h i
  simp_all only [uses_local_witnesses', Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  have : i < ops.local_length + c.local_length := by linarith [i.is_lt]
  specialize h ⟨ i, this ⟩
  simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at h
  rw [h]
  simp [Vector.get, Vector.append, Array.getElem_append]

lemma env_extends_subcircuit_inner {n: ℕ} {ops: Operations F n} {env: Environment F} {c} :
  env.uses_local_witnesses' (ops.subcircuit c) → env.extends_vector (witnesses env c.ops) n
:= by
  intro h i
  simp_all only [uses_local_witnesses', Operations.local_length, Operations.initial_offset, Operations.local_witnesses, Vector.push]
  have : ops.local_length + i < ops.local_length + c.local_length := by rw [c.local_length_eq]; linarith [i.is_lt]
  specialize h ⟨ ops.local_length + i, this ⟩
  simp only [Vector.get, Vector.append, Fin.cast_mk, List.get_eq_getElem] at h
  rw [←add_assoc, Circuit.total_length_eq] at h
  rw [h]
  simp only [SubCircuit.witnesses, Vector.get, List.get_eq_getElem, Fin.coe_cast]
  have lt1 : i < (witnesses env c.ops).toArray.size := by rw [(witnesses env c.ops).size_toArray]; exact i.is_lt
  rw [Array.getElem_append_right' (ops.local_witnesses env).toArray lt1]
  simp [Nat.add_comm, subcircuit_witness_eq]

lemma extends_vector_subcircuit (env : Environment F) {n} {circuit : SubCircuit F n} :
    env.extends_vector (circuit.witnesses env) n = env.extends_vector (FlatOperation.witnesses env circuit.ops) n := by
  have h_length : circuit.local_length = FlatOperation.witness_length circuit.ops := circuit.local_length_eq
  congr
  simp [SubCircuit.witnesses]

theorem can_replace_local_witnesses {env: Environment F} {n: ℕ} {ops: Operations F n}  :
  env.uses_local_witnesses' ops → env.uses_local_witnesses ops := by
  intro h
  induction ops with
  | empty => trivial
  | assert ops _ ih | lookup ops _ ih => simp_all [uses_local_witnesses', uses_local_witnesses, circuit_norm]
  | witness ops m _ ih =>
    exact ⟨ ih (env_extends_witness h), env_extends_witness_inner h ⟩
  | subcircuit ops circuit ih =>
    use ih (env_extends_subcircuit h)
    rw [extends_vector_subcircuit]
    exact env_extends_subcircuit_inner h

theorem can_replace_local_witnesses_completeness {env: Environment F} {n: ℕ} {ops: Operations F n}  :
  env.uses_local_witnesses ops → env.uses_local_witnesses_completeness ops := by
  intro h
  induction ops with
  | empty => trivial
  | witness | assert | lookup => simp_all [uses_local_witnesses, uses_local_witnesses_completeness]
  | subcircuit ops circuit ih =>
    simp_all [uses_local_witnesses, uses_local_witnesses_completeness]
    apply circuit.implied_by_local_witnesses
    rw [←extends_vector_subcircuit]
    exact h.right
end Environment

namespace Circuit
open Environment (env_extends_subcircuit env_extends_subcircuit_inner env_extends_witness env_extends_assert env_extends_lookup)

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness' {n: ℕ} {ops : Operations F n} {env} : env.uses_local_witnesses' ops →
  constraints_hold.completeness env ops → constraints_hold env ops := by
  intro h_env h
  induction ops with
  | empty => trivial
  | witness ops m c ih | assert ops c ih | lookup ops c ih =>
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

/--
Generic version of `constraints_hold`, to reason about soundness and completeness at the same time
-/
def constraints_hold.generic (from_subcircuit : {n : ℕ} → Environment F → SubCircuit F n → Prop)
  (eval : Environment F) {n : ℕ} : Operations F n → Prop
  | .empty _ => True
  | .witness ops _ _ => generic from_subcircuit eval ops
  | .assert ops e => generic from_subcircuit eval ops ∧ eval e = 0
  | .lookup ops { table, entry, .. } => generic from_subcircuit eval ops ∧ table.contains (entry.map eval)
  | .subcircuit ops s => generic from_subcircuit eval ops ∧ from_subcircuit eval s

theorem constraints_hold.soundness_iff_generic {n : ℕ} (env : Environment F) (ops : Operations F n) :
  soundness env ops ↔ generic (fun env s => s.soundness env) env ops := by
  induction ops with
  | empty => trivial
  | witness ops _ _ ih | assert ops _ ih | lookup ops _ ih | subcircuit ops _ ih =>
    cases ops <;> simp_all [soundness, generic]

theorem constraints_hold.completeness_iff_generic {n : ℕ} (env : Environment F) (ops : Operations F n) :
  completeness env ops ↔ generic (fun env s => s.completeness env) env ops := by
  induction ops with
  | empty => trivial
  | witness ops _ _ ih | assert ops _ ih | lookup ops _ ih | subcircuit ops _ ih =>
    cases ops <;> simp_all [completeness, generic]

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {n: ℕ} {ops : Operations F n} {env} : env.uses_local_witnesses ops →
  constraints_hold.completeness env ops → constraints_hold env ops := by
  rw [constraints_hold.completeness_iff_generic]
  intro h_env h
  induction ops with
  | empty => trivial
  | witness | assert | lookup => simp_all [circuit_norm, Environment.uses_local_witnesses, constraints_hold.generic]
  | subcircuit ops circuit ih =>
    simp only [Environment.uses_local_witnesses, constraints_hold.generic] at *
    exact ⟨ ih h_env.left h.left,
      circuit.implied_by_completeness env (env.extends_vector_subcircuit ▸ h_env.right) h.right ⟩

end Circuit

section
variable {α β: TypeMap} [ProvableType α] [ProvableType β]
open Circuit (constraints_hold)

/--
  Justification for using a modified statement for `constraints_hold`
  in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_soundness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    let a := eval env (circuit.output b_var offset)
    circuit.spec b a := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `uses_local_witnesses`
  and `constraints_hold` in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_completeness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.uses_local_witnesses (circuit.main b_var |>.operations offset) →
    -- the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env
  apply Circuit.can_replace_completeness h_env
  have h_env' := Environment.can_replace_local_witnesses_completeness h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions

/--
  Justification for using a modified statement for `constraints_hold`
  in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_soundness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    circuit.spec b := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `uses_local_witnesses`
  and `constraints_hold` in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_completeness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.uses_local_witnesses (circuit.main b_var |>.operations offset) →
    -- the spec implies that the constraints hold (original definition)
    circuit.spec b → constraints_hold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env h_spec
  apply Circuit.can_replace_completeness h_env
  have h_env' := Environment.can_replace_local_witnesses_completeness h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions h_spec
end
