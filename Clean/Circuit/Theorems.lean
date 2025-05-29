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
theorem can_replace_soundness {ops : Operations F} {env} :
  constraints_hold env ops → constraints_hold.soundness env ops := by
  intro h
  induction ops using Operations.induct with
  | empty => trivial
  | witness | assert | lookup =>
    simp_all [constraints_hold.soundness, constraints_hold]
  | subcircuit circuit ops ih =>
    dsimp only [constraints_hold.soundness]
    dsimp only [constraints_hold] at h
    exact ⟨ circuit.imply_soundness env h.left, ih h.right ⟩

end Circuit

namespace Environment
open FlatOperation (witness_length witnesses)
/-
what follows are relationships between different ways of deriving local witness generators,
and between different versions of `Environment.uses_local_witnesses`
-/

lemma witness_length_append {F} {a b: List (FlatOperation F)} :
    witness_length (a ++ b) = witness_length a + witness_length b := by
  induction a using FlatOperation.witness_length.induct with
  | case1 => simp only [List.nil_append, witness_length]; ac_rfl
  | case2 _ _ _ ih =>
    simp only [List.cons_append, witness_length, ih]; ac_rfl
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, witness_length, ih]

/--
The witness length from flat and nested operations is the same
-/
lemma flat_witness_length_eq {ops: Operations F} :
    witness_length (to_flat_operations ops) = ops.local_length := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ ops ih | assert _ ops ih | lookup _ ops ih  | subcircuit _ ops ih =>
    dsimp only [to_flat_operations, Operations.local_length]
    generalize to_flat_operations ops = flat_ops at *
    generalize Operations.local_length ops = n at *
    induction flat_ops using FlatOperation.witness_length.induct generalizing n with
    | case1 => simp_all [witness_length, add_comm, List.nil_append, right_eq_add, SubCircuit.local_length_eq]
    | case2 ops m' _ ih' =>
      dsimp only [witness_length, witness] at *
      specialize ih' (n - m') (by rw [←ih]; omega)
      simp_all +arith only [witness_length_append, witness_length]
      try omega
    | case3 ops _ ih' | case4 ops _ ih' =>
      simp_all only [witness_length_append, forall_eq', witness_length, List.cons_append]

lemma witnesses_append {F} {a b: List (FlatOperation F)} {env} :
    (witnesses env (a ++ b)).toArray = (witnesses env a).toArray ++ (witnesses env b).toArray := by
  induction a using FlatOperation.witness_length.induct with
  | case1 => simp only [List.nil_append, witness_length, witnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, ih, Vector.mk_toArray]

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {ops: Operations F} {env} :
  (witnesses env (to_flat_operations ops)).toArray = (ops.local_witnesses env).toArray := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp only [to_flat_operations, Operations.local_length, Operations.local_witnesses, Vector.toArray_append]
    rw [←ih]
    try rw [witnesses_append]
    try simp only [witness_length, witnesses, Vector.toArray_empty, Array.append_empty, SubCircuit.witnesses, Vector.toArray_cast]

/-- equivalent, non-inductive statement of `Environment.uses_local_witnesses` (that is harder to unfold for a circuit) -/
def uses_local_witnesses' (env: Environment F) (offset : ℕ) (ops: Operations F) :=
  env.extends_vector (ops.local_witnesses env) offset

/--
Helper lemma: An environment respects local witnesses if it does so in the flattened variant.
-/
lemma env_extends_of_flat {n: ℕ} {ops: Operations F} {env: Environment F} :
    env.extends_vector (witnesses env (to_flat_operations ops)) n →
    env.uses_local_witnesses' n ops := by
  simp only [uses_local_witnesses', extends_vector, Vector.get, flat_witness_eq_witness]
  intro h i
  exact h ⟨ i, by rw [flat_witness_length_eq]; exact i.is_lt ⟩

lemma env_extends_witness {n: ℕ} {ops: Operations F} {env: Environment F} {m c} :
    env.uses_local_witnesses' n (.witness m c :: ops) → env.uses_local_witnesses' (m + n) ops := by
  intro h i
  simp only [uses_local_witnesses', circuit_norm] at h
  specialize h ⟨ m + i, by omega ⟩
  rw [←add_assoc, add_comm n] at h
  rw [h]
  simp [Vector.get]

lemma env_extends_witness_inner {n: ℕ} {ops: Operations F} {env: Environment F} {m c} :
    env.uses_local_witnesses' n (.witness m c :: ops) → env.extends_vector (c env) n := by
  intro h i
  simp only [uses_local_witnesses', circuit_norm] at h
  specialize h ⟨ i, by linarith [i.is_lt] ⟩
  rw [h, Vector.getElem_append]
  simp [Vector.get]

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F} {env: Environment F} {n'} {s : SubCircuit F n'} :
    env.uses_local_witnesses' n (.subcircuit s :: ops) → env.uses_local_witnesses' (s.local_length + n) ops := by
  intro h i
  simp_all only [uses_local_witnesses', circuit_norm]
  specialize h ⟨ s.local_length + i, by linarith [i.is_lt] ⟩
  rw [←add_assoc, add_comm n] at h
  rw [h]
  simp [Vector.get]

lemma env_extends_subcircuit_inner {n: ℕ} {ops: Operations F} {env: Environment F} {n'} {s : SubCircuit F n'} :
    env.uses_local_witnesses' n (.subcircuit s :: ops) → env.extends_vector (witnesses env s.ops) n := by
  intro h i
  simp_all only [uses_local_witnesses', circuit_norm, witness_length]
  have : i < s.local_length + ops.local_length := by rw [s.local_length_eq]; linarith [i.is_lt]
  specialize h ⟨ i, this ⟩
  simp only at h
  rw [h, Vector.getElem_append]
  have : i < s.local_length := by rw [s.local_length_eq]; exact i.is_lt
  simp [this]

lemma extends_vector_subcircuit (env : Environment F) {n} {n'} {circuit : SubCircuit F n'} :
    env.extends_vector (circuit.witnesses env) n = env.extends_vector (FlatOperation.witnesses env circuit.ops) n := by
  have h_length : circuit.local_length = FlatOperation.witness_length circuit.ops := circuit.local_length_eq
  congr
  rw [SubCircuit.witnesses]
  apply Vector.cast_heq

theorem can_replace_local_witnesses {env: Environment F} (n: ℕ) {ops: Operations F}  :
  env.uses_local_witnesses' n ops → env.uses_local_witnesses n ops := by
  intro h
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih =>
    rw [uses_local_witnesses]
    exact ⟨ env_extends_witness_inner h, ih _ (env_extends_witness h) ⟩
  | assert | lookup =>
    simp_all [uses_local_witnesses', uses_local_witnesses, circuit_norm]
  | subcircuit _ _ ih =>
    rw [uses_local_witnesses, extends_vector_subcircuit]
    exact ⟨ env_extends_subcircuit_inner h, ih _ (env_extends_subcircuit h) ⟩

theorem can_replace_local_witnesses_completeness {env: Environment F} (ops: ConsistentOperations F) :
  env.uses_local_witnesses ops.initial_offset ops.ops → env.uses_local_witnesses_completeness ops.initial_offset ops.ops := by
  induction ops using ConsistentOperations.induct with
  | empty => intros; trivial
  | witness | assert | lookup =>
    simp_all +arith [uses_local_witnesses, uses_local_witnesses_completeness]
  | subcircuit n circuit ops ih =>
    simp only [uses_local_witnesses, uses_local_witnesses_completeness]
    intro h
    rw [add_comm]
    apply And.intro ?_ (ih h.right)
    apply circuit.implied_by_local_witnesses
    rw [←extends_vector_subcircuit]
    exact h.left

theorem uses_local_witnesses_completeness_iff_forAll {env: Environment F} {n: ℕ} {ops: Operations F} :
  env.uses_local_witnesses_completeness n ops ↔
    ops.forAll n {
      witness m _ c := env.extends_vector (c env) m,
      subcircuit _ _ s := s.uses_local_witnesses env
    } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | subcircuit =>
    simp_all +arith [uses_local_witnesses_completeness, Operations.forAll]
end Environment

namespace Circuit

theorem constraints_hold.soundness_iff_forAll (env : Environment F) (ops : Operations F) (n : ℕ := 0) :
  soundness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ _ s := s.soundness env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all [soundness, Operations.forAll]
    try intros
    apply ih

theorem constraints_hold.completeness_iff_forAll (env : Environment F) (ops : Operations F) (n : ℕ := 0) :
  completeness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ _ s := s.completeness env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all [completeness, Operations.forAll]
    try intros
    apply ih

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {env} (ops : ConsistentOperations F) : env.uses_local_witnesses ops.initial_offset ops.ops →
  constraints_hold.completeness env ops.ops → constraints_hold env ops.ops := by
  induction ops using ConsistentOperations.induct with
  | empty => intros; exact trivial
  | witness | assert | lookup =>
    simp_all [circuit_norm, Environment.uses_local_witnesses, Operations.forAll]
  | subcircuit n circuit ops ih =>
    simp_all only [constraints_hold, constraints_hold.completeness, Environment.uses_local_witnesses, and_true]
    intro h_env h_compl
    apply circuit.implied_by_completeness env ?_ h_compl.left
    rw [←env.extends_vector_subcircuit]
    exact h_env.left

end Circuit
