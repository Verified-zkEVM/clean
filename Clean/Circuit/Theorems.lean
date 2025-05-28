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
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    induction op with
    | witness | assert | lookup =>
      simp_all [constraints_hold.soundness, constraints_hold]
    | subcircuit circuit =>
      dsimp only [constraints_hold.soundness]
      dsimp only [constraints_hold] at h
      exact ⟨ circuit.imply_soundness env h.left, ih h.right ⟩

-- TODO initial offset doesn't make sense
-- /--
-- Initial offset + size of local witnesses = final offset of a circuit
-- -/
-- lemma total_length_eq {n: ℕ} {ops: Operations F} : ops.initial_offset + ops.local_length = n := by
--   open Operations (initial_offset) in
--   induction ops with
--   | empty n => simp only [initial_offset, Operations.local_length, add_zero]
--   | witness ops _ _ ih | subcircuit ops s ih =>
--     dsimp only [initial_offset, Operations.local_length]
--     rw [←add_assoc, ih]
--   | assert ops _ ih | lookup op _ ih =>
--     simp only [initial_offset, Operations.local_length, ih]

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
  induction ops with
  | nil => trivial
  | cons op ops ih => induction op with
  | witness m c | assert c | lookup  | subcircuit _ =>
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

lemma subcircuit_witness_eq {n: ℕ} (sc : SubCircuit F n) {env} :
    (sc.witnesses env).toArray = (FlatOperation.witnesses env sc.ops).toArray := by
  simp only [SubCircuit.witnesses, Vector.toArray_cast]

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {ops: Operations F} {env} :
  (witnesses env (to_flat_operations ops)).toArray = (ops.local_witnesses env).toArray := by
  induction ops with
  | nil => trivial
  | cons op ops ih => induction op with
  | witness m c | assert c | lookup c | subcircuit _ =>
    simp only [to_flat_operations, Operations.local_length, Operations.local_witnesses, Vector.toArray_append]
    rw [←ih]
    try rw [witnesses_append]
    try simp only [witness_length, witnesses, Vector.toArray_empty, Array.append_empty, subcircuit_witness_eq]

/-- equivalent, non-inductive statement of `Environment.uses_local_witnesses` (that is harder to unfold for a circuit) -/
def uses_local_witnesses' (env: Environment F) (ops: Operations F) (offset : ℕ) :=
  env.extends_vector (ops.local_witnesses env) offset

/--
Helper lemma: An environment respects local witnesses if it does so in the flattened variant.
-/
lemma env_extends_of_flat {n: ℕ} {ops: Operations F} {env: Environment F} :
    env.extends_vector (witnesses env (to_flat_operations ops)) n →
    env.uses_local_witnesses' ops n := by
  simp only [uses_local_witnesses', extends_vector, Vector.get, flat_witness_eq_witness]
  intro h i
  exact h ⟨ i, by rw [flat_witness_length_eq]; exact i.is_lt ⟩

lemma env_extends_witness {n: ℕ} {ops: Operations F} {env: Environment F} {m c} :
    env.uses_local_witnesses' (.witness m c :: ops) n → env.uses_local_witnesses' ops (m + n) := by
  intro h i
  simp only [uses_local_witnesses', circuit_norm] at h
  specialize h ⟨ m + i, by omega ⟩
  rw [←add_assoc, add_comm n] at h
  rw [h]
  simp [Vector.get]

lemma env_extends_witness_inner {n: ℕ} {ops: Operations F} {env: Environment F} {m c} :
    env.uses_local_witnesses' (.witness m c :: ops) n → env.extends_vector (c env) n := by
  intro h i
  simp only [uses_local_witnesses', circuit_norm] at h
  specialize h ⟨ i, by linarith [i.is_lt] ⟩
  rw [h, Vector.getElem_append]
  simp [Vector.get]

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F} {env: Environment F} {n'} {s : SubCircuit F n'} :
    env.uses_local_witnesses' (.subcircuit s :: ops) n → env.uses_local_witnesses' ops (s.local_length + n) := by
  intro h i
  simp_all only [uses_local_witnesses', circuit_norm]
  specialize h ⟨ s.local_length + i, by linarith [i.is_lt] ⟩
  rw [←add_assoc, add_comm n] at h
  rw [h]
  simp [Vector.get]

lemma env_extends_subcircuit_inner {n: ℕ} {ops: Operations F} {env: Environment F} {n'} {s : SubCircuit F n'} :
    env.uses_local_witnesses' (.subcircuit s :: ops) n → env.extends_vector (witnesses env s.ops) n := by
  intro h i
  simp_all only [uses_local_witnesses', circuit_norm, witness_length]
  have : i < s.local_length + ops.local_length := by rw [s.local_length_eq]; linarith [i.is_lt]
  specialize h ⟨ i, this ⟩
  simp only at h
  rw [h, Vector.getElem_append]
  have : i < s.local_length := by rw [s.local_length_eq]; exact i.is_lt
  simp [this]

lemma extends_vector_subcircuit (env : Environment F) {n} {circuit : SubCircuit F n} :
    env.extends_vector (circuit.witnesses env) n = env.extends_vector (FlatOperation.witnesses env circuit.ops) n := by
  have h_length : circuit.local_length = FlatOperation.witness_length circuit.ops := circuit.local_length_eq
  congr
  rw [SubCircuit.witnesses]
  apply Vector.cast_heq

theorem can_replace_local_witnesses {env: Environment F} {n: ℕ} {ops: Operations F}  :
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

theorem can_replace_local_witnesses_completeness {env: Environment F} {n: ℕ} {ops: Operations F}  :
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

theorem uses_local_witnesses_completeness_iff_forAll {env: Environment F} {n: ℕ} {ops: Operations F} :
  env.uses_local_witnesses_completeness ops ↔
    ops.forAll {
      witness n _ c := env.extends_vector (c env) n,
      assert _ _ := True,
      lookup _ _ := True,
      subcircuit _ s := s.uses_local_witnesses env
    } := by
  induction ops with
  | empty => trivial
  | assert | lookup | witness | subcircuit =>
    simp_all [uses_local_witnesses_completeness, Operations.forAll]
end Environment

namespace Circuit

theorem constraints_hold.soundness_iff_forAll {n : ℕ} (env : Environment F) (ops : Operations F) :
  soundness env ops ↔ ops.forAll {
    witness _ _ _ := True,
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ s := s.soundness env
  } := by
  induction ops with
  | empty => trivial
  | witness | assert | lookup | subcircuit =>
    simp_all [soundness, Operations.forAll]

theorem constraints_hold.completeness_iff_forAll {n : ℕ} (env : Environment F) (ops : Operations F) :
  completeness env ops ↔ ops.forAll {
    witness _ _ _ := True,
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ s := s.completeness env
  } := by
  induction ops with
  | empty => trivial
  | witness | assert | lookup | subcircuit =>
    simp_all [completeness, Operations.forAll]

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {n: ℕ} {ops : Operations F} {env} : env.uses_local_witnesses ops →
  constraints_hold.completeness env ops → constraints_hold env ops := by
  rw [constraints_hold.completeness_iff_forAll]
  intro h_env h
  induction ops with
  | empty => trivial
  | witness | assert | lookup =>
    simp_all [circuit_norm, Environment.uses_local_witnesses, Operations.forAll]
  | subcircuit ops circuit ih =>
    simp only [Environment.uses_local_witnesses] at *
    exact ⟨ ih h_env.left h.left,
      circuit.implied_by_completeness env (env.extends_vector_subcircuit ▸ h_env.right) h.right ⟩

end Circuit

-- append behaves as expected with `constraints_hold`

namespace Circuit.constraints_hold
variable {env : Environment F} {n : ℕ} {prop : Operations.Condition F}

theorem append_forAll (as : Operations F m) (bs : OperationsFrom F m n) :
  (as ++ bs).forAll prop ↔ as.forAll prop ∧ bs.val.forAll prop := by
  induction bs using OperationsFrom.induct with
  | empty n => rw [Operations.append_empty]; tauto
  | witness bs k c ih | assert bs _ ih | lookup bs _ ih | subcircuit bs _ ih =>
    specialize ih as
    simp only [Operations.append_lookup, Operations.append_assert, Operations.append_witness, Operations.append_subcircuit]
    simp only [OperationsFrom.lookup, OperationsFrom.assert, OperationsFrom.witness, OperationsFrom.subcircuit]
    simp only [Operations.forAll, ih, and_assoc]

theorem append_soundness (as : Operations F m) (bs : OperationsFrom F m n) :
    soundness env (as ++ bs) ↔ soundness env as ∧ soundness env bs.val := by
  simp only [soundness_iff_forAll, append_forAll]

theorem append_completeness (as : Operations F m) (bs : OperationsFrom F m n) :
  completeness env (as ++ bs) ↔ completeness env as ∧ completeness env bs.val := by
  simp only [completeness_iff_forAll, append_forAll]

end Circuit.constraints_hold
