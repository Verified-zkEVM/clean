/-
This file contains theorems that immediately follow from the definitions in `Circuit.Basic`.

For more complicated interconnected theorems, we have separate files,
such as `Circuit.SubCircuit` which focuses on establishing the foundation for subcircuit composition.
-/
import Clean.Circuit.Basic

variable {F: Type} [Field F]

-- basic simp lemmas

namespace Operations

@[circuit_norm]
theorem append_local_length {a b: Operations F} :
    (a ++ b).local_length = a.local_length + b.local_length := by
  induction a using induct with
  | empty => ac_rfl
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all +arith [local_length, ih]

@[circuit_norm]
theorem forAll_empty {condition : Condition F} {n: ℕ} : forAll n condition [] = True := rfl

@[circuit_norm]
theorem forAll_cons {condition : Condition F} {offset: ℕ} {op: Operation F} {ops: Operations F} :
  forAll offset condition (op :: ops) ↔
    condition.apply offset op ∧ forAll (op.local_length + offset) condition ops := by
  cases op <;> simp [forAll, Operation.local_length, Condition.apply]

@[circuit_norm]
theorem forAll_append {condition : Condition F} {offset: ℕ} {as bs: Operations F} :
  forAll offset condition (as ++ bs) ↔
    forAll offset condition as ∧ forAll (as.local_length + offset) condition bs := by
  induction as using induct generalizing offset with
  | empty => simp [forAll_empty, local_length]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp +arith only [List.cons_append, forAll, local_length, ih, and_assoc]
end Operations

namespace Circuit
variable {α β : Type}

theorem pure_operations_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).operations n = [] := rfl

theorem bind_operations_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl

theorem map_operations_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).operations n = f.operations n := rfl

theorem pure_local_length_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).local_length n = 0 := rfl

theorem bind_local_length_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).local_length n = f.local_length n + (g (f.output n)).local_length (n + f.local_length n) := by
  show (f.operations n ++ (g _).operations _).local_length = _
  rw [Operations.append_local_length]

theorem map_local_length_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).local_length n = f.local_length n := rfl

theorem pure_output_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).output n = a := rfl

theorem bind_output_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.local_length n) := rfl

theorem map_output_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).output n = g (f.output n) := rfl

/-- Extensionality theorem -/
theorem ext_iff {f g : Circuit F α} :
  (f = g) ↔ (∀ n, (f.output n = g.output n) ∧ (f.operations n = g.operations n)) := by
  constructor
  · intro h; subst h; intros; trivial
  intro h
  funext n
  ext1
  · exact (h n).left
  · exact (h n).right

@[ext]
theorem ext {f g : Circuit F α}
  (h_output : ∀ n, f.output n = g.output n)
  (h_operations : ∀ n, f.operations n = g.operations n) :
    f = g :=
  ext_iff.mpr fun n => ⟨ h_output n, h_operations n ⟩

-- lawful monad

instance : LawfulMonad (Circuit F) where
  bind_pure_comp {α β} (g : α → β) (f : Circuit F α) := by
    simp only [bind_def, Functor.map, List.append_nil]
  bind_map {α β} (g : Circuit F (α → β)) (f : Circuit F α) := rfl
  pure_bind {α β} (x : α) (f : α → Circuit F β) := by
    simp only [bind_def, pure, List.nil_append]; rfl
  bind_assoc {α β γ} (x : Circuit F α) (f : α → Circuit F β) (g : β → Circuit F γ) := by
    ext1 n
    · simp only [bind_output_eq, bind_local_length_eq, add_assoc]
    · simp only [bind_operations_eq, bind_local_length_eq, bind_output_eq,
        List.append_assoc, add_assoc]
  map_const := rfl
  id_map {α} (f : Circuit F α) := rfl
  seqLeft_eq {α β} (f : Circuit F α) (g : Circuit F β) := by
    funext n
    simp only [SeqLeft.seqLeft, bind, List.append_nil, Seq.seq]
    rfl
  seqRight_eq {α β} (f : Circuit F α) (g : Circuit F β) := by
    funext n
    simp only [SeqRight.seqRight, bind, Seq.seq]
    rfl
  pure_seq {α β} (g : α → β) (f : Circuit F α) := rfl

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

theorem can_replace_local_witnesses_completeness {env: Environment F} {ops: Operations F} {n: ℕ} (h: ops.subcircuits_consistent n) :
    env.uses_local_witnesses n ops → env.uses_local_witnesses_completeness n ops := by
  induction ops, n, h using Operations.induct_consistent with
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

theorem uses_local_witnesses_completeness_iff_forAll (n: ℕ) {env: Environment F} {ops: Operations F} :
  env.uses_local_witnesses_completeness n ops ↔ ops.forAll n {
    witness m _ c := env.extends_vector (c env) m,
    subcircuit _ _ s := s.uses_local_witnesses env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | subcircuit =>
    simp_all +arith [uses_local_witnesses_completeness, Operations.forAll]
end Environment

namespace Circuit

theorem constraints_hold.soundness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
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

theorem constraints_hold.completeness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
  completeness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.valid (l.entry.map env),
    subcircuit _ _ s := s.completeness env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all only [completeness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.SubCircuit.can_replace_subcircuits`, it justifies only proving the nested version
`constraints_hold.completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {env} {ops : Operations F} {n : ℕ} (h : ops.subcircuits_consistent n) : env.uses_local_witnesses n ops →
    constraints_hold.completeness env ops → constraints_hold env ops := by
  induction ops, n, h using Operations.induct_consistent with
  | empty => intros; exact trivial
  | witness | assert | lookup =>
    simp_all [circuit_norm, Environment.uses_local_witnesses, Operations.forAll, Table.implies]
  | subcircuit n circuit ops ih =>
    simp_all only [constraints_hold, constraints_hold.completeness, Environment.uses_local_witnesses, and_true]
    intro h_env h_compl
    apply circuit.implied_by_completeness env ?_ h_compl.left
    rw [←env.extends_vector_subcircuit]
    exact h_env.left
end Circuit

namespace Circuit
-- more theorems about forAll

variable {α β : Type} {n : ℕ} {prop : Operations.Condition F} {env: Environment F}

@[circuit_norm]
theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} :
  ((f >>= g).operations n).forAll n prop ↔
    (f.operations n).forAll n prop ∧ (((g (f.output n)).operations (n + f.local_length n)).forAll (n + f.local_length n)) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl
  rw [h_ops, Operations.forAll_append, add_comm n]

-- definition of `forAll` for circuits which uses the same offset in two places

@[reducible, circuit_norm]
def forAll (circuit : Circuit F α) (n : ℕ) (prop : Operations.Condition F) :=
  (circuit.operations n).forAll n prop

lemma forAll_def {circuit : Circuit F α} {n : ℕ} :
  circuit.forAll n prop ↔ (circuit.operations n).forAll n prop := by rfl

theorem bind_forAll' {f : Circuit F α} {g : α → Circuit F β} :
  (f >>= g).forAll n prop ↔
    f.forAll n prop ∧ ((g (f.output n)).forAll (n + f.local_length n) prop) := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl
  simp only [forAll]
  rw [bind_forAll]

theorem constraints_hold.soundness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  constraints_hold.soundness env (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.contains (l.entry.map env),
    subcircuit _ _ s := s.soundness env
  } := by
  rw [forAll_def, constraints_hold.soundness_iff_forAll n]

theorem constraints_hold.completeness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  constraints_hold.completeness env (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.valid (l.entry.map env),
    subcircuit _ _ s := s.completeness env
  } := by
  rw [forAll_def, constraints_hold.completeness_iff_forAll n]

-- specializations

@[circuit_norm] theorem constraints_hold.append_soundness {as bs : Operations F} :
  constraints_hold.soundness env (as ++ bs)
  ↔ constraints_hold.soundness env as ∧ constraints_hold.soundness env bs := by
  rw [constraints_hold.soundness_iff_forAll 0, Operations.forAll_append,
    ←constraints_hold.soundness_iff_forAll 0, ←constraints_hold.soundness_iff_forAll (as.local_length + 0)]

@[circuit_norm] theorem constraints_hold.bind_soundness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.soundness env ((f >>= g).operations n)
  ↔ constraints_hold.soundness env (f.operations n) ∧
    constraints_hold.soundness env ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [constraints_hold.soundness_iff_forAll n, constraints_hold.soundness_iff_forAll n,
    constraints_hold.soundness_iff_forAll (n + f.local_length n), bind_forAll]

@[circuit_norm] theorem constraints_hold.append_completeness {as bs : Operations F} :
  constraints_hold.completeness env (as ++ bs)
  ↔ constraints_hold.completeness env as ∧ constraints_hold.completeness env bs := by
  rw [constraints_hold.completeness_iff_forAll 0, Operations.forAll_append,
    ←constraints_hold.completeness_iff_forAll 0, ←constraints_hold.completeness_iff_forAll (as.local_length + 0)]

@[circuit_norm] theorem constraints_hold.bind_completeness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  constraints_hold.completeness env ((f >>= g).operations n)
  ↔ constraints_hold.completeness env (f.operations n) ∧
    constraints_hold.completeness env ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [constraints_hold.completeness_iff_forAll n, constraints_hold.completeness_iff_forAll n,
    constraints_hold.completeness_iff_forAll (n + f.local_length n), bind_forAll]

@[circuit_norm] theorem constraints_hold.append_local_witnesses {as bs : Operations F} (n : ℕ) :
  env.uses_local_witnesses_completeness n (as ++ bs)
  ↔ env.uses_local_witnesses_completeness n as ∧ env.uses_local_witnesses_completeness (as.local_length + n) bs := by
  rw [env.uses_local_witnesses_completeness_iff_forAll, Operations.forAll_append,
    ←env.uses_local_witnesses_completeness_iff_forAll n, ←env.uses_local_witnesses_completeness_iff_forAll (as.local_length + n)]

@[circuit_norm] theorem constraints_hold.bind_uses_local_witnesses {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  env.uses_local_witnesses_completeness n ((f >>= g).operations n)
  ↔ env.uses_local_witnesses_completeness n (f.operations n) ∧
    env.uses_local_witnesses_completeness (n + f.local_length n) ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [env.uses_local_witnesses_completeness_iff_forAll, env.uses_local_witnesses_completeness_iff_forAll,
    env.uses_local_witnesses_completeness_iff_forAll, bind_forAll]
end Circuit
