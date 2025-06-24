/-
This file contains theorems that immediately follow from the definitions in `Circuit.Operations` and `Circuit.Basic`.

For more complicated interconnected theorems, we have separate files,
such as `Circuit.SubCircuit` which focuses on establishing the foundation for subcircuit composition.
-/
import Clean.Circuit.Basic

variable {F: Type} [Field F] {α β : Type}

-- basic simp lemmas

namespace Operations
@[circuit_norm]
theorem append_local_length {a b: Operations F} :
    (a ++ b).local_length = a.local_length + b.local_length := by
  induction a using induct with
  | empty => ac_rfl
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all +arith [local_length, ih]

theorem local_length_cons {a : Operation F} {as: Operations F} :
    local_length (a :: as) = a.local_length + as.local_length := by
  cases a <;> simp_all [local_length, Operation.local_length]

theorem local_witnesses_cons (op : Operation F) (ops : Operations F) (env : Environment F) :
  local_witnesses env (op :: ops) =
    (op.local_witnesses env ++ ops.local_witnesses env).cast (local_length_cons.symm) := by
  cases op <;> simp only [local_witnesses, Operation.local_witnesses, Vector.cast_rfl]
  rw [Vector.empty_append]; simp
  rw [Vector.empty_append]; simp

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
    simp_all [constraints_hold.soundness, constraints_hold, RawTable.imply_soundness]
  | subcircuit circuit ops ih =>
    dsimp only [constraints_hold.soundness]
    dsimp only [constraints_hold] at h
    exact ⟨ circuit.imply_soundness env h.left, ih h.right ⟩

end Circuit

-- more about `FlatOperation`, and relationships to `Operations`

namespace FlatOperation
lemma local_length_cons {F} {op : FlatOperation F} {ops : List (FlatOperation F)} :
    local_length (op :: ops) = op.single_local_length + local_length ops := by
  cases op <;> simp +arith only [local_length, single_local_length, List.cons_append]

lemma local_length_append {F} {a b: List (FlatOperation F)} :
    local_length (a ++ b) = local_length a + local_length b := by
  induction a using local_length.induct with
  | case1 => simp only [List.nil_append, local_length]; ac_rfl
  | case2 _ _ _ ih =>
    simp only [List.cons_append, local_length, ih]; ac_rfl
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, local_length, ih]

theorem forAll_empty {condition : Condition F} {n: ℕ} : forAll n condition [] = True := rfl

theorem forAll_cons {condition : Condition F} {offset: ℕ} {op: FlatOperation F} {ops: List (FlatOperation F)} :
  forAll offset condition (op :: ops) ↔
    condition.applyFlat offset op ∧ forAll (op.single_local_length + offset) condition ops := by
  cases op <;> simp [forAll, Condition.applyFlat, single_local_length]

lemma forAll_append {condition : Condition F} {ops ops' : List (FlatOperation F)} (n : ℕ) :
  forAll n condition (ops ++ ops') ↔
    forAll n condition ops ∧ forAll (local_length ops + n) condition ops' := by
  induction ops generalizing n with
  | nil => simp only [List.nil_append, forAll, local_length, zero_add, true_and]
  | cons op ops ih =>
    specialize ih (n + op.single_local_length)
    simp_all +arith [forAll_cons, local_length_cons, and_assoc]

lemma witnesses_append {F} {a b: List (FlatOperation F)} {env} :
    (local_witnesses env (a ++ b)).toArray = (local_witnesses env a).toArray ++ (local_witnesses env b).toArray := by
  induction a using FlatOperation.local_length.induct with
  | case1 => simp only [List.nil_append, local_length, local_witnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, local_length, local_witnesses, Vector.toArray_append, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, local_length, local_witnesses, ih]

/--
The witness length from flat and nested operations is the same
-/
lemma flat_witness_length_eq {ops: Operations F} :
    local_length ops.toFlat = ops.local_length := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ ops ih | assert _ ops ih | lookup _ ops ih  | subcircuit _ ops ih =>
    dsimp only [Operations.toFlat, Operations.local_length]
    generalize ops.toFlat = flat_ops at *
    generalize Operations.local_length ops = n at *
    induction flat_ops using local_length.induct generalizing n with
    | case1 => simp_all [local_length, add_comm, List.nil_append, right_eq_add, SubCircuit.local_length_eq]
    | case2 m' _ ops' ih' =>
      dsimp only [local_length, witness] at *
      specialize ih' (n - m') (by rw [←ih]; omega)
      simp_all +arith only [local_length_append, local_length]
      try omega
    | case3 ops _ ih' | case4 ops _ ih' =>
      simp_all only [local_length_append, forall_eq', local_length, List.cons_append]

/--
The witnesses created from flat and nested operations are the same
-/
lemma flat_witness_eq_witness {ops: Operations F} {env} :
  (local_witnesses env ops.toFlat).toArray = (ops.local_witnesses env).toArray := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp only [Operations.toFlat, Operations.local_length, Operations.local_witnesses, Vector.toArray_append]
    rw [←ih]
    try rw [witnesses_append]
    try simp only [local_length, local_witnesses, Vector.toArray_append, SubCircuit.witnesses, Vector.toArray_cast]
end FlatOperation

namespace Environment
open FlatOperation (local_length local_witnesses flat_witness_length_eq flat_witness_eq_witness)
/-
what follows are relationships between different versions of `Environment.UsesLocalWitnesses`
-/

lemma env_extends_witness {F} {n: ℕ} {ops: List (FlatOperation F)} {env: Environment F} {m c} :
    env.extends_vector (local_witnesses env (.witness m c :: ops)) n ↔
      (env.extends_vector (c env) n ∧ env.extends_vector (local_witnesses env ops) (m + n)) := by
  simp_all only [extends_vector, local_length, local_witnesses, Vector.getElem_append]
  constructor
  · intro h
    constructor
    · intro i
      specialize h ⟨ i, by omega ⟩
      simp [h]
    · intro i
      specialize h ⟨ m + i, by omega ⟩
      ring_nf at *
      simp [h]
  · intro ⟨ h_inner, h_outer ⟩ ⟨ i, hi ⟩
    by_cases hi' : i < m <;> simp only [hi', reduceDIte]
    · exact h_inner ⟨ i, hi' ⟩
    · specialize h_outer ⟨ i - m, by omega ⟩
      simp only [←h_outer]
      congr 1
      omega

theorem usesLocalWitnessesFlat_iff_extends {env: Environment F} (n: ℕ) {ops: List (FlatOperation F)}  :
    env.UsesLocalWitnessesFlat n ops ↔ env.extends_vector (local_witnesses env ops) n := by
  induction ops using FlatOperation.induct generalizing n with
  | empty => simp [UsesLocalWitnessesFlat, FlatOperation.forAll_empty, extends_vector, local_length]
  | witness m _ _ ih =>
    rw [UsesLocalWitnessesFlat, FlatOperation.forAll, env_extends_witness,←ih (m + n)]
    trivial
  | assert | lookup =>
    simp_all [UsesLocalWitnessesFlat, circuit_norm,
      FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.single_local_length]

theorem can_replace_usesLocalWitnessesCompleteness {env : Environment F} {ops : Operations F} {n : ℕ} (h : ops.subcircuits_consistent n) :
  env.UsesLocalWitnesses n ops → env.UsesLocalWitnessesCompleteness n ops := by
  induction ops, n, h using Operations.induct_consistent with
  | empty => intros; trivial
  | witness | assert | lookup =>
    simp_all +arith [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll]
  | subcircuit n circuit ops ih =>
    simp only [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll_cons, Condition.apply]
    intro h
    rw [add_comm]
    apply And.intro ?_ (ih h.right)
    apply circuit.implied_by_local_witnesses
    rw [← usesLocalWitnessesFlat_iff_extends]
    exact h.left

theorem usesLocalWitnessesCompleteness_iff_forAll (n : ℕ) {env : Environment F} {ops : Operations F} :
  env.UsesLocalWitnessesCompleteness n ops ↔ ops.forAll n {
    witness m _ c := env.extends_vector (c env) m,
    subcircuit _ _ s := s.UsesLocalWitnesses env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | subcircuit =>
    simp_all +arith [UsesLocalWitnessesCompleteness, Operations.forAll]

theorem usesLocalWitnesses_iff_forAll (n: ℕ) {env: Environment F} {ops: Operations F} :
  env.UsesLocalWitnesses n ops ↔ ops.forAll n {
    witness n _ c := env.extends_vector (c env) n,
    subcircuit n _ s := FlatOperation.forAll n { witness n _ c := env.extends_vector (c env) n} s.ops
  } := by
  simp only [UsesLocalWitnesses, Operations.forAllFlat]
end Environment

namespace Circuit

theorem constraints_hold.soundness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
  soundness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.soundness (l.entry.map env),
    subcircuit _ _ s := s.soundness env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all only [soundness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih

theorem constraints_hold.completeness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
  completeness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.completeness (l.entry.map env),
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
theorem can_replace_completeness {env} {ops : Operations F} {n : ℕ} (h : ops.subcircuits_consistent n) : env.UsesLocalWitnesses n ops →
    constraints_hold.completeness env ops → constraints_hold env ops := by
  induction ops, n, h using Operations.induct_consistent with
  | empty => intros; exact trivial
  | witness | assert | lookup =>
    simp_all [circuit_norm, Environment.UsesLocalWitnesses, Operations.forAllFlat, Operations.forAll, RawTable.implied_by_completeness]
  | subcircuit n circuit ops ih =>
    simp_all only [constraints_hold, constraints_hold.completeness, Environment.UsesLocalWitnesses, Operations.forAllFlat, Operations.forAll, and_true]
    intro h_env h_compl
    apply circuit.implied_by_completeness env ?_ h_compl.left
    rw [←Environment.usesLocalWitnessesFlat_iff_extends]
    exact h_env.left
end Circuit

namespace Circuit
-- more theorems about forAll

variable {α β : Type} {n : ℕ} {prop : Condition F} {env: Environment F}

@[circuit_norm]
theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} :
  ((f >>= g).operations n).forAll n prop ↔
    (f.operations n).forAll n prop ∧ (((g (f.output n)).operations (n + f.local_length n)).forAll (n + f.local_length n)) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.local_length n) := rfl
  rw [h_ops, Operations.forAll_append, add_comm n]

-- definition of `forAll` for circuits which uses the same offset in two places

@[reducible, circuit_norm]
def forAll (circuit : Circuit F α) (n : ℕ) (prop : Condition F) :=
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
    lookup _ l := l.table.soundness (l.entry.map env),
    subcircuit _ _ s := s.soundness env
  } := by
  rw [forAll_def, constraints_hold.soundness_iff_forAll n]

theorem constraints_hold.completeness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  constraints_hold.completeness env (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.completeness (l.entry.map env),
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
  env.UsesLocalWitnessesCompleteness n (as ++ bs)
  ↔ env.UsesLocalWitnessesCompleteness n as ∧ env.UsesLocalWitnessesCompleteness (as.local_length + n) bs := by
  rw [env.usesLocalWitnessesCompleteness_iff_forAll, Operations.forAll_append,
    ←env.usesLocalWitnessesCompleteness_iff_forAll n, ←env.usesLocalWitnessesCompleteness_iff_forAll (as.local_length + n)]

@[circuit_norm] theorem constraints_hold.bind_usesLocalWitnesses {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  env.UsesLocalWitnessesCompleteness n ((f >>= g).operations n)
  ↔ env.UsesLocalWitnessesCompleteness n (f.operations n) ∧
    env.UsesLocalWitnessesCompleteness (n + f.local_length n) ((g (f.output n)).operations (n + f.local_length n)) := by
  rw [env.usesLocalWitnessesCompleteness_iff_forAll, env.usesLocalWitnessesCompleteness_iff_forAll,
    env.usesLocalWitnessesCompleteness_iff_forAll, bind_forAll]
end Circuit

-- more theorems about forAll / forAllFlat

namespace FlatOperation
theorem forAll_implies {c c' : Condition F} (n : ℕ) {ops : List (FlatOperation F)} :
    (forAll n (c.implies c').ignoreSubcircuit ops) → (forAll n c ops → forAll n c' ops) := by
  simp only [Condition.implies, Condition.ignoreSubcircuit]
  intro h
  induction ops generalizing n with
  | nil => simp [forAll_empty]
  | cons op ops ih =>
    specialize ih (op.single_local_length + n)
    cases op <;> simp_all [forAll_cons, Condition.applyFlat]
end FlatOperation

namespace Operations
lemma forAll_toFlat_iff (n : ℕ) (condition : Condition F) (ops : Operations F) :
    FlatOperation.forAll n condition ops.toFlat ↔ ops.forAllFlat n condition := by
  induction ops using Operations.induct generalizing n with
  | empty => simp only [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | witness | assert | lookup =>
    simp_all [forAllFlat, forAll, toFlat, FlatOperation.forAll, Condition.applyFlat, FlatOperation.local_length]
  | subcircuit s ops ih =>
    simp_all only [forAllFlat, forAll, toFlat]
    rw [FlatOperation.forAll_append, s.local_length_eq]
    simp_all
end Operations

/-- An environment respects local witnesses iff it does so in the flattened variant. -/
lemma Environment.usesLocalWitnesses_iff_flat {n: ℕ} {ops: Operations F} {env: Environment F} :
    env.UsesLocalWitnesses n ops ↔
    env.UsesLocalWitnessesFlat n ops.toFlat := by
  simp only [UsesLocalWitnessesFlat, UsesLocalWitnesses]
  rw [Operations.forAll_toFlat_iff]

-- theorems about witness generation

namespace FlatOperation
lemma dynamicWitness_length {op : FlatOperation F} {init : List F} :
    (op.dynamicWitness init).length = op.single_local_length := by
  rcases op <;> simp [dynamicWitness, single_local_length]

lemma dynamicWitnesses_length {ops : List (FlatOperation F)} (init : List F) :
    (dynamicWitnesses ops init).length = init.length + local_length ops := by
  induction ops generalizing init with
  | nil => rw [dynamicWitnesses, List.foldl_nil, local_length, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamicWitnesses, local_length_cons, dynamicWitness_length]

lemma dynamicWitnesses_cons {op : FlatOperation F} {ops: List (FlatOperation F)} {acc : List F} :
    dynamicWitnesses (op :: ops) acc = dynamicWitnesses ops (acc ++ op.dynamicWitness acc) := by
  simp only [dynamicWitnesses, List.foldl_cons]

lemma getElem?_dynamicWitnesses_of_lt {ops: List (FlatOperation F)} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (dynamicWitnesses ops acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamicWitnesses]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ op.dynamicWitness acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma getElem?_dynamicWitnesses_cons_right {op : FlatOperation F} {ops: List (FlatOperation F)} {init : List F} {i : ℕ} (hi : i < op.single_local_length) :
    (dynamicWitnesses (op :: ops) init)[init.length + i]?.getD 0 = (op.dynamicWitness init)[i]'(dynamicWitness_length (F:=F) ▸ hi) := by
  rw [dynamicWitnesses_cons, getElem?_dynamicWitnesses_of_lt (by simp [hi, dynamicWitness_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

/--
Flat version of the final theorem in this section, `Circuit.proverEnvironment_usesLocalWitnesses`.
-/
theorem proverEnvironment_usesLocalWitnesses {ops : List (FlatOperation F)} (init : List F) :
  (∀ (env env' : Environment F),
    forAll init.length { witness n _ c := env.agreesBelow n env' → c env = c env' } ops) →
    (proverEnvironment ops init).UsesLocalWitnessesFlat init.length ops := by
  simp only [proverEnvironment, Environment.UsesLocalWitnessesFlat, Environment.extends_vector]
  intro h_computable
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable ⊢
    cases op with
    | assert | lookup  =>
      simp_all [dynamicWitnesses_cons, Condition.applyFlat, single_local_length, dynamicWitness]
    | witness m compute =>
      simp_all only [Condition.applyFlat, single_local_length, dynamicWitness, Environment.agreesBelow]
      -- get rid of ih first
      constructor; case right =>
        specialize ih (init ++ (compute (.fromList init)).toList)
        simp only [List.length_append, Vector.length_toList] at ih
        ring_nf at *
        exact ih fun _ _ => (h_computable ..).right
      clear ih
      replace h_computable := fun env env' => (h_computable env env').left
      intro i
      simp only [Environment.fromList]
      rw [getElem?_dynamicWitnesses_cons_right i.is_lt]
      simp only [dynamicWitness, Vector.getElem_toList]
      congr 1
      apply h_computable
      intro j hj
      simp [Environment.fromList, hj, getElem?_dynamicWitnesses_of_lt]
end FlatOperation

/--
If a circuit satisfies `computableWitnesses`, then the `proverEnvironment` agrees with the
circuit's witness generators.
-/
theorem Circuit.proverEnvironment_usesLocalWitnesses (circuit : Circuit F α) (init : List F) :
  circuit.computableWitnesses init.length →
    (circuit.proverEnvironment init).UsesLocalWitnesses init.length (circuit.operations init.length) := by
  intro h_computable
  simp_all only [proverEnvironment, Circuit.computableWitnesses, Operations.computableWitnesses,
    ←Operations.forAll_toFlat_iff, Environment.UsesLocalWitnesses]
  exact FlatOperation.proverEnvironment_usesLocalWitnesses init h_computable

lemma Environment.agreesBelow_of_le {F} {n m : ℕ} {env env' : Environment F} :
    env.agreesBelow n env' → m ≤ n → env.agreesBelow m env' :=
  fun h_same hi i hi' => h_same i (Nat.lt_of_lt_of_le hi' hi)

namespace FlatOperation
/--
If all witness generators only access the environment below the current offset, then
the entire circuit only accesses the environment below `n + local_length`.

This is not currently used, but seemed like a nice result to have.
-/
theorem onlyAccessedBelow_all {ops : List (FlatOperation F)} (n : ℕ) :
  forAll n { witness n _ := Environment.onlyAccessedBelow n } ops →
    Environment.onlyAccessedBelow (n + local_length ops) (local_witnesses · ops) := by
  intro h_comp env env' h_env
  simp only
  induction ops generalizing n with
  | nil => simp [local_witnesses]
  | cons op ops ih =>
    simp_all only [forAll_cons, local_length_cons]
    have h_ih := h_comp.right
    replace h_comp := h_comp.left
    replace h_ih := ih (op.single_local_length + n) h_ih
    ring_nf at *
    specialize h_ih h_env
    clear ih
    cases op with
    | assert | lookup =>
      simp_all only [Condition.applyFlat, local_witnesses]
    | witness m c =>
      simp_all only [Condition.applyFlat, local_witnesses,
        Environment.onlyAccessedBelow, Environment.agreesBelow]
      congr 1
      apply h_comp env env'
      intro i hi
      exact h_env i (by linarith)
end FlatOperation
