/-
This file contains theorems that immediately follow from the definitions in `Circuit.Operations` and `Circuit.Basic`.

For more complicated interconnected theorems, we have separate files,
such as `Circuit.Subcircuit` which focuses on establishing the foundation for subcircuit composition.
-/
import Clean.Circuit.Basic
import Clean.Circuit.Provable

variable {F : Type} [Field F] {α β : Type}

namespace Operations
@[circuit_norm]
theorem append_localLength {a b: Operations F} :
    (a ++ b).localLength = a.localLength + b.localLength := by
  induction a using induct with
  | empty => ac_rfl
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp_all +arith [localLength]

theorem localLength_cons {a : Operation F} {as : Operations F} :
    localLength (a :: as) = a.localLength + as.localLength := by
  cases a <;> simp_all [localLength, Operation.localLength]

theorem localWitnesses_cons (op : Operation F) (ops : Operations F) (tape : Tape F) :
  localWitnesses tape (op :: ops) =
    (op.localWitnesses tape ++ ops.localWitnesses tape).cast (localLength_cons.symm) := by
  cases op <;> simp only [localWitnesses, Operation.localWitnesses, Vector.cast_rfl]
  all_goals (rw [Vector.empty_append]; simp)

@[circuit_norm]
theorem forAll_empty {condition : Condition F} {n : ℕ} : forAll n condition [] = True := rfl

@[circuit_norm]
theorem forAll_cons {condition : Condition F} {offset : ℕ} {op : Operation F} {ops : Operations F} :
  forAll offset condition (op :: ops) ↔
    condition.apply offset op ∧ forAll (op.localLength + offset) condition ops := by
  cases op <;> simp [forAll, Operation.localLength, Condition.apply]

@[circuit_norm]
theorem forAll_append {condition : Condition F} {offset : ℕ} {as bs: Operations F} :
  forAll offset condition (as ++ bs) ↔
    forAll offset condition as ∧ forAll (as.localLength + offset) condition bs := by
  induction as using induct generalizing offset with
  | empty => simp [forAll_empty, localLength]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp +arith only [List.cons_append, forAll, localLength, ih, and_assoc]
end Operations

namespace Circuit

theorem pure_operations_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).operations n = [] := rfl

theorem bind_operations_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl

theorem map_operations_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).operations n = f.operations n := rfl

theorem pure_localLength_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).localLength n = 0 := rfl

theorem bind_localLength_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
    (f >>= g).localLength n = f.localLength n + (g (f.output n)).localLength (n + f.localLength n) := by
  show (f.operations n ++ (g _).operations _).localLength = _
  rw [Operations.append_localLength]

theorem map_localLength_eq (f : Circuit F α) (g : α → β) (n : ℕ) :
  (g <$> f).localLength n = f.localLength n := rfl

theorem pure_output_eq (a : α) (n : ℕ) :
  (pure a : Circuit F α).output n = a := rfl

theorem bind_output_eq (f : Circuit F α) (g : α → Circuit F β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.localLength n) := rfl

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
    · simp only [bind_output_eq, bind_localLength_eq, add_assoc]
    · simp only [bind_operations_eq, bind_localLength_eq, bind_output_eq,
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
with their `Soundness` statement.

Together with `Circuit.Subcircuit.can_replace_subcircuits`, it justifies assuming the nested version
`ConstraintsHold.Soundness` when defining soundness for formal circuits,
because it is implied by the flat version.
-/
theorem can_replace_soundness {ops : Operations F} {env} :
  ConstraintsHold env ops → ConstraintsHold.Soundness env ops := by
  intro h
  induction ops using Operations.induct with
  | empty => trivial
  | witness | assert | lookup | yield | use =>
    simp_all [ConstraintsHold.Soundness, ConstraintsHold, RawTable.imply_soundness]
  | subcircuit circuit ops ih =>
    dsimp only [ConstraintsHold.Soundness]
    dsimp only [ConstraintsHold] at h
    exact ⟨ fun idx => circuit.imply_soundness idx env h.left, ih h.right ⟩

end Circuit

-- more about `FlatOperation`, and relationships to `Operations`

namespace FlatOperation
lemma localLength_cons {F} {op : FlatOperation F} {ops : List (FlatOperation F)} :
    localLength (op :: ops) = op.singleLocalLength + localLength ops := by
  cases op <;> simp +arith only [localLength, singleLocalLength]

lemma localLength_append {F} {a b: List (FlatOperation F)} :
    localLength (a ++ b) = localLength a + localLength b := by
  induction a using localLength.induct with
  | case1 => simp only [List.nil_append, localLength]; ac_rfl
  | case2 _ _ _ ih =>
    simp only [List.cons_append, localLength, ih]; ac_rfl
  | case3 _ _ ih | case4 _ _ ih | case5 _ _ ih | case6 _ _ ih =>
    simp only [List.cons_append, localLength, ih]

theorem forAll_empty {condition : Condition F} {n : ℕ} : forAll n condition [] = True := rfl

theorem forAll_cons {condition : Condition F} {offset : ℕ} {op : FlatOperation F} {ops : List (FlatOperation F)} :
  forAll offset condition (op :: ops) ↔
    condition.applyFlat offset op ∧ forAll (op.singleLocalLength + offset) condition ops := by
  cases op <;> simp [forAll, Condition.applyFlat, singleLocalLength]

lemma forAll_append {condition : Condition F} {ops ops' : List (FlatOperation F)} (n : ℕ) :
  forAll n condition (ops ++ ops') ↔
    forAll n condition ops ∧ forAll (localLength ops + n) condition ops' := by
  induction ops generalizing n with
  | nil => simp only [List.nil_append, forAll, localLength, zero_add, true_and]
  | cons op ops ih =>
    specialize ih (n + op.singleLocalLength)
    simp_all +arith [forAll_cons, localLength_cons, and_assoc]

lemma localWitnesses_append {F} {a b: List (FlatOperation F)} {tape : Tape F} :
    (localWitnesses tape (a ++ b)).toArray = (localWitnesses tape a).toArray ++ (localWitnesses tape b).toArray := by
  induction a using FlatOperation.localLength.induct with
  | case1 => simp only [List.nil_append, localLength, localWitnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, Vector.toArray_append, ih, Array.append_assoc]
  | case5 _ _ ih | case6 _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, ih]
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, ih]

/--
The witness length from flat and nested operations is the same
-/
lemma localLength_toFlat {ops : Operations F} :
    localLength ops.toFlat = ops.localLength := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ ops ih | assert _ ops ih | lookup _ ops ih | yield _ ops ih | use _ ops ih | subcircuit _ ops ih =>
    dsimp only [Operations.toFlat, Operations.localLength]
    generalize ops.toFlat = flat_ops at *
    generalize Operations.localLength ops = n at *
    induction flat_ops using localLength.induct generalizing n with
    | case1 => simp_all [localLength, add_comm, Subcircuit.localLength_eq]
    | case2 m' _ ops' ih' =>
      dsimp only [localLength, witness] at *
      specialize ih' (n - m') (by rw [←ih]; omega)
      simp_all +arith only [localLength_append, localLength]
      try omega
    | case3 ops _ ih' | case4 ops _ ih' | case5 ops _ ih' | case6 ops _ ih' =>
      simp_all only [localLength_append, forall_eq', localLength]

/--
The witnesses created from flat and nested operations are the same
-/
lemma localWitnesses_toFlat {ops : Operations F} {tape : Tape F} :
  (localWitnesses tape ops.toFlat).toArray = (ops.localWitnesses tape).toArray := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp only [Operations.toFlat, Operations.localLength, Operations.localWitnesses, Vector.toArray_append]
    rw [←ih]
    try rw [localWitnesses_append]
    try simp only [localLength, localWitnesses, Vector.toArray_append, Subcircuit.witnesses, Vector.toArray_cast]
end FlatOperation

namespace Environment
open FlatOperation (localLength localWitnesses localYields)
/-
what follows are relationships between different versions of `Environment.UsesLocalWitnesses`
-/

lemma tape_extends_append {F} [Field F] {m n : ℕ} {tape : Tape F} {v1 : Vector F m} {v2 : Vector F n} {offset : ℕ} :
    tape.ExtendsVector (v1 ++ v2) offset ↔
      tape.ExtendsVector v1 offset ∧ tape.ExtendsVector v2 (m + offset) := by
  simp only [Tape.ExtendsVector]
  constructor
  · intro h
    constructor
    · intro i
      have := h ⟨i, by omega⟩
      simp [Vector.getElem_append, i.isLt] at this
      exact this
    · intro i
      have := h ⟨m + i, by omega⟩
      simp [Vector.getElem_append] at this
      ring_nf at this ⊢
      exact this
  · intro ⟨h1, h2⟩ ⟨i, hi⟩
    simp [Vector.getElem_append]
    by_cases hi' : i < m
    · simp [hi']; exact h1 ⟨i, hi'⟩
    · simp [hi']
      have := h2 ⟨i - m, by omega⟩
      ring_nf at this ⊢
      convert this using 2
      omega

lemma env_extends_witness {F} [Field F] {n : ℕ} {ops : List (FlatOperation F)} {env : Environment F} {m c} :
    env.tape.ExtendsVector (localWitnesses env.tape (.witness m c :: ops)) n ↔
      (env.tape.ExtendsVector (c env.tape) n ∧ env.tape.ExtendsVector (localWitnesses env.tape ops) (m + n)) := by
  simp only [localWitnesses]
  rw [tape_extends_append]

theorem usesLocalWitnessesFlat_iff_extends {env : Environment F} (n : ℕ) {ops : List (FlatOperation F)}  :
    env.UsesLocalWitnessesFlat n ops ↔
      env.tape.ExtendsVector (localWitnesses env.tape ops) n ∧ localYields env.tape ops ⊆ env.yielded := by
  induction ops using FlatOperation.induct generalizing n with
  | empty => simp [UsesLocalWitnessesFlat, FlatOperation.forAll_empty, Tape.ExtendsVector, localLength, localYields]
  | witness m c _ ih =>
    simp only [UsesLocalWitnessesFlat, FlatOperation.forAll, localWitnesses, localYields]
    rw [tape_extends_append]
    have ih_applied := ih (m + n)
    simp only [UsesLocalWitnessesFlat, FlatOperation.forAll] at ih_applied
    rw [ih_applied]
    simp [and_assoc]
  | yield nl _ ih =>
    simp only [UsesLocalWitnessesFlat, FlatOperation.forAll, localWitnesses, localYields]
    have ih_applied := ih n
    simp only [UsesLocalWitnessesFlat] at ih_applied
    rw [ih_applied]
    constructor
    · intro ⟨h_mem, h_ext, h_subset⟩
      exact ⟨h_ext, Set.union_subset (Set.singleton_subset_iff.mpr h_mem) h_subset⟩
    · intro ⟨h_ext, h_union_subset⟩
      refine ⟨?_, h_ext, ?_⟩
      · exact Set.mem_of_subset_of_mem h_union_subset (Set.mem_union_left _ (Set.mem_singleton _))
      · exact Set.Subset.trans Set.subset_union_right h_union_subset
  | use nl _ ih =>
    simp only [UsesLocalWitnessesFlat, FlatOperation.forAll, localWitnesses, localYields]
    have ih_applied := ih n
    simp only [UsesLocalWitnessesFlat] at ih_applied
    rw [ih_applied]
    simp [and_assoc]
  | assert | lookup =>
    simp_all [UsesLocalWitnessesFlat, circuit_norm,
      FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.singleLocalLength, localYields]

theorem can_replace_usesLocalWitnessesCompleteness {env : Environment F} {ops : Operations F} {n : ℕ} (h : ops.SubcircuitsConsistent n) :
  env.UsesLocalWitnesses n ops → env.UsesLocalWitnessesCompleteness n ops := by
  induction ops, n, h using Operations.inductConsistent with
  | empty => intros; trivial
  | witness | assert | lookup | yield | use =>
    simp_all +arith [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll]
  | subcircuit n circuit ops ih =>
    simp only [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll_cons, Condition.apply]
    intro h
    rw [add_comm]
    apply And.intro ?_ (ih h.right)
    apply circuit.imply_usesLocalWitnesses
    · have := usesLocalWitnessesFlat_iff_extends (env := env) n (ops := circuit.ops)
      exact this.mp h.left |>.left
    · have := usesLocalWitnessesFlat_iff_extends (env := env) n (ops := circuit.ops)
      exact this.mp h.left |>.right

theorem usesLocalWitnessesCompleteness_iff_forAll (n : ℕ) {env : Environment F} {ops : Operations F} :
  env.UsesLocalWitnessesCompleteness n ops ↔ ops.forAll n {
    witness m _ c := env.tape.ExtendsVector (c env.tape) m,
    yield _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit _ _ s := s.UsesLocalWitnesses env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | yield | use | subcircuit =>
    simp_all +arith [UsesLocalWitnessesCompleteness, Operations.forAll]

theorem usesLocalWitnesses_iff_forAll (n : ℕ) {env : Environment F} {ops : Operations F} :
  env.UsesLocalWitnesses n ops ↔ ops.forAll n {
    witness n _ c := env.tape.ExtendsVector (c env.tape) n,
    yield _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit n _ s := FlatOperation.forAll n {
      witness n _ c := env.tape.ExtendsVector (c env.tape) n,
      yield _ nl := nl.eval env.tape ∈ env.yielded
    } s.ops
  } := by
  simp only [UsesLocalWitnesses, Operations.forAllFlat]
end Environment

namespace Circuit

theorem ConstraintsHold.soundness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
  ConstraintsHold.Soundness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Soundness (l.entry.map env),
    use _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit _ _ s := ∀ idx, s.Soundness idx env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp_all only [ConstraintsHold.Soundness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih

theorem ConstraintsHold.completeness_iff_forAll (n : ℕ) (env : Environment F) (ops : Operations F) :
  ConstraintsHold.Completeness env ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Completeness (l.entry.map env),
    use _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit _ _ s := s.Completeness env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp_all only [ConstraintsHold.Completeness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.Subcircuit.can_replace_subcircuits`, it justifies only proving the nested version
`ConstraintsHold.Completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {env} {ops : Operations F} {n : ℕ} (h : ops.SubcircuitsConsistent n) : env.UsesLocalWitnesses n ops →
    ConstraintsHold.Completeness env ops → ConstraintsHold env ops := by
  induction ops, n, h using Operations.inductConsistent with
  | empty => intros; exact trivial
  | witness | assert | lookup | yield | use =>
    simp_all [circuit_norm, Environment.UsesLocalWitnesses, Operations.forAllFlat, Operations.forAll, RawTable.implied_by_completeness]
  | subcircuit n circuit ops ih =>
    simp_all only [ConstraintsHold, ConstraintsHold.Completeness, Environment.UsesLocalWitnesses, Operations.forAllFlat, Operations.forAll, and_true]
    intro h_env h_compl
    have this := Environment.usesLocalWitnessesFlat_iff_extends (env := env) n (ops := circuit.ops)
    apply circuit.implied_by_completeness env (this.mp h_env.left |>.left) (this.mp h_env.left |>.right) h_compl.left
end Circuit

namespace Circuit
-- more theorems about forAll

variable {α β : Type} {n : ℕ} {prop : Condition F} {env : Environment F}

@[circuit_norm]
theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} :
  ((f >>= g).operations n).forAll n prop ↔
    (f.operations n).forAll n prop ∧ (((g (f.output n)).operations (n + f.localLength n)).forAll (n + f.localLength n)) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  rw [h_ops, Operations.forAll_append, add_comm n]

-- definition of `forAll` for circuits which uses the same offset in two places

@[reducible, circuit_norm]
def forAll (circuit : Circuit F α) (n : ℕ) (prop : Condition F) :=
  (circuit.operations n).forAll n prop

lemma forAll_def {circuit : Circuit F α} {n : ℕ} :
  circuit.forAll n prop ↔ (circuit.operations n).forAll n prop := by rfl

theorem bind_forAll' {f : Circuit F α} {g : α → Circuit F β} :
  (f >>= g).forAll n prop ↔
    f.forAll n prop ∧ ((g (f.output n)).forAll (n + f.localLength n) prop) := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  simp only [forAll]
  rw [bind_forAll]

theorem ConstraintsHold.soundness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  ConstraintsHold.Soundness env (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Soundness (l.entry.map env),
    use _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit _ _ s := ∀ idx, s.Soundness idx env
  } := by
  rw [forAll_def, ConstraintsHold.soundness_iff_forAll n]

theorem ConstraintsHold.completeness_iff_forAll' {env : Environment F} {circuit : Circuit F α} {n : ℕ} :
  ConstraintsHold.Completeness env (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Completeness (l.entry.map env),
    use _ nl := nl.eval env.tape ∈ env.yielded,
    subcircuit _ _ s := s.Completeness env
  } := by
  rw [forAll_def, ConstraintsHold.completeness_iff_forAll n]

-- specializations

@[circuit_norm] theorem ConstraintsHold.append_soundness {as bs : Operations F} :
  ConstraintsHold.Soundness env (as ++ bs)
  ↔ ConstraintsHold.Soundness env as ∧ ConstraintsHold.Soundness env bs := by
  rw [ConstraintsHold.soundness_iff_forAll 0, Operations.forAll_append,
    ←ConstraintsHold.soundness_iff_forAll 0, ←ConstraintsHold.soundness_iff_forAll (as.localLength + 0)]

@[circuit_norm] theorem ConstraintsHold.bind_soundness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  ConstraintsHold.Soundness env ((f >>= g).operations n)
  ↔ ConstraintsHold.Soundness env (f.operations n) ∧
    ConstraintsHold.Soundness env ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [ConstraintsHold.soundness_iff_forAll n, ConstraintsHold.soundness_iff_forAll n,
    ConstraintsHold.soundness_iff_forAll (n + f.localLength n), bind_forAll]

@[circuit_norm] theorem ConstraintsHold.append_completeness {as bs : Operations F} :
  ConstraintsHold.Completeness env (as ++ bs)
  ↔ ConstraintsHold.Completeness env as ∧ ConstraintsHold.Completeness env bs := by
  rw [ConstraintsHold.completeness_iff_forAll 0, Operations.forAll_append,
    ←ConstraintsHold.completeness_iff_forAll 0, ←ConstraintsHold.completeness_iff_forAll (as.localLength + 0)]

@[circuit_norm] theorem ConstraintsHold.bind_completeness {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  ConstraintsHold.Completeness env ((f >>= g).operations n)
  ↔ ConstraintsHold.Completeness env (f.operations n) ∧
    ConstraintsHold.Completeness env ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [ConstraintsHold.completeness_iff_forAll n, ConstraintsHold.completeness_iff_forAll n,
    ConstraintsHold.completeness_iff_forAll (n + f.localLength n), bind_forAll]

@[circuit_norm] theorem ConstraintsHold.append_localWitnesses {as bs : Operations F} (n : ℕ) :
  env.UsesLocalWitnessesCompleteness n (as ++ bs)
  ↔ env.UsesLocalWitnessesCompleteness n as ∧ env.UsesLocalWitnessesCompleteness (as.localLength + n) bs := by
  rw [env.usesLocalWitnessesCompleteness_iff_forAll, Operations.forAll_append,
    ←env.usesLocalWitnessesCompleteness_iff_forAll n, ←env.usesLocalWitnessesCompleteness_iff_forAll (as.localLength + n)]

@[circuit_norm] theorem ConstraintsHold.bind_usesLocalWitnesses {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  env.UsesLocalWitnessesCompleteness n ((f >>= g).operations n)
  ↔ env.UsesLocalWitnessesCompleteness n (f.operations n) ∧
    env.UsesLocalWitnessesCompleteness (n + f.localLength n) ((g (f.output n)).operations (n + f.localLength n)) := by
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
    specialize ih (op.singleLocalLength + n)
    cases op <;> simp_all [forAll_cons, Condition.applyFlat, singleLocalLength]

theorem forAll_True {c : Condition F} {n : ℕ} {ops : List (FlatOperation F)} :
    c.isTrue → forAll n c ops := by
  intro ⟨h_wit, h_assert, h_lookup, h_yield, h_use, h_sub⟩
  induction ops generalizing n with
  | nil => simp [forAll]
  | cons op ops ih =>
    rw [forAll_cons]
    constructor
    · cases op <;> simp [Condition.applyFlat, h_wit, h_assert, h_lookup, h_yield, h_use, h_sub]
    · exact ih
end FlatOperation

namespace Operations
lemma forAll_toFlat_iff (n : ℕ) (condition : Condition F) (ops : Operations F) :
    FlatOperation.forAll n condition ops.toFlat ↔ ops.forAllFlat n condition := by
  induction ops using Operations.induct generalizing n with
  | empty => simp only [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | witness | assert | lookup | yield | use =>
    simp_all [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | subcircuit s ops ih =>
    simp_all only [forAllFlat, forAll, toFlat]
    rw [FlatOperation.forAll_append, s.localLength_eq]
    simp_all
end Operations

/-- An environment respects local witnesses iff it does so in the flattened variant. -/
lemma Environment.usesLocalWitnesses_iff_flat {n : ℕ} {ops : Operations F} {env : Environment F} :
    env.UsesLocalWitnesses n ops ↔
    env.UsesLocalWitnessesFlat n ops.toFlat := by
  simp only [UsesLocalWitnessesFlat, UsesLocalWitnesses]
  rw [Operations.forAll_toFlat_iff]

-- theorems about witness generation

namespace FlatOperation
lemma dynamicWitness_length {op : FlatOperation F} {init : List F} :
    (op.dynamicWitness init).length = op.singleLocalLength := by
  rcases op <;> simp [dynamicWitness, singleLocalLength]

lemma dynamicWitnesses_length {ops : List (FlatOperation F)} (init : List F) :
    (dynamicWitnesses ops init).length = init.length + localLength ops := by
  induction ops generalizing init with
  | nil => rw [dynamicWitnesses, List.foldl_nil, localLength, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamicWitnesses, localLength_cons, dynamicWitness_length]

lemma dynamicWitnesses_cons {op : FlatOperation F} {ops : List (FlatOperation F)} {acc : List F} :
    dynamicWitnesses (op :: ops) acc = dynamicWitnesses ops (acc ++ op.dynamicWitness acc) := by
  simp only [dynamicWitnesses, List.foldl_cons]

lemma getElem?_dynamicWitnesses_of_lt {ops : List (FlatOperation F)} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (dynamicWitnesses ops acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamicWitnesses]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ op.dynamicWitness acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma getElem?_dynamicWitnesses_cons_right {op : FlatOperation F} {ops : List (FlatOperation F)} {init : List F} {i : ℕ} (hi : i < op.singleLocalLength) :
    (dynamicWitnesses (op :: ops) init)[init.length + i]?.getD 0 = (op.dynamicWitness init)[i]'(dynamicWitness_length (F:=F) ▸ hi) := by
  rw [dynamicWitnesses_cons, getElem?_dynamicWitnesses_of_lt (by simp [hi, dynamicWitness_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

/--
Flat version of the final theorem in this section, `Circuit.proverEnvironment_usesLocalWitnesses`.
-/
theorem proverEnvironment_usesLocalWitnesses {ops : List (FlatOperation F)} (init : List F) :
  (∀ (tape tape' : Tape F),
    forAll init.length {
      witness n _ c := tape.AgreesBelow n tape' → c tape = c tape'
    } ops) →
    (proverEnvironment ops init).UsesLocalWitnessesFlat init.length ops := by
  simp only [proverEnvironment, Environment.UsesLocalWitnessesFlat, Tape.ExtendsVector]
  intro h_computable
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable ⊢
    cases op with
    | assert | lookup | use _ =>
      simp only [dynamicWitnesses_cons, dynamicWitness, List.append_nil, Condition.applyFlat,
        singleLocalLength, FlatOperation.proverTape, Tape.fromList, zero_add] at h_computable ⊢ ih
      constructor
      · trivial
      · specialize ih init (by aesop)
        apply forAll_implies _ _ ih
        apply forAll_True
        and_intros
        · intro _ _ _ h; exact h
        · intro _ _ _; trivial
        · intro _ _ _; trivial
        · intro _ _ h_in
          simp only [collectYielded, yieldSet, Set.mem_iUnion] at h_in ⊢
          obtain ⟨op, h_in_op⟩ := h_in
          obtain ⟨h_mem, h_in_set⟩ := h_in_op
          refine ⟨op, ?_, h_in_set⟩
          exact List.mem_cons_of_mem _ h_mem
        · intro _ _ _; trivial
        · simp [Condition.ignoreSubcircuit]
    | yield nl =>
      simp only [dynamicWitnesses_cons, dynamicWitness, List.append_nil, Condition.applyFlat,
        singleLocalLength, FlatOperation.proverTape, Tape.fromList, zero_add, forAll_cons] at h_computable ⊢
      constructor
      · rw [FlatOperation.collectYielded_cons_yield]
        left
        rfl
      · have ih_applied := ih init (fun tape tape' => (h_computable tape tape').right)
        simp [FlatOperation.proverTape] at ih_applied ⊢
        apply forAll_implies _ _ ih_applied
        apply forAll_True
        and_intros
        · intro _ _ _ h; exact h
        · intro _ _ _; trivial
        · intro _ _ _; trivial
        · intro _ _ h_in
          simp only [collectYielded, yieldSet, Set.mem_iUnion] at h_in ⊢
          obtain ⟨op, h_in_op⟩ := h_in
          obtain ⟨h_mem, h_in_set⟩ := h_in_op
          refine ⟨op, ?_, h_in_set⟩
          exact List.mem_cons_of_mem _ h_mem
        · intro _ _ _; trivial
        · simp [Condition.ignoreSubcircuit]
    | witness m compute =>
      simp_all only [Condition.applyFlat, singleLocalLength, Tape.AgreesBelow]
      -- get rid of ih first
      constructor; case right =>
        specialize ih (init ++ (compute (.fromList init)).toList)
        simp only [List.length_append, Vector.length_toList] at ih
        ring_nf at *
        have h_tape_eq : proverTape (witness m compute :: ops) init = proverTape ops (init ++ (compute (.fromList init)).toList) := by
          simp [proverTape, dynamicWitnesses_cons, dynamicWitness]
        simp only [h_tape_eq]
        have h_collect : collectYielded (witness m compute :: ops) (proverTape ops (init ++ (compute (.fromList init)).toList)) =
                         collectYielded ops (proverTape ops (init ++ (compute (.fromList init)).toList)) := by
          simp [collectYielded, yieldSet]
        simp only [h_collect]
        exact ih fun _ _ => (h_computable ..).right
      clear ih
      replace h_computable := fun tape tape' => (h_computable tape tape').left
      intro i
      simp only [proverTape, Tape.fromList]
      rw [getElem?_dynamicWitnesses_cons_right i.is_lt]
      simp only [dynamicWitness, Vector.getElem_toList]
      congr 1
      apply h_computable
      intro j hj
      simp [Tape.fromList, hj, getElem?_dynamicWitnesses_of_lt]
end FlatOperation

/--
If a circuit satisfies `computableWitnesses`, then the `proverEnvironment` agrees with the
circuit's witness generators.
-/
theorem Circuit.proverEnvironment_usesLocalWitnesses (circuit : Circuit F α) (init : List F) :
  circuit.ComputableWitnesses init.length →
    (circuit.proverEnvironment init).UsesLocalWitnesses init.length (circuit.operations init.length) := by
  intro h_computable
  simp_all only [proverEnvironment, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
    ←Operations.forAll_toFlat_iff, Environment.UsesLocalWitnesses]
  exact FlatOperation.proverEnvironment_usesLocalWitnesses init h_computable

lemma Tape.agreesBelow_of_le {F} {n m : ℕ} {tape tape' : Tape F} :
    tape.AgreesBelow n tape' → m ≤ n → tape.AgreesBelow m tape' :=
  fun h_same hi i hi' => h_same i (Nat.lt_of_lt_of_le hi' hi)

namespace FlatOperation
/--
If all witness generators only access the environment below the current offset, then
the entire circuit only accesses the environment below `n + localLength`.

This is not currently used, but seemed like a nice result to have.
-/
theorem onlyAccessedBelow_all {ops : List (FlatOperation F)} (n : ℕ) :
  forAll n { witness n _ := Tape.OnlyAccessedBelow n } ops →
    Tape.OnlyAccessedBelow (n + localLength ops) (fun tape => localWitnesses tape ops) := by
  intro h_comp tape tape' h_tape
  simp only
  induction ops generalizing n with
  | nil => simp [localWitnesses]
  | cons op ops ih =>
    simp_all only [forAll_cons, localLength_cons]
    have h_ih := h_comp.right
    replace h_comp := h_comp.left
    replace h_ih := ih (op.singleLocalLength + n) h_ih
    ring_nf at *
    specialize h_ih h_tape
    clear ih
    cases op with
    | assert | lookup | yield | use =>
      simp_all only [Condition.applyFlat, localWitnesses]
    | witness m c =>
      simp_all only [Condition.applyFlat, localWitnesses,
        Tape.OnlyAccessedBelow, Tape.AgreesBelow]
      congr 1
      apply h_comp tape tape'
      intro i hi
      exact h_tape i (by linarith)
end FlatOperation

-- theorem about relationship between FormalCircuit and GeneralFormalCircuit

/--
`FormalCircuit.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` a generalization of
`FormalCircuit`. The idea is to make `FormalCircuit.Assumption` available in the soundness
by assuming it within `GeneralFormalCircuit.Spec`.
-/
def FormalCircuit.isGeneralFormalCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Output] [ProvableType Input]
    {SoundnessIndex : Type} (orig : FormalCircuit F Input Output SoundnessIndex): GeneralFormalCircuit F Input Output := by
  let Spec input output := ∀ idx, orig.Assumptions idx input → orig.Spec idx input output
  exact {
    elaborated := orig.elaborated,
    Assumptions := fun input => ∀ idx, orig.Assumptions idx input,
    Spec,
    soundness := by
      intro offset env input_var input h_input h_holds
      dsimp [Spec]
      intro idx h_assumptions_idx
      exact orig.soundness offset env input_var input h_input idx h_assumptions_idx h_holds
    ,
    completeness := by
      intro offset env input_var h_env input h_input h_assumptions
      exact orig.completeness offset env input_var h_env input h_input h_assumptions
  }

/--
`FormalAssertion.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` is a generalization of
`FormalAssertion`.  The idea is to make `FormalAssertion.Spec` available in the completeness
by putting it within `GeneralFormalCircuit.Assumption`.
-/
def FormalAssertion.isGeneralFormalCircuit (F : Type) (Input : TypeMap) [Field F] [ProvableType Input]
    (orig : FormalAssertion F Input) : GeneralFormalCircuit F Input unit := by
  let Spec input (_ : Unit) := orig.Assumptions input → orig.Spec input
  exact {
    elaborated := orig.elaborated,
    Assumptions input := orig.Assumptions input ∧ orig.Spec input,
    Spec,
    soundness := by
      simp only [GeneralFormalCircuit.Soundness, forall_eq', Spec]
      intros
      apply orig.soundness <;> trivial
    ,
    completeness := by
      simp only [GeneralFormalCircuit.Completeness, forall_eq']
      rintro _ _ _ _ ⟨ _, _ ⟩
      apply orig.completeness <;> trivial
  }
