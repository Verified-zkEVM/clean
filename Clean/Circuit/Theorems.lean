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
theorem append_localLength {sentences : PropertySet F} {a b: Operations sentences} :
    (a ++ b).localLength = a.localLength + b.localLength := by
  induction a using induct with
  | empty => ac_rfl
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp_all +arith [localLength, ih]

theorem localLength_cons {sentences : PropertySet F} {a : Operation sentences} {as : Operations sentences} :
    localLength (a :: as) = a.localLength + as.localLength := by
  cases a <;> simp_all [localLength, Operation.localLength]

theorem localWitnesses_cons {sentences : PropertySet F} (op : Operation sentences) (ops : Operations sentences) (env : Environment F) :
  localWitnesses env (op :: ops) =
    (op.localWitnesses env ++ ops.localWitnesses env).cast (localLength_cons.symm) := by
  cases op <;> simp only [localWitnesses, Operation.localWitnesses, Vector.cast_rfl]
  rw [Vector.empty_append]; simp
  rw [Vector.empty_append]; simp
  rw [Vector.empty_append]; simp
  rw [Vector.empty_append]; simp

@[circuit_norm]
theorem forAll_empty {sentences : PropertySet F} {condition : Condition sentences} {n : ℕ} : forAll n condition [] = True := rfl

@[circuit_norm]
theorem forAll_cons {sentences : PropertySet F} {condition : Condition sentences} {offset : ℕ} {op : Operation sentences} {ops : Operations sentences} :
  forAll offset condition (op :: ops) ↔
    condition.apply offset op ∧ forAll (op.localLength + offset) condition ops := by
  cases op <;> simp [forAll, Operation.localLength, Condition.apply]

@[circuit_norm]
theorem forAll_append {sentences : PropertySet F} {condition : Condition sentences} {offset : ℕ} {as bs: Operations sentences} :
  forAll offset condition (as ++ bs) ↔
    forAll offset condition as ∧ forAll (as.localLength + offset) condition bs := by
  induction as using induct generalizing offset with
  | empty => simp [forAll_empty, localLength]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp +arith only [List.cons_append, forAll, localLength, ih, and_assoc]
end Operations

namespace Circuit

theorem pure_operations_eq {sentences : PropertySet F} (a : α) (n : ℕ) :
  (pure a : Circuit sentences α).operations n = [] := rfl

theorem bind_operations_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → Circuit sentences β) (n : ℕ) :
  (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl

theorem map_operations_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → β) (n : ℕ) :
  (g <$> f).operations n = f.operations n := rfl

theorem pure_localLength_eq {sentences : PropertySet F} (a : α) (n : ℕ) :
  (pure a : Circuit sentences α).localLength n = 0 := rfl

theorem bind_localLength_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → Circuit sentences β) (n : ℕ) :
    (f >>= g).localLength n = f.localLength n + (g (f.output n)).localLength (n + f.localLength n) := by
  show (f.operations n ++ (g _).operations _).localLength = _
  rw [Operations.append_localLength]

theorem map_localLength_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → β) (n : ℕ) :
  (g <$> f).localLength n = f.localLength n := rfl

theorem pure_output_eq {sentences : PropertySet F} (a : α) (n : ℕ) :
  (pure a : Circuit sentences α).output n = a := rfl

theorem bind_output_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → Circuit sentences β) (n : ℕ) :
  (f >>= g).output n = (g (f.output n)).output (n + f.localLength n) := rfl

theorem map_output_eq {sentences : PropertySet F} (f : Circuit sentences α) (g : α → β) (n : ℕ) :
  (g <$> f).output n = g (f.output n) := rfl

/-- Extensionality theorem -/
theorem ext_iff {sentences : PropertySet F} {f g : Circuit sentences α} :
  (f = g) ↔ (∀ n, (f.output n = g.output n) ∧ (f.operations n = g.operations n)) := by
  constructor
  · intro h; subst h; intros; trivial
  intro h
  funext n
  ext1
  · exact (h n).left
  · exact (h n).right

@[ext]
theorem ext {sentences : PropertySet F} {f g : Circuit sentences α}
  (h_output : ∀ n, f.output n = g.output n)
  (h_operations : ∀ n, f.operations n = g.operations n) :
    f = g :=
  ext_iff.mpr fun n => ⟨ h_output n, h_operations n ⟩

-- lawful monad

instance {sentences : PropertySet F} : LawfulMonad (Circuit sentences) where
  bind_pure_comp {α β} (g : α → β) (f : Circuit sentences α) := by
    simp only [bind_def, Functor.map, List.append_nil]
  bind_map {α β} (g : Circuit sentences (α → β)) (f : Circuit sentences α) := rfl
  pure_bind {α β} (x : α) (f : α → Circuit sentences β) := by
    simp only [bind_def, pure, List.nil_append]; rfl
  bind_assoc {α β γ} (x : Circuit sentences α) (f : α → Circuit sentences β) (g : β → Circuit sentences γ) := by
    ext1 n
    · simp only [bind_output_eq, bind_localLength_eq, add_assoc]
    · simp only [bind_operations_eq, bind_localLength_eq, bind_output_eq,
        List.append_assoc, add_assoc]
  map_const := rfl
  id_map {α} (f : Circuit sentences α) := rfl
  seqLeft_eq {α β} (f : Circuit sentences α) (g : Circuit sentences β) := by
    funext n
    simp only [SeqLeft.seqLeft, bind, List.append_nil, Seq.seq]
    rfl
  seqRight_eq {α β} (f : Circuit sentences α) (g : Circuit sentences β) := by
    funext n
    simp only [SeqRight.seqRight, bind, Seq.seq]
    rfl
  pure_seq {α β} (g : α → β) (f : Circuit sentences α) := rfl

/--
Soundness theorem which proves that we can replace constraints in subcircuits
with their `Soundness` statement.

Together with `Circuit.Subcircuit.can_replace_subcircuits`, it justifies assuming the nested version
`ConstraintsHold.Soundness` when defining soundness for formal circuits,
because it is implied by the flat version.
-/
theorem can_replace_soundness {sentences : PropertySet F} {ops : Operations sentences} {env} (yields : YieldContext sentences) (checked : CheckedYields sentences) :
  ConstraintsHold env yields checked ops → ConstraintsHold.Soundness env yields checked ops := by
  intro h
  induction ops using Operations.induct with
  | empty => trivial
  | witness | assert | lookup | yield | use =>
    simp_all [ConstraintsHold.Soundness, ConstraintsHold, RawTable.imply_soundness]
  | subcircuit circuit ops ih =>
    dsimp only [ConstraintsHold.Soundness]
    dsimp only [ConstraintsHold] at h
    exact ⟨ circuit.imply_soundness env _ _ h.left, ih h.right ⟩

end Circuit

-- more about `FlatOperation`, and relationships to `Operations`

namespace FlatOperation
lemma localLength_cons {F} {sentences : PropertySet F} {op : FlatOperation sentences} {ops : List (FlatOperation sentences)} :
    localLength (op :: ops) = op.singleLocalLength + localLength ops := by
  cases op <;> simp +arith only [localLength, singleLocalLength]

lemma localLength_append {F} {sentences : PropertySet F} {a b: List (FlatOperation sentences)} :
    localLength (a ++ b) = localLength a + localLength b := by
  induction a using localLength.induct with
  | case1 => simp only [List.nil_append, localLength]; ac_rfl
  | case2 _ _ _ ih =>
    simp only [List.cons_append, localLength, ih]; ac_rfl
  | case3 _ _ ih | case4 _ _ ih | case5 _ _ ih | case6 _ _ ih =>
    simp only [List.cons_append, localLength, ih]

theorem forAll_empty {sentences : PropertySet F} {condition : Condition sentences} {n : ℕ} : forAll n condition [] = True := rfl

theorem forAll_cons {sentences : PropertySet F} {condition : Condition sentences} {offset : ℕ} {op : FlatOperation sentences} {ops : List (FlatOperation sentences)} :
  forAll offset condition (op :: ops) ↔
    condition.applyFlat offset op ∧ forAll (op.singleLocalLength + offset) condition ops := by
  cases op <;> simp [forAll, Condition.applyFlat, singleLocalLength]

lemma forAll_append {sentences : PropertySet F} {condition : Condition sentences} {ops ops' : List (FlatOperation sentences)} (n : ℕ) :
  forAll n condition (ops ++ ops') ↔
    forAll n condition ops ∧ forAll (localLength ops + n) condition ops' := by
  induction ops generalizing n with
  | nil => simp only [List.nil_append, forAll, localLength, zero_add, true_and]
  | cons op ops ih =>
    specialize ih (n + op.singleLocalLength)
    simp_all +arith [forAll_cons, localLength_cons, and_assoc]

lemma localWitnesses_append {F} {sentences : PropertySet F} {a b: List (FlatOperation sentences)} {env} :
    (localWitnesses env (a ++ b)).toArray = (localWitnesses env a).toArray ++ (localWitnesses env b).toArray := by
  induction a using FlatOperation.localLength.induct with
  | case1 => simp only [List.nil_append, localLength, localWitnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, Vector.toArray_append, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih | case5 _ _ ih | case6 _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, ih]

/--
The witness length from flat and nested operations is the same
-/
lemma localLength_toFlat {sentences : PropertySet F} {ops : Operations sentences} :
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
      simp_all only [localLength_append, forall_eq', localLength, List.cons_append]

/--
The witnesses created from flat and nested operations are the same
-/
lemma localWitnesses_toFlat {sentences : PropertySet F} {ops : Operations sentences} {env} :
  (localWitnesses env ops.toFlat).toArray = (ops.localWitnesses env).toArray := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp only [Operations.toFlat, Operations.localLength, Operations.localWitnesses, Vector.toArray_append]
    rw [←ih]
    try rw [localWitnesses_append]
    try simp only [localLength, localWitnesses, Vector.toArray_append, Subcircuit.witnesses, Vector.toArray_cast]
end FlatOperation

namespace Environment
open FlatOperation (localLength localWitnesses)
/-
what follows are relationships between different versions of `Environment.UsesLocalWitnessesAndYields`
-/

lemma env_extends_witness {F} {sentences : PropertySet F} {n : ℕ} {ops : List (FlatOperation sentences)} {env : Environment F} {m c} :
    env.ExtendsVector (localWitnesses env (.witness m c :: ops)) n ↔
      (env.ExtendsVector (c env) n ∧ env.ExtendsVector (localWitnesses env ops) (m + n)) := by
  simp_all only [ExtendsVector, localLength, localWitnesses, Vector.getElem_append]
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

theorem usesLocalWitnessesFlat_iff_extends {env : Environment F} {sentences : PropertySet F} (n : ℕ) {ops : List (FlatOperation sentences)}  :
    env.UsesLocalWitnessesFlat n ops ↔ env.ExtendsVector (localWitnesses env ops) n := by
  induction ops using FlatOperation.induct generalizing n with
  | empty => simp [UsesLocalWitnessesFlat, FlatOperation.forAll_empty, ExtendsVector, localLength]
  | witness m _ _ ih =>
    rw [UsesLocalWitnessesFlat, FlatOperation.forAll, env_extends_witness,←ih (m + n)]
    trivial
  | assert | lookup | yield | use =>
    simp_all [UsesLocalWitnessesFlat, circuit_norm,
      FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.singleLocalLength]

theorem usesLocalWitnessesAndYieldsFlat_iff_extends {env : Environment F} {sentences : PropertySet F} (yields : YieldContext sentences) (n : ℕ) {ops : List (FlatOperation sentences)}  :
    env.UsesLocalWitnessesAndYieldsFlat yields n ops ↔
      env.ExtendsVector (localWitnesses env ops) n ∧ FlatOperation.localYields env ops ⊆ yields.yielded := by
  induction ops using FlatOperation.induct generalizing n yields with
  | empty => simp [UsesLocalWitnessesAndYieldsFlat, FlatOperation.forAll_empty, ExtendsVector, localLength, FlatOperation.localYields]
  | witness m _ _ ih =>
    rw [UsesLocalWitnessesAndYieldsFlat, FlatOperation.forAll, env_extends_witness, FlatOperation.localYields]
    have ih' := ih yields (m + n)
    conv_rhs =>
      rw [and_assoc]
      rw [← ih']
    trivial
  | assert | lookup | use =>
    simp_all [UsesLocalWitnessesAndYieldsFlat, circuit_norm,
      FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.singleLocalLength, FlatOperation.localYields]
  | yield _ _ ih =>
    rw [UsesLocalWitnessesAndYieldsFlat, FlatOperation.forAll, FlatOperation.localYields, localWitnesses]
    simp only [Set.union_subset_iff, Set.singleton_subset_iff]
    have ih' := ih yields n
    conv_rhs =>
      rw [and_comm, and_assoc]
      arg 2
      rw [and_comm]
      rw [← ih']
    trivial

theorem can_replace_usesLocalWitnessesCompleteness {env : Environment F} {sentences : PropertySet F} {yields : YieldContext sentences} {ops : Operations sentences} {n : ℕ} (h : ops.SubcircuitsConsistent n) :
  env.UsesLocalWitnessesAndYields yields n ops → env.UsesLocalWitnessesAndYieldsCompleteness yields n ops := by
  induction ops, n, h using Operations.inductConsistent with
  | empty => intros; trivial
  | witness | assert | lookup | yield | use =>
    simp_all +arith [UsesLocalWitnessesAndYields, UsesLocalWitnessesAndYieldsCompleteness, Operations.forAllFlat, Operations.forAll]
  | subcircuit n circuit ops ih =>
    simp only [UsesLocalWitnessesAndYields, UsesLocalWitnessesAndYieldsCompleteness, Operations.forAllFlat, Operations.forAll_cons, Condition.apply]
    intro h
    rw [add_comm]
    apply And.intro ?_ (ih h.right)
    apply circuit.imply_usesLocalWitnessesAndYields
    rw [← usesLocalWitnessesAndYieldsFlat_iff_extends yields]
    exact h.left

theorem usesLocalWitnessesAndYieldsCompleteness_iff_forAll {sentences : PropertySet F} (yields : YieldContext sentences) (n : ℕ) {env : Environment F} {ops : Operations sentences} :
  env.UsesLocalWitnessesAndYieldsCompleteness yields n ops ↔ ops.forAll n {
    witness m _ c := env.ExtendsVector (c env) m,
    yield _ s := s.eval env ∈ yields.yielded,
    subcircuit _ _ s := s.UsesLocalWitnessesAndYields env yields
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | yield | use | subcircuit =>
    simp_all +arith [UsesLocalWitnessesAndYieldsCompleteness, Operations.forAll]

theorem usesLocalWitnessesAndYields_iff_forAll {sentences : PropertySet F} (yields : YieldContext sentences) (n : ℕ) {env : Environment F} {ops : Operations sentences} :
  env.UsesLocalWitnessesAndYields yields n ops ↔ ops.forAll n {
    witness n _ c := env.ExtendsVector (c env) n,
    yield _ s := s.eval env ∈ yields.yielded,
    subcircuit n _ s := FlatOperation.forAll n {
      witness n _ c := env.ExtendsVector (c env) n,
      yield _ s := s.eval env ∈ yields.yielded
    } s.ops
  } := by
  simp only [UsesLocalWitnessesAndYields, Operations.forAllFlat]

/-- Environment uses local witnesses (witness checking only) -/
def UsesLocalWitnesses {sentences : PropertySet F} (env : Environment F) (n : ℕ) (ops : Operations sentences) : Prop :=
  ops.forAllFlat n {
    witness n _ compute := env.ExtendsVector (compute env) n
  }

/-- Environment uses local yields (yield checking only) -/
def UsesLocalYields {sentences : PropertySet F} (env : Environment F) (yields : YieldContext sentences) (n : ℕ) (ops : Operations sentences) : Prop :=
  ops.forAllFlat n {
    yield _ s := s.eval env ∈ yields.yielded
  }

-- Helper lemma: if each component of conditions is equivalent, forAll is equivalent
lemma FlatOperation.forAll_equiv {sentences : PropertySet F} (n : ℕ) (c1 c2 : Condition sentences) (ops : List (FlatOperation sentences))
  (h_witness : ∀ offset m compute, c1.witness offset m compute ↔ c2.witness offset m compute)
  (h_assert : ∀ offset e, c1.assert offset e ↔ c2.assert offset e)
  (h_lookup : ∀ offset l, c1.lookup offset l ↔ c2.lookup offset l)
  (h_yield : ∀ offset s, c1.yield offset s ↔ c2.yield offset s)
  (h_use : ∀ offset s, c1.use offset s ↔ c2.use offset s) :
  FlatOperation.forAll n c1 ops ↔ FlatOperation.forAll n c2 ops := by
  induction ops generalizing n with
  | nil => simp [FlatOperation.forAll]
  | cons op ops ih =>
    simp only [FlatOperation.forAll_cons]
    cases op with
    | witness m c =>
      simp only [Condition.applyFlat]
      rw [h_witness, ih]
    | assert e =>
      simp only [Condition.applyFlat]
      rw [h_assert, ih]
    | lookup l =>
      simp only [Condition.applyFlat]
      rw [h_lookup, ih]
    | yield s =>
      simp only [Condition.applyFlat]
      rw [h_yield, ih]
    | use s =>
      simp only [Condition.applyFlat]
      rw [h_use, ih]

-- Helper lemma for FlatOperation.forAll with combined conditions
lemma FlatOperation.forAll_and {sentences : PropertySet F} (n : ℕ) (c1 c2 : Condition sentences) (ops : List (FlatOperation sentences)) :
  FlatOperation.forAll n c1 ops ∧ FlatOperation.forAll n c2 ops ↔
  FlatOperation.forAll n {
    witness n offset compute := c1.witness n offset compute ∧ c2.witness n offset compute,
    assert offset e := c1.assert offset e ∧ c2.assert offset e,
    lookup offset l := c1.lookup offset l ∧ c2.lookup offset l,
    yield offset s := c1.yield offset s ∧ c2.yield offset s,
    use offset s := c1.use offset s ∧ c2.use offset s
  } ops := by
  induction ops generalizing n with
  | nil => simp [FlatOperation.forAll]
  | cons op ops ih =>
    simp only [FlatOperation.forAll_cons]
    cases op <;> simp [Condition.applyFlat, ← ih, and_assoc, and_comm, and_left_comm]

-- Helper lemma: if each component of conditions is equivalent, forAll is equivalent
lemma Operations.forAll_equiv {sentences : PropertySet F} (n : ℕ) (c1 c2 : Condition sentences) (ops : Operations sentences)
  (h_witness : ∀ offset m compute, c1.witness offset m compute ↔ c2.witness offset m compute)
  (h_assert : ∀ offset e, c1.assert offset e ↔ c2.assert offset e)
  (h_lookup : ∀ offset l, c1.lookup offset l ↔ c2.lookup offset l)
  (h_yield : ∀ offset s, c1.yield offset s ↔ c2.yield offset s)
  (h_use : ∀ offset s, c1.use offset s ↔ c2.use offset s)
  (h_subcircuit : ∀ offset {m} (s : Subcircuit sentences m), c1.subcircuit offset s ↔ c2.subcircuit offset s) :
  ops.forAll n c1 ↔ ops.forAll n c2 := by
  induction ops using Operations.induct generalizing n with
  | empty => simp [Operations.forAll]
  | witness m c ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_witness, ih]
  | assert e ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_assert, ih]
  | lookup l ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_lookup, ih]
  | yield s ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_yield, ih]
  | use s ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_use, ih]
  | subcircuit s ops ih =>
    simp only [Operations.forAll_cons, Condition.apply]
    rw [h_subcircuit, ih]

-- Helper lemma for forAll with combined conditions
lemma Operations.forAll_and {sentences : PropertySet F} (n : ℕ) (c1 c2 : Condition sentences) (ops : Operations sentences) :
  ops.forAll n c1 ∧ ops.forAll n c2 ↔ ops.forAll n {
    witness offset m compute := c1.witness offset m compute ∧ c2.witness offset m compute,
    assert offset e := c1.assert offset e ∧ c2.assert offset e,
    lookup offset l := c1.lookup offset l ∧ c2.lookup offset l,
    yield offset s := c1.yield offset s ∧ c2.yield offset s,
    use offset s := c1.use offset s ∧ c2.use offset s,
    subcircuit offset _ s := c1.subcircuit offset s ∧ c2.subcircuit offset s
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => simp [Operations.forAll]
  | witness m _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | use _ _ ih | subcircuit _ _ ih =>
    simp only [Operations.forAll_cons, Condition.apply, and_assoc]
    rw [← ih]
    tauto

theorem usesLocalWitnessesAndYields_iff_conjunction {sentences : PropertySet F} (yields : YieldContext sentences) (n : ℕ) {env : Environment F} {ops : Operations sentences} :
  env.UsesLocalWitnessesAndYields yields n ops ↔
    UsesLocalWitnesses env n ops ∧ UsesLocalYields env yields n ops := by
  simp only [UsesLocalWitnessesAndYields, UsesLocalWitnesses, UsesLocalYields, Operations.forAllFlat]
  -- Apply the forAll_and lemma
  rw [Operations.forAll_and]
  -- Now we need to show the conditions are equivalent
  apply Operations.forAll_equiv
  -- witness case
  · intros; simp [and_comm]
  -- assert case
  · intros; simp
  -- lookup case
  · intros; simp
  -- yield case
  · intros; simp
  -- use case
  · intros; simp
  -- subcircuit case
  · intros offset m s
    simp only
    rw [FlatOperation.forAll_and]
    apply FlatOperation.forAll_equiv
    · intros; simp
    · intros; simp
    · intros; simp
    · intros; simp
    · intros; simp

end Environment

namespace Circuit

theorem ConstraintsHold.soundness_iff_forAll (n : ℕ) (env : Environment F) {sentences : PropertySet F} (ops : Operations sentences) (yields : YieldContext sentences) (checked : CheckedYields sentences) :
  ConstraintsHold.Soundness env yields checked ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Soundness (l.entry.map env),
    use _ s := s.eval env ∈ yields.yielded ∧ (s.eval env ∈ checked → SentenceHolds (s.eval env)),
    subcircuit _ _ s := s.Soundness env yields checked
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | subcircuit _ _ ih =>
    simp_all only [ConstraintsHold.Soundness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih
  | use _ _ ih =>
    simp_all only [ConstraintsHold.Soundness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    rw [ih n]
    tauto

theorem ConstraintsHold.completeness_iff_forAll (n : ℕ) (env : Environment F) {sentences : PropertySet F} (ops : Operations sentences) (yields : YieldContext sentences) :
  ConstraintsHold.Completeness env yields ops ↔ ops.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Completeness (l.entry.map env),
    use _ s := s.eval env ∈ yields.yielded ∧ (s.eval env ∈ Set.univ → SentenceHolds (s.eval env)),
    subcircuit _ _ s := s.Completeness env yields
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | yield _ _ ih | subcircuit _ _ ih =>
    simp_all only [ConstraintsHold.Completeness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    apply ih
  | use _ _ ih =>
    simp_all only [ConstraintsHold.Completeness, Operations.forAll, true_and, and_congr_right_iff]
    try intros
    rw [ih n]
    tauto

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.Subcircuit.can_replace_subcircuits`, it justifies only proving the nested version
`ConstraintsHold.Completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {env} {sentences : PropertySet F} {ops : Operations sentences} {n : ℕ} (yields : YieldContext sentences) (checked : CheckedYields sentences) (h : ops.SubcircuitsConsistent n) : env.UsesLocalWitnessesAndYields yields n ops →
    ConstraintsHold.Completeness env yields ops → ConstraintsHold env yields checked ops := by
  induction ops, n, h using Operations.inductConsistent with
  | empty => intros; exact trivial
  | witness | assert | lookup | yield | use =>
    simp_all [circuit_norm, Environment.UsesLocalWitnessesAndYields, Operations.forAllFlat, Operations.forAll, RawTable.implied_by_completeness]
  | subcircuit n circuit ops ih =>
    simp_all only [ConstraintsHold, ConstraintsHold.Completeness, Environment.UsesLocalWitnessesAndYields, Operations.forAllFlat, Operations.forAll, and_true]
    intro h_env h_compl
    apply circuit.implied_by_completeness env yields checked ?_ h_compl.left
    rw [←Environment.usesLocalWitnessesAndYieldsFlat_iff_extends yields]
    exact h_env.left
end Circuit

namespace Circuit
-- more theorems about forAll

variable {α β : Type} {n : ℕ} {sentences : PropertySet F} {prop : Condition sentences} {env : Environment F}

@[circuit_norm]
theorem bind_forAll {f : Circuit sentences α} {g : α → Circuit sentences β} :
  ((f >>= g).operations n).forAll n prop ↔
    (f.operations n).forAll n prop ∧ (((g (f.output n)).operations (n + f.localLength n)).forAll (n + f.localLength n)) prop := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  rw [h_ops, Operations.forAll_append, add_comm n]

-- definition of `forAll` for circuits which uses the same offset in two places

@[reducible, circuit_norm]
def forAll {sentences : PropertySet F} (circuit : Circuit sentences α) (n : ℕ) (prop : Condition sentences) :=
  (circuit.operations n).forAll n prop

lemma forAll_def {circuit : Circuit sentences α} {n : ℕ} :
  circuit.forAll n prop ↔ (circuit.operations n).forAll n prop := by rfl

theorem bind_forAll' {f : Circuit sentences α} {g : α → Circuit sentences β} :
  (f >>= g).forAll n prop ↔
    f.forAll n prop ∧ ((g (f.output n)).forAll (n + f.localLength n) prop) := by
  have h_ops : (f >>= g).operations n = f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  simp only [forAll]
  rw [bind_forAll]

theorem ConstraintsHold.soundness_iff_forAll' {env : Environment F} {sentences : PropertySet F} {circuit : Circuit sentences α} {n : ℕ} (yields : YieldContext sentences) (checked : CheckedYields sentences) :
  ConstraintsHold.Soundness env yields checked (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Soundness (l.entry.map env),
    use _ s := s.eval env ∈ yields.yielded ∧ (s.eval env ∈ checked → SentenceHolds (s.eval env)),
    subcircuit _ _ s := s.Soundness env yields checked
  } := by
  rw [forAll_def, ConstraintsHold.soundness_iff_forAll n _ _ yields checked]

theorem ConstraintsHold.completeness_iff_forAll' {env : Environment F} {sentences : PropertySet F} {circuit : Circuit sentences α} {n : ℕ} (yields : YieldContext sentences) :
  ConstraintsHold.Completeness env yields (circuit.operations n) ↔ circuit.forAll n {
    assert _ e := env e = 0,
    lookup _ l := l.table.Completeness (l.entry.map env),
    use _ s := s.eval env ∈ yields.yielded ∧ (s.eval env ∈ Set.univ → SentenceHolds (s.eval env)),
    subcircuit _ _ s := s.Completeness env yields
  } := by
  rw [forAll_def, ConstraintsHold.completeness_iff_forAll n _ _ yields]

-- specializations

@[circuit_norm] theorem ConstraintsHold.append_soundness {sentences : PropertySet F} {as bs : Operations sentences} (yields : YieldContext sentences) (checked : CheckedYields sentences) :
  ConstraintsHold.Soundness env yields checked (as ++ bs)
  ↔ ConstraintsHold.Soundness env yields checked as ∧ ConstraintsHold.Soundness env yields checked bs := by
  rw [ConstraintsHold.soundness_iff_forAll 0 _ _ yields checked, Operations.forAll_append,
    ←ConstraintsHold.soundness_iff_forAll 0 _ _ yields checked, ←ConstraintsHold.soundness_iff_forAll (as.localLength + 0) _ _ yields checked]

@[circuit_norm] theorem ConstraintsHold.bind_soundness {sentences : PropertySet F} {f : Circuit sentences α} {g : α → Circuit sentences β} (n : ℕ) (yields : YieldContext sentences) (checked : CheckedYields sentences) :
  ConstraintsHold.Soundness env yields checked ((f >>= g).operations n)
  ↔ ConstraintsHold.Soundness env yields checked (f.operations n) ∧
    ConstraintsHold.Soundness env yields checked ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [ConstraintsHold.soundness_iff_forAll n _ _ yields checked, ConstraintsHold.soundness_iff_forAll n _ _ yields checked,
    ConstraintsHold.soundness_iff_forAll (n + f.localLength n) _ _ yields checked, bind_forAll]

@[circuit_norm] theorem ConstraintsHold.append_completeness {sentences : PropertySet F} {as bs : Operations sentences} (yields : YieldContext sentences) :
  ConstraintsHold.Completeness env yields (as ++ bs)
  ↔ ConstraintsHold.Completeness env yields as ∧ ConstraintsHold.Completeness env yields bs := by
  rw [ConstraintsHold.completeness_iff_forAll 0 _ _ yields, Operations.forAll_append,
    ←ConstraintsHold.completeness_iff_forAll 0 _ _ yields, ←ConstraintsHold.completeness_iff_forAll (as.localLength + 0) _ _ yields]

@[circuit_norm] theorem ConstraintsHold.bind_completeness {sentences : PropertySet F} {f : Circuit sentences α} {g : α → Circuit sentences β} (n : ℕ) (yields : YieldContext sentences) :
  ConstraintsHold.Completeness env yields ((f >>= g).operations n)
  ↔ ConstraintsHold.Completeness env yields (f.operations n) ∧
    ConstraintsHold.Completeness env yields ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [ConstraintsHold.completeness_iff_forAll n _ _ yields, ConstraintsHold.completeness_iff_forAll n _ _ yields,
    ConstraintsHold.completeness_iff_forAll (n + f.localLength n) _ _ yields, bind_forAll]

@[circuit_norm] theorem ConstraintsHold.append_localWitnesses {sentences : PropertySet F} {as bs : Operations sentences} (n : ℕ) (yields : YieldContext sentences) :
  env.UsesLocalWitnessesAndYieldsCompleteness yields n (as ++ bs)
  ↔ env.UsesLocalWitnessesAndYieldsCompleteness yields n as ∧ env.UsesLocalWitnessesAndYieldsCompleteness yields (as.localLength + n) bs := by
  rw [env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields, Operations.forAll_append,
    ←env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields n, ←env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields (as.localLength + n)]

@[circuit_norm] theorem ConstraintsHold.bind_usesLocalWitnesses {sentences : PropertySet F} {f : Circuit sentences α} {g : α → Circuit sentences β} (n : ℕ) (yields : YieldContext sentences) :
  env.UsesLocalWitnessesAndYieldsCompleteness yields n ((f >>= g).operations n)
  ↔ env.UsesLocalWitnessesAndYieldsCompleteness yields n (f.operations n) ∧
    env.UsesLocalWitnessesAndYieldsCompleteness yields (n + f.localLength n) ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields, env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields,
    env.usesLocalWitnessesAndYieldsCompleteness_iff_forAll yields, bind_forAll]
end Circuit

-- more theorems about forAll / forAllFlat

namespace FlatOperation
theorem forAll_implies {sentences : PropertySet F} {c c' : Condition sentences} (n : ℕ) {ops : List (FlatOperation sentences)} :
    (forAll n (c.implies c').ignoreSubcircuit ops) → (forAll n c ops → forAll n c' ops) := by
  simp only [Condition.implies, Condition.ignoreSubcircuit]
  intro h
  induction ops generalizing n with
  | nil => simp [forAll_empty]
  | cons op ops ih =>
    specialize ih (op.singleLocalLength + n)
    cases op <;> simp_all [forAll_cons, Condition.applyFlat]
end FlatOperation

namespace Operations
lemma forAll_toFlat_iff {sentences : PropertySet F} (n : ℕ) (condition : Condition sentences) (ops : Operations sentences) :
    FlatOperation.forAll n condition ops.toFlat ↔ ops.forAllFlat n condition := by
  induction ops using Operations.induct generalizing n with
  | empty => simp only [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | witness | assert | lookup | yield | use =>
    simp_all [forAllFlat, forAll, toFlat, FlatOperation.forAll, Condition.applyFlat, FlatOperation.localLength]
  | subcircuit s ops ih =>
    simp_all only [forAllFlat, forAll, toFlat]
    rw [FlatOperation.forAll_append, s.localLength_eq]
    simp_all
end Operations

/-- An environment respects local witnesses and yields iff it does so in the flattened variant. -/
lemma Environment.usesLocalWitnessesAndYields_iff_flat {n : ℕ} {sentences : PropertySet F} {ops : Operations sentences} {env : Environment F} (yields : YieldContext sentences) :
    env.UsesLocalWitnessesAndYields yields n ops ↔
    env.UsesLocalWitnessesAndYieldsFlat yields n ops.toFlat := by
  simp only [UsesLocalWitnessesAndYieldsFlat, UsesLocalWitnessesAndYields]
  rw [Operations.forAll_toFlat_iff]

-- theorems about witness generation

namespace FlatOperation
lemma dynamicWitness_length {sentences : PropertySet F} {op : FlatOperation sentences} {init : List F} :
    (op.dynamicWitness init).length = op.singleLocalLength := by
  rcases op <;> simp [dynamicWitness, singleLocalLength]

lemma dynamicWitnesses_length {sentences : PropertySet F} {ops : List (FlatOperation sentences)} (init : List F) :
    (dynamicWitnesses ops init).length = init.length + localLength ops := by
  induction ops generalizing init with
  | nil => rw [dynamicWitnesses, List.foldl_nil, localLength, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamicWitnesses, localLength_cons, dynamicWitness_length]

lemma dynamicWitnesses_cons {sentences : PropertySet F} {op : FlatOperation sentences} {ops : List (FlatOperation sentences)} {acc : List F} :
    dynamicWitnesses (op :: ops) acc = dynamicWitnesses ops (acc ++ op.dynamicWitness acc) := by
  simp only [dynamicWitnesses, List.foldl_cons]

lemma getElem?_dynamicWitnesses_of_lt {sentences : PropertySet F} {ops : List (FlatOperation sentences)} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (dynamicWitnesses ops acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamicWitnesses]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ op.dynamicWitness acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma getElem?_dynamicWitnesses_cons_right {sentences : PropertySet F} {op : FlatOperation sentences} {ops : List (FlatOperation sentences)} {init : List F} {i : ℕ} (hi : i < op.singleLocalLength) :
    (dynamicWitnesses (op :: ops) init)[init.length + i]?.getD 0 = (op.dynamicWitness init)[i]'(dynamicWitness_length (F:=F) ▸ hi) := by
  rw [dynamicWitnesses_cons, getElem?_dynamicWitnesses_of_lt (by simp [hi, dynamicWitness_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

/--
Flat version of the final theorem in this section, `Circuit.proverEnvironment_usesLocalWitnesses`.
-/
theorem proverEnvironment_usesLocalWitnesses {sentences : PropertySet F} {ops : List (FlatOperation sentences)} (init : List F) :
  (∀ (env env' : Environment F),
    forAll init.length { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops) →
    (proverEnvironment ops init).UsesLocalWitnessesFlat init.length ops := by
  simp only [proverEnvironment, Environment.UsesLocalWitnessesFlat, Environment.ExtendsVector]
  intro h_computable
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable ⊢
    cases op with
    | assert | lookup | yield | use =>
      simp_all [dynamicWitnesses_cons, Condition.applyFlat, singleLocalLength, dynamicWitness, proverYields]
    | witness m compute =>
      simp_all only [Condition.applyFlat, singleLocalLength, Environment.AgreesBelow]
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
A condition that always implies another condition, regardless of the operation.
-/
def Condition.always_implies {sentences : PropertySet F} (c c' : Condition sentences) : Prop :=
  (∀ n m compute, c.witness n m compute → c'.witness n m compute) ∧
  (∀ offset e, c.assert offset e → c'.assert offset e) ∧
  (∀ offset l, c.lookup offset l → c'.lookup offset l) ∧
  (∀ offset s, c.yield offset s → c'.yield offset s) ∧
  (∀ offset s, c.use offset s → c'.use offset s)

/--
If a condition always implies another, then forAll is monotonic.
-/
lemma FlatOperation.forAll_mono {sentences : PropertySet F} (n : ℕ) {c c' : Condition sentences} (ops : List (FlatOperation sentences)) :
    c.always_implies c' → FlatOperation.forAll n c ops → FlatOperation.forAll n c' ops := by
  intro h_implies h_forAll
  induction ops generalizing n with
  | nil => exact h_forAll
  | cons op ops ih =>
    simp only [FlatOperation.forAll_cons] at h_forAll ⊢
    constructor
    · cases op with
      | witness m compute =>
        simp [Condition.applyFlat] at h_forAll ⊢
        exact h_implies.1 _ _ _ h_forAll.1
      | assert e =>
        simp [Condition.applyFlat] at h_forAll ⊢
        exact h_implies.2.1 _ _ h_forAll.1
      | lookup l =>
        simp [Condition.applyFlat] at h_forAll ⊢
        exact h_implies.2.2.1 _ _ h_forAll.1
      | yield s =>
        simp [Condition.applyFlat] at h_forAll ⊢
        exact h_implies.2.2.2.1 _ _ h_forAll.1
      | use s =>
        simp [Condition.applyFlat] at h_forAll ⊢
        exact h_implies.2.2.2.2 _ _ h_forAll.1
    · exact ih (op.singleLocalLength + n) h_forAll.2

/--
The local yields from a tail of operations is a subset of the local yields from the full list.
-/
lemma FlatOperation.localYields_cons_subset {sentences : PropertySet F} (env : Environment F) (op : FlatOperation sentences) (ops : List (FlatOperation sentences)) :
    FlatOperation.localYields env ops ⊆ FlatOperation.localYields env (op :: ops) := by
  intro x hx
  cases op <;> simp [FlatOperation.localYields] at hx ⊢
  · exact hx
  · exact hx
  · exact hx
  · exact Or.inr hx
  · exact hx

/--
Any list of flat operations satisfies the yield condition when checked against its own computed yields.
-/
theorem FlatOperation.forAll_localYields {sentences : PropertySet F} (env : Environment F) (n : ℕ) (ops : List (FlatOperation sentences)) :
    FlatOperation.forAll n { yield := fun _ s ↦ s.eval env ∈ FlatOperation.localYields env ops } ops := by
  induction ops generalizing n with
  | nil => simp [FlatOperation.forAll]
  | cons op ops ih =>
    simp only [FlatOperation.forAll_cons]
    constructor
    · cases op with
      | witness _ _ => simp [Condition.applyFlat]
      | assert _ => simp [Condition.applyFlat]
      | lookup _ => simp [Condition.applyFlat]
      | use _ => simp [Condition.applyFlat]
      | yield s =>
        simp [Condition.applyFlat, FlatOperation.localYields]
    · -- Apply IH with monotonicity using the subset lemma
      apply FlatOperation.forAll_mono (op.singleLocalLength + n) ops (c:={ yield := fun x s ↦ Sentence.eval env s ∈ localYields env ops })
      · -- Show that the smaller yields condition implies the larger one
        simp only [Condition.always_implies]
        constructor
        · intros; trivial  -- witness case: both conditions are trivial
        constructor
        · intros; trivial  -- assert case: both conditions are trivial
        constructor
        · intros; trivial  -- lookup case: both conditions are trivial
        constructor
        · intros _ s h      -- yield case: need to show subset property
          -- h says: s.eval env ∈ localYields env ops
          -- goal: s.eval env ∈ localYields env (op :: ops)
          apply FlatOperation.localYields_cons_subset env op ops h
        · intros; trivial  -- use case: both conditions are trivial
      · exact ih (op.singleLocalLength + n)

/--
Any environment satisfies `UsesLocalYieldsFlat` when the yields are computed from that same environment.
-/
theorem usesLocalYieldsFlat_of_localYields {sentences : PropertySet F} (env : Environment F) (n : ℕ) (ops : Operations sentences) :
    env.UsesLocalYields { yielded := FlatOperation.localYields env ops.toFlat } n ops := by
  simp only [Environment.UsesLocalYields]
  simp only [← Operations.forAll_toFlat_iff]
  exact FlatOperation.forAll_localYields env n ops.toFlat


/--
If a circuit satisfies `computableWitnesses`, then the `proverEnvironment` agrees with the
circuit's witness generators.
-/
theorem Circuit.proverEnvironment_usesLocalWitnessesAndYields {sentences : PropertySet F} (circuit : Circuit sentences α) (init : List F) :
  circuit.ComputableWitnesses init.length →
    (circuit.proverEnvironment init).UsesLocalWitnessesAndYields (circuit.proverYields init) init.length (circuit.operations init.length) := by
  intro h_computable
  rw [Environment.usesLocalWitnessesAndYields_iff_conjunction]
  constructor
  · -- Prove the witness part
    simp_all only [Environment.UsesLocalWitnesses, Circuit.proverEnvironment, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
      ←Operations.forAll_toFlat_iff]
    exact FlatOperation.proverEnvironment_usesLocalWitnesses init h_computable
  · -- Prove the yield part
    simp only [proverYields, FlatOperation.proverYields, proverEnvironment,
               FlatOperation.proverEnvironment, Operations.forAllFlat]
    apply usesLocalYieldsFlat_of_localYields

lemma Environment.agreesBelow_of_le {F} {n m : ℕ} {env env' : Environment F} :
    env.AgreesBelow n env' → m ≤ n → env.AgreesBelow m env' :=
  fun h_same hi i hi' => h_same i (Nat.lt_of_lt_of_le hi' hi)

namespace FlatOperation
/--
If all witness generators only access the environment below the current offset, then
the entire circuit only accesses the environment below `n + localLength`.

This is not currently used, but seemed like a nice result to have.
-/
theorem onlyAccessedBelow_all {sentences : PropertySet F} {ops : List (FlatOperation sentences)} (n : ℕ) :
  forAll n { witness n _ := Environment.OnlyAccessedBelow n } ops →
    Environment.OnlyAccessedBelow (n + localLength ops) (localWitnesses · ops) := by
  intro h_comp env env' h_env
  simp only
  induction ops generalizing n with
  | nil => simp [localWitnesses]
  | cons op ops ih =>
    simp_all only [forAll_cons, localLength_cons]
    have h_ih := h_comp.right
    replace h_comp := h_comp.left
    replace h_ih := ih (op.singleLocalLength + n) h_ih
    ring_nf at *
    specialize h_ih h_env
    clear ih
    cases op with
    | assert | lookup | yield | use =>
      simp_all only [Condition.applyFlat, localWitnesses]
    | witness m c =>
      simp_all only [Condition.applyFlat, localWitnesses,
        Environment.OnlyAccessedBelow, Environment.AgreesBelow]
      congr 1
      apply h_comp env env'
      intro i hi
      exact h_env i (by linarith)
end FlatOperation

-- theorem about relationship between FormalCircuit and GeneralFormalCircuit

/--
`FormalCircuit.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` is a generalization of
`FormalCircuit`. The idea is to make `FormalCircuit.Assumptions` available in the soundness
by putting it in `GeneralFormalCircuit.SoundnessAssumptions`.
-/
def FormalCircuit.isGeneralFormalCircuit {F : Type} {sentences : PropertySet F} (order : SentenceOrder sentences) (Input Output : TypeMap) [Field F] [ProvableType Output] [ProvableType Input]
    (orig : FormalCircuit order Input Output): GeneralFormalCircuit order Input Output := by
  exact {
    elaborated := orig.elaborated,
    Assumptions := orig.CompletenessAssumptions,
    SoundnessAssumptions := orig.Assumptions,
    Spec := orig.Spec,
    soundness := by
      intro offset env yields checked input_var input h_eq h_assumptions constraints_hold
      have h := orig.soundness offset env yields checked input_var input h_eq h_assumptions constraints_hold
      exact h
    ,
    completeness := by
      simp only [GeneralFormalCircuit.Completeness, forall_eq']
      intros
      apply orig.completeness <;> trivial
  }

/--
`FormalAssertion.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` is a generalization of
`FormalAssertion`. The assumptions are placed in `SoundnessAssumptions` for soundness,
and `FormalAssertion.Spec` is made available in the completeness by putting it within `GeneralFormalCircuit.Assumptions`.
-/
def FormalAssertion.isGeneralFormalCircuit {F : Type} {sentences : PropertySet F} (order : SentenceOrder sentences) (Input : TypeMap) [Field F] [ProvableType Input]
    (orig : FormalAssertion order Input) : GeneralFormalCircuit order Input unit := by
  let Spec (checked : CheckedYields sentences) input (_ : Unit) := orig.Spec checked input
  exact {
    elaborated := orig.elaborated,
    Assumptions _ input := orig.Assumptions input ∧ orig.Spec Set.univ input,
    SoundnessAssumptions := orig.Assumptions,
    Spec,
    soundness := by
      intro offset env yields checked input_var input h_eq h_assumptions constraints_hold
      simp only [Spec]
      have h := orig.soundness offset env yields checked input_var input h_eq h_assumptions constraints_hold
      exact ⟨h.1, h.2⟩
    ,
    completeness := by
      simp only [GeneralFormalCircuit.Completeness, forall_eq']
      intros
      apply orig.completeness <;> aesop
  }
