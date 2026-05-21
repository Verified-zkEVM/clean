/-
This file contains theorems that immediately follow from the definitions in `Circuit.Operations` and `Circuit.Basic`.

For more complicated interconnected theorems, we have separate files,
such as `Circuit.Subcircuit` which focuses on establishing the foundation for subcircuit composition.
-/
import Clean.Circuit.Formal
import Clean.Circuit.Provable

variable {F : Type} [Field F] {α β : Type}

namespace Circuit

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
  ops.ConstraintsHold env → ops.FullGuarantees env →
    ConstraintsHold.Soundness env ops := by
  simp only [Operations.ConstraintsHold, Operations.FullGuarantees,
    constraintsHold_soundness_iff_forall_mem, Operations.forall_constraints_iff,
    Operations.forall_lookups_iff, Operations.forall_interactions_iff]
  rintro ⟨⟨h_constraints, h_sub_constraints⟩, ⟨h_lookups, h_sub_lookups⟩⟩ ⟨h_guarantees, h_sub_guarantees⟩
  simp_all only [implies_true, true_and]
  constructor
  · intro l h_mem
    apply l.table.imply_soundness _ _ (h_lookups l h_mem)
  · intro s h_mem
    have soundness := s.2.soundness env
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem,
      FlatOperation.guarantees_iff_forall_mem] at soundness
    exact fun h_assumptions =>
      soundness h_assumptions ⟨h_sub_constraints s h_mem, h_sub_lookups s h_mem⟩
        (h_sub_guarantees s h_mem) |>.1

open Operations in
/--
Recursive requirements lifting from top-level requirements, recursive constraints,
and flattened guarantees.

The direct `ops.Requirements env` hypothesis contains both shallow interaction
requirements and direct subcircuit assumptions. The subcircuit assumptions are
passed to `Subcircuit.soundness`, which derives each subcircuit's flat
requirements internally.
-/
theorem requirements_toFlat_of_soundness {ops : Operations F} {env} :
  ops.SubcircuitChannelsLawful → ops.ConstraintsHold env → ops.FullGuarantees env → ops.Requirements env →
    ops.FullRequirements env := by
  simp only [Operations.ConstraintsHold, Operations.FullGuarantees, Operations.FullRequirements,
    Operations.subcircuitChannelsLawful_iff_forall, requirements_iff_forall_mem]
  intro h_lawful h_constraints h_guarantees h_requirements
  rw [Operations.forall_interactions_iff]
  use h_requirements.1
  intro s h_mem
  rcases h_requirements.2 s h_mem with h_empty | h_assumptions
  · have h_requirements_iff := (h_lawful s h_mem).2.1 env
    rw [FlatOperation.inChannelsOrRequirements_iff_forall_mem] at h_requirements_iff
    intro i i_mem
    specialize h_requirements_iff i i_mem
    simp [h_empty] at h_requirements_iff
    exact h_requirements_iff
  · have soundness := s.2.soundness env
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem,
      FlatOperation.guarantees_iff_forall_mem, FlatOperation.requirements_iff_forall_mem] at soundness
    rw [Operations.forall_constraints_iff, Operations.forall_lookups_iff] at h_constraints
    rw [Operations.forall_interactions_iff] at h_guarantees
    exact (soundness h_assumptions
      ⟨h_constraints.1.2 s h_mem, h_constraints.2.2 s h_mem⟩
      (h_guarantees.2 s h_mem)).2

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
  | case3 _ _ ih | case4 _ _ ih | case5 _ _ ih =>
    simp only [List.cons_append, localLength, ih]

theorem forAll_empty {condition : _root_.Condition F} {n : ℕ} : forAll n condition [] = True := rfl

theorem forAll_cons {condition : _root_.Condition F} {offset : ℕ} {op : FlatOperation F} {ops : List (FlatOperation F)} :
  forAll offset condition (op :: ops) ↔
    condition.applyFlat offset op ∧ forAll (op.singleLocalLength + offset) condition ops := by
  cases op <;> simp [forAll, Condition.applyFlat, singleLocalLength]

lemma forAll_append {condition : _root_.Condition F} {ops ops' : List (FlatOperation F)} (n : ℕ) :
  forAll n condition (ops ++ ops') ↔
    forAll n condition ops ∧ forAll (localLength ops + n) condition ops' := by
  induction ops generalizing n with
  | nil => simp only [List.nil_append, forAll, localLength, zero_add, true_and]
  | cons op ops ih =>
    specialize ih (n + op.singleLocalLength)
    simp_all +arith [forAll_cons, localLength_cons, and_assoc]

lemma localWitnesses_append {F} {a b: List (FlatOperation F)} {env} :
    (localWitnesses env (a ++ b)).toArray = (localWitnesses env a).toArray ++ (localWitnesses env b).toArray := by
  induction a using FlatOperation.localLength.induct with
  | case1 => simp only [List.nil_append, localLength, localWitnesses, Vector.toArray_empty,
    Array.empty_append]
  | case2 _ _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, Vector.toArray_append, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih | case5 _ _ ih =>
    simp only [List.cons_append, localLength, localWitnesses, ih]

/--
The witness length from flat and nested operations is the same
-/
lemma localLength_toFlat {ops : Operations F} :
    localLength ops.toFlat = ops.localLength := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ ops ih | assert _ ops ih | lookup _ ops ih  | subcircuit _ ops ih | interact _ ops ih =>
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
    | case3 ops _ ih' | case4 ops _ ih' | case5 _ ops ih' =>
      simp_all only [localLength_append, forall_eq', localLength]

/--
The witnesses created from flat and nested operations are the same
-/
lemma localWitnesses_toFlat {ops : Operations F} {env} :
  (localWitnesses env ops.toFlat).toArray = (ops.localWitnesses env).toArray := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih | interact _ _ ih =>
    simp only [Operations.toFlat, Operations.localLength, Operations.localWitnesses, Vector.toArray_append]
    rw [←ih]
    try rw [localWitnesses_append]
    try simp only [localLength, localWitnesses, Vector.toArray_append, Subcircuit.witnesses, Vector.toArray_cast]
end FlatOperation

namespace ProverEnvironment
open FlatOperation (localLength localWitnesses)
/-
what follows are relationships between different versions of `ProverEnvironment.UsesLocalWitnesses`
-/

lemma env_extends_witness {F} {n : ℕ} {ops : List (FlatOperation F)} {env : ProverEnvironment F} {m c} :
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

theorem usesLocalWitnessesFlat_iff_extends {env : ProverEnvironment F} (n : ℕ) {ops : List (FlatOperation F)}  :
    env.UsesLocalWitnessesFlat n ops ↔ env.ExtendsVector (localWitnesses env ops) n := by
  induction ops using FlatOperation.induct generalizing n with
  | empty => simp [UsesLocalWitnessesFlat, FlatOperation.forAll_empty, ExtendsVector, localLength]
  | witness m _ _ ih =>
    rw [UsesLocalWitnessesFlat, FlatOperation.forAll, env_extends_witness,←ih (m + n)]
    trivial
  | assert | lookup | interact =>
    simp_all [UsesLocalWitnessesFlat, circuit_norm,
      FlatOperation.forAll_cons, Condition.applyFlat, FlatOperation.singleLocalLength]

theorem can_replace_usesLocalWitnessesCompleteness {env : ProverEnvironment F} {ops : Operations F} {n : ℕ} (h : ops.SubcircuitsConsistent n) :
  env.UsesLocalWitnesses n ops → env.UsesLocalWitnessesCompleteness n ops := by
  induction ops, n, h using Operations.inductConsistent with
  | empty => intros; trivial
  | witness | assert | lookup | interact =>
    simp_all +arith [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll]
  | subcircuit n circuit ops ih =>
    simp only [UsesLocalWitnesses, UsesLocalWitnessesCompleteness, Operations.forAllFlat, Operations.forAll_cons, Condition.apply]
    intro h
    rw [add_comm]
    apply And.intro ?_ (ih h.right)
    apply (circuit.completeness _ _).2
    rw [← usesLocalWitnessesFlat_iff_extends]
    exact h.left

theorem usesLocalWitnessesCompleteness_iff_forAll (n : ℕ) {env : ProverEnvironment F} {ops : Operations F} :
  env.UsesLocalWitnessesCompleteness n ops ↔ ops.forAll n {
    witness m _ c := env.ExtendsVector (c env) m,
    subcircuit _ _ s := s.ProverSpec env
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | subcircuit | interact =>
    simp_all +arith [UsesLocalWitnessesCompleteness, Operations.forAll]

theorem usesLocalWitnesses_iff_forAll (n : ℕ) {env : ProverEnvironment F} {ops : Operations F} :
  env.UsesLocalWitnesses n ops ↔ ops.forAll n {
    witness n _ c := env.ExtendsVector (c env) n,
    subcircuit n _ s := FlatOperation.forAll n { witness n _ c := env.ExtendsVector (c env) n} s.ops.toFlat
  } := by
  simp only [UsesLocalWitnesses, Operations.forAllFlat]

lemma usesLocalWitnesses_to_subcircuit {env : ProverEnvironment F} {ops : Operations F} {n : ℕ}
  (h_consistent : ops.SubcircuitsConsistent n) :
    env.UsesLocalWitnesses n ops →
    ∀ s ∈ ops.subcircuits, env.UsesLocalWitnessesFlat s.1 s.2.ops.toFlat := by
  intro h_env
  induction ops, n, h_consistent using Operations.inductConsistent <;>
    simp_all [circuit_norm, ProverEnvironment.UsesLocalWitnesses, ProverEnvironment.UsesLocalWitnessesFlat,
      Operations.forAllFlat]
end ProverEnvironment

namespace Circuit

/--
Completeness theorem which proves that we can replace constraints in subcircuits
with their `completeness` statement.

Together with `Circuit.Subcircuit.can_replace_subcircuits`, it justifies only proving the nested version
`ConstraintsHold.Completeness` when defining formal circuits,
because it already implies the flat version.
-/
theorem can_replace_completeness {env} {ops : Operations F} {n : ℕ}
  (h_consistent : ops.SubcircuitsConsistent n) :
    env.UsesLocalWitnesses n ops →
    ConstraintsHold.Completeness env ops →
    ops.ConstraintsHold env := by
  rw [constraintsHold_completeness_iff_forall_mem,
    Operations.ConstraintsHold, Operations.forall_constraints_iff, Operations.forall_lookups_iff]
  intro h_env ⟨ h_constraints, h_lookups, h_guarantees, h_subcircuit ⟩
  have lookups_contains : (∀ l ∈ ops.shallowLookups, l.Contains env) := by
    intro l h_mem
    apply l.table.implied_by_completeness
    apply h_lookups l h_mem
  simp_all only [implies_true, true_and, ←forall_and]
  intro ⟨n', s⟩ h_mem
  have h := s.completeness env
  rw [FlatOperation.guarantees_iff_forall_mem, FlatOperation.constraintsHoldFlat_iff_forall_mem,
    ←ProverEnvironment.usesLocalWitnessesFlat_iff_extends] at h
  suffices env.UsesLocalWitnessesFlat n' s.ops.toFlat by
    exact ((h this).1 (h_subcircuit _ h_mem)).1
  apply ProverEnvironment.usesLocalWitnesses_to_subcircuit h_consistent h_env _ h_mem

theorem can_replace_completeness_guarantees {env} {ops : Operations F} {n : ℕ}
  (h_consistent : ops.SubcircuitsConsistent n) :
    env.UsesLocalWitnesses n ops →
    ConstraintsHold.Completeness env ops →
    ops.FullGuarantees env := by
  rw [constraintsHold_completeness_iff_forall_mem,
    Operations.FullGuarantees, Operations.forall_interactions_iff]
  intro h_env ⟨ h_constraints, h_lookups, h_guarantees, h_subcircuit ⟩
  use h_guarantees
  intro ⟨n', s⟩ h_mem
  have h := s.completeness env
  rw [FlatOperation.guarantees_iff_forall_mem, ←ProverEnvironment.usesLocalWitnessesFlat_iff_extends] at h
  suffices env.UsesLocalWitnessesFlat n' s.ops.toFlat by
    exact ((h this).1 (h_subcircuit _ h_mem)).2
  apply ProverEnvironment.usesLocalWitnesses_to_subcircuit h_consistent h_env _ h_mem

-- TODO prove this first and the previous two as trivial consequences
theorem can_replace_completeness_and_guarantees {env} {ops : Operations F} {n : ℕ}
  (h_consistent : ops.SubcircuitsConsistent n) :
    env.UsesLocalWitnesses n ops →
    ConstraintsHold.Completeness env ops →
    (ops.ConstraintsHold env ∧ ops.FullGuarantees env) := by
  intro h_env h_compl
  exact ⟨ can_replace_completeness h_consistent h_env h_compl,
    can_replace_completeness_guarantees h_consistent h_env h_compl ⟩
end Circuit

namespace Circuit
-- more theorems about forAll

variable {α β : Type} {n : ℕ} {prop : Condition F} {env : Environment F} {env_p : ProverEnvironment F}

@[circuit_norm]
theorem bind_forAllNoOffset {f : Circuit F α} {g : α → Circuit F β} {prop : ConditionNoOffset F} :
  ((f >>= g).operations n).forAllNoOffset prop ↔
    (f.operations n).forAllNoOffset prop ∧
      (((g (f.output n)).operations (n + f.localLength n)).forAllNoOffset prop) := by
  have h_ops : (f >>= g).operations n =
      f.operations n ++ (g (f.output n)).operations (n + f.localLength n) := rfl
  rw [h_ops, Operations.forAllNoOffset_append]

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

-- specializations

@[circuit_norm] theorem ConstraintsHold.append_localWitnesses {as bs : Operations F} (n : ℕ) :
  env_p.UsesLocalWitnessesCompleteness n (as ++ bs)
  ↔ env_p.UsesLocalWitnessesCompleteness n as ∧ env_p.UsesLocalWitnessesCompleteness (as.localLength + n) bs := by
  rw [env_p.usesLocalWitnessesCompleteness_iff_forAll, Operations.forAll_append,
    ←env_p.usesLocalWitnessesCompleteness_iff_forAll n, ←env_p.usesLocalWitnessesCompleteness_iff_forAll (as.localLength + n)]

@[circuit_norm] theorem ConstraintsHold.bind_usesLocalWitnesses {f : Circuit F α} {g : α → Circuit F β} (n : ℕ) :
  env_p.UsesLocalWitnessesCompleteness n ((f >>= g).operations n)
  ↔ env_p.UsesLocalWitnessesCompleteness n (f.operations n) ∧
    env_p.UsesLocalWitnessesCompleteness (n + f.localLength n) ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [env_p.usesLocalWitnessesCompleteness_iff_forAll, env_p.usesLocalWitnessesCompleteness_iff_forAll,
    env_p.usesLocalWitnessesCompleteness_iff_forAll, bind_forAll]
end Circuit

-- more theorems about forAll / forAllFlat

namespace FlatOperation
theorem forAll_implies {c c' : _root_.Condition F} (n : ℕ) {ops : List (FlatOperation F)} :
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
lemma forAll_toFlat_iff (n : ℕ) (condition : Condition F) (ops : Operations F) :
    FlatOperation.forAll n condition ops.toFlat ↔ ops.forAllFlat n condition := by
  induction ops using Operations.induct generalizing n with
  | empty => simp only [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | witness | assert | lookup | interact =>
    simp_all [forAllFlat, forAll, toFlat, FlatOperation.forAll]
  | subcircuit s ops ih =>
    simp_all only [forAllFlat, forAll, toFlat]
    rw [FlatOperation.forAll_append, s.localLength_eq]
    simp_all
end Operations

lemma FlatOperation.forAll_toFlat_iff (condition : Condition F) (ops : Operations F) :
    FlatOperation.forAllNoOffset condition ops.toFlat ↔ ops.forAllNoOffset {
      condition with
      subcircuit s := FlatOperation.forAllNoOffset condition s.ops.toFlat
    } := by
  induction ops using Operations.induct
  <;> simp_all [circuit_norm, Operations.toFlat]

/-- An environment respects local witnesses iff it does so in the flattened variant. -/
lemma ProverEnvironment.usesLocalWitnesses_iff_flat {n : ℕ} {ops : Operations F} {env : ProverEnvironment F} :
    env.UsesLocalWitnesses n ops ↔
    env.UsesLocalWitnessesFlat n ops.toFlat := by
  simp only [UsesLocalWitnessesFlat, UsesLocalWitnesses]
  rw [Operations.forAll_toFlat_iff]

-- theorems about witness generation

namespace FlatOperation
variable {hint : ProverHint F}

lemma dynamicWitness_length {op : FlatOperation F} {init : List F} :
    (op.dynamicWitness hint init).length = op.singleLocalLength := by
  rcases op <;> simp [dynamicWitness, singleLocalLength]

lemma dynamicWitnesses_length {ops : List (FlatOperation F)} (init : List F) :
    (dynamicWitnesses ops hint init).length = init.length + localLength ops := by
  induction ops generalizing init with
  | nil => rw [dynamicWitnesses, List.foldl_nil, localLength, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamicWitnesses, localLength_cons, dynamicWitness_length]

lemma dynamicWitnesses_cons {op : FlatOperation F} {ops : List (FlatOperation F)} {acc : List F} :
    dynamicWitnesses (op :: ops) hint acc = dynamicWitnesses ops hint (acc ++ op.dynamicWitness hint acc) := by
  simp only [dynamicWitnesses, List.foldl_cons]

lemma getElem?_dynamicWitnesses_of_lt {ops : List (FlatOperation F)} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (dynamicWitnesses ops hint acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamicWitnesses]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ op.dynamicWitness hint acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma getElem?_dynamicWitnesses_cons_right {op : FlatOperation F} {ops : List (FlatOperation F)} {init : List F} {i : ℕ} (hi : i < op.singleLocalLength) :
    (dynamicWitnesses (op :: ops) hint init)[init.length + i]?.getD 0 =
      (op.dynamicWitness hint init)[i]'(dynamicWitness_length (F:=F) ▸ hi) := by
  rw [dynamicWitnesses_cons, getElem?_dynamicWitnesses_of_lt (by simp [hi, dynamicWitness_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

/--
Flat version of the final theorem in this section, `Circuit.proverEnvironment_usesLocalWitnesses`.
-/
theorem proverEnvironment_usesLocalWitnesses {ops : List (FlatOperation F)} (init : List F) :
  (∀ (env env' : ProverEnvironment F),
    forAll init.length { witness n _ c := env.AgreesBelow n env' → c env = c env' } ops) →
    (proverEnvironment ops hint init).UsesLocalWitnessesFlat init.length ops := by
  simp only [proverEnvironment, ProverEnvironment.UsesLocalWitnessesFlat, ProverEnvironment.ExtendsVector]
  intro h_computable
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable ⊢
    cases op with
    | assert | lookup | interact =>
      simp_all [dynamicWitnesses_cons, Condition.applyFlat, singleLocalLength, dynamicWitness]
    | witness m compute =>
      simp_all only [Condition.applyFlat, singleLocalLength, ProverEnvironment.AgreesBelow]
      -- get rid of ih first
      constructor; case right =>
        specialize ih (init ++ (compute (.fromList init hint)).toList)
        simp only [List.length_append, Vector.length_toList] at ih
        ring_nf at *
        exact ih fun _ _ => (h_computable ..).right
      clear ih
      replace h_computable := fun env env' => (h_computable env env').left
      intro i
      simp only [ProverEnvironment.fromList]
      rw [getElem?_dynamicWitnesses_cons_right i.is_lt]
      simp only [dynamicWitness, Vector.getElem_toList]
      congr 1
      apply h_computable
      intro j hj
      simp [ProverEnvironment.fromList, hj,
        getElem?_dynamicWitnesses_of_lt]
end FlatOperation

/--
If a circuit satisfies `computableWitnesses`, then the `proverEnvironment` agrees with the
circuit's witness generators.
-/
theorem Circuit.proverEnvironment_usesLocalWitnesses (circuit : Circuit F α) (hint : ProverHint F) (init : List F) :
  circuit.ComputableWitnesses init.length →
    (circuit.proverEnvironment hint init).UsesLocalWitnesses init.length (circuit.operations init.length) := by
  intro h_computable
  simp_all only [proverEnvironment, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
    ←Operations.forAll_toFlat_iff, ProverEnvironment.UsesLocalWitnesses]
  exact FlatOperation.proverEnvironment_usesLocalWitnesses init h_computable

lemma ProverEnvironment.agreesBelow_of_le {F} {n m : ℕ} {env env' : ProverEnvironment F} :
    env.AgreesBelow n env' → m ≤ n → env.AgreesBelow m env' :=
  fun h_same hi i hi' => h_same i (Nat.lt_of_lt_of_le hi' hi)

namespace FlatOperation
/--
If all witness generators only access the environment below the current offset, then
the entire circuit only accesses the environment below `n + localLength`.

This is not currently used, but seemed like a nice result to have.
-/
theorem onlyAccessedBelow_all {ops : List (FlatOperation F)} (n : ℕ) :
  forAll n { witness n _ := ProverEnvironment.OnlyAccessedBelow n } ops →
    ProverEnvironment.OnlyAccessedBelow (n + localLength ops) (localWitnesses · ops) := by
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
    | assert | lookup | interact =>
      simp_all only [Condition.applyFlat, localWitnesses]
    | witness m c =>
      simp_all only [Condition.applyFlat, localWitnesses,
        ProverEnvironment.OnlyAccessedBelow, ProverEnvironment.AgreesBelow]
      congr 1
      apply h_comp env env'
      intro i hi
      exact h_env i (by linarith)
end FlatOperation

section
variable {F : Type} {Input Output : TypeMap} [Field F] [ProvableType Output] [ProvableType Input]

-- theorem about relationship between FormalCircuit and GeneralFormalCircuit

/--
`FormalCircuit.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` a generalization of
`FormalCircuit`. The idea is to make `FormalCircuit.Assumption` available in the soundness
by assuming it within `GeneralFormalCircuit.Spec`.
-/
@[circuit_norm]
def FormalCircuit.isGeneralFormalCircuit
    (orig : FormalCircuit F Input Output) : GeneralFormalCircuit F Input Output where
  base := orig.base
  Assumptions i _ := orig.Assumptions i
  Spec i o _ := orig.Spec i o
  ProverAssumptions i _ _ := orig.Assumptions i
  soundness := by
    intro offset env input_var input h_input h_assumptions h_holds
    exact orig.soundness offset env input_var input h_input h_assumptions h_holds
  completeness := by
    intro offset env input_var h_env input h_input h_assumptions
    exact ⟨orig.completeness offset env input_var h_env input h_input h_assumptions, trivial⟩

/--
`FormalAssertion.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` is a generalization of
`FormalAssertion`.  The idea is to make `FormalAssertion.Spec` available in the completeness
by putting it within `GeneralFormalCircuit.Assumption`.
-/
@[circuit_norm]
def FormalAssertion.isGeneralFormalCircuit
    (orig : FormalAssertion F Input) : GeneralFormalCircuit F Input unit where
  base := orig.base
  Assumptions i _ := orig.Assumptions i
  Spec i _ _ := orig.Spec i
  ProverAssumptions i _ _ := orig.Assumptions i ∧ orig.Spec i
  soundness := by
    intro offset env input_var input h_input h_assumptions h_holds
    exact orig.soundness offset env input_var input h_input h_assumptions h_holds
  completeness := by
    intro offset env input_var h_env input h_input h_assumptions
    exact ⟨orig.completeness offset env input_var h_env input h_input h_assumptions.1 h_assumptions.2, trivial⟩

namespace FormalCircuitBase
omit [ProvableType Output] [ProvableType Input] in
theorem in_channels_or_guarantees_full
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output)
  (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    circuit.main input_var |>.operations n
    |>.InChannelsOrGuaranteesFull circuit.channelsWithGuarantees env := by
  have h_sublist := circuit.subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees input_var n
  have h_guarantees_iff := circuit.inChannelsOrGuarantees_channelsWithGuarantees input_var n
  have h_lawful := circuit.subcircuitChannelsLawful input_var n
  generalize h_channels : circuit.channelsWithGuarantees = channels at *
  generalize h_ops : (circuit.main input_var).operations n = ops at *
  simp only [Operations.InChannelsOrGuaranteesFull, Operations.inChannelsOrGuarantees_iff_forall_mem,
    Operations.forall_interactions_iff, Operations.subcircuitChannelsWithGuarantees_subset_iff_forall,
    Operations.subcircuitChannelsLawful_iff_forall] at *
  simp_all only [implies_true, true_and]
  intro ⟨n, s⟩ s_mem i i_mem
  have h_guarantees_iff := (h_lawful ⟨n, s⟩ s_mem).1 env
  rw [FlatOperation.inChannelsOrGuarantees_iff_forall_mem] at h_guarantees_iff
  specialize h_guarantees_iff i i_mem
  tauto

omit [ProvableType Output] [ProvableType Input] in
theorem in_channels_or_requirements_full
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output)
  (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    circuit.main input_var |>.operations n
    |>.InChannelsOrRequirementsFull circuit.channelsWithRequirements env := by
  have h_sublist := circuit.subcircuitChannelsWithRequirements_subset_channelsWithRequirements input_var n
  have h_requirements_iff := circuit.inChannelsOrRequirements_channelsWithRequirements input_var n
  have h_lawful := circuit.subcircuitChannelsLawful input_var n
  generalize h_channels : circuit.channelsWithRequirements = channels at *
  generalize h_ops : (circuit.main input_var).operations n = ops at *
  simp only [Operations.InChannelsOrRequirementsFull, Operations.inChannelsOrRequirements_iff_forall_mem,
    Operations.forall_interactions_iff, Operations.subcircuitChannelsWithRequirements_subset_iff_forall,
    Operations.subcircuitChannelsLawful_iff_forall] at *
  simp_all only [implies_true, true_and]
  intro ⟨n, s⟩ s_mem i i_mem
  have h_requirements_iff := (h_lawful ⟨n, s⟩ s_mem).2.1 env
  rw [FlatOperation.inChannelsOrRequirements_iff_forall_mem] at h_requirements_iff
  specialize h_requirements_iff i i_mem
  tauto
end FormalCircuitBase

theorem Operations.guarantees_of_not_mem (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrGuaranteesFull channels env →
    ∀ channel, channel ∉ channels → ops.ChannelGuarantees channel env := by
  simp only [circuit_norm]
  intro h_in_or_guars channel h_not_mem i i_mem h_eq
  specialize h_in_or_guars i i_mem
  rw [h_eq] at h_in_or_guars
  tauto

theorem Operations.requirements_of_not_mem (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrRequirementsFull channels env →
    ∀ channel, channel ∉ channels → ops.ChannelRequirements channel env := by
  simp only [circuit_norm]
  intro h_in_or_reqs channel h_not_mem i i_mem h_eq
  specialize h_in_or_reqs i i_mem
  rw [h_eq] at h_in_or_reqs
  tauto

theorem GeneralFormalCircuit.requirements_of_not_mem
  (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
  (input_var : Var Input F) (n : ℕ) (env : Environment F)
  (h_not_mem : channel ∉ circuit.channelsWithRequirements) :
    circuit.main input_var |>.operations n
    |>.ChannelRequirements channel env := by
  apply Operations.requirements_of_not_mem
  apply circuit.in_channels_or_requirements_full
  assumption

theorem Operations.guarantees_iff (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrGuaranteesFull channels env →
    (ops.FullGuarantees env ↔
      ∀ channel ∈ channels, ops.ChannelGuarantees channel env) := by
  simp only [circuit_norm]
  intro h_in_or_guars
  constructor
  · tauto
  intro h_guars i hi
  specialize h_in_or_guars i hi
  tauto

theorem GeneralFormalCircuit.guarantees_iff'
  (circuit : GeneralFormalCircuit F Input Output) (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    (circuit.main input_var |>.operations n).FullGuarantees env ↔
      ∀ channel ∈ circuit.channelsWithGuarantees, (circuit.main input_var |>.operations n).ChannelGuarantees channel env := by
  apply Operations.guarantees_iff
  apply circuit.in_channels_or_guarantees_full

theorem Operations.requirements_iff (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrRequirementsFull channels env →
    (ops.FullRequirements env ↔
      ∀ channel ∈ channels, ops.ChannelRequirements channel env) := by
  simp only [circuit_norm]
  intro h_in_or_reqs
  constructor
  · tauto
  intro h_reqs i hi
  specialize h_in_or_reqs i hi
  tauto

theorem GeneralFormalCircuit.requirements_iff'
  (circuit : GeneralFormalCircuit F Input Output) (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    (circuit.main input_var |>.operations n).FullRequirements env ↔
      ∀ channel ∈ circuit.channelsWithRequirements, (circuit.main input_var |>.operations n).ChannelRequirements channel env := by
  apply Operations.requirements_iff
  apply circuit.in_channels_or_requirements_full

theorem Operations.channels_subset {ops : Operations F} :
    ops.SubcircuitChannelsLawful →
    ops.channels ⊆ ops.shallowChannels ++
      ops.subcircuitChannelsWithGuarantees ++ ops.subcircuitChannelsWithRequirements := by
  intro h_lawful
  simp only [List.subset_def, channels, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [forall_interactions_iff, shallowChannels_eq_interactions_map]
  rw [Operations.subcircuitChannelsLawful_iff_forall] at h_lawful
  constructor
  · intro i i_mem; simp; left; use i
  intro ⟨ n, s ⟩ s_mem
  have h_all := (h_lawful ⟨n, s⟩ s_mem).2.2
  simp only [FlatOperation.channels, List.subset_def, List.mem_map, List.mem_append,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h_all
  simp only [subcircuitChannelsWithGuarantees_eq_subcircuits_map,
    subcircuitChannelsWithRequirements_eq_subcircuits_map, List.append_assoc, List.mem_append,
    List.mem_map, List.mem_flatten, PSigma.exists, ↓existsAndEq, and_true]
  intro i i_mem
  right
  specialize h_all i i_mem
  rcases h_all
  · left; use n, s
  · right; use n, s

omit [ProvableType Output] [ProvableType Input] in
theorem FormalCircuitBase.channels_subset
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output) (input_var : Var Input F) (n : ℕ) :
    ((circuit.main input_var).operations n).channels ⊆ circuit.channels := by
  have shallowChannels_subset := circuit.mem_channelsWithGuarantees_or_mem_channelsWithRequirements_of_mem_shallowChannels input_var n
  have channelsWithGuarantees_subset := circuit.subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees input_var n
  have channelsWithRequirements_subset := circuit.subcircuitChannelsWithRequirements_subset_channelsWithRequirements input_var n
  simp only at *
  set ops := (circuit.main input_var).operations n
  trans ops.shallowChannels ++ ops.subcircuitChannelsWithGuarantees ++ ops.subcircuitChannelsWithRequirements
  apply Operations.channels_subset
  exact circuit.subcircuitChannelsLawful input_var n
  simp_all only [channels, List.append_assoc, List.append_subset, List.subset_append_of_subset_left,
    List.subset_append_of_subset_right, and_self, and_true]
  simp only [List.subset_def, List.mem_append]
  tauto
end
