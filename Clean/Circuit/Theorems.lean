/-
This file contains theorems that immediately follow from the definitions in `Circuit.Basic`.

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
    Operations.local_length (a :: as) = a.local_length + as.local_length := by
  cases a <;> simp_all [local_length, Operation.local_length]

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

theorem forAll_implies {c c' : Condition F} {n : ℕ} {ops : Operations F} :
  c.implies c' → (forAll n c ops → forAll n c' ops) := by
  simp only [Condition.implies]
  intro h
  induction ops using Operations.induct generalizing n with
  | empty => simp [forAll_empty]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp_all [forAll_cons, forAll_append, Operations.local_length, h]
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
    | case2 m' _ ops' ih' =>
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
    simp only [List.cons_append, witness_length, witnesses, Vector.toArray_append, ih, Array.append_assoc]
  | case3 _ _ ih | case4 _ _ ih =>
    simp only [List.cons_append, witness_length, witnesses, ih]

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
    try simp only [witness_length, witnesses, Vector.toArray_append, SubCircuit.witnesses, Vector.toArray_cast]

/-- equivalent, non-inductive statement of `Environment.uses_local_witnesses` (that is harder to unfold for a circuit) -/
def uses_local_witnesses' (env: Environment F) (offset : ℕ) (ops: Operations F) :=
  env.extends_vector (ops.local_witnesses env) offset

/--
Helper lemma: An environment respects local witnesses if it does so in the flattened variant.
-/
lemma env_extends_iff_flat {n: ℕ} {ops: Operations F} {env: Environment F} :
    env.extends_vector (witnesses env (to_flat_operations ops)) n ↔
    env.uses_local_witnesses' n ops := by
  simp only [extends_vector, uses_local_witnesses', Fin.forall_iff, flat_witness_length_eq]
  constructor
  · intro h i hi
    rw [h i hi, Vector.getElem_mk]
    simp [flat_witness_eq_witness]
  · intro h i hi
    rw [h i hi, Vector.getElem_mk, Vector.getElem_mk]
    simp [flat_witness_eq_witness]

lemma env_extends_witness {n: ℕ} {ops: Operations F} {env: Environment F} {m c} :
    env.uses_local_witnesses' n (.witness m c :: ops) ↔ (env.extends_vector (c env) n ∧ env.uses_local_witnesses' (m + n) ops) := by
  simp_all only [uses_local_witnesses', circuit_norm, Vector.getElem_append]
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

lemma env_extends_subcircuit {n: ℕ} {ops: Operations F} {env: Environment F} {n'} {s : SubCircuit F n'} :
    env.uses_local_witnesses' n (.subcircuit s :: ops) ↔ (env.extends_vector (witnesses env s.ops) n ∧ env.uses_local_witnesses' (s.local_length + n) ops) := by
  simp_all only [uses_local_witnesses', circuit_norm, witness_length, Vector.getElem_append, Fin.forall_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      have : i < s.local_length := by rw [s.local_length_eq]; exact hi
      specialize h i (by omega)
      simp [h, this]
    · intro i hi
      specialize h (s.local_length + i) (by linarith [hi])
      ring_nf at *
      simp [h]
  · intro ⟨ h_inner, h_outer ⟩ i hi
    by_cases hi' : i < s.local_length <;> simp only [hi', reduceDIte]
    · exact h_inner i (by rw [s.local_length_eq] at hi'; exact hi')
    · specialize h_outer (i - s.local_length) (by omega)
      simp only [←h_outer]
      congr 1
      omega

lemma extends_vector_subcircuit (env : Environment F) {n} {n'} {circuit : SubCircuit F n'} :
    env.extends_vector (circuit.witnesses env) n = env.extends_vector (FlatOperation.witnesses env circuit.ops) n := by
  have h_length : circuit.local_length = FlatOperation.witness_length circuit.ops := circuit.local_length_eq
  congr
  rw [SubCircuit.witnesses]
  apply Vector.cast_heq

theorem can_replace_local_witnesses {env: Environment F} (n: ℕ) {ops: Operations F}  :
    env.uses_local_witnesses' n ops ↔ env.uses_local_witnesses n ops := by
  induction ops using Operations.induct generalizing n with
  | empty => simp [uses_local_witnesses, uses_local_witnesses', extends_vector, Operations.local_witnesses, Operations.local_length]
  | witness m _ _ ih =>
    rw [uses_local_witnesses, env_extends_witness, ih (m + n)]
  | assert | lookup =>
    simp_all [uses_local_witnesses', uses_local_witnesses, circuit_norm]
  | subcircuit s _ ih =>
    rw [uses_local_witnesses, env_extends_subcircuit, extends_vector_subcircuit, ih (_ + n)]

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

theorem uses_local_witnesses_iff_forAll (n: ℕ) {env: Environment F} {ops: Operations F} :
  env.uses_local_witnesses n ops ↔ ops.forAll n {
    witness n _ c := env.extends_vector (c env) n,
    subcircuit n _ s := env.extends_vector (s.witnesses env) n
  } := by
  induction ops using Operations.induct generalizing n with
  | empty => trivial
  | assert | lookup | witness | subcircuit =>
    simp_all +arith [uses_local_witnesses, Operations.forAll]
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

-- theorems about witness generation

lemma FlatOperation.dynamic_witnesses_length {op : FlatOperation F} {init : List F} :
    (op.dynamic_witnesses init).length = op.local_length := by
  rcases op <;> simp [dynamic_witnesses, local_length]

lemma FlatOperation.dynamic_witnesses_list_length {ops : List (FlatOperation F)} (init : List F) :
    (dynamic_witnesses_list ops init).length = init.length + witness_length ops := by
  induction ops generalizing init with
  | nil => rw [dynamic_witnesses_list, List.foldl_nil, witness_length, add_zero]
  | cons op ops ih =>
    simp_all +arith [dynamic_witnesses_list, witness_length_cons, dynamic_witnesses_length]

lemma Operation.witnesses_length {op : Operation F} {init : List F} :
    (op.witnesses init).length = op.local_length := by
  rcases op <;> simp only [witnesses, local_length, Vector.length_toList, List.length_nil]

lemma FlatOperation.dynamic_witnesses_cons {op : FlatOperation F} {ops: List (FlatOperation F)} {acc : List F} :
    dynamic_witnesses_list (op :: ops) acc = dynamic_witnesses_list ops (acc ++ op.dynamic_witnesses acc) := by
  simp only [dynamic_witnesses_list, List.foldl_cons]

lemma Operations.witnesses_cons (op : Operation F) (ops: Operations F) (init : List F) :
    witnesses (op :: ops) init = ops.witnesses (init ++ op.witnesses init) := by
  simp only [witnesses, List.foldl_cons]

lemma FlatOperation.getD_dynamic_witnesses_of_lt {ops: List (FlatOperation F)} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (dynamic_witnesses_list ops acc)[i]?.getD 0 = acc[i] := by
  simp only [dynamic_witnesses_list]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ dynamic_witnesses op acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma Operations.getD_witnesses_of_lt {ops: Operations F} {acc : List F} {i : ℕ} (hi : i < acc.length) :
    (ops.witnesses acc)[i]?.getD 0 = acc[i] := by
  simp only [Operations.witnesses]
  induction ops generalizing acc with
  | nil => simp [hi]
  | cons op ops ih =>
    have : i < (acc ++ op.witnesses acc).length := by rw [List.length_append]; linarith
    rw [List.foldl_cons, ih this, List.getElem_append_left]

lemma FlatOperation.getD_dynamic_witnesses_cons_right {op : FlatOperation F} {ops: List (FlatOperation F)} {init : List F} {i : ℕ} (hi : i < op.local_length) :
    (dynamic_witnesses_list (op :: ops) init)[init.length + i]?.getD 0 = (op.dynamic_witnesses init)[i]'(dynamic_witnesses_length (F:=F) ▸ hi) := by
  rw [dynamic_witnesses_cons, getD_dynamic_witnesses_of_lt (by simp [hi, dynamic_witnesses_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

lemma Operations.getD_witnesses_cons_right {op : Operation F} {ops: Operations F} {init : List F} {i : ℕ} (hi : i < op.local_length) :
    (Operations.witnesses (op :: ops) init)[init.length + i]?.getD 0 = (op.witnesses init)[i]'(Operation.witnesses_length (F:=F) ▸ hi) := by
  rw [witnesses_cons, Operations.getD_witnesses_of_lt (by simp [hi, Operation.witnesses_length]),
    List.getElem_append_right (by linarith)]
  simp only [add_tsub_cancel_left]

theorem Operations.local_witnesses_cons (op : Operation F) (ops : Operations F) (env : Environment F) :
  Operations.local_witnesses env (op :: ops) =
    (op.local_witnesses env ++ ops.local_witnesses env).cast (Operations.local_length_cons.symm) := by
  cases op <;> simp only [local_witnesses, Operation.local_witnesses, Vector.cast_rfl]
  rw [Vector.empty_append]; simp
  rw [Vector.empty_append]; simp

theorem FlatOperation.only_accessed_below_all {ops : List (FlatOperation F)} (n : ℕ) :
  forAll n { witness n _ := Environment.only_accessed_below n } ops →
    Environment.only_accessed_below (n + witness_length ops) (witnesses · ops) := by
  intro h_comp env env' h_env
  simp only
  induction ops generalizing n with
  | nil => simp [witnesses]
  | cons op ops ih =>
    simp_all only [forAll_cons, witness_length_cons]
    obtain ⟨ h_comp, h_ih ⟩ := h_comp
    replace h_ih := ih (op.local_length + n) h_ih
    ring_nf at *
    specialize h_ih h_env
    clear ih
    cases op with
    | assert | lookup =>
      simp_all only [Operations.Condition.applyFlat, witnesses]
    | witness m c =>
      simp_all only [Operations.Condition.applyFlat, witnesses, Environment.only_accessed_below]
      congr 1
      apply h_comp env env'
      intro i hi
      exact h_env i (by linarith)

def Environment.uses_local_witnesses_flat (env : Environment F) (n : ℕ) (ops : List (FlatOperation F)) : Prop :=
  env.extends_vector (FlatOperation.witnesses env ops) n

theorem FlatOperation.proverEnvironment_uses_local_witnesses {ops : List (FlatOperation F)} (init : List F) :
  forAll init.length { witness n _ := Environment.only_accessed_below n } ops →
    (Environment.fromFlatOperations ops init).uses_local_witnesses_flat init.length ops := by
  intro h_computable
  simp only [Environment.fromFlatOperations, Environment.uses_local_witnesses_flat, Environment.extends_vector]
  induction ops generalizing init with
  | nil => intro i; nomatch i
  | cons op ops ih =>
    simp only [forAll_cons] at h_computable
    simp only [dynamic_witnesses_cons, Environment.extends_vector]
    cases op with
    | assert | lookup  =>
      simp_all [witnesses, witness_length, local_length, zero_add, dynamic_witnesses, List.append_nil]
    | witness m compute =>
      simp_all only [local_length, witness_length, dynamic_witnesses, witnesses, Operations.Condition.applyFlat]
      intro i
      set env := Environment.fromList init with h_env
      specialize ih (init ++ (compute env).toList)
      simp only [List.length_append, Vector.length_toList] at ih
      ring_nf at *
      specialize ih h_computable.right
      rcases i with ⟨ i , hi ⟩
      simp only
      by_cases hi' : i < m
      -- TODO
      stop
      rw [Operations.getD_witnesses_cons_right i.is_lt]
      simp only [Operation.witnesses, Vector.getElem_toList]
      simp only [Operations.Condition.apply] at h_computable
      congr 1
      apply h_computable.left
      intro j hj
      simp only [Environment.fromList, hj, List.getElem?_eq_getElem, Option.getD_some, h_env,
        Operations.getD_witnesses_of_lt]
    -- constructor
    -- -- get rid of ih first
    -- case right =>
    --   simp only [Operations.witnesses_cons]
    --   set acc := init ++ op.witnesses init
    --   have h_acc : acc.length = op.local_length + init.length := by rw [List.length_append, Operation.witnesses_length, add_comm]
    --   specialize ih acc
    --   rw [h_acc, Environment.uses_local_witnesses_iff_forAll] at ih
    --   exact ih h_computable.right
    -- clear ih
    -- set env := Environment.fromList (Operations.witnesses (op :: ops) init) with h_env
    -- nth_rw 1 3 [h_env]
    -- simp only [Environment.fromList, add_tsub_cancel_left, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte, Environment.extends_vector]
    -- cases op with
    -- | assert | lookup  => simp only [Operations.Condition.apply]

theorem Circuit.proverEnvironment_uses_local_witnesses (circuit : Circuit F α) (init : List F) :
  circuit.computable_witnesses →
    (circuit.proverEnvironment init).uses_local_witnesses init.length (circuit.operations init.length) := by
  intro h_computable
  specialize h_computable init.length
  simp only [proverEnvironment]
  generalize circuit.operations init.length = ops at *
  clear circuit
  induction ops generalizing init with
  | nil => trivial
  | cons op ops ih =>
    simp only [Operations.computable_witnesses, Operations.forAll_cons] at h_computable
    simp only [Environment.uses_local_witnesses_iff_forAll, Operations.forAll_cons]
    constructor
    -- get rid of ih first
    case right =>
      simp only [Operations.witnesses_cons]
      set acc := init ++ op.witnesses init
      have h_acc : acc.length = op.local_length + init.length := by rw [List.length_append, Operation.witnesses_length, add_comm]
      specialize ih acc
      rw [h_acc, Environment.uses_local_witnesses_iff_forAll] at ih
      exact ih h_computable.right
    clear ih
    set env := Environment.fromList (Operations.witnesses (op :: ops) init) with h_env
    nth_rw 1 3 [h_env]
    simp only [Environment.fromList, add_tsub_cancel_left, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte, Environment.extends_vector]
    cases op with
    | assert | lookup  => simp only [Operations.Condition.apply]
    | witness m c =>
      intro i
      rw [Operations.getD_witnesses_cons_right i.is_lt]
      simp only [Operation.witnesses, Vector.getElem_toList]
      simp only [Operations.Condition.apply] at h_computable
      congr 1
      apply h_computable.left
      intro j hj
      simp only [Environment.fromList, hj, List.getElem?_eq_getElem, Option.getD_some, h_env,
        Operations.getD_witnesses_of_lt]
    | subcircuit s =>
      simp only [Operations.Condition.apply] at h_computable ⊢
      intro i
      rw [Operations.getD_witnesses_cons_right i.is_lt]
      simp only [Operation.witnesses, Vector.getElem_toList]
      congr 1
      set env' := Environment.fromFlatOperations s.ops init with h_env'
      have h_env_eq : ∀ i < init.length + s.local_length, env'.get i = env.get i := by
        intro i hi
        simp only [h_env, h_env', Environment.fromList, Environment.fromFlatOperations]
        by_cases hi' : i < init.length
        · rw [Operations.getD_witnesses_of_lt hi', FlatOperation.getD_dynamic_witnesses_of_lt hi']
        obtain ⟨ k, hk ⟩ : ∃ k, i = init.length + k := by
          have : i ≥ init.length := by omega
          exact Nat.exists_eq_add_of_le this
        subst hk
        have hk : k < s.local_length := Nat.lt_of_add_lt_add_left hi
        rw [Operations.getD_witnesses_cons_right (by simp only [Operation.local_length]; exact hk)]
        simp only [Operation.witnesses, Vector.getElem_toList]
        simp only [Option.getD_some, Vector.getElem_cast]
        suffices h_env_extends : env'.extends_vector (FlatOperation.witnesses env' s.ops) init.length by
          simp only [Environment.extends_vector, env'] at h_env_extends
          nth_rw 1 [Environment.fromFlatOperations] at h_env_extends
          simp only [Environment.fromList] at h_env_extends
          rw [s.local_length_eq] at hk
          exact h_env_extends ⟨ k, hk ⟩
        sorry
      simp only [SubCircuit.witnesses, Vector.cast_eq_cast, Vector.cast_rfl]
      rw [s.local_length_eq] at h_env_eq
      apply FlatOperation.only_accessed_below_all _ h_computable.left
      exact h_env_eq

theorem Operations.only_accessed_below_all (ops : Operations F) (n : ℕ) :
  ops.computable_witnesses n →
    Environment.only_accessed_below (n + ops.local_length) ops.local_witnesses := by
  simp only [computable_witnesses]
  induction ops generalizing n with
  | nil => simp [Environment.only_accessed_below, local_witnesses, forAll_empty]
  | cons op ops ih =>
    simp only [local_witnesses, forAll_cons, and_congr_right_iff]
    intro ⟨ h_comp, h_ih ⟩ env env' h_env
    simp only [local_length_cons] at h_env
    replace h_ih := ih (op.local_length + n) h_ih env env'
    simp only at h_ih
    clear ih
    simp only [local_witnesses_cons, Vector.cast_eq_cast, Vector.cast_rfl]
    ring_nf at *
    congr 1
    · cases op with
      | assert | lookup =>
        simp_all only [Condition.apply, Operation.local_witnesses, Operation.local_length, local_length]
      | witness m c =>
        simp_all only [Condition.apply, Operation.local_witnesses, Operation.local_length, local_length]
        apply h_comp env env'
        intro i hi
        exact h_env i (by linarith)
      | subcircuit s =>
        simp_all only [Condition.apply, Operation.local_witnesses, Operation.local_length, local_length]
        simp only [SubCircuit.witnesses, Vector.cast_eq_cast, Vector.cast_rfl]
        clear h_ih
        sorry
    exact h_ih h_env
