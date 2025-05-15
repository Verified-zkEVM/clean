import Clean.Circuit.Lawful
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

-- we prove a few properties about the circuit `forM xs circuit`, where `circuit : α → Circuit F Unit`
-- TODO handle more general loops

instance LawfulCircuit.from_forM {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] (xs : List α) :
    LawfulCircuit (forM xs circuit) := by
  induction xs
  case nil => rw [List.forM_nil]; infer_instance
  case cons x xs ih => rw [List.forM_cons]; exact from_bind inferInstance inferInstance

instance LawfulCircuit.from_mapM {circuit : α → Circuit F β} [∀ x : α, LawfulCircuit (circuit x)] (xs : List α) :
    LawfulCircuit (xs.mapM circuit) := by
  induction xs
  case nil => rw [List.mapM_nil]; infer_instance
  case cons x xs ih =>  rw [List.mapM_cons]; infer_lawful_circuit

instance LawfulCircuit.from_foldlM {circuit : β → α → Circuit F β}
  (lawful : ∀ z x, LawfulCircuit (circuit z x)) (xs : List α) (init : β) :
    LawfulCircuit (xs.foldlM circuit init) := by
  induction xs generalizing init
  case nil => rw [List.foldlM_nil]; infer_instance
  case cons x xs ih => rw [List.foldlM_cons]; exact from_bind inferInstance inferInstance

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    forM xs body = forM xs.toList body := by
  rw [Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

lemma Vector.mapM_toList (xs : Vector α n) {m : Type → Type} [monad: Monad m] [LawfulMonad m] (body : α → m β) :
    (fun v => v.toArray.toList) <$> (xs.mapM body) = xs.toList.mapM body := by
  rw [←Array.toList_mapM, ←Vector.toArray_mapM, Functor.map_map]

lemma Vector.foldlM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : β → α → m β) (init : β) :
    xs.foldlM body init = xs.toList.foldlM body init := by
  rw [Vector.foldlM_mk, List.foldlM_toArray]

instance LawfulCircuit.from_forM_vector {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] {n : ℕ} (xs : Vector α n) :
    LawfulCircuit (forM xs circuit) := by
  rw [Vector.forM_toList]
  apply from_forM

instance LawfulCircuit.from_foldlM_vector {circuit : β → α → Circuit F β} (lawful : ∀ z x, LawfulCircuit (circuit z x)) {n : ℕ} (xs : Vector α n) (init : β) :
    LawfulCircuit (xs.foldlM circuit init) := by
  rw [Vector.foldlM_toList]
  apply from_foldlM inferInstance

namespace Circuit
theorem forM_local_length {circuit : α → Circuit F Unit} [lawful : ConstantLawfulCircuits circuit]
  {xs : List α} {n : ℕ} :
    (forM xs circuit).local_length n = lawful.local_length * xs.length := by
  set k := lawful.local_length
  induction xs generalizing n with
  | nil =>
    rw [List.forM_nil, LawfulCircuit.local_length_eq]
    rfl
  | cons x xs ih =>
    rw [List.forM_cons, LawfulCircuit.bind_local_length, LawfulCircuit.local_length_eq, ih]
    rw [List.length_cons, mul_add, mul_one, add_comm _ k]
    rfl
    all_goals infer_instance
end Circuit

lemma ConstantLawfulCircuit.from_mapM_vector.offset_independent {circuit : α → Circuit F β} [Nonempty β]
  {xs : Vector α m} [lawful: ConstantLawfulCircuits circuit] (ops : OperationsList F) :
    (Vector.mapM circuit xs ops).2.offset = ops.offset + lawful.local_length * m := by
  induction xs using Vector.induct_push
  case nil => simp only [Vector.mapM_mk_empty, pure, StateT.pure, mul_zero, add_zero]
  case push xs x ih =>
    rename_i n'
    rw [Vector.mapM_push]
    simp only [bind_pure_comp] at ih ⊢
    show (circuit x (xs.mapM circuit ops).2).2.offset = _
    rw [lawful.offset_independent x (Vector.mapM circuit xs ops).2, ih]
    ring

instance ConstantLawfulCircuit.from_mapM_vector {circuit : α → Circuit F β} [Nonempty β]
  (xs : Vector α m) (lawful : ConstantLawfulCircuits circuit) :
    ConstantLawfulCircuit (xs.mapM circuit) where

  output n := xs.mapIdx fun i x => lawful.output x (n + lawful.local_length * i)
  local_length := lawful.local_length * m
  final_offset n := n + lawful.local_length * m

  operations n : OperationsFrom F n (n + lawful.local_length * m) := by
    set k := ConstantLawfulCircuits.local_length circuit
    induction xs using Vector.induct_push
    case nil => exact .empty n
    case push xs x ops =>
      rename_i n'
      rw [mul_add, ←add_assoc, mul_one]
      exact ops ++ lawful.operations x (n + k * n')

  offset_independent := from_mapM_vector.offset_independent

  output_independent ops := by
    induction xs using Vector.induct_push
    case nil => simp
    case push xs x ih =>
      rename_i n'
      rw [Vector.mapM_push]
      simp only [Vector.mapIdx, Vector.eq_mk, bind_pure_comp, Vector.toArray_push,
        Array.mapIdx_push, Vector.size_toArray] at ih ⊢
      rw [←ih]
      show ((xs.mapM circuit ops).1.push (circuit x (xs.mapM circuit ops).2).1).toArray = _
      simp only [Vector.toArray_push]
      rw [lawful.output_independent x (Vector.mapM circuit xs ops).2]
      congr
      apply from_mapM_vector.offset_independent

  append_only ops := by
    simp only [eq_mpr_eq_cast, cast_cast, cast_eq]
    induction xs using Vector.induct_push
    case nil =>
      simp [Vector.mapM_mk_empty, pure, StateT.pure, Vector.induct_push, Operations.append_empty]
    case push xs x ih =>
      rename_i n'
      simp only [Vector.mapM_push]
      let g (bs : Vector β n') := (do let b ← circuit x; pure (bs.push b))
      let bs := ((xs.mapM circuit) ops).1
      change (g bs ((xs.mapM circuit) ops).2).2 = _
      let lawful' : LawfulCircuit (g bs) := by infer_lawful_circuit
      simp only [ih, lawful'.append_only, lawful', LawfulCircuit.final_offset, LawfulCircuit.operations]
      set k := lawful.local_length
      have h_offset : ops.offset + lawful.local_length * n' + lawful.local_length
        = ops.offset + lawful.local_length * (n' + 1) := by ring
      simp only [OperationsFrom.append_empty, OperationsList.mk.injEq, h_offset, true_and, lawful']
      rw [Operations.append_assoc]
      congr
      simp [Vector.induct_push_push]


instance ConstantLawfulCircuits.from_foldlM_vector' [Inhabited β] {circuit : β → α → Circuit F β}
  (xs : Vector α m) (lawful : ConstantLawfulCircuits fun (z, x) => circuit z x) :
    ConstantLawfulCircuits (xs.foldlM circuit) := by
  apply ConstantLawfulCircuits.from_constant_length (.from_foldlM_vector (fun z x =>
    lawful.to_single _ (z, x) |>.toLawfulCircuit) xs)
  intro init n
  simp only [←LawfulCircuit.final_offset_eq, Circuit.final_offset]
  suffices h : ∀ ops init,
    (xs.foldlM circuit init ops).2.offset = ops.offset + ((xs.foldlM circuit default).final_offset 0) by rw [h]
  induction xs using Vector.induct
  case nil => intros; rfl
  case cons x xs ih =>
    intro ops init
    rw [Vector.foldlM_toList, Vector.foldlM_toList, Vector.cons, List.foldlM_cons, List.foldlM_cons]
    simp only [←Vector.foldlM_toList]
    show (xs.foldlM circuit ..).2.offset = _ + (xs.foldlM circuit ..).2.offset
    rw [ih, ih]
    let prod_circuit := fun (z, x) => circuit z x
    show (prod_circuit (init, x) _).2.offset + _ = ops.offset + ((prod_circuit (default, x) _).2.offset + _)
    simp only [ConstantLawfulCircuits.offset_independent]
    ac_rfl

lemma ConstantLawfulCircuits.from_foldlM_vector.offset_independent {circuit : β → α → Circuit F β} [Inhabited β]
  (xs : Vector α m) (lawful : ConstantLawfulCircuits fun (acc, x) => circuit acc x) (init : β) (ops : OperationsList F) :
    (xs.foldlM circuit init ops).2.offset = ops.offset + lawful.local_length * m := by
  simp only
  set k := lawful.local_length
  induction xs using Vector.induct generalizing init ops
  case nil => rfl
  case cons x xs ih =>
    rw [Vector.foldlM_toList, Vector.cons, List.foldlM_cons]
    simp only [←Vector.foldlM_toList]
    show (xs.foldlM circuit ..).2.offset = _
    rw [ih]
    let prod_circuit := fun (z, x) => circuit z x
    show (prod_circuit (init, x) _).2.offset + _ = _
    simp only [ConstantLawfulCircuits.offset_independent]
    ring

instance ConstantLawfulCircuits.from_foldlM_vector [Inhabited β] {circuit : β → α → Circuit F β}
  (xs : Vector α m) (lawful : ConstantLawfulCircuits fun (acc, x) => circuit acc x) :
    ConstantLawfulCircuits (xs.foldlM circuit) where

  output init n := Fin.foldl m (fun acc i => lawful.output (acc, xs[i]) (n + lawful.local_length * i)) init
  local_length := lawful.local_length * m
  operations init n :=
    let k := lawful.local_length
    let ops : OperationsFrom F n (n + k * m) := by
      induction xs using Vector.induct_push
      case nil => exact .empty n
      case push xs x ops =>
        rename_i n'
        rw [mul_add, ←add_assoc, mul_one]
        let acc := ((xs.foldlM circuit) init ops).1
        let ops' := ops ++ lawful.operations (acc, x) (n + k * n')
        exact ops'
    ops

  offset_independent := from_foldlM_vector.offset_independent xs lawful

  output_independent init ops := by
    simp only
    induction xs using Vector.induct generalizing init ops
    case nil => rfl
    case cons x xs ih =>
      rename_i n
      rw [Vector.foldlM_toList, Vector.cons, List.foldlM_cons]
      simp only [←Vector.foldlM_toList]
      show (xs.foldlM circuit ..).1 = _
      rw [ih, Fin.foldl_succ]
      simp only [Fin.getElem_fin, Fin.val_succ, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, Array.getElem_toList, Vector.getElem_toArray, Fin.val_zero,
        List.getElem_cons_zero, mul_zero, add_zero]
      congr
      · funext acc i
        let prod_circuit := fun (t : β × α) => circuit t.1 t.2
        show output prod_circuit (acc, xs[i.val]) ((prod_circuit (init, x) _).2.offset + _) = _
        rw [ConstantLawfulCircuits.offset_independent]
        ring_nf
        rfl
      rw [←lawful.output_independent]

  append_only init ops := by
    simp only [eq_mpr_eq_cast, cast_cast, cast_eq]
    induction xs using Vector.induct_push
    case nil =>
      simp [pure, StateT.pure, Vector.induct_push, Operations.append_empty]
    case push xs x ih =>
      rename_i n'
      rcases ops with ⟨ offset, ops ⟩
      simp only [Vector.foldlM_push] at ih ⊢
      let prod_circuit := fun (t : β × α) => circuit t.1 t.2
      have h_offset : offset + (local_length prod_circuit) * n' + local_length prod_circuit
        = offset + (local_length prod_circuit) * (n' + 1) := by ring
      let acc := ((xs.foldlM circuit) init ops).1
      change (prod_circuit (acc, x) ((xs.foldlM circuit) init ops).2).2 = _
      rw [ConstantLawfulCircuits.append_only, ih]
      simp only
      simp +arith only [Nat.mul_zero, OperationsList.mk.injEq,
        prod_circuit, h_offset, true_and]
      rw [Operations.append_assoc]
      simp only [Vector.induct_push_push, acc]
      congr
      rw [heq_cast_iff_heq]
      simp only [heq_eq_eq, prod_circuit, acc]
      -- TODO
      -- conv => rhs; simp
      congr 1
      congr

namespace Circuit.constraints_hold
-- characterize `constraints_hold` for variants of `forM`
section
variable {env : Environment F} {n m : ℕ} {prop : Operations.Condition F}
variable {circuit : α → Circuit F Unit} [lawful : ConstantLawfulCircuits circuit]

theorem forM_forAll {xs : List α} :
  (forM xs circuit |>.operations n).forAll prop ↔
    xs.zipIdx.Forall fun (x, i) => (circuit x |>.operations (n + i*lawful.local_length)).forAll prop := by

  induction xs generalizing n with
  | nil => simp [Operations.forAll, circuit_norm]
  | cons x xs ih =>
    rw [List.forM_cons, List.zipIdx_cons, List.forall_cons]
    simp only at ih ⊢
    rw [zero_mul, add_zero, zero_add]
    specialize ih (n := n + lawful.local_length)

    have h_zip : xs.zipIdx.Forall (fun (x, i) => ((circuit x).operations (n + lawful.local_length + i * lawful.local_length)).forAll prop)
      ↔ (xs.zipIdx 1).Forall (fun (x, i) => ((circuit x).operations (n + i * lawful.local_length)).forAll prop) := by
      rw [List.zipIdx_succ, List.forall_map_iff]
      conv =>
        rhs
        change xs.zipIdx.Forall fun (x, i) => ((circuit x).operations (n + (i + 1) * lawful.local_length)).forAll prop
        lhs
        intro t
        simp only
        rw [add_mul, one_mul, add_comm _ lawful.local_length, ←add_assoc]

    rw [←h_zip, ←ih]
    clear h_zip ih
    rw [bind_forAll inferInstance inferInstance]
    exact Iff.intro id id

theorem forM_vector_forAll {xs : Vector α n} :
  (forM xs circuit |>.operations m).forAll prop ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), (circuit x |>.operations (m + i*lawful.local_length)).forAll prop := by
  rw [Vector.forM_toList, forM_forAll, List.forall_iff_forall_mem, Prod.forall]
  have h_elem_iff : ∀ {t}, (t ∈ xs.zipIdx ↔ t ∈ xs.toList.zipIdx) := by
    intro t
    rw [←Array.toList_zipIdx, ←Vector.mem_toList_iff]
    exact ⟨ id, id ⟩
  constructor
  · exact fun h x _ i hxi => h x i (h_elem_iff.mp hxi)
  · intro h x i hxi
    rw [←h_elem_iff (t:=(x, i))] at hxi
    have hx : x ∈ xs := by
      rw [Vector.mem_iff_getElem?]
      exact ⟨ i, Vector.mem_zipIdx_iff_getElem? (x:=(x, i)).mp hxi⟩
    exact h x hx i hxi

theorem forM_vector_forAll' {xs : Vector α n} :
  (forM xs circuit |>.operations m).forAll prop ↔
    ∀ (i : Fin n), (circuit xs[i.val] |>.operations (m + i*lawful.local_length)).forAll prop := by
  rw [forM_vector_forAll]
  constructor
  · intro h i
    exact h xs[i] (by simp) i (by simp [Vector.mem_zipIdx_iff_getElem?])
  · intro h x hx i hxi
    simp only [Vector.mem_zipIdx_iff_getElem?, Vector.getElem?_eq_some_iff] at hxi
    have ⟨ i_lt, x_eq ⟩ := hxi
    exact x_eq ▸ h ⟨ i, i_lt ⟩

-- specialization to soundness / completeness
theorem forM_soundness {xs : List α} :
  soundness env (forM xs circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => soundness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [soundness_iff_forAll, forM_forAll]

theorem forM_completeness {xs : List α} :
  completeness env (forM xs circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => completeness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [completeness_iff_forAll, forM_forAll]

theorem forM_vector_soundness {xs : Vector α n} :
  soundness env (forM xs circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), soundness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [soundness_iff_forAll, forM_vector_forAll]

theorem forM_vector_completeness {xs : Vector α n} :
  completeness env (forM xs circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), completeness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [completeness_iff_forAll, forM_vector_forAll]

/-- simpler version for when the constraints don't depend on the input offset -/
theorem forM_vector_soundness' {xs : Vector α n} :
    soundness env (forM xs circuit |>.operations m) → ∀ x ∈ xs, ∃ k : ℕ, soundness env (circuit x |>.operations k) := by
  intro h
  replace h := forM_vector_soundness.mp h
  intro x hx
  obtain ⟨ i, hxi ⟩ := Vector.mem_iff_getElem?.mp hx
  rw [←Vector.mem_zipIdx_iff_getElem? (x:=(x, i))] at hxi
  specialize h x hx i hxi
  use m + i * lawful.local_length
end

end Circuit.constraints_hold
section
def Circuit.ignore (circuit : Circuit F β) : Circuit F Unit := do
  let _ ← circuit

instance LawfulCircuit.ignore (circuit : Circuit F β) [LawfulCircuit circuit] :
    LawfulCircuit circuit.ignore := by infer_lawful_circuit

instance ConstantLawfulCircuits.ignore (circuit : α → Circuit F β) [lawful : ConstantLawfulCircuits circuit] :
    ConstantLawfulCircuits (fun x => (circuit x).ignore) where
  output _ _ := ()
  local_length := local_length circuit
  operations x n := operations x n

  offset_independent x ops := by
    change (circuit x ops).2.offset = _
    apply offset_independent
  append_only x ops := by
    change (circuit x ops).2 = _
    apply append_only

lemma LawfulCircuit.ignore_final_offset {circuit : Circuit F β} [LawfulCircuit circuit] :
    final_offset circuit.ignore = final_offset circuit := rfl

  -- `.operations` doesn't care about circuit outputs

lemma operations_map {circuit : Circuit F α} (f : α → β) :
    (f <$> circuit).operations n = circuit.operations n := rfl

lemma operations_ignore {circuit : Circuit F α} :
    circuit.ignore.operations n = circuit.operations n := rfl

namespace Circuit.constraints_hold
variable {env : Environment F} {n m : ℕ} {prop : Operations.Condition F}
section
variable {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit]

lemma mapM_forAll_iff_forM {xs : List α} :
  (xs.mapM circuit |>.operations n).forAll prop ↔
    (forM xs (fun a => (circuit a).ignore) |>.operations n).forAll prop := by

  induction xs generalizing n with
  | nil =>
    exact ⟨ fun _ => trivial, fun _ => trivial ⟩
  | cons xs x ih =>
    rw [List.mapM_cons, List.forM_cons]
    rw [bind_forAll, bind_forAll, bind_forAll, ih]
    constructor
    · rintro ⟨ h, hrest, hpure ⟩
      rw [LawfulCircuit.ignore_final_offset]
      exact ⟨ h, hrest ⟩
    · rintro ⟨ h, hrest ⟩
      rw [LawfulCircuit.ignore_final_offset] at hrest
      use h, hrest
      simp only [Operations.forAll, circuit_norm]
    infer_lawful_circuit

omit lawful in
lemma mapM_forAll_vector_iff_list {xs : Vector α n} :
  (xs.mapM circuit |>.operations m).forAll prop ↔
    (xs.toList.mapM circuit |>.operations m).forAll prop := by
  rw [←Vector.mapM_toList xs, operations_map]

theorem mapM_forAll {xs : List α} :
  (xs.mapM circuit |>.operations m).forAll prop ↔
    xs.zipIdx.Forall fun (x, i) => (circuit x |>.operations (m + i*lawful.local_length)).forAll prop := by
  rw [mapM_forAll_iff_forM, forM_forAll]
  simp only [operations_ignore]
  trivial

theorem mapM_vector_forAll {xs : Vector α n} :
  (xs.mapM circuit |>.operations m).forAll prop ↔
    ∀ i : Fin n, (circuit xs[i.val] |>.operations (m + i*lawful.local_length)).forAll prop := by
  rw [mapM_forAll_vector_iff_list, mapM_forAll_iff_forM, ←Vector.forM_toList, forM_vector_forAll']
  simp only [operations_ignore]
  trivial

-- specialization to soundness / completeness

theorem mapM_soundness {xs : List α} :
  soundness env (xs.mapM circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => soundness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [soundness_iff_forAll, mapM_forAll]

theorem mapM_completeness {xs : List α} :
  completeness env (xs.mapM circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => completeness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [completeness_iff_forAll, mapM_forAll]
end

-- specialization to mapFinRangeM
theorem mapFinRangeM_forAll {n : ℕ} {circuit : Fin m → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
  (Vector.mapFinRangeM m circuit |>.operations n).forAll prop ↔
    ∀ i : Fin m, (circuit i |>.operations (n + i*lawful.local_length)).forAll prop := by
  rw [Vector.mapFinRangeM, mapM_vector_forAll]
  constructor
  · intro h i
    specialize h i
    rw [Vector.getElem_finRange] at h
    exact h
  · intro h i
    rw [Vector.getElem_finRange]
    exact h i

end constraints_hold

-- Loop constructs designed to simplify under `circuit_norm`

def mapFinRange (m : ℕ) [NeZero m] [Nonempty β] (body : Fin m → Circuit F β)
    (_lawful : ConstantLawfulCircuits body := by infer_constant_lawful_circuits) : Circuit F (Vector β m) :=
  Vector.mapFinRangeM m body

def map {m : ℕ} [Nonempty β] (xs : Vector α m) (body : α → Circuit F β)
    (_lawful : ConstantLawfulCircuits body := by infer_constant_lawful_circuits) : Circuit F (Vector β m) :=
  xs.mapM body

def foldl {m : ℕ} [Nonempty β] (xs : Vector α m) (init : β) (body : β → α → Circuit F β)
  (_lawful : ConstantLawfulCircuits (fun (s, a) => body s a) := by infer_constant_lawful_circuits) :
    Circuit F β :=
  xs.foldlM body init

section
variable {env : Environment F} {m n : ℕ} [NeZero m] [Nonempty β] {body : Fin m → Circuit F β} {lawful : ConstantLawfulCircuits body}

@[circuit_norm]
lemma mapFinRange.soundness :
  constraints_hold.soundness env (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.soundness env (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, constraints_hold.soundness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma mapFinRange.completeness :
  constraints_hold.completeness env (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.completeness env (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, constraints_hold.completeness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma mapFinRange.uses_local_witnesses :
  env.uses_local_witnesses_completeness (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, env.uses_local_witnesses_completeness (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, env.uses_local_witnesses_completeness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma mapFinRange.local_length_eq :
    (mapFinRange m body lawful).local_length n = m * (body 0).local_length := by
  let lawful_loop : ConstantLawfulCircuit (mapFinRange m body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [LawfulCircuit.local_length_eq]
  ac_rfl

@[circuit_norm]
lemma mapFinRange.initial_offset_eq :
    (mapFinRange m body lawful |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuit (mapFinRange m body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.initial_offset_eq]

@[circuit_norm]
lemma mapFinRange.output_eq :
  (mapFinRange m body lawful).output n =
    Vector.mapFinRange m fun i => (body i).output (n + i*(body 0).local_length) := by
  let lawful_loop : ConstantLawfulCircuit (mapFinRange m body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.output_eq]
  simp only [lawful_loop, lawful_norm]
  ext i hi
  rw [Vector.getElem_mapIdx, Vector.getElem_finRange, Vector.getElem_mapFinRange,
    LawfulCircuit.output_eq, LawfulCircuit.local_length_eq]
  ac_rfl
end

section
variable {env : Environment F} {m n : ℕ} [Inhabited α] [Nonempty β] {xs : Vector α m}
  {body : α → Circuit F β} {lawful : ConstantLawfulCircuits body}

@[circuit_norm]
lemma map.soundness :
  constraints_hold.soundness env (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.soundness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, constraints_hold.soundness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma map.completeness :
  constraints_hold.completeness env (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.completeness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, constraints_hold.completeness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma map.uses_local_witnesses :
  env.uses_local_witnesses_completeness (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, env.uses_local_witnesses_completeness (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, env.uses_local_witnesses_completeness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm]
lemma map.local_length_eq :
    (map xs body lawful).local_length n = m * (body default).local_length := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [LawfulCircuit.local_length_eq]
  ac_rfl

omit [Inhabited α] in
@[circuit_norm]
lemma map.initial_offset_eq :
    (map xs body lawful |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.initial_offset_eq]

@[circuit_norm]
lemma map.output_eq :
  (map xs body lawful).output n =
    xs.mapIdx fun i x => (body x).output (n + i*(body default).local_length) := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.output_eq]
  simp only [lawful_loop, lawful_norm]
  ext i hi
  rw [Vector.getElem_mapIdx, Vector.getElem_mapIdx, LawfulCircuit.output_eq, LawfulCircuit.local_length_eq]
  ac_rfl
end

section
variable {env : Environment F} {m n : ℕ} [Inhabited β] [Inhabited α] {xs : Vector α m}
  {body : β → α → Circuit F β} {init : β} {lawful : ConstantLawfulCircuits fun (t : β × α) => body t.1 t.2}

@[circuit_norm]
lemma foldl.local_length_eq :
    (foldl xs init body lawful).local_length n = m * (body default default).local_length := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful) := .from_foldlM_vector xs lawful
  rw [lawful_loop.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [←lawful.local_length_eq (default, default) 0]
  ac_rfl

omit [Inhabited α] in
@[circuit_norm]
lemma foldl.initial_offset_eq :
    (foldl xs init body lawful |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful) := .from_foldlM_vector xs lawful
  apply lawful_loop.initial_offset_eq

@[circuit_norm]
lemma foldl.output_eq :
  (foldl xs init body lawful).output n =
    Fin.foldl m (fun acc i => (body acc xs[i.val]).output (n + i*(body default default).local_length)) init := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful) := .from_foldlM_vector xs lawful
  rw [lawful_loop.output_eq]
  simp only [lawful_loop, lawful_norm, ←lawful.output_eq]
  rw [lawful.local_length_eq (default, default) 0]
  ac_rfl
end

end Circuit
end
