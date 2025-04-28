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

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    forM xs body = forM xs.toList body := by
  rw [Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

lemma Vector.mapM_toList (xs : Vector α n) {m : Type → Type} [monad: Monad m] [LawfulMonad m] (body : α → m β) :
    (fun v => v.toArray.toList) <$> (xs.mapM body) = xs.toList.mapM body := by
  rw [←Array.toList_mapM, ←Vector.toArray_mapM, Functor.map_map]

instance LawfulCircuit.from_forM_vector {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] {n : ℕ} (xs : Vector α n) :
    LawfulCircuit (forM xs circuit) := by
  rw [Vector.forM_toList]
  apply from_forM

namespace Circuit
theorem forM_local_length {circuit : α → Circuit F Unit} [lawful : ConstantLawfulCircuits circuit]
  {xs : List α} {n : ℕ} :
    ((forM xs circuit).operations n).local_length = lawful.local_length * xs.length := by
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

theorem mapM_local_length {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit]
  {xs : List α} {n : ℕ} :
    ((xs.mapM circuit).operations n).local_length = lawful.local_length * xs.length := by
  set k := lawful.local_length
  induction xs generalizing n with
  | nil =>
    rw [List.mapM_nil, LawfulCircuit.local_length_eq]
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    rw [LawfulCircuit.bind_local_length _ _ inferInstance (fun x => LawfulCircuit.from_bind inferInstance inferInstance)]
    rw [LawfulCircuit.bind_local_length _ _ inferInstance inferInstance]
    rw [ih, List.length_cons, mul_add, mul_one, add_comm _ k, LawfulCircuit.local_length_eq]
    rfl
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
      let lawful' : LawfulCircuit (g bs) := by infer_lawful_circuit
      change (g bs ((xs.mapM circuit) ops).2).2 = _
      simp only [ih, lawful'.append_only, lawful', LawfulCircuit.final_offset, LawfulCircuit.operations]
      set k := lawful.local_length
      have h_offset : ops.offset + lawful.local_length * n' + lawful.local_length
        = ops.offset + lawful.local_length * (n' + 1) := by ring
      simp only [OperationsFrom.append_empty, OperationsList.mk.injEq, h_offset, true_and, lawful']
      rw [Operations.append_assoc]
      congr
      simp [Vector.induct_push_push]

namespace Circuit.constraints_hold
-- characterize `constraints_hold` for variants of `forM`
section
variable {env : Environment F} {n m : ℕ} (from_subcircuit : {n : ℕ} → Environment F → SubCircuit F n → Prop)
variable {circuit : α → Circuit F Unit} [lawful : ConstantLawfulCircuits circuit]

theorem forM_generic {xs : List α} :
  generic from_subcircuit env (forM xs circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => generic from_subcircuit env (circuit x |>.operations (n + i*lawful.local_length)) := by

  induction xs generalizing n with
  | nil => simp [generic, circuit_norm]
  | cons x xs ih =>
    rw [List.forM_cons, List.zipIdx_cons, List.forall_cons]
    simp only at ih ⊢
    rw [zero_mul, add_zero, zero_add]
    specialize ih (n := n + lawful.local_length)

    have h_zip : List.Forall (fun (x, i) ↦ generic from_subcircuit env ((circuit x).operations (n + lawful.local_length + i * lawful.local_length))) xs.zipIdx
      ↔ List.Forall (fun (x, i) ↦ generic from_subcircuit env ((circuit x).operations (n + i * lawful.local_length))) (xs.zipIdx 1) := by
      rw [List.zipIdx_succ, List.forall_map_iff]
      conv =>
        rhs
        change List.Forall (fun (x, i) ↦ generic from_subcircuit env ((circuit x).operations (n + (i + 1) * lawful.local_length))) xs.zipIdx
        lhs
        intro t
        simp only
        rw [add_mul, one_mul, add_comm _ lawful.local_length, ←add_assoc]

    rw [←h_zip, ←ih]
    clear h_zip ih
    rw [bind_generic _ inferInstance inferInstance]
    exact Iff.intro id id

theorem forM_vector_generic {xs : Vector α n} :
  generic from_subcircuit env (forM xs circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), generic from_subcircuit env (circuit x |>.operations (m + i*lawful.local_length)) := by
  rw [Vector.forM_toList, forM_generic, List.forall_iff_forall_mem, Prod.forall]
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

-- specialization to soundness / completeness
theorem forM_soundness {xs : List α} :
  soundness env (forM xs circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => soundness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [soundness_iff_generic, forM_generic]

theorem forM_completeness {xs : List α} :
  completeness env (forM xs circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => completeness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [completeness_iff_generic, forM_generic]

theorem forM_vector_soundness {xs : Vector α n} :
  soundness env (forM xs circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), soundness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [soundness_iff_generic, forM_vector_generic]

theorem forM_vector_completeness {xs : Vector α n} :
  completeness env (forM xs circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), completeness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [completeness_iff_generic, forM_vector_generic]

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
variable {env : Environment F} {n m : ℕ} (from_subcircuit : {n : ℕ} → Environment F → SubCircuit F n → Prop)
section
variable {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit]

lemma mapM_generic_iff_forM {xs : List α} :
  generic from_subcircuit env (xs.mapM circuit |>.operations n) ↔
    generic from_subcircuit env (forM xs (fun a => (circuit a).ignore) |>.operations n) := by

  induction xs generalizing n with
  | nil =>
    exact ⟨ fun _ => trivial, fun _ => trivial ⟩
  | cons xs x ih =>
    rw [List.mapM_cons, List.forM_cons]
    rw [bind_generic, bind_generic, bind_generic, ih]
    constructor
    · rintro ⟨ h, hrest, hpure ⟩
      rw [LawfulCircuit.ignore_final_offset]
      exact ⟨ h, hrest ⟩
    · rintro ⟨ h, hrest ⟩
      rw [LawfulCircuit.ignore_final_offset] at hrest
      use h, hrest
      simp only [generic, circuit_norm]
    infer_lawful_circuit

omit lawful in
lemma mapM_generic_vector_iff_list {xs : Vector α n} :
  generic from_subcircuit env (xs.mapM circuit |>.operations m) ↔
    generic from_subcircuit env (xs.toList.mapM circuit |>.operations m) := by
  rw [←Vector.mapM_toList xs, operations_map]

theorem mapM_generic {xs : List α} :
  generic from_subcircuit env (xs.mapM circuit |>.operations m) ↔
    xs.zipIdx.Forall fun (x, i) => generic from_subcircuit env (circuit x |>.operations (m + i*lawful.local_length)) := by
  rw [mapM_generic_iff_forM, forM_generic]
  simp only [operations_ignore]
  trivial

theorem mapM_vector_generic {xs : Vector α n} :
  generic from_subcircuit env (xs.mapM circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), generic from_subcircuit env (circuit x |>.operations (m + i*lawful.local_length)) := by
  rw [mapM_generic_vector_iff_list, mapM_generic_iff_forM, ←Vector.forM_toList, forM_vector_generic]
  simp only [operations_ignore]
  trivial

-- specialization to soundness / completeness

theorem mapM_soundness {xs : List α} :
  soundness env (xs.mapM circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => soundness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [soundness_iff_generic, mapM_generic]

theorem mapM_completeness {xs : List α} :
  completeness env (xs.mapM circuit |>.operations n) ↔
    xs.zipIdx.Forall fun (x, i) => completeness env (circuit x |>.operations (n + i*lawful.local_length)) := by
  simp only [completeness_iff_generic, mapM_generic]

theorem mapM_vector_soundness {xs : Vector α n} :
  soundness env (xs.mapM circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), soundness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [soundness_iff_generic, mapM_vector_generic]

theorem mapM_vector_completeness {xs : Vector α n} :
  completeness env (xs.mapM circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), completeness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [completeness_iff_generic, mapM_vector_generic]
end

-- specialization to mapRangeM / mapFinRangeM
section
variable {circuitNat : ℕ → Circuit F β} [lawfulNat : ConstantLawfulCircuits circuitNat]
variable {circuitFin : Fin m → Circuit F β} [lawfulFin : ConstantLawfulCircuits circuitFin]

theorem mapFinRangeM_generic {n : ℕ} :
  generic from_subcircuit env (Vector.mapFinRangeM m circuitFin |>.operations n) ↔
    ∀ i : Fin m, generic from_subcircuit env (circuitFin i |>.operations (n + i*lawfulFin.local_length)) := by
  rw [Vector.mapFinRangeM, mapM_vector_generic]
  constructor
  case mpr =>
    intro h i
    intro _ i' hi'
    -- TODO can we simplify this?
    have hi : i' = i.val := by
      rw [Vector.mem_zipIdx_iff_getElem?, Vector.finRange] at hi'
      simp only [Vector.getElem?_mk, List.getElem?_toArray, List.finRange_eq_pmap_range] at hi'
      simp only [List.getElem?_pmap, Option.pmap_eq_some_iff, exists_and_left] at hi'
      obtain ⟨ ival, hival, ival_lt, ival_eq ⟩ := hi'
      rw [ival_eq]
      rw [List.getElem?_range, Option.some_inj] at hival
      exact hival
      rw [List.getElem?_eq_some_iff] at hival
      obtain ⟨ hlt, _ ⟩ := hival
      simpa using hlt
    subst hi
    exact h i

  intro h i
  specialize h i
  have : i ∈ Vector.finRange m := by simp [Vector.finRange]
  specialize h this i
  have : (i, ↑i) ∈ (Vector.finRange m).zipIdx := by
    simp only [Vector.mem_zipIdx_iff_getElem?, Fin.is_lt, Vector.getElem?_eq_getElem, Option.some.injEq]
    simp [Vector.finRange]
  specialize h this
  exact h

theorem mapFinRangeM_soundness {n : ℕ} :
  soundness env (Vector.mapFinRangeM m circuitFin |>.operations n) ↔
    ∀ i : Fin m, soundness env (circuitFin i |>.operations (n + i*lawfulFin.local_length)) := by
  simp only [soundness_iff_generic, mapFinRangeM_generic]

theorem mapFinRangeM_completeness {n : ℕ} :
  completeness env (Vector.mapFinRangeM m circuitFin |>.operations n) ↔
    ∀ i : Fin m, completeness env (circuitFin i |>.operations (n + i*lawfulFin.local_length)) := by
  simp only [completeness_iff_generic, mapFinRangeM_generic]
end
end constraints_hold
end Circuit
end
