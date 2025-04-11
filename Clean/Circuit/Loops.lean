import Clean.Circuit.Lawful
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

-- we prove a few properties about the circuit `forM xs circuit`, where `circuit : α → Circuit F Unit`
-- TODO handle more general loops

instance LawfulCircuit.from_forM {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] (xs : List α) :
    LawfulCircuit (forM xs circuit) := by
  induction xs
  case nil => rw [List.forM_nil]; infer_instance
  case cons x xs ih => rw [List.forM_cons]; exact from_bind inferInstance inferInstance

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    forM xs body = forM xs.toList body := by
  rw [Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

instance LawfulCircuit.from_forM_vector {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] {n : ℕ} (xs : Vector α n) :
    LawfulCircuit (forM xs circuit) := by
  rw [Vector.forM_toList]
  apply from_forM

theorem Circuit.forM_local_length {circuit : α → Circuit F Unit} [lawful : ConstantLawfulCircuits circuit]
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

namespace Circuit.constraints_hold
-- characterize `constraints_hold` for variants of `forM`

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
end Circuit.constraints_hold
