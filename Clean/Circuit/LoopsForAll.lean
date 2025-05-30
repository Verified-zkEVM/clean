/-
minimal version of Loops that only contains the forM case
-/
import Clean.Circuit.Lawful
import Clean.Circuit.SimpLemmas
import Clean.Utils.Misc
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    xs.forM body = forM xs.toList body := by
  rw [Vector.forM_eq_forM, Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

namespace Circuit
namespace ForM
variable {circuit : α → Circuit F Unit} (xs : Vector α m) (lawful : ConstantCircuits circuit) (n : ℕ)

theorem local_length_eq : (xs.forM circuit).local_length n = lawful.local_length * m := by
  set k := lawful.local_length
  induction xs using Vector.induct generalizing n
  case nil => rfl
  case cons x xs ih =>
    rw [Vector.forM_toList, Vector.cons, List.forM_cons, ←Vector.forM_toList,
      bind_local_length, ih, lawful.local_length_eq]
    ring

theorem output_eq : (xs.forM circuit).output n = () := rfl

variable {env : Environment F} {prop : Operations.Condition F}

theorem forAll_iff_list {xs : List α} :
  (forM xs circuit).forAll prop n ↔
    xs.zipIdx.Forall fun (x, i) => (circuit x).forAll prop (n + i*lawful.local_length) := by
  set k := lawful.local_length

  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forM_cons, List.zipIdx_cons, List.forall_cons]
    simp only at ih ⊢
    rw [zero_mul, add_zero, zero_add]
    specialize ih (n := n + k)

    have h_zip : xs.zipIdx.Forall (fun (x, i) => (circuit x).forAll prop (n + k + i * k))
      ↔ (xs.zipIdx 1).Forall (fun (x, i) => (circuit x).forAll prop (n + i * k)) := by
      rw [List.zipIdx_succ, List.forall_map_iff]
      conv =>
        rhs
        change xs.zipIdx.Forall fun (x, i) => (circuit x).forAll prop (n + (i + 1) * k)
        lhs
        intro t
        simp only
        rw [add_mul, one_mul, add_comm _ k, ←add_assoc]
    rw [←h_zip, ←ih]
    clear h_zip ih
    rw [bind_forAll, lawful.local_length_eq]

theorem forAll_iff :
  (xs.forM circuit).forAll prop n ↔
    ∀ (i : Fin m), (circuit xs[i.val]).forAll prop (n + i*lawful.local_length) := by
  rw [Vector.forM_toList, forAll_iff_list, List.forall_iff_forall_mem, Prod.forall]
  simp only
  have h_elem_iff {t} :(t ∈ xs.toList.zipIdx ↔ t ∈ xs.zipIdx) := by
    rw [←Array.toList_zipIdx, ←Vector.mem_toList_iff]
    trivial
  constructor
  · intro h i
    apply h xs[i]
    simp [h_elem_iff, Vector.mem_zipIdx_iff_getElem?]
  · intro h x i hxi
    simp only [h_elem_iff, Vector.mem_zipIdx_iff_getElem?, Vector.getElem?_eq_some_iff] at hxi
    have ⟨ i_lt, x_eq ⟩ := hxi
    exact x_eq ▸ h ⟨ i, i_lt ⟩
end ForM

def forEach {m : ℕ} (xs : Vector α m) [Inhabited α] (body : α → Circuit F Unit)
    (_lawful : ConstantCircuits body := by infer_constant_circuits) : Circuit F Unit :=
  xs.forM body

section forEach
variable {env : Environment F} {m n : ℕ} [Inhabited α] {xs : Vector α m}
  {body : α → Circuit F Unit} {lawful : ConstantCircuits body} {prop : Operations.Condition F}

@[circuit_norm ↓]
lemma forEach.soundness :
  constraints_hold.soundness env ((forEach xs body lawful).operations n) ↔
    ∀ i : Fin m, constraints_hold.soundness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [forEach, constraints_hold.soundness_iff_forAll']
  rw [ForM.forAll_iff, ConstantCircuits.local_length_eq]

/-- variant of `forEach.soundness`, for when the constraints don't depend on the input offset -/
lemma forEach.soundness' :
  constraints_hold.soundness env (forEach xs body lawful |>.operations n) →
    ∀ x ∈ xs, ∃ k : ℕ, constraints_hold.soundness env (body x |>.operations k) := by
  simp only [forEach, constraints_hold.soundness_iff_forAll', ForM.forAll_iff]
  intro h x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact ⟨ _ , h ⟨i, hi⟩ ⟩

@[circuit_norm ↓]
lemma forEach.completeness :
  constraints_hold.completeness env ((forEach xs body lawful).operations n) ↔
    ∀ i : Fin m, constraints_hold.completeness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [forEach, constraints_hold.completeness_iff_forAll']
  rw [ForM.forAll_iff, ConstantCircuits.local_length_eq]

@[circuit_norm ↓]
lemma forEach.uses_local_witnesses :
  env.uses_local_witnesses_completeness n ((forEach xs body lawful).operations n) ↔
    ∀ i : Fin m, env.uses_local_witnesses_completeness (n + i*(body default).local_length) (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [forEach, env.uses_local_witnesses_completeness_iff_forAll, ←forAll_def]
  rw [ForM.forAll_iff, ConstantCircuits.local_length_eq]

@[circuit_norm ↓]
lemma forEach.forAll :
  Operations.forAll n prop ((forEach xs body lawful).operations n) ↔
    ∀ i : Fin m, (body xs[i.val]
      |>.operations (n + i*(body default).local_length)
      |>.forAll (n + i*(body default).local_length)) prop := by
  simp only [forEach, ←forAll_def]
  rw [ForM.forAll_iff, ConstantCircuits.local_length_eq]

@[circuit_norm ↓]
lemma forEach.local_length_eq :
    (forEach xs body lawful).local_length n = m * (body default).local_length := by
  rw [forEach, ForM.local_length_eq, mul_comm, lawful.local_length_eq]

@[circuit_norm ↓]
lemma forEach.local_length_eq' :
    ((forEach xs body lawful).operations n).local_length = m * (body default).local_length := by
  rw [←local_length_eq]; rfl

@[circuit_norm]
lemma forEach.final_offset_eq :
    (forEach xs body lawful).final_offset n = n + m * (body default).local_length := by
  rw [offset_consistent, local_length_eq]

@[circuit_norm ↓]
lemma forEach.output_eq :
  (forEach xs body lawful).output n = () := rfl

-- def opaqueOperations (circuit : Circuit F α) (n : ℕ) : Operations F :=
--   circuit.operations n

-- @[circuit_norm ↓]
-- lemma forEach.apply_eq :
--   forEach xs body lawful n = (((), (forEach xs body lawful).opaqueOperations n), n + m *(body default).local_length) := by
--   apply Prod.ext
--   · rfl
--   apply final_offset_eq

end forEach
