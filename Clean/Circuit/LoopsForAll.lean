/-
minimal version of Loops that only contains the forM case
-/
import Clean.Circuit.Lawful
import Clean.Utils.Misc
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    xs.forM body = forM xs.toList body := by
  rw [Vector.forM_eq_forM, Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

namespace Circuit.ForM
variable {circuit : α → Circuit F Unit} (xs : Vector α m) (lawful : ConstantLawfulCircuits circuit) (n : ℕ)

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
    rw [bind_forAll_lawful inferInstance, lawful.local_length_eq]

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
end Circuit.ForM
