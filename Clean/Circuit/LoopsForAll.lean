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

theorem forAll_iff {xs : List α} :
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
end Circuit.ForM
