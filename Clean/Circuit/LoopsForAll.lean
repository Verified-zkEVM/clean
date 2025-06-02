/-
minimal version of Loops that only contains the forM case
-/
import Clean.Circuit.Lawful
import Clean.Utils.Misc
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    xs.forM body = forM xs.toList body := by
  rw [Vector.forM_eq_forM, Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

namespace Circuit

lemma forAll_flatten (xs : Vector α m) {circuit : α → Circuit F β} (lawful : ConstantCircuits circuit)
  {prop : Operations.Condition F} :
  Operations.forAll n prop (List.ofFn fun (i : Fin m) => (circuit xs[i.val]).operations (n + i * lawful.local_length)).flatten
    ↔ ∀ (i : Fin m), (circuit xs[i.val]).forAll prop (n + i * lawful.local_length) := by
  induction m generalizing n
  case zero => simp [Operations.forAll]
  case succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, Operations.forAll_append, Fin.forall_fin_succ, Circuit.forAll_def]
    simp only [Fin.val_zero, zero_mul, add_zero, Fin.val_succ]
    specialize ih (n := n + lawful.local_length) (xs := xs.drop 1)
    simp only [Vector.drop_eq_cast_extract, Nat.add_one_sub_one, Vector.getElem_cast,
      Vector.getElem_extract] at ih
    have : ((circuit xs[0]).operations n).local_length + n = n + lawful.local_length := by
      rw [←lawful.local_length_eq (xs[0]) n]; ac_rfl
    rw [this]
    ring_nf at ih ⊢
    rw [ih]

namespace ForM
variable {circuit : α → Circuit F Unit} (xs : Vector α m) (lawful : ConstantCircuits circuit) (n : ℕ)

theorem local_length_eq : (xs.forM circuit).local_length n = m * lawful.local_length := by
  set k := lawful.local_length
  induction xs using Vector.induct generalizing n
  case nil => ac_rfl
  case cons x xs ih =>
    rw [Vector.forM_toList, Vector.cons, List.forM_cons, ←Vector.forM_toList,
      bind_local_length_eq, ih, lawful.local_length_eq]
    ring

theorem output_eq : (xs.forM circuit).output n = () := rfl

theorem operations_eq :
  (xs.forM circuit).operations n =
    (List.ofFn fun (i : Fin m) => (circuit xs[i.val]).operations (n + i * lawful.local_length)).flatten := by
  induction xs using Vector.induct generalizing n
  case nil => rfl
  case cons x xs ih =>
    rw [Vector.forM_toList, Vector.cons, List.forM_cons, ←Vector.forM_toList,
      bind_operations_eq, ih, lawful.local_length_eq, List.ofFn_succ, List.flatten_cons]
    simp only [Vector.getElem_mk, List.getElem_toArray, Fin.val_zero, Fin.val_succ,
      List.getElem_zero, List.getElem_cons_succ, List.head_cons, Array.getElem_toList, Vector.getElem_toArray]
    ring_nf

variable {env : Environment F} {prop : Operations.Condition F}

theorem forAll_iff :
  (xs.forM circuit).forAll prop n ↔
    ∀ (i : Fin m), (circuit xs[i.val]).forAll prop (n + i*lawful.local_length) := by
  rw [forAll_def, operations_eq, forAll_flatten]
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
    ∀ i : Fin m, (body xs[i.val] |>.forAll prop (n + i*(body default).local_length)) := by
  simp only [forEach, ←forAll_def]
  rw [ForM.forAll_iff, ConstantCircuits.local_length_eq]

@[circuit_norm ↓]
lemma forEach.local_length_eq :
    (forEach xs body lawful).local_length n = m * (body default).local_length := by
  rw [forEach, ForM.local_length_eq, lawful.local_length_eq]

@[circuit_norm ↓]
lemma forEach.output_eq :
  (forEach xs body lawful).output n = () := rfl

end forEach
