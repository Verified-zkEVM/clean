/-
This file proves some properties about `forM`, `mapM`, and `foldlM` monad loops when used in a `Circuit`,
typically leveraging a `ConstantLawfulCircuits` assumption on the loop body.

The end result are loop methods `Circuit.{mapFinRange, map, forEach, foldl}` that simplify
under `circuit_norm` in every way we need them to.
-/
import Clean.Circuit.Lawful
import Clean.Utils.Misc
variable {n m : ℕ} {F : Type} [Field F] {α β : Type}

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
  (lawful : ∀ x z, LawfulCircuit (circuit z x)) (xs : List α) (init : β) :
    LawfulCircuit (xs.foldlM circuit init) := by
  induction xs generalizing init
  case nil => rw [List.foldlM_nil]; infer_instance
  case cons x xs ih => rw [List.foldlM_cons]; exact from_bind inferInstance inferInstance

lemma Vector.forM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : α → m Unit) :
    xs.forM body = forM xs.toList body := by
  rw [Vector.forM_eq_forM, Vector.forM_mk, List.forM_toArray, List.forM_eq_forM]

lemma Vector.mapM_toList (xs : Vector α n) {m : Type → Type} [monad: Monad m] [LawfulMonad m] (body : α → m β) :
    (fun v => v.toArray.toList) <$> (xs.mapM body) = xs.toList.mapM body := by
  rw [←Array.toList_mapM, ←Vector.toArray_mapM, Functor.map_map]

lemma Vector.foldlM_toList (xs : Vector α n) {m : Type → Type} [Monad m] (body : β → α → m β) (init : β) :
    xs.foldlM body init = xs.toList.foldlM body init := by
  rw [Vector.foldlM_mk, List.foldlM_toArray]

instance LawfulCircuit.from_forM_vector {circuit : α → Circuit F Unit} [∀ x : α, LawfulCircuit (circuit x)] {n : ℕ} (xs : Vector α n) :
    LawfulCircuit (xs.forM circuit) := by
  rw [Vector.forM_toList]
  apply from_forM

instance LawfulCircuit.from_foldlM_vector {circuit : β → α → Circuit F β} (lawful : ∀ x z, LawfulCircuit (circuit z x)) {n : ℕ} (xs : Vector α n) (init : β) :
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
    let lawful_loop := LawfulCircuit.from_foldlM_vector (fun x z => .from_constants lawful (z, x)) xs
    cast (by rw [←LawfulCircuit.final_offset_eq, Circuit.final_offset, from_foldlM_vector.offset_independent])
      ((lawful_loop init).operations n)

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
    let k := lawful.local_length
    let lawful_loop := LawfulCircuit.from_foldlM_vector (fun x z => .from_constants lawful (z, x)) xs
    simp only [LawfulCircuit.append_only, OperationsList.mk.injEq]
    have h_offset : LawfulCircuit.final_offset (Vector.foldlM circuit init xs) ops.offset = ops.offset + lawful.local_length * m := by
      rw [←LawfulCircuit.final_offset_eq, Circuit.final_offset, from_foldlM_vector.offset_independent]
    constructor
    · exact h_offset
    congr
    simp

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
  (xs.forM circuit |>.operations m).forAll prop ↔
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
  (xs.forM circuit |>.operations m).forAll prop ↔
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
  soundness env (xs.forM circuit |>.operations m) ↔
    ∀ x ∈ xs, ∀ (i : ℕ) (_ : (x, i) ∈ xs.zipIdx), soundness env (circuit x |>.operations (m + i*lawful.local_length)) := by
  simp only [soundness_iff_forAll, forM_vector_forAll]

theorem forM_vector_completeness {xs : Vector α n} :
  completeness env (xs.forM circuit |>.operations m) ↔
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

section
variable {env : Environment F} {prop : Operations.Condition F} {m n : ℕ} [Inhabited β] [Inhabited α] {xs : Vector α n}
  {body : β → α → Circuit F β} {init : β} {lawful : ConstantLawfulCircuits fun (t : β × α) => body t.1 t.2}

def foldlAcc (m : ℕ) (xs : Vector α n) (body : β → α → Circuit F β) (init : β) (j : Fin n) : β :=
  Fin.foldl j (fun acc i => (body acc xs[i.val]).output (m + i*(body default default).local_length)) init

lemma foldlAcc_zero [NeZero n] : foldlAcc m xs body init 0 = init := by
  simp [foldlAcc, Fin.foldl_zero]

lemma foldlAcc_cons_succ (i : Fin n) (x : α) [lawful : ConstantLawfulCircuits fun (t : β × α) => body t.1 t.2] :
  foldlAcc m (Vector.cons x xs) body init i.succ =
    foldlAcc ((body init x).final_offset m) xs body ((body init x).output m) i := by
  let lawful_body : LawfulCircuit (body init x) := .from_constants lawful (init, x)
  rw [lawful.final_offset_eq (init,x), ←lawful.local_length_eq (default, default) 0]
  simp only [foldlAcc]
  simp only [Fin.val_succ, Vector.cons, Vector.getElem_mk, List.getElem_toArray, Fin.foldl_succ,
    List.getElem_cons_succ, Array.getElem_toList, Vector.getElem_toArray, add_mul, one_mul,
    Fin.val_zero, List.getElem_cons_zero, zero_mul, add_zero]
  ac_rfl

theorem constraints_hold.foldM_vector_forAll {xs : Vector α n} {lawful : ConstantLawfulCircuits fun (t : β × α) => body t.1 t.2} :
  (xs.foldlM body init |>.operations m).forAll prop ↔
    ∀ i : Fin n, (body (foldlAcc m xs body init i) xs[i.val] |>.operations (m + i*(body default default).local_length)).forAll prop := by

  induction xs using Vector.induct generalizing m init with
  | nil => simp; trivial
  | cons x xs ih =>
    rename_i n
    let lawful_body (x : α) (acc : β) : LawfulCircuit (body acc x) := .from_constants lawful (acc, x)
    let lawful_list (acc : β) : LawfulCircuit (List.foldlM body acc xs.toList) := by
      apply LawfulCircuit.from_foldlM lawful_body
    rw [Vector.foldlM_toList, Vector.cons, List.foldlM_cons, bind_forAll inferInstance inferInstance]
    specialize ih (m:=(LawfulCircuit.final_offset (body init x) m)) (init:=(LawfulCircuit.output (body init x) m))
    rw [Vector.foldlM_toList] at ih
    rw [ih]
    clear ih
    rw [Fin.forall_fin_succ, foldlAcc_zero]
    simp only [Fin.val_zero, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    rw [zero_mul, add_zero]
    have h {p q r : Prop} : (q ↔ r) → (p ∧ q ↔ p ∧ r) := by tauto
    apply h; clear h
    have h {q r : Fin n → Prop} : (∀ i, (q i ↔ r i)) → ((∀ i, q i) ↔ (∀ i, r i)) := by simp_all
    apply h; clear h
    intro i
    simp only [Fin.val_succ, List.getElem_cons_succ]
    rw [Vector.getElem_toList]
    rw [add_mul, one_mul, add_comm _ (body default default).local_length, ←add_assoc m]
    have : LawfulCircuit.final_offset (body init x) m = m + lawful.local_length := by simp [lawful_body, lawful_norm]
    rw [lawful.local_length_eq (default, default), ←this]
    change _ ↔ Operations.forAll prop (body (foldlAcc m (Vector.cons x xs) body init i.succ) _ |>.operations _)
    rw [←LawfulCircuit.output_eq, ←LawfulCircuit.final_offset_eq, ←foldlAcc_cons_succ]

-- we can massively simplify the theory above when assuming the body's output is independent of the input

theorem foldlAcc_const_succ (h_const_out : lawful.constant_output) (i : ℕ) (hi : i + 1 < n) :
  foldlAcc m xs body init ⟨ i + 1, hi ⟩ =
    (body default xs[i]).output (m + i*(body default default).local_length) := by
  simp only [foldlAcc]
  rw [lawful.output_eq (_, xs[i]), h_const_out, ←lawful.output_eq]
  conv => lhs; lhs; intro acc i; rw [lawful.output_eq (acc, _), h_const_out, ←lawful.output_eq]
  simp [Fin.foldl_const]

theorem foldlAcc_const (h_const_out : lawful.constant_output) (i : ℕ) (hi : i < n) :
  foldlAcc m xs body init ⟨ i, hi ⟩ = match i with
    | 0 => init
    | i + 1 => (body default xs[i]).output (m + i*(body default default).local_length) := by
  rcases i with _ | i
  · simp [foldlAcc]
  · rw [foldlAcc_const_succ h_const_out]

theorem constraints_hold.foldM_vector_forAll_const (h_const_out : lawful.constant_output) [NeZero n] :
  (xs.foldlM body init |>.operations m).forAll prop ↔
  (body init (xs[0]'(NeZero.pos n)) |>.operations m).forAll prop ∧
  ∀ (i : ℕ) (hi : i + 1 < n),
    let acc := (body default xs[i]).output (m + i*(body default default).local_length);
    (body acc xs[i + 1] |>.operations (m + (i + 1)*(body default default).local_length)).forAll prop := by
  rw [constraints_hold.foldM_vector_forAll (lawful:=lawful)]
  set k := (body default default).local_length
  simp only
  constructor
  · intro h
    constructor
    · specialize h 0
      simp only [Fin.val_zero] at h
      rw [foldlAcc_zero, zero_mul, add_zero] at h
      exact h
    · intro i hi
      specialize h ⟨ i + 1, hi ⟩
      rw [foldlAcc_const_succ h_const_out] at h
      exact h
  intro h i
  rcases i with ⟨ _ | i, hi ⟩
  · simp only [Fin.mk_zero', Fin.val_zero]
    rw [foldlAcc_zero, zero_mul, add_zero]
    exact h.left
  · rw [foldlAcc_const_succ h_const_out]
    exact h.right i hi

end

-- Loop constructs designed to simplify under `circuit_norm`

def mapFinRange (m : ℕ) [NeZero m] [Nonempty β] (body : Fin m → Circuit F β)
    (_lawful : ConstantLawfulCircuits body := by infer_constant_lawful_circuits) : Circuit F (Vector β m) :=
  Vector.mapFinRangeM m body

def map {m : ℕ} [Nonempty β] (xs : Vector α m) (body : α → Circuit F β)
    (_lawful : ConstantLawfulCircuits body := by infer_constant_lawful_circuits) : Circuit F (Vector β m) :=
  xs.mapM body

def forEach {m : ℕ} (xs : Vector α m) (body : α → Circuit F Unit)
    (_lawful : ConstantLawfulCircuits body := by infer_constant_lawful_circuits) : Circuit F Unit :=
  xs.forM body

def foldl {m : ℕ} [Inhabited β] [Inhabited α] (xs : Vector α m) (init : β) (body : β → α → Circuit F β)
  (lawful : ConstantLawfulCircuits (fun (s, a) => body s a) := by infer_constant_lawful_circuits)
  (_h_const_out : lawful.constant_output := by
      simp only [lawful_norm, ConstantLawfulCircuits.constant_output]
      intros
      rfl) : Circuit F β :=
  xs.foldlM body init

section mapFinRange
variable {env : Environment F} {m n : ℕ} [NeZero m] [Nonempty β] {body : Fin m → Circuit F β} {lawful : ConstantLawfulCircuits body}

@[circuit_norm ↓]
lemma mapFinRange.soundness :
  constraints_hold.soundness env (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.soundness env (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, constraints_hold.soundness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma mapFinRange.completeness :
  constraints_hold.completeness env (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.completeness env (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, constraints_hold.completeness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma mapFinRange.uses_local_witnesses :
  env.uses_local_witnesses_completeness (mapFinRange m body lawful |>.operations n) ↔
    ∀ i : Fin m, env.uses_local_witnesses_completeness (body i |>.operations (n + i*(body 0).local_length)) := by
  simp only [mapFinRange, env.uses_local_witnesses_completeness_iff_forAll, constraints_hold.mapFinRangeM_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma mapFinRange.local_length_eq :
    (mapFinRange m body lawful).local_length n = m * (body 0).local_length := by
  let lawful_loop : ConstantLawfulCircuit (mapFinRange m body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [LawfulCircuit.local_length_eq]
  ac_rfl

@[circuit_norm ↓]
lemma mapFinRange.initial_offset_eq :
    (mapFinRange m body lawful |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuit (mapFinRange m body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.initial_offset_eq]

@[circuit_norm ↓]
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
end mapFinRange

section map
variable {env : Environment F} {m n : ℕ} [Inhabited α] [Nonempty β] {xs : Vector α m}
  {body : α → Circuit F β} {lawful : ConstantLawfulCircuits body}

@[circuit_norm ↓]
lemma map.soundness :
  constraints_hold.soundness env (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.soundness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, constraints_hold.soundness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma map.completeness :
  constraints_hold.completeness env (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, constraints_hold.completeness env (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, constraints_hold.completeness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma map.uses_local_witnesses :
  env.uses_local_witnesses_completeness (map xs body lawful |>.operations n) ↔
    ∀ i : Fin m, env.uses_local_witnesses_completeness (body xs[i.val] |>.operations (n + i*(body default).local_length)) := by
  simp only [map, env.uses_local_witnesses_completeness_iff_forAll, constraints_hold.mapM_vector_forAll]
  rw [LawfulCircuit.local_length_eq]
  trivial

@[circuit_norm ↓]
lemma map.local_length_eq :
    (map xs body lawful).local_length n = m * (body default).local_length := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [LawfulCircuit.local_length_eq]
  ac_rfl

omit [Inhabited α] in
@[circuit_norm ↓]
lemma map.initial_offset_eq :
    (map xs body lawful |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.initial_offset_eq]

@[circuit_norm ↓]
lemma map.output_eq :
  (map xs body lawful).output n =
    xs.mapIdx fun i x => (body x).output (n + i*(body default).local_length) := by
  let lawful_loop : ConstantLawfulCircuit (map xs body lawful) := .from_mapM_vector _ lawful
  rw [LawfulCircuit.output_eq]
  simp only [lawful_loop, lawful_norm]
  ext i hi
  rw [Vector.getElem_mapIdx, Vector.getElem_mapIdx, LawfulCircuit.output_eq, LawfulCircuit.local_length_eq]
  ac_rfl
end map

section foldl
variable {env : Environment F} {m n : ℕ} [Inhabited β] [Inhabited α] {xs : Vector α m}
  {body : β → α → Circuit F β} {init : β} {lawful : ConstantLawfulCircuits fun (t : β × α) => body t.1 t.2}
  {const_out : lawful.constant_output}

@[circuit_norm ↓]
lemma foldl.soundness [NeZero m] :
  constraints_hold.soundness env (foldl xs init body lawful const_out |>.operations n) ↔
    constraints_hold.soundness env (body init (xs[0]'(NeZero.pos m)) |>.operations n) ∧
    ∀ (i : ℕ) (hi : i + 1 < m),
      let acc := (body default xs[i]).output (n + i*(body default default).local_length);
      constraints_hold.soundness env (body acc xs[i + 1] |>.operations (n + (i + 1)*(body default default).local_length)) := by
  simp only [constraints_hold.soundness_iff_forAll, foldl, constraints_hold.foldM_vector_forAll_const const_out]

@[circuit_norm ↓]
lemma foldl.completeness [NeZero m] :
  constraints_hold.completeness env (foldl xs init body lawful const_out |>.operations n) ↔
    constraints_hold.completeness env (body init (xs[0]'(NeZero.pos m)) |>.operations n) ∧
    ∀ (i : ℕ) (hi : i + 1 < m),
      let acc := (body default xs[i]).output (n + i*(body default default).local_length);
      constraints_hold.completeness env (body acc xs[i + 1] |>.operations (n + (i + 1)*(body default default).local_length)) := by
  simp only [constraints_hold.completeness_iff_forAll, foldl, constraints_hold.foldM_vector_forAll_const const_out]

@[circuit_norm ↓]
lemma foldl.uses_local_witnesses [NeZero m] :
  env.uses_local_witnesses_completeness (foldl xs init body lawful const_out |>.operations n) ↔
    env.uses_local_witnesses_completeness (body init (xs[0]'(NeZero.pos m)) |>.operations n) ∧
    ∀ (i : ℕ) (hi : i + 1 < m),
      let acc := (body default xs[i]).output (n + i*(body default default).local_length);
      env.uses_local_witnesses_completeness (body acc xs[i + 1] |>.operations (n + (i + 1)*(body default default).local_length)) := by
  simp only [env.uses_local_witnesses_completeness_iff_forAll, foldl, constraints_hold.foldM_vector_forAll_const const_out]

@[circuit_norm ↓]
lemma foldl.local_length_eq :
    (foldl xs init body lawful const_out).local_length n = m * (body default default).local_length := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful const_out) := .from_foldlM_vector xs lawful
  rw [lawful_loop.local_length_eq]
  simp only [lawful_loop, lawful_norm]
  rw [←lawful.local_length_eq (default, default) 0]
  ac_rfl

@[circuit_norm ↓]
lemma foldl.initial_offset_eq :
    (foldl xs init body lawful const_out |>.operations n).initial_offset = n := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful const_out) := .from_foldlM_vector xs lawful
  apply lawful_loop.initial_offset_eq

@[circuit_norm ↓]
lemma foldl.output_eq [NeZero m] :
  (foldl xs init body lawful const_out).output n =
    (body default (xs[m-1]'(Nat.pred_lt (NeZero.ne m)))).output (n + (m - 1)*(body default default).local_length) := by
  let lawful_loop : ConstantLawfulCircuits (foldl xs · body lawful const_out) := .from_foldlM_vector xs lawful
  rw [lawful_loop.output_eq]
  simp only [lawful_loop, lawful_norm, ←lawful.output_eq]
  rw [lawful.local_length_eq (default, default) 0]
  have : m-1 < m := Nat.pred_lt (NeZero.ne m)
  rw [lawful.output_eq (_, xs[m-1]), const_out, ←lawful.output_eq]
  conv => lhs; lhs; intro acc i; rw [lawful.output_eq (acc, _), const_out, ←lawful.output_eq]
  rcases m with _ | m
  · simp at this
  simp only [Fin.foldl_const, add_tsub_cancel_right, Fin.natCast_eq_last, Fin.val_last]
  ac_rfl
end foldl

end Circuit
end
