import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition8.Addition8

namespace Tables.Addition8
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure RowType (F : Type) where
  x: F
  y: F
  z: F

instance : NonEmptyProvableType RowType where
  size := 3
  to_elements x := #v[x.x, x.y, x.z]
  from_elements v :=
    let ⟨ .mk [x, y, z], _ ⟩ := v
    ⟨ x, y, z ⟩

def add8_inline : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  lookup (ByteLookup row.x)
  lookup (ByteLookup row.y)
  let z ← subcircuit Gadgets.Addition8.circuit { x := row.x, y := row.y }
  assign (.curr 2) z

def add8_table : List (TableOperation RowType (F p)) := [
  TableOperation.EveryRow add8_inline
]

def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))

lemma induction_step (env : ℕ → ℕ → Environment (F p)) (rest : Trace (F p) RowType) (row : Row (F p) RowType)
  (ih : table_constraints_hold.foldl [(TableOperation.EveryRow add8_inline, env 0)] rest
    [(TableOperation.EveryRow add8_inline, env 0)] →
  TraceOfLength.forAllRowsOfTrace.inner rest fun row ↦ ZMod.val row.z = (ZMod.val row.x + ZMod.val row.y) % 256)
  : table_constraints_hold.foldl [(TableOperation.EveryRow add8_inline, env 0)] (rest +> row)
    [(TableOperation.EveryRow add8_inline, env 0)] →
    TraceOfLength.forAllRowsOfTrace.inner (rest +> row) fun row ↦ ZMod.val row.z = (ZMod.val row.x + ZMod.val row.y) % 256
  := by

  simp only [table_constraints_hold.foldl.eq_3, TableConstraint.constraints_hold_on_window,
    table_constraints_hold.foldl.eq_5]
  -- show _ ∧ _ → _
  rintro ⟨ h_holds, h_rest ⟩
  specialize ih h_rest
  suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih ⟩
  clear ih h_rest

  -- first, generalize `env` to keep expression size controlled
  let env' := TableConstraint.window_env add8_inline ⟨<+> +> row, rfl⟩ (env 0 rest.len)
  change Circuit.constraints_hold.soundness env' _ at h_holds
  simp [table_norm, circuit_norm, add8_inline, Gadgets.Addition8.circuit, ByteLookup] at h_holds
  simp only [subcircuit_norm, circuit_norm] at h_holds
  change _ ∧ (_ + _ = 0) at h_holds

  -- now we prove a local property about the current row

  -- resolve assignment/env
  have h_x_env : env'.get 0 = row.x := by rfl
  have h_y_env : env'.get 1 = row.y := by rfl
  have h_z_env : env'.get 5 = row.z := by rfl
  simp only [h_x_env, h_y_env, h_z_env] at h_holds

  obtain ⟨⟨⟨ lookup_x, lookup_y ⟩, h_curr⟩, h_assign ⟩ := h_holds

  have h_z'_env : env'.get 3 = row.z := calc
    _ = env'.get 3 - 0 := by ring
    _ = env'.get 3 - (env'.get 3 + -row.z) := by rw [h_assign]
    _ = row.z := by ring
  simp only [h_z'_env] at h_curr
  clear h_z'_env h_z_env h_assign

  replace lookup_x := ByteTable.soundness row.x lookup_x
  replace lookup_y := ByteTable.soundness row.y lookup_y
  rw [Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
  specialize h_curr ⟨ lookup_x, lookup_y ⟩
  exact h_curr

lemma soundness : ∀ (N : ℕ) (trace : TraceOfLength (F p) RowType N) (envs : ℕ → ℕ → Environment (F p)),
  (fun _ ↦ True) N → table_constraints_hold add8_table trace envs → spec_add8 trace := by
    intro N trace envs _
    simp only [TraceOfLength.forAllRowsOfTrace, table_constraints_hold, add8_table, spec_add8]
    simp [List.mapIdx, List.mapIdx.go]
    set t := trace.val
    induction t with
    | empty => simp [table_norm]
    | cons rest row ih =>
        -- get rid of induction hypothesis
        simp only [table_norm]
        rintro ⟨ h_holds, h_rest ⟩
        suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih h_rest ⟩
        clear ih h_rest

        -- simplify constraints

        -- first, abstract away `env` to avoid blow-up of expression size
        let env := add8_inline.window_env ⟨<+> +> row, rfl⟩ (envs 0 rest.len)
        change Circuit.constraints_hold.soundness env _ at h_holds

        -- this is the slowest step, but still ok
        simp [table_norm, circuit_norm, subcircuit_norm,  add8_inline, Gadgets.Addition8.circuit, ByteLookup] at h_holds
        change _ ∧ (_ + _ = 0) at h_holds

        -- resolve assignment
        have h_x_env : env.get 0 = row.x := by rfl
        have h_y_env : env.get 1 = row.y := by rfl
        have h_z_env : env.get 5 = row.z := by rfl
        simp only [h_x_env, h_y_env, h_z_env] at h_holds

        -- now we prove a local property about the current row, from the constraints
        obtain ⟨⟨⟨ lookup_x, lookup_y ⟩, h_add⟩, h_assign ⟩ := h_holds

        have h_z'_env : env.get 3 = row.z := calc
          _ = env.get 3 - 0 := by ring
          _ = env.get 3 - (env.get 3 + -row.z) := by rw [h_assign]
          _ = row.z := by ring
        simp only [h_z'_env] at h_add
        clear h_z'_env h_z_env h_assign

        replace lookup_x := ByteTable.soundness row.x lookup_x
        replace lookup_y := ByteTable.soundness row.y lookup_y
        rw [Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_add
        exact h_add ⟨ lookup_x, lookup_y ⟩

def formal_add8_table : FormalTable (F p) RowType := {
  constraints := add8_table,
  spec := spec_add8,
  soundness := soundness
}

end Tables.Addition8
