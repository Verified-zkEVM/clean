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

-- def byte_lookup_circuit : FormalAssertion (F p) Provable.field where
--   main x := lookup (ByteLookup x)
--   assumptions _ := True
--   spec x := x.val < 256
--   soundness := by
--     intro _ env x_var x hx _ h_holds
--     dsimp [circuit_norm] at h_holds
--     exact hx ▸ ByteTable.soundness (eval env x_var) h_holds
--   completeness := by
--     intro _ env x_var _ x hx _ spec
--     dsimp [circuit_norm]
--     exact ByteTable.completeness (eval env x_var) (hx ▸ spec)

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

lemma add8_inline_offset : (add8_inline (p:=p) .empty).snd.assignment.offset = 6 := by
  dsimp only [add8_inline]
  -- simp only [table_assignment_norm]
  -- rw [from_circuit_circuit, from_circuit_circuit]
  -- simp [table_assignment_norm]
  sorry

-- lemma constraints_hold (env : Environment (F p))
--     (h_holds:  ((ByteTable.contains ⟨[env.get 0], rfl⟩ ∧ ByteTable.contains ⟨[env.get 1], rfl⟩) ∧
--     (Gadgets.Addition8.circuit.assumptions { x := env.get 0, y := env.get 1 } →
--       Gadgets.Addition8.circuit.spec { x := env.get 0, y := env.get 1 } (env.get 3))) ∧
--   env.get 3 + -env.get 5 = 0) :
--     Circuit.constraints_hold.soundness env add8_inline.operations := by
--   -- sorry
--   simp [table_norm, circuit_norm, add8_inline]
--   repeat rw [from_circuit_circuit]
--   simp
--   simp [Circuit.formal_circuit_to_subcircuit, circuit_norm]


-- induction step
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
  let env' := TableConstraint.window_env add8_inline ⟨<+> +> row, rfl⟩ (env 0 rest.len)
  change Circuit.constraints_hold.soundness env' _ at h_holds
  simp [table_norm, circuit_norm, add8_inline] at h_holds
  repeat rw [from_circuit_circuit] at h_holds

  simp at h_holds

  simp [Circuit.formal_circuit_to_subcircuit, circuit_norm] at h_holds

  -- TODO moving sorry further down crashes the lean compiler
  -- is it that proof terms become too big?
  sorry

  -- change _ ∧ (_ + _ = 0) at h_holds

  -- now we prove a local property about the current row
  -- TODO: simp should suffice, but couldn't get it to work
  have h_offset : (add8_inline (p:=p) .empty).snd.assignment.offset = 6 := by
    -- TODO simplifying this proof seems important
    -- simp? [add8_inline, table_assignment_norm, circuit_norm]
    simp only [add8_inline, bind, StateT.bind, get_curr_row, TableConstraint.get_row, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, from_vars, from_elements, Vector.map, size,
      Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, TableContext.offset, Nat.cast_zero,
      Fin.isValue, Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one,
      Fin.val_one, zero_add, List.singleton_append, Nat.cast_ofNat, Fin.val_two,
      List.cons_append, List.map_cons, List.map_nil, Expression.eval, CellAssignment.push_row,
      CellAssignment.push_var_input, CellAssignment.empty, Id.pure_eq, assign,
      TableConstraint.assign_var, modify, monadLift, assert_zero, witness_var, subcircuit,
      Circuit.lookup.eq_1, modify.eq_1, TableContext.empty, Vector.init.eq_2, Fin.val_natCast,
      Vector.init.eq_1, Nat.reduceMod, Nat.add_zero, Vector.push.eq_1, Vector.map.eq_1,
      Expression.eval.eq_1, CellAssignment.push_row.eq_1, CellAssignment.push_var_input.eq_1,
      id_eq, monadLift_self, StateT.modifyGet.eq_1, Provable.instProvableTypeField.eq_1,
      Vector.get.eq_1, Fin.cast_zero, List.get_eq_getElem, from_circuit_circuit,
      SubCircuit.witness_length, FlatOperation.witness_length, subcircuit.eq_1,
      CellAssignment.set_var_input, Circuit.witness_var.eq_1, Circuit.assert_zero.eq_1,
      Vector.set?, from_circuit_offset]

  -- resolve assignment
  have h_x : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 0, by simp [h_offset]⟩) = .input (.curr 0) := by sorry
  have h_y : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 1, by simp [h_offset]⟩) = .input (.curr 1) := by sorry
  have h_z : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 5, by simp [h_offset]⟩) = .input (.curr 2) := by sorry
  -- resolve env
  have h_x_env : env'.get 0 = row.x := by
    simp only [env', TableConstraint.window_env, h_offset, h_x]
    simp only [Nat.reduceLT, reduceDIte]
    simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
  have h_y_env : env'.get 1 = row.y := by
    simp only [env', TableConstraint.window_env, h_offset, h_y]
    simp only [Nat.reduceLT, reduceDIte]
    simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
  have h_z_env : env'.get 5 = row.z := by
    simp only [env', TableConstraint.window_env, h_offset, h_z]
    simp only [Nat.reduceLT, reduceDIte]
    simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
  clear h_x h_y h_z

  simp only [h_x_env, h_y_env, h_z_env] at h_holds
  have lookup_x := h_holds.left.left.left
  have lookup_y := h_holds.left.left.right
  have h_curr := h_holds.left.right
  have h_assign := h_holds.right
  clear h_holds
  have h_z'_env : env'.get 3 = row.z := calc
    _ = env'.get 3 - 0 := by ring
    _ = env'.get 3 - (env'.get 3 + -row.z) := by rw [h_assign]
    _ = row.z := by ring
  simp only [h_z'_env] at h_curr
  clear h_z'_env h_z_env h_assign

  replace lookup_x := ByteTable.soundness row.x lookup_x
  replace lookup_y := ByteTable.soundness row.y lookup_y
  dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
  specialize h_curr ⟨ lookup_x, lookup_y ⟩
    -- TODO commenting this in crashes the lean compiler
    -- exact h_curr

lemma soundness : ∀ (N : ℕ) (trace : TraceOfLength (F p) RowType N) (env : ℕ → ℕ → Environment (F p)),
  (fun _ ↦ True) N → table_constraints_hold add8_table trace env → spec_add8 trace := by
    intro N trace env _
    simp only [TraceOfLength.forAllRowsOfTrace, table_constraints_hold, add8_table, spec_add8]
    simp [List.mapIdx, List.mapIdx.go]
    set t := trace.val

    induction t with
    | empty => simp [table_norm]
    | cons rest row ih =>
      -- exact induction_step env rest row ih
      simp only [table_constraints_hold.foldl.eq_3, TableConstraint.constraints_hold_on_window,
        TableConstraint.final_offset, TableContext.empty, TableConstraint.operations,
        table_constraints_hold.foldl.eq_5, TraceOfLength.forAllRowsOfTrace.inner]
      show _ ∧ _ → _
      rintro ⟨ h_holds, h_rest ⟩
      specialize ih h_rest
      suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih ⟩
      clear ih h_rest
      let env' := TableConstraint.window_env add8_inline ⟨<+> +> row, rfl⟩ (env 0 rest.len)
      change Circuit.constraints_hold.soundness env' _ at h_holds
      simp [table_norm, circuit_norm, add8_inline,
        --  Circuit.formal_circuit_to_subcircuit,
      ] at h_holds
      repeat rw [from_circuit_circuit] at h_holds

      simp at h_holds

      simp [Circuit.formal_circuit_to_subcircuit, circuit_norm] at h_holds
      change _ ∧ (_ + _ = 0) at h_holds

      -- now we prove a local property about the current row
      -- TODO: simp should suffice, but couldn't get it to work
      have h_offset : (add8_inline (p:=p) .empty).snd.assignment.offset = 6 := by
        -- TODO simplifying this proof seems important
        -- simp? [add8_inline, table_assignment_norm, circuit_norm]
        simp only [add8_inline, bind, StateT.bind, get_curr_row, TableConstraint.get_row, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, from_vars, from_elements, Vector.map, size,
          Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, TableContext.offset, Nat.cast_zero,
          Fin.isValue, Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one,
          Fin.val_one, zero_add, List.singleton_append, Nat.cast_ofNat, Fin.val_two,
          List.cons_append, List.map_cons, List.map_nil, Expression.eval, CellAssignment.push_row,
          CellAssignment.push_var_input, CellAssignment.empty, Id.pure_eq, assign,
          TableConstraint.assign_var, modify, monadLift, assert_zero, witness_var, subcircuit,
          Circuit.lookup.eq_1, modify.eq_1, TableContext.empty, Vector.init.eq_2, Fin.val_natCast,
          Vector.init.eq_1, Nat.reduceMod, Nat.add_zero, Vector.push.eq_1, Vector.map.eq_1,
          Expression.eval.eq_1, CellAssignment.push_row.eq_1, CellAssignment.push_var_input.eq_1,
          id_eq, monadLift_self, StateT.modifyGet.eq_1, Provable.instProvableTypeField.eq_1,
          Vector.get.eq_1, Fin.cast_zero, List.get_eq_getElem, from_circuit_circuit,
          SubCircuit.witness_length, FlatOperation.witness_length, subcircuit.eq_1,
          CellAssignment.set_var_input, Circuit.witness_var.eq_1, Circuit.assert_zero.eq_1,
          Vector.set?, from_circuit_offset]

      -- resolve assignment
      have h_x : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 0, by simp [h_offset]⟩) = .input (.curr 0) := by sorry
      have h_y : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 1, by simp [h_offset]⟩) = .input (.curr 1) := by sorry
      have h_z : ((add8_inline (p:=p) .empty).snd.assignment.vars.get ⟨ 5, by simp [h_offset]⟩) = .input (.curr 2) := by sorry
      -- resolve env
      have h_x_env : env'.get 0 = row.x := by
        simp only [env', TableConstraint.window_env, h_offset, h_x]
        simp only [Nat.reduceLT, reduceDIte]
        simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
      have h_y_env : env'.get 1 = row.y := by
        simp only [env', TableConstraint.window_env, h_offset, h_y]
        simp only [Nat.reduceLT, reduceDIte]
        simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
      have h_z_env : env'.get 5 = row.z := by
        simp only [env', TableConstraint.window_env, h_offset, h_z]
        simp only [Nat.reduceLT, reduceDIte]
        simp [TraceOfLength.get, Trace.getLeFromBottom, Row.get, to_elements, CellOffset.curr]
      clear h_x h_y h_z

      simp only [h_x_env, h_y_env, h_z_env] at h_holds
      have lookup_x := h_holds.left.left.left
      have lookup_y := h_holds.left.left.right
      have h_curr := h_holds.left.right
      have h_assign := h_holds.right
      clear h_holds
      have h_z'_env : env'.get 3 = row.z := calc
        _ = env'.get 3 - 0 := by ring
        _ = env'.get 3 - (env'.get 3 + -row.z) := by rw [h_assign]
        _ = row.z := by ring
      simp only [h_z'_env] at h_curr
      clear h_z'_env h_z_env h_assign

      replace lookup_x := ByteTable.soundness row.x lookup_x
      replace lookup_y := ByteTable.soundness row.y lookup_y
      dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
      specialize h_curr ⟨ lookup_x, lookup_y ⟩
      -- TODO commenting this in crashes the lean compiler
      -- exact h_curr

def formal_add8_table : FormalTable (F p) RowType := {
  constraints := add8_table,
  spec := spec_add8,
  soundness := soundness
}

end Tables.Addition8
