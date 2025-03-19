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
  to_elements x := vec [x.x, x.y, x.z]
  from_elements v :=
    let ⟨ [x, y, z], _ ⟩ := v
    ⟨ x, y, z ⟩

-- def byte_lookup_circuit : FormalAssertion (F p) Provable.field where
--   main x := byte_lookup x
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
  byte_lookup row.x
  byte_lookup row.y

  let z ← subcircuit Gadgets.Addition8.circuit { x := row.x, y := row.y }
  assign (.curr 2) z

def add8_table : List (TableOperation RowType (F p)) := [
  TableOperation.EveryRow add8_inline
]

def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))

def formal_add8_table : FormalTable (F p) RowType := {
  constraints := add8_table,
  spec := spec_add8,
  soundness := by
    intro N trace env _
    simp only [TraceOfLength.forAllRowsOfTrace, table_constraints_hold, add8_table, spec_add8]
    simp [List.mapIdx, List.mapIdx.go]

    induction trace.val with
    | empty => {
      simp [table_norm]
    }
    | cons rest row ih => {
      -- simplify induction
      simp only [table_norm, Vector.nil]
      show _ ∧ _ → _
      rintro ⟨ h_holds, h_rest ⟩
      specialize ih h_rest
      suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih ⟩
      clear ih h_rest
      let env' := TableConstraint.window_env add8_inline ⟨<+> +> row, rfl⟩ (env 0 rest.len)
      change Circuit.constraints_hold.soundness env' _ at h_holds
      simp [table_norm, add8_inline, byte_lookup,
         circuit_norm, Circuit.formal_circuit_to_subcircuit,
        liftM, monadLift,
        bind, StateT.bind,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ] at h_holds
      repeat rw [from_circuit_circuit] at h_holds
      simp at h_holds

      simp [circuit_norm] at h_holds

      -- have modify1 : ∀ ops f, ((modify f : Circuit (F p) PUnit) ops).1 = () := by simp
      -- conv in ((modify _ : Circuit (F p) PUnit) _).1 =>
      -- rw [modify1]

      -- simp [TableConstraint.window_env, table_norm, circuit_norm, add8_inline, byte_lookup] at env'
      change _ ∧ (_ + _ = 0) at h_holds
      -- simp [TableContext.from_circuit.from_circuit_with_consistency] at h_holds
      -- simp only [modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h_holds

      -- simp at h_holds


      -- intros lookup_x lookup_y h_curr h_rest
      -- specialize ih h_rest
      -- simp [ih]

      -- -- now we prove a local property about the current row
      -- -- TODO: simp should suffice, but couldn't get it to work

      -- have h_x : ((add8_inline (p:=p) .empty).snd.assignment 0) = CellOffset.curr 0
      --   := by
      --   simp [add8_inline, bind, table_norm]
      --   rfl
      -- have h_y : ((add8_inline (p:=p) .empty).snd.assignment 1) = CellOffset.curr 1
      --   := by
      --   simp [add8_inline, bind, table_norm]
      --   rfl
      -- have h_z : ((add8_inline (p:=p) .empty).snd.assignment 2) = CellOffset.curr 2
      --   := by
      --   simp [add8_inline, bind, table_norm]
      --   rfl
      -- have h_z' : ((add8_inline (p:=p) .empty).snd.assignment 3) = CellOffset.curr 2
      --   := by
      --   simp [add8_inline, bind, table_norm]
      --   rfl

      -- dsimp [Circuit.formal_assertion_to_subcircuit, Circuit.subassertion_soundness,
      --   byte_lookup_circuit, circuit_norm] at lookup_x lookup_y

      -- simp only [h_x, h_y, h_z, h_z', table_norm, CellOffset.column] at h_curr lookup_x lookup_y
      -- simp at lookup_x lookup_y

      -- dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
      -- simp [lookup_x, lookup_y] at h_curr
      -- assumption
      -- sorry
    }
}

end Tables.Addition8
