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

def byte_lookup_circuit : FormalAssertion (F p) Provable.field where
  main x := byte_lookup x
  assumptions _ := True
  spec x := x.val < 256
  soundness := by
    intro _ env x_var x hx _ h_holds
    dsimp [circuit_norm] at h_holds
    exact hx ▸ ByteTable.soundness (eval env x_var) h_holds
  completeness := by
    intro _ env x_var _ x hx _ spec
    dsimp [circuit_norm]
    exact ByteTable.completeness (eval env x_var) (hx ▸ spec)


def add8_inline : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  TableConstraint.assertion byte_lookup_circuit row.x
  TableConstraint.assertion byte_lookup_circuit row.y

  let z ← TableConstraint.subcircuit Gadgets.Addition8.circuit { x := row.x, y := row.y }

  if let var z := z then
    TableConstraint.assign z (.curr 2)

def add8_table : List (TableOperation RowType (F p)) := [
  TableOperation.EveryRow add8_inline
]

def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))


def formal_add8_table : FormalTable (F p) RowType := {
  constraints := add8_table,
  spec := spec_add8,
  soundness := by
    intro N trace _
    simp only [TraceOfLength.forAllRowsOfTrace, table_constraints_hold, add8_table, spec_add8]

    induction trace.val with
    | empty => {
      simp [table_norm]
    }
    | cons rest row ih => {
      -- simplify induction
      simp [circuit_norm, table_norm]
      intros lookup_x lookup_y h_curr h_rest
      specialize ih h_rest
      simp [ih]

      -- now we prove a local property about the current row
      -- TODO: simp should suffice, but couldn't get it to work

      have h_x : ((add8_inline (p:=p) .empty).snd.assignment 0) = CellOffset.curr 0
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_y : ((add8_inline (p:=p) .empty).snd.assignment 1) = CellOffset.curr 1
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_z : ((add8_inline (p:=p) .empty).snd.assignment 2) = CellOffset.curr 2
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_z' : ((add8_inline (p:=p) .empty).snd.assignment 3) = CellOffset.curr 2
        := by
        simp [add8_inline, bind, table_norm]
        rfl

      dsimp [Circuit.formal_assertion_to_subcircuit, Circuit.subassertion_soundness,
        byte_lookup_circuit, circuit_norm] at lookup_x lookup_y

      simp only [h_x, h_y, h_z, h_z', table_norm, CellOffset.column] at h_curr lookup_x lookup_y
      simp at lookup_x lookup_y

      dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
      simp [lookup_x, lookup_y] at h_curr
      assumption
    }
}

end Tables.Addition8
