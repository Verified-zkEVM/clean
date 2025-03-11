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

def add8_inline : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  let z ← TableConstraint.subcircuit Gadgets.Addition8.circuit {
    x := row.x,
    y := row.y
  }

  if let var z := z then
    TableConstraint.assign z (.curr 2)

def add8Table : List (TableOperation RowType (F p)) := [
  TableOperation.EveryRow add8_inline
]

def assumptions_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTrace (fun row => row.x.val < 256 ∧ row.y.val < 256)


def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))


def formal_add8_table : FormalTable (F p) RowType := {
  constraints := add8Table,
  assumptions := assumptions_add8,
  spec := spec_add8,
  soundness := by
    intro N trace
    simp only [assumptions_add8]
    simp only [TraceOfLength.forAllRowsOfTrace, table_constraints_hold, add8Table, spec_add8]

    induction trace.val with
    | empty => {
      simp [table_norm]
    }
    | cons rest row ih => {
      -- simplify induction
      simp [circuit_norm, table_norm]
      intros lookup_x lookup_y lookup_rest h_curr h_rest
      specialize ih lookup_rest h_rest
      simp [ih]

      -- now we prove a local property about the current row
      -- TODO: simp should suffice, but couldn't get it to work

      have h_x : ((add8_inline (p:=p) .empty).1.1.assignment 0) = CellOffset.curr 0
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_y : ((add8_inline (p:=p) .empty).1.1.2 1) = CellOffset.curr 1
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_z : ((add8_inline (p:=p) .empty).1.1.2 2) = CellOffset.curr 2
        := by
        simp [add8_inline, bind, table_norm]
        rfl
      have h_z' : ((add8_inline (p:=p) .empty).1.1.2 3) = CellOffset.curr 2
        := by
        simp [add8_inline, bind, table_norm]
        rfl

      -- and now it is easy!
      simp only [h_x, h_y, h_z, h_z', table_norm, CellOffset.column] at h_curr
      dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h_curr
      simp [lookup_x, lookup_y] at h_curr
      assumption
    }
}

end Tables.Addition8
