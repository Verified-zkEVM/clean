import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition8.Addition8

namespace Tables.Addition8
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def add8_inline : SingleRowConstraint (F p) 3 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  let z : Expression (F p) <- TableConstraint.subcircuit Gadgets.Addition8.circuit {x, y}

  if let var z := z then
    TableConstraint.assign z (CellOffset.curr 2)

def add8Table : List (TableOperation (F p) 3) := [
  TableOperation.EveryRow add8_inline
]

def assumptions_add8 {N : ℕ} (trace : TraceOfLength (F p) 3 N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row 0).val < 256 ∧ (row 1).val < 256)


def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) 3 N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row 2).val = ((row 0).val + (row 1).val) % 256)

def formal_add8_table : FormalTable (F:=(F p)) := {
  M := 3,
  constraints := add8Table,
  assumptions := assumptions_add8,
  spec := spec_add8,
  soundness := by
    intro N trace
    simp [assumptions_add8]
    simp [add8Table, spec_add8]

    induction trace.val with
    | empty => {
      simp
    }
    | cons rest row ih => {
      -- simplify induction
      simp [gadget_norm, TraceOfLength.forAllRowsOfTrace.inner, TableConstraint.constraints_hold_on_window,
        TableConstraint.constraints_hold_on_window.foldl]
      intros lookup_x lookup_y lookup_rest h_curr h_rest
      specialize ih lookup_rest h_rest
      simp [ih]

      -- now we prove a local property about the current row
      -- TODO: simp should suffice, but couldn't get it to work
      have h_varx : ((add8_inline (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
        := by rfl
      have h_vary : ((add8_inline (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
        := by rfl
      have h_varz : ((add8_inline (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 2).column = 2
        := by rfl

      simp [from_values, to_vars] at h_curr
      rw [h_varx, h_vary, h_varz] at h_curr

      -- and now it is easy!
      dsimp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions] at h_curr
      simp [lookup_x, lookup_y] at h_curr
      assumption
    }
}

end Tables.Addition8
