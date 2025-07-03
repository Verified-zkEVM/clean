import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition8.Addition8

namespace Tables.Addition8
open Gadgets
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure RowType (F : Type) where
  x: F
  y: F
  z: F

instance : ProvableType RowType where
  size := 3
  toElements x := #v[x.x, x.y, x.z]
  fromElements v :=
    let ⟨ .mk [x, y, z], _ ⟩ := v
    ⟨ x, y, z ⟩

def add8Inline : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.getCurrRow
  lookup ByteTable row.x
  lookup ByteTable row.y
  let z ← Gadgets.Addition8.circuit { x := row.x, y := row.y }
  assign (.curr 2) z

def add8Table : List (TableOperation RowType (F p)) := [
  .everyRow add8Inline
]

def Spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.ForAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))

def formalAdd8Table : FormalTable (F p) RowType := {
  constraints := add8Table,
  Spec := Spec_add8,
  soundness := by
    intro N trace envs _
    simp [table_norm, add8Table, Spec_add8]
    induction trace.val with
    | empty => simp [table_norm]
    | cons rest row ih =>
        -- get rid of induction hypothesis
        simp only [table_norm]
        rintro ⟨ h_holds, h_rest ⟩
        suffices h' : row.z.val = (row.x.val + row.y.val) % 256 from ⟨ h', ih h_rest ⟩
        clear ih h_rest

        -- simplify constraints

        -- first, abstract away `env` to avoid blow-up of expression size
        let env := add8Inline.windowEnv ⟨<+> +> row, rfl⟩ (envs 0 rest.len)
        change Circuit.ConstraintsHold.Soundness env _ at h_holds

        -- this is the slowest step, but still ok
        simp [table_norm, circuit_norm, subcircuit_norm, varFromOffset, Vector.mapRange,
          add8Inline, Gadgets.Addition8.circuit, ByteTable
        ] at h_holds

        change _ ∧ _ ∧ (_ → _) at h_holds

        -- resolve assignment
        have h_x_env : env.get 0 = row.x := by rfl
        have h_y_env : env.get 1 = row.y := by rfl
        have h_z_env : env.get 3 = row.z := by rfl
        simp only [h_x_env, h_y_env, h_z_env] at h_holds

        -- now we prove a local property about the current row, from the constraints
        obtain ⟨ lookup_x, lookup_y, h_add⟩ := h_holds
        exact h_add lookup_x lookup_y
}

end Tables.Addition8
