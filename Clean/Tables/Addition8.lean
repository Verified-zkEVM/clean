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
  .everyRow 0 add8Inline  -- TODO: compute stride
]

def Spec_add8 {N : ℕ} (trace : TraceOfLength (F p) RowType N) (_env : ProverData (F p)) : Prop :=
  trace.ForAllRowsOfTrace (fun row => (row.z.val = (row.x.val + row.y.val) % 256))

def formalAdd8Table : FormalTable (F p) RowType := {
  constraints := add8Table,
  Spec := Spec_add8,
  soundness := by
    intro N trace env _
    sorry,
  completeness := by
    intro N trace env _ _
    sorry
}

end Tables.Addition8
