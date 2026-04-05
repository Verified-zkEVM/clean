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
    intro N trace env _ h
    rcases trace with ⟨trace, rfl⟩
    suffices goal : ∀ M, TableConstraintsHold.foldl env M [.everyRow 0 add8Inline] trace [.everyRow 0 add8Inline] →
        TraceOfLength.ForAllRowsOfTrace.inner trace (fun row => row.z.val = (row.x.val + row.y.val) % 256) by
      exact goal _ (by simp only [Spec_add8, add8Table, table_norm, TableConstraintsHold] at h; exact h)
    intro M; clear h
    induction trace with
    | empty => intro; trivial
    | cons rest row ih =>
      simp only [table_norm, TableConstraintsHold.foldl, TraceOfLength.ForAllRowsOfTrace.inner]
      intro ⟨h_row, h_rest⟩
      refine ⟨?_, ih h_rest⟩
      -- Per-row step: ConstraintHoldsOnRow add8Inline row env' → row.z.val = (row.x.val + row.y.val) % 256
      -- This follows from: (1) ByteTable lookup soundness gives row.x.val < 256, row.y.val < 256
      -- (2) Addition8.circuit soundness gives z.val = (row.x.val + row.y.val) % 256
      -- (3) windowEnv maps row variables to actual trace cells, including assign (.curr 2) z
      -- Requires env mapping lemmas specific to add8Inline (similar to wrappedEnv_maps_* in Inductive.lean)
      sorry,
  completeness := by
    intro N trace env _ _
    -- Not provable with HonestProverAssumption = True.
    -- The lookup completeness for ByteTable requires row.x.val < 256 and row.y.val < 256,
    -- which must come from a non-trivial HonestProverAssumption.
    sorry
}

end Tables.Addition8
