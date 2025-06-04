/-
"Inductive" table constraints are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

The common `k=2` case gets its own special definition.
-/
import Clean.Table.Basic
import Clean.Gadgets.Equality

/--
In the case of two-row windows, an `InductiveTable` is basically a `FormalCircuit` but
- with the same input and output types
- with an extra input to the spec: the current (input) row number
- with assumptions replaced by the spec on the previous row
- with input offset hard-coded to zero
-/
structure InductiveTable (F : Type) [Field F] (Row : Type → Type) [LawfulProvableType Row] where
  main : Var Row F → Circuit F (Var Row F)
  spec : ℕ → Row F → Prop

  soundness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- if the constraints hold
    Circuit.constraints_hold.soundness env (main input_var |>.operations) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- we can conclude the spec on the output row
    spec (row_index + 1) (eval env (main input_var |>.output))

  completeness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- when using honest-prover witnesses
    env.uses_local_witnesses_completeness 0 (main input_var |>.operations) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- the constraints hold
    Circuit.constraints_hold.completeness env (main input_var |>.operations)

  subcircuits_consistent : ∀ var, ((main var).operations).subcircuits_consistent 0
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [Field F] {Row : TypeMap} [LawfulProvableType Row]

def tableSpec (table : InductiveTable F Row) {N : ℕ} (trace : TraceOfLength F Row N) : Prop :=
  trace.forAllRowsOfTraceWithIndex fun row i => table.spec i row

def inductiveConstraint (table : InductiveTable F Row) : TableConstraint 2 Row F Unit := do
  let input ← get_curr_row
  let output ← get_next_row
  let output' ← table.main input
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  assert_equals output output'

def equalityConstraint (target : Row F) : SingleRowConstraint Row F := do
  let actual ← get_curr_row
  assert_equals actual (const target)

def tableConstraints (table : InductiveTable F Row) (input output: Row F) :
  List (TableOperation Row F) := [
    .EveryRowExceptLast table.inductiveConstraint,
    .Boundary 0 (equalityConstraint input),
    -- TODO enable "last row" equality constraint without knowing the length `N` up front
    -- .Boundary (N - 1) (equalityConstraint output)
  ]

theorem tableSoundness : ∀ (table : InductiveTable F Row) (input output: Row F)
  (N : ℕ) (trace: TraceOfLength F Row N) (env: ℕ → ℕ → Environment F),
  table_constraints_hold (table.tableConstraints input output) trace env →
    table.tableSpec trace := by
  sorry

def toFormal (table : InductiveTable F Row) (input output: Row F) : FormalTable F Row where
  constraints := table.tableConstraints input output
  spec := table.tableSpec
  soundness := by
    simp only [true_implies]
    exact table.tableSoundness input output
  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, assignment_from_circuit_offset]

end InductiveTable
