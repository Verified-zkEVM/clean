/-
"Inductive" table constraints are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

The common `k=2` case gets its own special definition.
-/
import Clean.Table.Theorems
import Clean.Gadgets.Equality

/--
In the case of two-row windows, an `InductiveTable` is basically a `FormalCircuit` but
- with the same input and output types
- with an extra input to the spec: the current (input) row number
- with assumptions replaced by the spec on the previous row
- with input offset hard-coded to `size Row`
-/
structure InductiveTable (F : Type) [Field F] (Row : Type → Type) [ProvableType Row] where
  main : Var Row F → Circuit F (Var Row F)
  spec : ℕ → Row F → Prop

  soundness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- if the constraints hold
    Circuit.constraints_hold.soundness env (main input_var |>.operations (size Row)) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- we can conclude the spec on the output row
    spec (row_index + 1) (eval env (main input_var |>.output (size Row)))

  completeness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- when using honest-prover witnesses
    env.uses_local_witnesses_completeness (size Row) (main input_var |>.operations (size Row)) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- the constraints hold
    Circuit.constraints_hold.completeness env (main input_var |>.operations (size Row))

  subcircuits_consistent : ∀ var, ((main var).operations).subcircuits_consistent 0
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [Field F] {Row : TypeMap} [ProvableType Row]

def tableSpec (table : InductiveTable F Row) {N : ℕ} (trace : TraceOfLength F Row N) : Prop :=
  trace.forAllRowsOfTraceWithIndex fun row i => table.spec i row

def inductiveConstraint (table : InductiveTable F Row) : TableConstraint 2 Row F Unit := do
  let input ← get_curr_row
  let output ← table.main input
  let output' ← get_next_row
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  assert_equals output' output

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

theorem tableSoundness (table : InductiveTable F Row) (input output: Row F)
  (N : ℕ) (trace: TraceOfLength F Row N) (env: ℕ → ℕ → Environment F) :
  table.spec 0 input →
  table_constraints_hold (table.tableConstraints input output) trace env →
    table.tableSpec trace := by
  intro input_spec
  simp only [table_norm, tableConstraints, tableSpec]
  induction' trace.val using Trace.everyRowTwoRowsInduction
  case zero => intro; trivial

  case one first_row =>
    intro constraints
    simp only [table_norm, tableConstraints, List.size_toArray, List.length_nil, List.push_toArray, List.nil_append,
      List.length_cons, zero_add, List.cons_append, reduceIte, and_true] at constraints
    set env' := window_env (equalityConstraint input) ⟨<+> +> first_row, _⟩ (env 1 0)
    simp only [table_norm, equalityConstraint, circuit_norm] at constraints
    simp only [table_norm, and_true]
    have h_env i (hi : i < size Row) : (to_elements first_row)[i] = env'.get i := by
      have h_env' : env' = window_env (equalityConstraint input) ⟨<+> +> first_row, _⟩ (env 1 0) := rfl
      simp only [window_env, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
      simp [h_env', hi, Vector.getElem_mapFinRange, Trace.getLeFromBottom, _root_.Row.get, Vector.get_eq,
        Vector.mapRange_zero, Vector.append_empty]
    have input_eq : first_row = input := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env i hi, ←constraints, ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]
    rw [input_eq]
    exact input_spec

  case more curr next rest ih1 ih2 =>
    simp only [table_norm, tableConstraints, List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero, one_ne_zero,
      and_false, reduceIte] at ih1 ih2 ⊢
    intro ⟨ constraints, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.spec rest.len curr := by simp [ih2]
    simp only [ih2, and_self, and_true]
    clear ih1 ih2
    set env' := window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1))
    simp only [table_norm, circuit_norm, inductiveConstraint] at constraints
    obtain ⟨ main_constraints, output_eq ⟩ := constraints
    have h_env' : env' = window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1)) := rfl
    simp only [window_env, table_assignment_norm, inductiveConstraint, circuit_norm] at h_env'
    simp only [zero_add, Nat.add_zero, Fin.isValue, PNat.val_ofNat, Nat.reduceAdd,
      Nat.add_one_sub_one] at h_env'
    set curr_var := var_from_offset Row 0
    set main_ops : Operations F := (table.main (var_from_offset Row 0) (size Row)).2
    set s := size Row
    set t := main_ops.local_length

    have h_env_input i (hi : i < s) : (to_elements curr)[i] = env'.get i := by
      have hi' : i < s + t + s := by linarith
      have hi'' : i < 0 + s := by linarith
      have hi''' : i < 0 + s + t := by linarith
      rw [h_env']
      simp only [main_ops, s, t, hi', hi'', hi''', table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]

    have h_env_output i (hi : i < s) : (to_elements next)[i] = env'.get (i + s + t) := by
      have hi' : i + s + t < s + t + s := by linarith
      have hi'' : ¬(i + s + t < 0 + s) := by linarith
      have hi''' : ¬(i + s + t < 0 + s + t) := by linarith
      rw [h_env']
      simp only [main_ops, hi', hi'', hi''', s, t, table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]
      simp +arith [add_assoc]

    have input_eq : eval env' curr_var = curr := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env_input i hi, ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]

    have next_eq : eval env' (var_from_offset Row (size Row + main_ops.local_length)) = next := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env_output i hi, ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange, add_comm _ i, add_assoc]

    have h_soundness := table.soundness rest.len env' curr_var curr input_eq main_constraints spec_previous
    rw [←output_eq, next_eq] at h_soundness
    exact h_soundness

def toFormal (table : InductiveTable F Row) (input output: Row F) (h_input : table.spec 0 input) : FormalTable F Row where
  constraints := table.tableConstraints input output
  spec := table.tableSpec
  soundness := by
    intro N trace env _ constraints
    exact table.tableSoundness input output _ _ _ h_input constraints
  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignment_from_circuit_offset]

end InductiveTable
