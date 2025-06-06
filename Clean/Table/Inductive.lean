/-
"Inductive" tables are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

Thus far, only the common `k=2` case is handled.
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
  step : Var Row F → Circuit F (Var Row F)
  spec : ℕ → Row F → Prop

  soundness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- if the constraints hold
    Circuit.constraints_hold.soundness env (step input_var |>.operations (size Row)) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- we can conclude the spec on the output row
    spec (row_index + 1) (eval env (step input_var |>.output (size Row)))

  completeness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows
    ∀ (input_var : Var Row F) (input : Row F), eval env input_var = input →
    -- when using honest-prover witnesses
    env.uses_local_witnesses_completeness (size Row) (step input_var |>.operations (size Row)) →
    -- and assuming the spec on the input row
    spec row_index input →
    -- the constraints hold
    Circuit.constraints_hold.completeness env (step input_var |>.operations (size Row))

  subcircuits_consistent : ∀ var, ((step var).operations (size Row)).subcircuits_consistent (size Row)
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [Field F] {Row : TypeMap} [ProvableType Row]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.spec 0 input → table.spec (N-1) output`

for any given public `input` and `ouput`.
-/

def inductiveConstraint (table : InductiveTable F Row) : TableConstraint 2 Row F Unit := do
  let input ← get_curr_row
  let output ← table.step input
  let output' ← get_next_row
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  assert_equals output' output

def equalityConstraint (target : Row F) : SingleRowConstraint Row F := do
  let actual ← get_curr_row
  assert_equals actual (const target)

def tableConstraints (table : InductiveTable F Row) (input output: Row F) :
  List (TableOperation Row F) := [
    .EveryRowExceptLast table.inductiveConstraint,
    .Boundary (.fromStart 0) (equalityConstraint input),
    .Boundary (.fromEnd 0) (equalityConstraint output),
  ]

theorem equalityConstraint.soundness  {row : Row F} {input : Row F} {env : Environment F} :
  Circuit.constraints_hold.soundness (window_env (equalityConstraint input) ⟨<+> +> row, rfl⟩ env)
    (equalityConstraint input .empty).2.circuit
    ↔ row = input := by
  set env' := window_env (equalityConstraint input) ⟨<+> +> row, rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm]

  have h_env_in i (hi : i < size Row) : (to_elements row)[i] = env'.get i := by
    have h_env' : env' = window_env (equalityConstraint input) ⟨<+> +> row, _⟩ env := rfl
    simp only [window_env, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    simp [h_env', hi, Vector.getElem_mapFinRange, Trace.getLeFromBottom, _root_.Row.get, Vector.get_eq,
      Vector.mapRange_zero, Vector.append_empty]

  have h_env : eval env' (var_from_offset Row 0) = row := by
    rw [ProvableType.ext_iff]
    intro i hi
    rw [h_env_in i hi, ProvableType.eval_var_from_offset,
      ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]
  rw [h_env]

lemma tableSoundnessAux (table : InductiveTable F Row) (input output: Row F)
  (N : ℕ+) (trace: TraceOfLength F Row N) (env: ℕ → ℕ → Environment F) :
  table.spec 0 input →
  table_constraints_hold (table.tableConstraints input output) trace env →
    trace.forAllRowsOfTraceWithIndex (fun row i => table.spec i row)
    ∧ trace.lastRow = output := by
  intro input_spec

  -- add a condition on the trace length to the goal,
  -- so that we can change the induction to not depend on `N` (which would make it unprovable)
  rcases trace with ⟨ trace, h_trace ⟩
  suffices goal : table_constraints_hold (table.tableConstraints input output) ⟨ trace, h_trace ⟩ env →
    trace.forAllRowsOfTraceWithIndex (fun row i => table.spec i row) ∧
    (∀ (h_len : trace.len = N), trace.lastRow (by rw [h_len]; exact N.pos) = output) by
      intro constraints
      specialize goal constraints
      exact ⟨ goal.left, goal.right h_trace ⟩

  simp only [table_norm, tableConstraints]
  clear h_trace
  induction trace using Trace.everyRowTwoRowsInduction

  case zero =>
    intro constraints
    simp only [Trace.forAllRowsOfTraceWithIndex.inner, true_and]
    intro N0
    nomatch N

  case one first_row =>
    intro constraints
    simp only [table_norm, tableConstraints, List.size_toArray, List.length_nil, List.push_toArray, List.nil_append,
      List.length_cons, zero_add, List.cons_append, reduceIte, and_true] at constraints
    obtain ⟨ input_eq, output_eq ⟩ := constraints
    rw [equalityConstraint.soundness] at input_eq output_eq
    simp only [table_norm, and_true, Trace.lastRow]
    constructor
    · rw [input_eq]
      exact input_spec
    intro h_len
    rw [←h_len] at output_eq
    simp only [zero_add, tsub_self, reduceIte] at output_eq
    exact output_eq

  case more curr next rest ih1 ih2 =>
    intro constraints
    simp only [table_norm, tableConstraints, List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero, one_ne_zero,
      and_false, reduceIte, PNat.mk_coe, Nat.add_one_sub_one, tsub_zero, Nat.add_left_inj,
      Nat.reduceAdd, true_and] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.spec rest.len curr := by simp [ih2]
    simp only [ih2, and_self, and_true, Trace.lastRow]
    clear ih1 ih2
    set env' := window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1))
    simp only [table_norm, circuit_norm, inductiveConstraint] at constraints
    obtain ⟨ main_constraints, return_eq ⟩ := constraints
    have h_env' : env' = window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1)) := rfl
    simp only [window_env, table_assignment_norm, inductiveConstraint, circuit_norm] at h_env'
    simp only [zero_add, Nat.add_zero, Fin.isValue, PNat.val_ofNat, Nat.reduceAdd, Nat.add_one_sub_one,
      CellAssignment.assignment_from_circuit_offset, CellAssignment.assignment_from_circuit_vars] at h_env'
    set curr_var := var_from_offset Row 0
    set main_ops : Operations F := (table.step (var_from_offset Row 0) (size Row)).2
    set s := size Row
    set t := main_ops.local_length

    have h_env_input i (hi : i < s) : (to_elements curr)[i] = env'.get i := by
      have hi' : i < s + t + s := by linarith
      have hi'' : i < 0 + s := by linarith
      have hi''' : i < 0 + s + t := by linarith
      rw [h_env']
      simp only [main_ops, s, t, hi', hi'', hi''', table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        CellAssignment.assignment_from_circuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]

    have h_env_output i (hi : i < s) : (to_elements next)[i] = env'.get (i + s + t) := by
      have hi' : i + s + t < s + t + s := by linarith
      have hi'' : ¬(i + s + t < 0 + s) := by linarith
      have hi''' : ¬(i + s + t < 0 + s + t) := by linarith
      rw [h_env']
      simp only [main_ops, hi', hi'', hi''', s, t, table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        CellAssignment.assignment_from_circuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]
      simp +arith [add_assoc]
    clear h_env'

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
    rw [←return_eq, next_eq] at h_soundness
    use h_soundness

    intro h_len
    rw [equalityConstraint.soundness] at output_eq
    rw [←h_len] at output_eq
    simp only [add_tsub_cancel_right, Nat.add_left_inj, reduceIte] at output_eq
    exact output_eq

theorem tableSoundness (table : InductiveTable F Row) (input output: Row F)
  (N : ℕ+) (trace: TraceOfLength F Row N) (env: ℕ → ℕ → Environment F) :
  table.spec 0 input → table_constraints_hold (table.tableConstraints input output) trace env →
    table.spec (N-1) output := by
  intro h_input h_constraints
  have ⟨ h_spec, h_output ⟩ := table.tableSoundnessAux input output N trace env h_input h_constraints
  rw [←h_output]
  exact TraceOfLength.lastRow_of_forAll (prop := fun row i => table.spec i row) trace h_spec

def toFormal (table : InductiveTable F Row) (input output: Row F) : FormalTable F Row where
  constraints := table.tableConstraints input output
  assumption N := N > 0 ∧ table.spec 0 input
  spec {N} _ := table.spec (N-1) output

  soundness N trace env assumption constraints :=
    table.tableSoundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignment_from_circuit_offset]

end InductiveTable
