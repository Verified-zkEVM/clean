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
- with extra inputs to the spec: the current row number, and the list of all inputs up to and including the current row
- with assumptions replaced by the spec on the previous row, plus extra assumptions on honest prover inputs for completeness
- with input offset hard-coded to `size Row + size Input`
-/
structure InductiveTable (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input] where
  /-- the `step` circuit encodes the transition logic from one state to the next -/
  step : Var State F → Var Input F → Circuit F (Var State F)

  /-- the `spec` characterizes the `i`th state, possibly in relation to the full list of inputs up to that point -/
  spec : (i : ℕ) → State F → (xs : List (Input F)) → (xs.length = i) → Prop

  /--
    assumptions on inputs for completeness.
    explanation: in general, we expect the `step` circuit to impose some constraints on the `input`.
    in the completeness proof, we therefore need to restrict the possible inputs a prover can provide in order to satisfy the constraints.
    by design, completeness for the full table holds for any list of inputs that satisfy the `input_assumptions`.
  -/
  input_assumptions : ℕ → Input F → Prop := fun _ _ => True

  soundness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows and inputs
    ∀ (acc_var : Var State F) (x_var : Var Input F)
      (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
      (eval env acc_var = acc) ∧ (eval env x_var = x) →
    -- if the constraints hold
    Circuit.constraints_hold.soundness env (step acc_var x_var |>.operations ((size State) + (size Input))) →
    -- and assuming the spec on the current row and previous inputs
    spec row_index acc xs xs_len →
    -- we can conclude the spec on the next row and inputs including the current input
    spec (row_index + 1) (eval env (step acc_var x_var |>.output ((size State) + (size Input)))) (xs.concat x) (xs_len ▸ List.length_concat)

  completeness : ∀ (row_index : ℕ) (env : Environment F),
    -- for all rows and inputs
    ∀ (acc_var : Var State F) (x_var : Var Input F)
      (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
      (eval env acc_var = acc) ∧ (eval env x_var = x) →
    -- when using honest-prover witnesses
    env.uses_local_witnesses_completeness ((size State) + (size Input)) (step acc_var x_var |>.operations ((size State) + (size Input))) →
    -- assuming the spec on the current row, and the input_spec on the input
    spec row_index acc xs xs_len ∧ input_assumptions row_index x →
    -- the constraints hold
    Circuit.constraints_hold.completeness env (step acc_var x_var |>.operations ((size State) + (size Input)))

  subcircuits_consistent : ∀ acc x, ((step acc x).operations ((size State) + (size Input))).subcircuits_consistent ((size State) + (size Input))
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [Field F] {State Input : TypeMap} [ProvableType State] [ProvableType Input]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.spec 0 input → table.spec (N-1) output`

for any given public `input` and `ouput`.
-/

def inductiveConstraint (table : InductiveTable F State Input) : TableConstraint 2 (ProvablePair State Input) F Unit := do
  let (acc, x) ← get_curr_row
  let output ← table.step acc x
  let (output', _) ← get_next_row
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  assert_equals output' output

def equalityConstraint (Input : TypeMap) [ProvableType Input] (target : State F) : SingleRowConstraint (ProvablePair State Input) F := do
  let (actual, _) ← get_curr_row
  assert_equals actual (const target)

def tableConstraints (table : InductiveTable F State Input) (input_state output_state: State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .EveryRowExceptLast table.inductiveConstraint,
    .Boundary (.fromStart 0) (equalityConstraint Input input_state),
    .Boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

theorem equalityConstraint.soundness {row : State F × Input F} {input_state : State F} {env : Environment F} :
  Circuit.constraints_hold.soundness (window_env (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env)
    (equalityConstraint Input input_state .empty).2.circuit
    ↔ row.1 = input_state := by
  set env' := window_env (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm]

  have h_env_in i (hi : i < size State) : (to_elements row.1)[i] = env'.get i := by
    have h_env' : env' = window_env (equalityConstraint Input input_state) ⟨<+> +> row, _⟩ env := rfl
    simp only [window_env, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    have hi' : i < size State + size Input := by linarith
    simp [h_env', hi, hi', Vector.getElem_mapFinRange, Trace.getLeFromBottom, _root_.Row.get, Vector.get_eq,
      Vector.mapRange_zero, Vector.append_empty, ProvablePair.instance]

  have h_env : eval env' (var_from_offset State 0) = row.1 := by
    rw [ProvableType.ext_iff]
    intro i hi
    rw [h_env_in i hi, ProvableType.eval_var_from_offset,
      ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]
  rw [h_env]

def traceInputs {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) : List (Input F) :=
  trace.val.toList.map Prod.snd

omit [Field F] in
lemma traceInputs_length {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) :
    (traceInputs trace).length = N := by
  rw [traceInputs, List.length_map, trace.val.toList_length, trace.prop]

lemma tableSoundnessAux (table : InductiveTable F State Input) (input output: State F)
  (N : ℕ+) (trace: TraceOfLength F (ProvablePair State Input) N) (env: ℕ → ℕ → Environment F) :
  table.spec 0 input [] rfl →
  table_constraints_hold (table.tableConstraints input output) trace env →
    trace.forAllRowsWithPrevious (fun row i rest => table.spec i row.1 (traceInputs rest) (traceInputs_length rest))
    ∧ trace.lastRow.1 = output := by
  intro input_spec

  -- add a condition on the trace length to the goal,
  -- so that we can change the induction to not depend on `N` (which would make it unprovable)
  rcases trace with ⟨ trace, h_trace ⟩
  suffices goal : table_constraints_hold (table.tableConstraints input output) ⟨ trace, h_trace ⟩ env →
    trace.forAllRowsWithPrevious (fun row rest => table.spec rest.len row.1 (traceInputs ⟨ rest, rfl ⟩) (traceInputs_length ⟨ rest, rfl ⟩)) ∧
    (∀ (h_len : trace.len = N), (trace.lastRow (by rw [h_len]; exact N.pos)).1 = output) by
      intro constraints
      specialize goal constraints
      exact ⟨ goal.left, goal.right h_trace ⟩

  simp only [table_norm, tableConstraints]
  clear h_trace
  induction trace using Trace.everyRowTwoRowsInduction

  case zero =>
    intro constraints
    simp only [Trace.forAllRowsWithPrevious, true_and]
    intros
    nomatch N

  case one first_row =>
    intro constraints
    simp only [table_norm, tableConstraints,
      List.size_toArray, List.length_nil, List.push_toArray, List.nil_append,
      List.length_cons, zero_add, List.cons_append, reduceIte, and_true] at constraints
    obtain ⟨ input_eq, output_eq ⟩ := constraints
    rw [equalityConstraint.soundness] at input_eq output_eq
    simp only [table_norm, and_true, Trace.lastRow, Trace.forAllRowsWithPrevious]
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
      Nat.reduceAdd, true_and, Trace.forAllRowsWithPrevious] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.spec rest.len curr.1 (traceInputs ⟨rest, rfl⟩) (traceInputs_length ⟨rest, rfl⟩) := by
      simp [ih2]
    simp only [ih2, and_self, and_true, Trace.lastRow]
    clear ih1 ih2
    set env' := window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1))
    simp only [table_norm, circuit_norm, inductiveConstraint] at constraints
    obtain ⟨ main_constraints, return_eq ⟩ := constraints
    have h_env' : env' = window_env table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env 0 (rest.len + 1)) := rfl
    simp only [window_env, table_assignment_norm, inductiveConstraint, circuit_norm] at h_env'
    simp only [zero_add, Nat.add_zero, Fin.isValue, PNat.val_ofNat, Nat.reduceAdd, Nat.add_one_sub_one,
      CellAssignment.assignment_from_circuit_offset, CellAssignment.assignment_from_circuit_vars] at h_env'
    set curr_var : Var State F × Var Input F := var_from_offset (ProvablePair State Input) 0
    set s := size State
    set x := size Input
    set main_ops : Operations F := (table.step (var_from_offset State 0) (var_from_offset Input s) (s + x)).2
    set t := main_ops.local_length

    have h_env_input_1 i (hi : i < s) : (to_elements curr.1)[i] = env'.get i := by
      have hi' : i < s + x + t + (s + x) := by linarith
      have hi'' : i < 0 + (s + x) := by linarith
      have hi''' : i < 0 + (s + x) + t := by linarith
      rw [h_env']
      simp +arith only [main_ops, s, t, x, hi, hi', hi'', hi''', table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        CellAssignment.assignment_from_circuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]

    have h_env_input_2 i (hi : i < x) : (to_elements curr.2)[i] = env'.get (i + s) := by
      have hi' : i + s < s + x + t + (s + x) := by linarith
      have hi'' : i + s < 0 + (s + x) := by linarith
      have hi''' : i + s < 0 + (s + x) + t := by linarith
      rw [h_env']
      simp +arith only [main_ops, s, t, x, hi, hi', hi'', hi''', table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        CellAssignment.assignment_from_circuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]
      congr; omega

    have h_env_output i (hi : i < s) : (to_elements next.1)[i] = env'.get (i + (s + x) + t) := by
      have hi' : i + (s + x) + t < s + x + t + (s + x) := by linarith
      have hi'' : ¬(i + (s + x) + t < 0 + (s + x)) := by linarith
      have hi''' : ¬(i + (s + x) + t < 0 + (s + x) + t) := by linarith
      rw [h_env']
      simp +arith only [main_ops, hi, hi', hi'', hi''', s, t, x, table_assignment_norm, inductiveConstraint, circuit_norm, reduceDIte,
        CellAssignment.assignment_from_circuit_offset,
        Vector.mapRange_zero, Vector.empty_append, Vector.append_empty, Vector.getElem_append]
      simp +arith [hi, s, add_assoc]
    clear h_env'

    have input_eq_1 : eval env' curr_var.1 = curr.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, var_from_offset_pair]
      rw [h_env_input_1 i hi]
      simp only [ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]

    have input_eq_2 : eval env' curr_var.2 = curr.2 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, var_from_offset_pair]
      rw [h_env_input_2 i hi]
      simp only [s, ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange, zero_add]
      ac_rfl

    have next_eq : eval env' (var_from_offset State (size State + size Input + main_ops.local_length)) = next.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env_output i hi, ProvableType.eval_var_from_offset,
        ProvableType.to_elements_from_elements, Vector.getElem_mapRange]
      simp only [t, s, x]
      ac_rfl

    simp only [t, x] at main_constraints
    have constraints : Circuit.constraints_hold.soundness
        env' ((table.step curr_var.1 curr_var.2).operations (size State + size Input)) := by
      simp only [curr_var, var_from_offset_pair]
      exact main_constraints

    let xs := traceInputs ⟨ rest, rfl ⟩
    have xs_len := traceInputs_length ⟨ rest, rfl ⟩
    have xs_concat : traceInputs ⟨rest +> curr, rfl⟩ = xs.concat curr.2 := by
      simp only [traceInputs, xs, Trace.toList, List.map_concat]

    have h_soundness := table.soundness rest.len env' curr_var.1 curr_var.2 curr.1 curr.2 xs xs_len
      ⟨ input_eq_1, input_eq_2 ⟩ constraints spec_previous
    simp only [curr_var, var_from_offset_pair] at h_soundness
    simp only [s, x, t, main_ops] at *
    simp +arith only at return_eq h_soundness
    rw [←return_eq, next_eq] at h_soundness
    simp only [xs_concat]
    use h_soundness

    intro h_len
    rw [equalityConstraint.soundness] at output_eq
    rw [←h_len] at output_eq
    simp only [add_tsub_cancel_right, Nat.add_left_inj, reduceIte] at output_eq
    exact output_eq

theorem tableSoundness (table : InductiveTable F State Input) (input output: State F)
  (N : ℕ+) (trace: TraceOfLength F (ProvablePair State Input) N) (env: ℕ → ℕ → Environment F) :
  table.spec 0 input [] rfl → table_constraints_hold (table.tableConstraints input output) trace env →
    table.spec (N-1) output (traceInputs trace.tail) (traceInputs_length trace.tail) := by
  intro h_input h_constraints
  have ⟨ h_spec, h_output ⟩ := table.tableSoundnessAux input output N trace env h_input h_constraints
  rw [←h_output]
  exact TraceOfLength.lastRow_of_forAllWithPrevious trace h_spec

def toFormal (table : InductiveTable F State Input) (input output: State F) : FormalTable F (ProvablePair State Input) where
  constraints := table.tableConstraints input output
  assumption N := N > 0 ∧ table.spec 0 input [] rfl
  spec {N} trace := table.spec (N-1) output (traceInputs trace.tail) (traceInputs_length trace.tail)

  soundness N trace env assumption constraints :=
    table.tableSoundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignment_from_circuit_offset]

end InductiveTable
