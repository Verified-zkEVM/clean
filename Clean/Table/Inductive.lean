/-
"Inductive" tables are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

Thus far, only the common `k=2` case is handled.
-/
import Clean.Circuit.Extensions
import Clean.Table.Theorems
import Clean.Gadgets.Equality

def InductiveTable.Soundness (F : Type) [FiniteField F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → ProverData F → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : Environment F),
  -- for all rows and inputs
  ∀ (acc_var : Var State F) (x_var : Var Input F)
    (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
      (eval env acc_var = acc) ∧ (eval env x_var = x) →
    -- if the constraints hold
    ConstraintsHold.Soundness env (step acc_var x_var |>.operations ((size State) + (size Input))) →
    -- and assuming the spec on the current row and previous inputs
    Spec initialState xs row_index xs_len acc env.data →
    -- we can conclude the spec on the next row and inputs including the current input
    Spec initialState (xs.concat x) (row_index + 1) (xs_len ▸ List.length_concat)
      (eval env (step acc_var x_var |>.output ((size State) + (size Input)))) env.data

def InductiveTable.Completeness (F : Type) [FiniteField F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (InputAssumptions : ℕ → Input F → ProverData F → Prop)
    (InitialStateAssumptions : State F → ProverData F → Prop)
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → ProverData F → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : ProverEnvironment F),
  -- for all rows and inputs
  ∀ (acc_var : Var State F) (x_var : Var Input F)
    (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
    (eval env acc_var = acc) ∧ (eval env x_var = x) →
  -- when using honest-prover witnesses
  env.UsesLocalWitnessesCompleteness ((size State) + (size Input)) (step acc_var x_var |>.operations ((size State) + (size Input))) →
  -- assuming the spec on the current row, the input_spec on the input, and initial state assumptions
  InitialStateAssumptions initialState env.data ∧
  Spec initialState xs row_index xs_len acc env.data ∧ InputAssumptions row_index x env.data →
  -- the constraints hold
  ConstraintsHold.Completeness env (step acc_var x_var |>.operations ((size State) + (size Input)))

/--
In the case of two-row windows, an `InductiveTable` is basically a `FormalCircuit` but
- with the same input and output types
- with extra inputs to the spec: the current row number, and the list of all inputs up to and including the current row
- with assumptions replaced by the spec on the previous row, plus extra assumptions on honest prover inputs for completeness
- with input offset hard-coded to `size Row + size Input`
-/
structure InductiveTable (F : Type) [FiniteField F] (State Input : Type → Type) [ProvableType State] [ProvableType Input] where
  /-- the `step` circuit encodes the transition logic from one state to the next -/
  step : Var State F → Var Input F → Circuit F (Var State F)

  /-- the `Spec` characterizes the `i`th state, possibly in relation to the initial state and the full list of inputs up to that point -/
  Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → ProverData F → Prop

  /--
    assumptions on inputs and initial state for completeness.
    explanation: in general, we expect the `step` circuit to impose some constraints on the `input`.
    similarly, the initial state may need to satisfy certain properties (e.g., normalization) for the table to work correctly.
    in the completeness proof, we therefore need to restrict the possible inputs and initial states a prover can provide.
    by design, completeness for the full table holds for any initial state and list of inputs that satisfy these assumptions.
  -/
  InputAssumptions : ℕ → Input F → ProverData F → Prop := fun _ _ _ => True
  InitialStateAssumptions : State F  → ProverData F → Prop := fun _ _ => True

  soundness : InductiveTable.Soundness F State Input Spec step

  completeness : InductiveTable.Completeness F State Input InputAssumptions InitialStateAssumptions Spec step

  subcircuitsConsistent : ∀ acc x, ((step acc x).operations ((size State) + (size Input))).SubcircuitsConsistent ((size State) + (size Input))
    := by intros; and_intros <;> (
      try simp only [circuit_norm]
      try first | ac_rfl | trivial
    )

namespace InductiveTable
variable {F : Type} [FiniteField F] {State Input : TypeMap} [ProvableType State] [ProvableType Input]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.Spec 0 input → table.Spec (N-1) output`

for any given public `input` and `ouput`.
-/

def inductiveConstraint (table : InductiveTable F State Input) : TableConstraint 2 (ProvablePair State Input) F Unit := do
  let (acc, x) ← readCurrRow
  let output ← table.step acc x
  let output' : Var State F ← modifyGet fun ctx =>
    let circuit : Circuit F Unit := do
      let _state : Var State F ← witness output
      let _input : Var Input F ← witnessAny Input
    let (_, ops) := circuit ctx.offset
    let ctx' : TableContext 2 (ProvablePair State Input) F := {
      inputSize := ctx.inputSize,
      circuit := ctx.circuit ++ ops,
      assignment := ctx.assignment.pushRow 1
    }
    (varFromOffset State ctx.offset, ctx')
  -- TODO make this more efficient by assigning variables as long as they don't come from the input
  output' === output

def equalityConstraint (Input : TypeMap) [ProvableType Input] (target : State F) : SingleRowConstraint (ProvablePair State Input) F := do
  let (actual, _) ← getCurrRow
  actual === (const target)

def tableConstraints (table : InductiveTable F State Input) (input_state output_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveConstraint,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
    .boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

/--
Helper for reasoning about the cell assignment produced by a single-row constraint:
variables at indices below `size S` are assigned to that row's input cells.
Stated for a generic `ops`, so that all vector lengths stay symbolic and clean.
-/
private lemma single_vars_first {W : ℕ+} {S : TypeMap} [ProvableType S]
    {r0 : Fin W} {ops : Operations F} {j : ℕ} (hj : j < size S)
    (hoff : j < (assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).offset) :
    (assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).vars[j]'hoff
      = .input ⟨r0, ⟨j, hj⟩⟩ := by
  simp [CellAssignment.assignmentFromCircuit_vars, CellAssignment.pushRow, CellAssignment.empty,
    Vector.getElem_cast, Vector.getElem_mapFinRange, hj]

theorem equalityConstraint.soundness {row : State F × Input F} {input_state : State F} {env : ProverEnvironment F} :
  ConstraintsHold.Soundness (windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env)
    (equalityConstraint Input input_state .empty).2.circuit
    ↔ row.1 = input_state := by
  obtain ⟨row₁, row₂⟩ := row
  set env' := windowEnv (equalityConstraint Input input_state) ⟨<+> +> (row₁, row₂), rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm, MonadLift.monadLift, pure]

  have h_sp : size (ProvablePair State Input) = size State + size Input := rfl

  have h_env_in i (hi : i < size State) : (toElements row₁)[i] = env'.get i := by
    have h_env' : env' = windowEnv (equalityConstraint Input input_state) ⟨<+> +> (row₁, row₂), _⟩ env := rfl
    simp only [windowEnv, TableConstraint.finalAssignment, equalityConstraint, circuit_norm,
      table_norm, MonadLift.monadLift, pure] at h_env'
    rw [h_env']
    dsimp only
    split
    · rw [single_vars_first (j := i) (by rw [h_sp]; omega)]
      simp
      exact (Vector.getElem_append_left hi).symm
    · exfalso; apply ‹¬_›
      simp only [CellAssignment.assignmentFromCircuit_offset, CellAssignment.pushRow_offset,
        CellAssignment.empty, h_sp]
      omega

  have h_env : (eval env'.toEnvironment (varFromOffset State 0 : State (Expression F)) : State F) = row₁ := by
    rw [ProvableType.ext_iff]
    intro i hi
    rw [h_env_in i hi, ProvableType.eval_varFromOffset,
      ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]
  rw [h_env]

def traceInputs {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) : List (Input F) :=
  trace.val.toList.map Prod.snd

omit [FiniteField F] in
lemma traceInputs_length {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) :
    (traceInputs trace).length = N := by
  rw [traceInputs, List.length_map, trace.val.toList_length, trace.prop]

/--
Helper for reasoning about the cell assignment produced by `inductiveConstraint`:
variables at indices below `size S` are assigned to the first row's input cells.
Stated for generic `ops`/`ops2`, so that all vector lengths stay symbolic and clean.
-/
private lemma composite_vars_first {W : ℕ+} {S : TypeMap} [ProvableType S]
    {r0 r1 : Fin W} {ops ops2 : Operations F} {j : ℕ} (hj : j < size S)
    (hoff : j < (assignmentFromCircuit ((assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).pushRow r1) ops2).offset) :
    (assignmentFromCircuit ((assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).pushRow r1) ops2).vars[j]'hoff
      = .input ⟨r0, ⟨j, hj⟩⟩ := by
  simp [CellAssignment.assignmentFromCircuit_vars, CellAssignment.assignmentFromCircuit_offset,
    CellAssignment.pushRow, CellAssignment.empty, Vector.getElem_cast, Vector.getElem_append,
    Vector.getElem_mapFinRange, hj]
  intro h
  exact absurd h (by omega)

/--
Variables at indices `size S + ops.localLength + i` (for `i < size S`) are assigned
to the second row's input cells.
-/
private lemma composite_vars_second {W : ℕ+} {S : TypeMap} [ProvableType S]
    {r0 r1 : Fin W} {ops ops2 : Operations F} {i j : ℕ} (hi : i < size S)
    (hj : j = size S + ops.localLength + i)
    (hoff : j < (assignmentFromCircuit ((assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).pushRow r1) ops2).offset) :
    (assignmentFromCircuit ((assignmentFromCircuit ((CellAssignment.empty W).pushRow r0) ops).pushRow r1) ops2).vars[j]'hoff
      = .input ⟨r1, ⟨i, hi⟩⟩ := by
  subst hj
  simp [CellAssignment.assignmentFromCircuit_vars, CellAssignment.assignmentFromCircuit_offset,
    CellAssignment.pushRow, CellAssignment.empty, Vector.getElem_cast,
    Vector.getElem_mapFinRange, hi]

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data →
  TableConstraintsHold (table.tableConstraints input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1 env.data)
    ∧ trace.lastRow.1 = output := by
  intro input_spec

  -- add a condition on the trace length to the goal,
  -- so that we can change the induction to not depend on `N` (which would make it unprovable)
  rcases trace with ⟨ trace, h_trace ⟩
  suffices goal : TableConstraintsHold (table.tableConstraints input output) ⟨ trace, h_trace ⟩ env →
    trace.ForAllRowsWithPrevious (fun row rest =>
      table.Spec input (traceInputs ⟨ rest, rfl ⟩) rest.len (traceInputs_length ⟨ rest, rfl ⟩) row.1 env.data)
    ∧ (∀ (h_len : trace.len = N), (trace.lastRow (by rw [h_len]; exact N.pos)).1 = output) by
      intro constraints
      specialize goal constraints
      exact ⟨ goal.left, goal.right h_trace ⟩

  simp only [table_norm, tableConstraints]
  clear h_trace
  induction trace using Trace.every_row_two_rows_induction

  case zero =>
    intro constraints
    simp only [Trace.ForAllRowsWithPrevious, true_and]
    intros
    nomatch N

  case one first_row =>
    intro constraints
    simp only [table_norm,
      List.size_toArray, List.length_nil, List.push_toArray, List.nil_append,
      List.length_cons, zero_add, List.cons_append, reduceIte, and_true] at constraints
    obtain ⟨ input_eq, output_eq ⟩ := constraints
    replace input_eq := equalityConstraint.soundness.mp input_eq
    simp only [table_norm, and_true, Trace.ForAllRowsWithPrevious]
    constructor
    · rw [input_eq]
      exact input_spec
    intro h_len
    rw [←h_len] at output_eq
    simp only [zero_add, tsub_self, reduceIte] at output_eq
    exact equalityConstraint.soundness.mp output_eq

  case more curr next rest ih1 ih2 =>
    intro constraints
    simp only [table_norm, List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, reduceIte, tsub_zero,
      Nat.reduceAdd, true_and, Trace.ForAllRowsWithPrevious] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) curr.1 env.data := by
      simp [ih2]
    simp only [ih2, and_self, and_true]
    clear ih1 ih2
    set env' := windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1))
    change ConstraintsHold.Soundness env'.toEnvironment _ at constraints
    simp only [table_norm, circuit_norm, witnessAny, inductiveConstraint, zero_add, Nat.add_zero,
      MonadLift.monadLift, pure] at constraints
    obtain ⟨ main_constraints, return_eq ⟩ := constraints
    have h_env' : env' = windowEnv table.inductiveConstraint ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1)) := rfl
    simp only [windowEnv, TableConstraint.finalAssignment, inductiveConstraint, circuit_norm, table_norm,
      MonadLift.monadLift, witnessAny, zero_add, Nat.add_zero, pure] at h_env'
    set curr_var : Var State F × Var Input F := varFromOffset (ProvablePair State Input) 0
    set s := size State
    set x := size Input
    set main_ops : Operations F := (table.step (varFromOffset State 0) (varFromOffset Input s) (s + x)).2
    set t := main_ops.localLength

    have h_sp : size (ProvablePair State Input) = size State + size Input := rfl

    have h_env_input_1 i (hi : i < s) : (toElements curr.1)[i] = env'.get i := by
      simp only [s] at hi
      rw [h_env']
      dsimp only
      split
      · rw [composite_vars_first (j := i) (by rw [h_sp]; omega)]
        simp
        exact (Vector.getElem_append_left hi).symm
      · exfalso; apply ‹¬_›
        simp only [CellAssignment.assignmentFromCircuit_offset, CellAssignment.pushRow_offset,
          CellAssignment.empty, h_sp]
        omega

    have h_env_input_2 i (hi : i < x) : (toElements curr.2)[i] = env'.get (i + s) := by
      simp only [x] at hi
      rw [h_env']
      dsimp only
      split
      · rw [composite_vars_first (j := i + s) (by rw [h_sp]; simp only [s]; omega)]
        simp
        have h1 : i + s < size State + size Input := by simp only [s]; omega
        have h2 : size State ≤ i + s := by simp only [s]; omega
        have e := Vector.getElem_append_right (xs := toElements curr.1) (ys := toElements curr.2) h1 h2
        simp only [s, Nat.add_sub_cancel] at e
        exact e.symm
      · exfalso; apply ‹¬_›
        simp only [CellAssignment.assignmentFromCircuit_offset, CellAssignment.pushRow_offset,
          CellAssignment.empty, h_sp, s]
        omega

    have h_env_output i (hi : i < s) : (toElements next.1)[i] = env'.get (i + (s + x) + t) := by
      simp only [s] at hi
      have h_idx : i + (s + x) + t = size (ProvablePair State Input) +
          Operations.localLength ((table.step (varFromOffset (ProvablePair State Input) 0).1
            (varFromOffset (ProvablePair State Input) 0).2 (0 + (size State + size Input))).2) + i := by
        rw [varFromOffset_pair]
        simp only [s, x, t, main_ops, zero_add, h_sp]
        omega
      rw [h_env']
      dsimp only
      split
      · rw [composite_vars_second (i := i) (by rw [h_sp]; omega) h_idx]
        simp
        exact (Vector.getElem_append_left hi).symm
      · exfalso; apply ‹¬_›
        simp only [CellAssignment.assignmentFromCircuit_offset, CellAssignment.pushRow_offset,
          CellAssignment.empty, h_sp, s, x, t, main_ops]
        change i + (size State + size Input) +
            Operations.localLength (table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).2 <
          0 + (size State + size Input) +
            Operations.localLength (table.step (varFromOffset State 0) (varFromOffset Input (size State)) (size State + size Input)).2 +
            (size State + size Input) + _
        omega
    clear h_env'

    have input_eq_1 : eval env'.toEnvironment curr_var.1 = curr.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, varFromOffset_pair]
      convert (h_env_input_1 i hi).symm
      simp only [ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, zero_add]
      exact Vector.getElem_mapRange _ hi

    have input_eq_2 : eval env'.toEnvironment curr_var.2 = curr.2 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, varFromOffset_pair]
      convert (h_env_input_2 i hi).symm
      simp only [s, ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, zero_add]
      rw [Vector.getElem_mapRange]
      ac_rfl

    have next_eq : eval env'.toEnvironment (varFromOffset (F := F) State (size State + size Input + main_ops.localLength)) = next.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env_output i hi, ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, Vector.getElem_mapRange]
      simp only [t, s, x]
      ac_rfl

    have constraints : ConstraintsHold.Soundness
        env' ((table.step curr_var.1 curr_var.2).operations (size State + size Input)) := by
      simp only [curr_var, varFromOffset_pair, zero_add]
      exact main_constraints

    let xs := traceInputs ⟨ rest, rfl ⟩
    have xs_len := traceInputs_length ⟨ rest, rfl ⟩
    have xs_concat : traceInputs (N := rest.len + 1) ⟨rest +> curr, rfl⟩ = xs.concat curr.2 := by
      simp only [traceInputs, xs, Trace.toList, List.map_concat]

    have h_soundness := table.soundness input rest.len env' curr_var.1 curr_var.2 curr.1 curr.2 xs xs_len
      ⟨ input_eq_1, input_eq_2 ⟩ constraints spec_previous
    simp only [curr_var, varFromOffset_pair] at h_soundness
    simp only [s, x, t, main_ops] at *
    simp +arith only at return_eq h_soundness
    rw [←return_eq, next_eq] at h_soundness
    simp only [xs_concat]
    use h_soundness

    intro h_len
    rw [←h_len] at output_eq
    simp only [add_tsub_cancel_right, reduceIte] at output_eq
    exact equalityConstraint.soundness.mp output_eq

theorem table_soundness (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data → TableConstraintsHold (table.tableConstraints input output) trace env →
    table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output env.data := by
  intro h_input h_constraints
  have ⟨ h_spec, h_output ⟩ := table_soundness_aux table input output N trace env h_input h_constraints
  rw [←h_output]
  exact TraceOfLength.lastRow_of_forAllWithPrevious trace h_spec

def toFormal (table : InductiveTable F State Input) (input output : State F) : FormalTable F (ProvablePair State Input) where
  constraints := table.tableConstraints input output
  Assumption N env := N > 0 ∧ table.Spec input [] 0 rfl input env
  Spec {N} trace env := table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output env

  soundness N trace env assumption constraints :=
    table.table_soundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, witnessAny, MonadLift.monadLift, pure,
      CellAssignment.assignmentFromCircuit_offset]

end InductiveTable
