/-
"Inductive" tables are specified by a circuit on a `k`-row window of cells, which
take the first `k-1` rows as input variables and return the `k`-th row as output.

Assignment of cells is handled in the background, which simplifies reasoning about the table.

Thus far, only the common `k=2` case is handled.
-/
import Clean.Table.Theorems
import Clean.Gadgets.Equality

def InductiveTable.Soundness (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → ProverData F → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : Environment F),
  -- for all rows and inputs
  ∀ (acc_var : Var State F) (x_var : Var Input F)
    (acc : State F) (x : Input F) (xs : List (Input F)) (xs_len : xs.length = row_index),
      (eval env acc_var = acc) ∧ (eval env x_var = x) →
    -- if the constraints hold
    Circuit.ConstraintsHold.Soundness env (step acc_var x_var |>.operations ((size State) + (size Input))) →
    -- and assuming the spec on the current row and previous inputs
    Spec initialState xs row_index xs_len acc env.data →
    -- we can conclude the spec on the next row and inputs including the current input
    Spec initialState (xs.concat x) (row_index + 1) (xs_len ▸ List.length_concat)
      (eval env (step acc_var x_var |>.output ((size State) + (size Input)))) env.data

def InductiveTable.Completeness (F : Type) [Field F] (State Input : Type → Type) [ProvableType State] [ProvableType Input]
    (InputAssumptions : ℕ → Input F → ProverData F → Prop)
    (InitialStateAssumptions : State F → ProverData F → Prop)
    (Spec : (initialState : State F) → (xs : List (Input F)) → (i : ℕ) → (xs.length = i) → (currentState : State F) → ProverData F → Prop)
    (step : Var State F → Var Input F → Circuit F (Var State F)) :=
  ∀ (initialState : State F) (row_index : ℕ) (env : Environment F),
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
  Circuit.ConstraintsHold.Completeness env (step acc_var x_var |>.operations ((size State) + (size Input)))

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
variable {F : Type} [Field F] {State Input : TypeMap} [ProvableType State] [ProvableType Input]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.Spec 0 input → table.Spec (N-1) output`

for any given public `input` and `ouput`.
-/

def inductiveConstraint (table : InductiveTable F State Input)
    (curr : Var (ProvablePair State Input) F) :
    TableConstraint 2 (ProvablePair State Input) F (Var (ProvablePair State Input) F) := do
  let (acc, x) := curr
  let output ← table.step acc x
  let next ← getNextRow
  let (output', _) := next
  output' === output
  return next

def equalityConstraint (Input : TypeMap) [ProvableType Input] (target : State F) : SingleRowConstraint (ProvablePair State Input) F := do
  let (actual, _) ← getCurrRow
  actual === (const target)

def tableConstraints (table : InductiveTable F State Input) (input_state output_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveConstraint,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
    .boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

theorem equalityConstraint.soundness_row {row : State F × Input F} {input_state : State F} {env : Environment F} :
  ConstraintHoldsOnRow (equalityConstraint Input input_state) row env
    ↔ row.1 = input_state := by
  simp only [ConstraintHoldsOnRow]
  set env' := TableConstraint.singleRowEnv (equalityConstraint Input input_state) row env
  simp only [equalityConstraint, circuit_norm, table_norm]
  -- goal: eval env' (varFromOffset State 0) = input_state ↔ row.1 = input_state
  have h_env_in i (hi : i < size State) : (toElements row.1)[i] = env'.get i := by
    have h_env' : env' = TableConstraint.singleRowEnv (equalityConstraint Input input_state) row env := rfl
    simp only [TableConstraint.singleRowEnv, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    have hi' : i < size State + size Input := by omega
    simp [h_env', hi, hi', Vector.getElem_mapFinRange, _root_.Row.get,
      Vector.mapRange_zero, Vector.append_empty, ProvablePair.instance]
  have h_env : eval env' (varFromOffset State 0) = row.1 := by
    rw [ProvableType.ext_iff]
    intro i hi
    rw [h_env_in i hi, ProvableType.eval_varFromOffset,
      ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]
  rw [h_env]

def traceInputs {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) : List (Input F) :=
  trace.val.toList.map Prod.snd

omit [Field F] in
lemma traceInputs_length {N : ℕ} (trace : TraceOfLength F (ProvablePair State Input) N) :
    (traceInputs trace).length = N := by
  rw [traceInputs, List.length_map, trace.val.toList_length, trace.prop]

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data →
  TableConstraintsHold (table.tableConstraints input output) trace.val env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1 env.data)
    ∧ trace.lastRow.1 = output := by
  intro input_spec

  -- Destructure TraceOfLength and generalize on the foldl's N parameter
  rcases trace with ⟨ trace, h_trace ⟩
  suffices goal : ∀ M, TableConstraintsHold.foldl M
      (tableConstraints table input output |>.mapIdx fun i cs => (cs, env.toEnvironment i))
      trace
      (tableConstraints table input output |>.mapIdx fun i cs => (cs, env.toEnvironment i)) →
    trace.ForAllRowsWithPrevious (fun row rest =>
      table.Spec input (traceInputs ⟨ rest, rfl ⟩) rest.len (traceInputs_length ⟨ rest, rfl ⟩) row.1 env.data)
    ∧ (∀ (_ : trace.len = M) (h_pos : trace.len > 0), (trace.lastRow h_pos).1 = output) by
      intro constraints
      simp only [TableConstraintsHold, table_norm, tableConstraints] at constraints
      have goal' := goal trace.len constraints
      exact ⟨ goal'.left, goal'.right rfl (h_trace ▸ N.pos) ⟩

  intro M
  clear h_trace
  simp only [table_norm, tableConstraints]
  induction trace using Trace.every_row_two_rows_induction

  case zero =>
    intro constraints
    simp only [Trace.ForAllRowsWithPrevious, true_and]
    intros _ h_pos; exact absurd h_pos (by simp [Trace.len])

  case one first_row =>
    intro constraints
    simp only [table_norm,
      List.size_toArray, List.length_nil, List.push_toArray, List.nil_append,
      List.length_cons, zero_add, List.cons_append, reduceIte, and_true,
      TableConstraintsHold.foldl] at constraints
    obtain ⟨ input_eq, output_eq ⟩ := constraints
    -- Convert the unfolded form back to ConstraintHoldsOnRow
    have input_eq' : ConstraintHoldsOnRow (equalityConstraint Input input) first_row (env.toEnvironment 1 0) := input_eq
    rw [equalityConstraint.soundness_row] at input_eq'
    simp only [table_norm, and_true, Trace.ForAllRowsWithPrevious]
    constructor
    · rw [input_eq']; exact input_spec
    · intro h_len _
      have output_eq' : ConstraintHoldsOnRow (equalityConstraint Input output) first_row (env.toEnvironment 2 0) := by
        simp only [Nat.sub_zero] at output_eq
        rwa [if_pos (by omega : 0 = M - 1)] at output_eq
      rw [equalityConstraint.soundness_row] at output_eq'
      exact output_eq'

  case more curr next rest ih1 ih2 =>
    intro constraints
    simp only [table_norm, List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero, one_ne_zero,
      and_false, reduceIte, tsub_zero,
      Nat.reduceAdd, true_and, Trace.ForAllRowsWithPrevious,
      TableConstraintsHold.foldl] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) curr.1 env.data := by
      simp [ih2]
    simp only [ih2, and_self, and_true]
    clear ih1 ih2

    -- TODO: The inductive step proof needs adaptation of the env mapping lemmas
    -- (h_env_input_1, h_env_input_2, h_env_output) for transitionEnv vs windowEnv.
    -- The proof structure is: extract step constraint from ConstraintHoldsOnStep,
    -- prove env' maps variables to row values, use table.soundness for the inductive step.
    sorry

theorem table_soundness (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data → TableConstraintsHold (table.tableConstraints input output) trace.val env →
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

  completeness := by
    intro N trace env _ _ _
    sorry

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_offset,
      Functor.map, StateT.map]

end InductiveTable
