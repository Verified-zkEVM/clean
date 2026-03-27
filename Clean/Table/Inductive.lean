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

/-- The wrapped form of inductiveConstraint used in ConstraintHoldsOnStep:
    getRowAssignOnly assigns current row vars without witnessing, then runs the constraint. -/
def wrappedInductiveConstraint (table : InductiveTable F State Input) :
    TwoRowsConstraint (ProvablePair State Input) F :=
  TableConstraint.getRowAssignOnly 0 >>= fun curr => table.inductiveConstraint curr >>= fun _ => pure ()

def tableConstraints (table : InductiveTable F State Input) (input_state output_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveConstraint,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
    .boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

theorem equalityConstraint.soundness_row {row : State F × Input F} {input_state : State F} {env : Environment F} :
  ConstraintHoldsOnRow (equalityConstraint Input input_state) row env
    ↔ row.1 = input_state := by
  simp only [ConstraintHoldsOnRow, TableConstraint.ConstraintsHoldOnWindow]
  set env' := windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm]
  have h_env_in i (hi : i < size State) : (toElements row.1)[i] = env'.get i := by
    have h_env' : env' = windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, _⟩ env := rfl
    simp only [windowEnv, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    have hi' : i < size State + size Input := by omega
    simp [h_env', hi, hi', Vector.getElem_mapFinRange, Trace.getLeFromBottom, _root_.Row.get,
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
    -- Unfold foldl but NOT ConstraintHoldsOnStep (we'll unfold that manually)
    simp only [ConstraintHoldsOnRow, TableConstraint.ConstraintsHoldOnWindow,
      List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero, one_ne_zero,
      and_false, reduceIte, tsub_zero,
      Nat.reduceAdd, true_and, Trace.ForAllRowsWithPrevious,
      TableConstraintsHold.foldl] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, output_boundary, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) curr.1 env.data := by
      simp [ih2]
    simp only [ih2, and_self, and_true]
    clear ih1 ih2

    -- constraints is ConstraintHoldsOnStep (folded); unfold step by step
    simp only [ConstraintHoldsOnStep, TableConstraint.ConstraintsHoldOnWindow] at constraints
    set wrapped : TwoRowsConstraint (ProvablePair State Input) F :=
      TableConstraint.getRowAssignOnly 0 >>= fun curr => table.inductiveConstraint curr >>= fun _ => pure ()
    set env' := windowEnv wrapped ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1))
    dsimp only [TableConstraint.ConstraintsHoldOnWindow, TableConstraint.operations,
      TableContext.empty] at constraints
    change Circuit.ConstraintsHold.Soundness env' (wrapped .empty).2.circuit at constraints
    -- Simplify the ops in constraints (env' stays opaque via set)
    simp only [wrapped, table_norm, circuit_norm, inductiveConstraint] at constraints
    -- Decompose constraints: step ops ∧ [witness (trivial), equality subcircuit]
    rcases Circuit.ConstraintsHold.append_soundness.mp constraints with ⟨ main_constraints, return_eq ⟩
    simp only [table_norm, circuit_norm] at return_eq
    -- Compute h_env' (same structure as old proof)
    have h_env' : env' = windowEnv wrapped ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1)) := rfl
    simp only [windowEnv, table_assignment_norm, inductiveConstraint, circuit_norm, wrapped,
      pure, StateT.pure] at h_env'
    simp only [zero_add, Nat.add_zero, Fin.isValue, PNat.val_ofNat, Nat.reduceAdd, Nat.add_one_sub_one,
      CellAssignment.assignmentFromCircuit_offset, CellAssignment.assignmentFromCircuit_vars] at h_env'
    set curr_var : Var State F × Var Input F := varFromOffset (ProvablePair State Input) 0
    set s := size State
    set x := size Input
    set main_ops : Operations F := (table.step (varFromOffset State 0) (varFromOffset Input s) (s + x)).2
    set t := main_ops.localLength

    -- The env mapping lemmas show that windowEnv maps variables to the expected row cells.
    -- These follow the same pattern as the old windowEnv proof but need dsimp for getLeFromBottom.
    -- env mapping: windowEnv maps variable indices to row cell values
    -- Verified by #eval: vars 0..s-1 → .input ⟨0, col⟩ → curr, vars s..s+x-1 → .input ⟨0, col⟩ → curr
    -- vars s+x+t..s+x+t+s-1 → .input ⟨1, col⟩ → next
    -- Proof needs: rw [h_env'], simp with reduceDIte + Vector.getElem_append/cast/mapFinRange,
    -- then dsimp [Trace.getLeFromBottom, Row.get]
    have h_env_input_1 i (hi : i < s) : (toElements curr.1)[i] = env'.get i := by
      sorry
    have h_env_input_2 i (hi : i < x) : (toElements curr.2)[i] = env'.get (i + s) := by
      sorry
    have h_env_output i (hi : i < s) : (toElements next.1)[i] = env'.get (i + (s + x) + t) := by
      sorry
    clear h_env'

    have input_eq_1 : eval env' curr_var.1 = curr.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, varFromOffset_pair]
      rw [h_env_input_1 i hi]
      simp only [ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]

    have input_eq_2 : eval env' curr_var.2 = curr.2 := by
      rw [ProvableType.ext_iff]
      intro i hi
      simp only [curr_var, varFromOffset_pair]
      rw [h_env_input_2 i hi]
      simp only [s, ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, Vector.getElem_mapRange, zero_add]
      ac_rfl

    have next_eq : eval env' (varFromOffset State (size State + size Input + main_ops.localLength)) = next.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [h_env_output i hi, ProvableType.eval_varFromOffset,
        ProvableType.toElements_fromElements, Vector.getElem_mapRange]
      simp only [t, s, x]
      ac_rfl

    simp only [x, s, Nat.zero_add] at main_constraints
    have constraints : Circuit.ConstraintsHold.Soundness
        env' ((table.step curr_var.1 curr_var.2).operations (size State + size Input)) := by
      simp only [curr_var, varFromOffset_pair, Nat.zero_add]
      exact main_constraints

    let xs := traceInputs ⟨ rest, rfl ⟩
    have xs_len := traceInputs_length ⟨ rest, rfl ⟩
    have xs_concat : traceInputs ⟨rest +> curr, rfl⟩ = xs.concat curr.2 := by
      simp only [traceInputs, xs, Trace.toList, List.map_concat]

    have h_soundness := table.soundness input rest.len env' curr_var.1 curr_var.2 curr.1 curr.2 xs xs_len
      ⟨ input_eq_1, input_eq_2 ⟩ constraints spec_previous
    simp only [curr_var, varFromOffset_pair] at h_soundness
    simp only [s, x, t, main_ops] at *
    simp +arith only at return_eq h_soundness
    rw [←return_eq, next_eq] at h_soundness
    simp only [xs_concat]
    use h_soundness

    intro h_len _
    have output_eq' : ConstraintHoldsOnRow (equalityConstraint Input output) next (env.toEnvironment 2 (rest.len + 1)) := by
      simp only [ConstraintHoldsOnRow, TableConstraint.ConstraintsHoldOnWindow]
      have h : (rest +> curr).len = M - 1 := by simp [Trace.len] at h_len ⊢; omega
      rwa [if_pos h] at output_boundary
    rw [equalityConstraint.soundness_row] at output_eq'
    exact output_eq'

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
  HonestProverAssumption trace env :=
    table.InitialStateAssumptions input env ∧
    trace.ForAllRowsOfTraceWithIndex (fun row i => table.InputAssumptions i row.2 env)
  Spec {N} trace env := table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output env

  soundness N trace env assumption constraints :=
    table.table_soundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  completeness := by
    intro N trace env _ _
    sorry

  offset_consistent := by
    simp +arith [List.Forall, tableConstraints, inductiveConstraint, equalityConstraint,
      table_assignment_norm, circuit_norm, CellAssignment.assignmentFromCircuit_offset,
      Functor.map, StateT.map]

end InductiveTable
