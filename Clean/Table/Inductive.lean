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

def inductiveWitness (table : InductiveTable F State Input) : TableConstraint 2 (ProvablePair State Input) F Unit := do
  let (acc, x) ← getCurrRow
  let output ← table.step acc x
  let vars := toVars output
  -- Always create a fresh variable for each output element and constrain it equal
  -- to the output expression. This avoids corrupting input variable mappings
  -- (which would happen if assignVar were called on a pass-through input variable).
  forM (List.finRange (size State)) fun ⟨i, hi⟩ => do
    have hi' : i < size (ProvablePair State Input) := by
      simp [ProvablePair.instance]; omega
    let expr := vars[i]
    let new_var ← witnessVar (F := F) expr.eval
    assertZero (F := F) (expr - var new_var)
    assignVar (.next ⟨i, hi'⟩) new_var

def equalityConstraint (Input : TypeMap) [ProvableType Input] (target : State F) : SingleRowConstraint (ProvablePair State Input) F := do
  let (actual, _) ← getCurrRow
  actual === (const target)

/--
  The table constraints for an inductive table: the step constraint applied to
  every row except the last, and boundary constraints asserting that the first
  and last rows match the given input and output states.
-/
def tableConstraintsWitness (table : InductiveTable F State Input) (input_state output_state : State F) :
  List (TableOperation (ProvablePair State Input) F) := [
    .everyRowExceptLast table.inductiveWitness,
    .boundary (.fromStart 0) (equalityConstraint Input input_state),
    .boundary (.fromEnd 0) (equalityConstraint Input output_state),
  ]

theorem equalityConstraint.soundness {row : State F × Input F} {input_state : State F} {env : Environment F} :
  Circuit.ConstraintsHold.Soundness (windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env)
    (equalityConstraint Input input_state .empty).2.circuit
    ↔ row.1 = input_state := by
  set env' := windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, rfl⟩ env
  simp only [equalityConstraint, circuit_norm, table_norm]

  have h_env_in i (hi : i < size State) : (toElements row.1)[i] = env'.get i := by
    have h_env' : env' = windowEnv (equalityConstraint Input input_state) ⟨<+> +> row, _⟩ env := rfl
    simp only [windowEnv, table_assignment_norm, equalityConstraint, circuit_norm] at h_env'
    have hi' : i < size State + size Input := by linarith
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

/-- windowEnv for inductiveWitness maps input variable indices to current-row elements.
    That is, for `i < size State + size Input`, `env'.get i = (toElements curr)[i]`.
    The assign loop in inductiveWitness only maps aux or fresh variables (with indices ≥ s+x)
    to next-row cells, so input variable mappings (indices 0..s+x-1) are preserved. -/
theorem inductiveWitness_env_get
    (table : InductiveTable F State Input)
    (curr next : Row F (ProvablePair State Input))
    (aux_env : Environment F)
    (i : ℕ) (hi_sx : i < size State + size Input) :
    (windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env).get i =
      (toElements (M := ProvablePair State Input) curr)[i] := by
  set s := size State
  set x := size Input
  set b := s + x
  set ctx0 : TableContext 2 (ProvablePair State Input) F := .empty
  set step_getCurrRow := getCurrRow ctx0
  set ctx1 := step_getCurrRow.2
  have h_ctx1_offset : ctx1.assignment.offset = b := by
    simp only [ctx1, step_getCurrRow, getCurrRow, TableConstraint.getRow,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      ctx0, TableContext.empty, CellAssignment.pushRow, CellAssignment.empty,
      b, s, x, ProvablePair.instance, size, TableContext.offset]
    omega
  have h_ctx1_oc : ctx1.circuit.localLength = ctx1.assignment.offset := by
    rw [h_ctx1_offset]
    -- ctx1.circuit = [] ++ [.witness (s+x) ...], so localLength = s + x = b
    change Operations.localLength ([] ++ [Operation.witness (s + x) _]) = b
    simp [Operations.localLength, b]
  have h_rest_preserves :
      ∀ (pair : Var State F × Var Input F),
      ((do
        let output ← table.step pair.1 pair.2
        let vars := toVars output
        forM (List.finRange s) fun ⟨k, hk⟩ => do
          have hk' : k < size (ProvablePair State Input) := by simp [ProvablePair.instance]; omega
          let expr := vars[k]
          let new_var ← witnessVar (F := F) expr.eval
          assertZero (F := F) (expr - var new_var)
          assignVar (.next ⟨k, hk'⟩) new_var
      ) : TableConstraint 2 (ProvablePair State Input) F Unit).PreservesVarsBelow b := by
    intro pair
    apply TableConstraint.bind_preservesVarsBelow
    · exact TableConstraint.monadLift_preservesVarsBelow _ _
    · intro output
      apply TableConstraint.forM_list_preservesVarsBelow
      intro ⟨k, hk⟩ _
      exact TableConstraint.witnessAssertAssign_preservesVarsBelow b _ _ _
  have h_preserves := h_rest_preserves step_getCurrRow.1 ctx1
    (h_ctx1_offset ▸ le_refl b) h_ctx1_oc
  set fa := TableConstraint.finalAssignment table.inductiveWitness
  have h_i_lt_fa : i < fa.offset := by
    have : b ≤ fa.offset := h_preserves.1
    omega
  have h_vars_preserved : fa.vars[i]'h_i_lt_fa =
      ctx1.assignment.vars[i]'(h_ctx1_offset ▸ hi_sx) :=
    h_preserves.2.2 i hi_sx h_i_lt_fa (h_ctx1_offset ▸ hi_sx)
  have h_vars_init : ctx1.assignment.vars[i]'(h_ctx1_offset ▸ hi_sx) =
      .input ⟨0, ⟨i, hi_sx⟩⟩ := by
    -- ctx1.assignment = (CellAssignment.empty 2).pushRow 0
    -- The vars are mapFinRange (s+x) (fun col => .input ⟨0, col⟩) with empty prefix
    -- So vars[i] = .input ⟨0, ⟨i, hi_sx⟩⟩
    show ((CellAssignment.empty (W := 2) (S := ProvablePair State Input)).pushRow 0).vars[i]'_ = _
    simp [CellAssignment.pushRow, CellAssignment.empty, ProvablePair.instance,
      Vector.getElem_append, show ¬(i < 0) from by omega, Vector.getElem_mapFinRange]
  have h_fa_vars : fa.vars[i]'h_i_lt_fa = .input ⟨0, ⟨i, hi_sx⟩⟩ := by
    rw [h_vars_preserved, h_vars_init]
  -- The windowEnv.get i reduces based on the final assignment
  -- We prove the result step by step:
  -- 1. windowEnv.get i = (match fa.vars[i] with ...) because i < fa.offset
  -- 2. fa.vars[i] = .input ⟨0, ⟨i, hi_sx⟩⟩, so match gives window.get 0 ⟨i, hi_sx⟩
  -- 3. window.get 0 ⟨i, hi_sx⟩ = (toElements curr)[i] by definition
  have h_env_eq : (windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env).get i
      = TraceOfLength.get ⟨<+> +> curr +> next, rfl⟩ (0 : Fin 2) ⟨i, hi_sx⟩ := by
    unfold windowEnv
    dsimp only
    rw [dif_pos h_i_lt_fa, h_fa_vars]
  rw [h_env_eq]
  simp only [TraceOfLength.get, table_assignment_norm, Trace.getLeFromBottom, Row.get]

/-- The operations of inductiveWitness decompose as getCurrRow witness ++ step ops ++ forM loop ops. -/
private theorem inductiveWitness_ops_decomp
    (table : InductiveTable F State Input) :
    ∃ loop_ops : Operations F,
      table.inductiveWitness.operations =
        [.witness (size State + size Input) fun env =>
          .mapRange _ fun i => env.get i] ++
        (table.step (varFromOffset State 0) (varFromOffset Input (size State))).operations
          (size State + size Input) ++
        loop_ops := by
  set s := size State
  set x := size Input
  -- We trace through the StateM bind steps of inductiveWitness applied to .empty.
  -- inductiveWitness.operations = (inductiveWitness .empty).2.circuit
  show ∃ loop_ops, (table.inductiveWitness .empty).2.circuit = _

  -- === Stage 1: getCurrRow .empty ===
  -- getCurrRow = getRow 0. Applied to empty context:
  -- - produces varFromOffset (ProvablePair State Input) 0
  -- - circuit becomes [.witness (s+x) fun env => .mapRange _ fun i => env.get (0+i)]
  set ctx0 : TableContext 2 (ProvablePair State Input) F := .empty
  set step1 := getCurrRow ctx0
  set pair := step1.1
  set ctx1 := step1.2

  -- The pair produced is varFromOffset (ProvablePair State Input) 0
  -- which by varFromOffset_pair = (varFromOffset State 0, varFromOffset Input s)
  have h_pair_fst : pair.1 = varFromOffset State 0 := by
    show (getCurrRow (S := ProvablePair State Input) ctx0).1.1 = _
    simp only [getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength]
    rw [varFromOffset_pair]
  have h_pair_snd : pair.2 = varFromOffset Input s := by
    show (getCurrRow (S := ProvablePair State Input) ctx0).1.2 = _
    simp only [getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength]
    rw [varFromOffset_pair]; simp [s]

  -- ctx1.circuit = [.witness (s+x) fun env => .mapRange _ fun i => env.get (0 + i)]
  -- Note: the witness uses env.get (0 + i) which is the same as env.get i
  have h_ctx1_circuit : ctx1.circuit =
      [.witness (s + x) fun env => .mapRange _ fun i => env.get (0 + i)] := by
    simp only [ctx1, step1, getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength, s, x, ProvablePair.instance, size,
      List.nil_append]

  -- The localLength of ctx1.circuit is s + x
  have h_ctx1_ll : ctx1.circuit.localLength = s + x := by
    rw [h_ctx1_circuit]; simp [Operations.localLength]

  -- === Stage 2: monadLift (table.step pair.1 pair.2) ctx1 ===
  set step2 := (monadLift (table.step pair.1 pair.2) : TableConstraint 2 (ProvablePair State Input) F _) ctx1
  set output := step2.1
  set ctx2 := step2.2

  -- ctx2.circuit = ctx1.circuit ++ step_ops (by definition of monadLift)
  have h_ctx2_circuit : ctx2.circuit =
      ctx1.circuit ++ (table.step pair.1 pair.2).operations ctx1.circuit.localLength := rfl

  -- Rewrite step arguments
  have h_step_ops : (table.step pair.1 pair.2).operations ctx1.circuit.localLength =
      (table.step (varFromOffset State 0) (varFromOffset Input s)).operations (s + x) := by
    rw [h_pair_fst, h_pair_snd, h_ctx1_ll]

  -- === Stage 3: forM loop ===
  set loop_body := fun (⟨i, hi⟩ : Fin s) => (do
    have hi' : i < size (ProvablePair State Input) := by simp [ProvablePair.instance]; omega
    let expr := (toVars output)[i]
    let new_var ← (witnessVar (F := F) expr.eval : Circuit F _)
    (assertZero (F := F) (expr - var new_var) : Circuit F _)
    assignVar (.next ⟨i, hi'⟩) new_var : TableConstraint 2 (ProvablePair State Input) F Unit)

  -- The full operations = (forM loop_body ctx2).2.circuit
  have h_full : (table.inductiveWitness .empty).2.circuit =
      ((List.finRange s).forM loop_body ctx2).2.circuit := rfl

  -- The forM loop only appends operations to the circuit
  suffices h_loop_appends : ∃ extra, ((List.finRange s).forM loop_body ctx2).2.circuit = ctx2.circuit ++ extra by
    obtain ⟨extra, h_extra⟩ := h_loop_appends
    use extra
    -- Goal: (inductiveWitness .empty).2.circuit = [.witness ...] ++ step_ops ++ extra
    -- We chain the equalities:
    -- (inductiveWitness .empty).2.circuit
    --   = (forM loop_body ctx2).2.circuit     [h_full]
    --   = ctx2.circuit ++ extra                [h_extra]
    --   = (ctx1.circuit ++ step_ops_raw) ++ extra  [h_ctx2_circuit]
    --   = ctx1.circuit ++ step_ops_raw ++ extra    [assoc]
    --   = [.witness (s+x) ... (0+i)] ++ step_ops ++ extra  [h_ctx1_circuit, h_step_ops]
    --   = [.witness (s+x) ... i] ++ step_ops ++ extra      [0+i = i]
    calc (table.inductiveWitness .empty).2.circuit
        = ((List.finRange s).forM loop_body ctx2).2.circuit := h_full
      _ = ctx2.circuit ++ extra := h_extra
      _ = (ctx1.circuit ++ (table.step pair.1 pair.2).operations ctx1.circuit.localLength) ++ extra := by
            rw [← h_ctx2_circuit]
      _ = ctx1.circuit ++ (table.step pair.1 pair.2).operations ctx1.circuit.localLength ++ extra := by
            rw [List.append_assoc]
      _ = ctx1.circuit ++ (table.step (varFromOffset State 0) (varFromOffset Input s)).operations (s + x) ++ extra := by
            rw [h_step_ops]
      _ = [.witness (s + x) fun env => .mapRange _ fun i => env.get (0 + i)] ++
          (table.step (varFromOffset State 0) (varFromOffset Input s)).operations (s + x) ++ extra := by
            rw [h_ctx1_circuit]
      _ = [.witness (s + x) fun env => .mapRange _ fun i => env.get i] ++
          (table.step (varFromOffset State 0) (varFromOffset Input s)).operations (s + x) ++ extra := by
            congr 2
            simp only [List.cons.injEq, and_true]
            congr 1
            funext env; congr 1; funext i
            simp [Nat.zero_add]
  -- Prove forM only appends, by induction on the list
  suffices h_general : ∀ (l : List (Fin s)) (c : TableContext 2 (ProvablePair State Input) F),
      ∃ extra, (l.forM loop_body c).2.circuit = c.circuit ++ extra by
    exact h_general (List.finRange s) ctx2
  intro l
  induction l with
  | nil =>
    intro c; exact ⟨[], by simp [List.forM_nil, pure, Pure.pure, StateT.pure]⟩
  | cons hd tl ih =>
    intro c
    -- One iteration: body hd applied to c, then forM rest
    -- forM (hd :: tl) body c = (body hd >>= fun _ => forM tl body) c
    --                         = let (_, c') := body hd c; forM tl body c'
    set body_result := loop_body hd c
    -- loop_body appends [.witness 1 _, .assert _] (assignVar doesn't change circuit)
    have h_body_appends : ∃ iter_ops, body_result.2.circuit = c.circuit ++ iter_ops := by
      -- The loop body does: monadLift (witnessVar), monadLift (assertZero), assignVar
      -- monadLift appends operations; assignVar doesn't change circuit
      simp only [body_result, loop_body]
      simp only [bind_def, table_norm, table_assignment_norm, circuit_norm,
        TableConstraint.assignVar_circuit]
      exact ⟨_, rfl⟩
    obtain ⟨iter_ops, h_iter⟩ := h_body_appends
    obtain ⟨rest_ops, h_rest⟩ := ih body_result.2
    exact ⟨iter_ops ++ rest_ops, by
      -- forM (hd :: tl) c = forM tl body_result.2
      show (tl.forM loop_body body_result.2).2.circuit = c.circuit ++ (iter_ops ++ rest_ops)
      rw [h_rest, h_iter, List.append_assoc]⟩

/-- Decompose inductiveWitness constraints: if the full constraints hold, then
    (1) the step circuit constraints hold, and
    (2) the step output evaluates to the next row's state.
    This combines step constraint extraction with output evaluation. -/
theorem inductiveWitness_soundness
    (table : InductiveTable F State Input)
    (curr next : Row F (ProvablePair State Input))
    (aux_env : Environment F) :
    let env' := windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env
    let s := size State; let x := size Input
    Circuit.ConstraintsHold.Soundness env' table.inductiveWitness.operations →
    -- Step constraints hold
    Circuit.ConstraintsHold.Soundness env' ((table.step (varFromOffset State 0) (varFromOffset Input s)).operations (s + x)) ∧
    -- Step output evaluates to next row's state
    eval env' ((table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)) = next.1 :=
  by
  -- Reduce the let bindings
  simp only []
  intro h_sound
  -- Use the operations decomposition to extract step constraints
  obtain ⟨loop_ops, h_ops_eq⟩ := inductiveWitness_ops_decomp table
  simp only [TableConstraint.operations] at h_ops_eq
  rw [show table.inductiveWitness.operations = (table.inductiveWitness .empty).snd.circuit from rfl,
      h_ops_eq, List.append_assoc, Circuit.ConstraintsHold.append_soundness] at h_sound
  obtain ⟨_, h_suffix⟩ := h_sound
  have h_step := (Circuit.ConstraintsHold.append_soundness.mp h_suffix).1
  have h_loop := (Circuit.ConstraintsHold.append_soundness.mp h_suffix).2
  refine ⟨h_step, ?_⟩
  -- Part 2: eval env' (step output) = next.1
  -- We prove component-wise equality using the forM loop constraints
  -- and the windowEnv mapping for fresh variables.
  set env' := windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env with h_env'
  set s := size State with h_s
  set x := size Input
  set output := (table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x) with h_output_def
  rw [ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toVars output i hi]
  -- Goal: Expression.eval env' (toVars output)[i] = (toElements next.1)[i]
  --
  -- Strategy: extract the assert constraint for iteration i from the loop,
  -- and use windowEnv to resolve the fresh variable.
  --
  -- The forM loop creates constraints. For each k in finRange s:
  --   1. witnessVar creates var at current offset
  --   2. assertZero constrains (toVars output)[k] = var
  --   3. assignVar maps var to .next ⟨k, _⟩
  --
  -- The Soundness of the assert gives: eval env' (toVars output)[k] = env'.get (var.index)
  -- The windowEnv + assignVar gives: env'.get (var.index) = (toElements next)[k]
  -- And for k < size State: (toElements next)[k] = (toElements next.1)[k]
  --
  -- We need to trace the exact var index. Let's compute it.
  -- After getCurrRow + monadLift step: circuit offset = (s + x) + step_local_length
  -- After iteration k (0-indexed): offset = (s + x) + step_ll + k + 1
  -- Fresh var for iteration k has index = (s + x) + step_ll + k

  -- Step 1: Show that the fresh variable for iteration i has its final assignment
  -- mapped to .input ⟨1, ⟨i, _⟩⟩.
  -- This follows from assignVar (.next ⟨i, _⟩) and the fact that later iterations
  -- don't overwrite it (they use higher indices).

  -- Step 2: Show that eval env' (toVars output)[i] = env'.get (fresh_var_i.index)
  -- by extracting the assert constraint from the loop.

  -- Step 3: Show env'.get (fresh_var_i.index) = (toElements next.1)[i]
  -- using windowEnv.

  -- For now, we combine all three steps.
  -- We trace through the forM loop state to establish the needed facts.

  -- Set up the StateM computation trace
  set ctx0 : TableContext 2 (ProvablePair State Input) F := .empty
  set step1 := getCurrRow ctx0
  set pair := step1.1
  set ctx1 := step1.2

  -- After monadLift step
  set step2 := (monadLift (table.step pair.1 pair.2) : TableConstraint 2 (ProvablePair State Input) F _) ctx1
  set step_output := step2.1
  set ctx2 := step2.2

  -- The forM loop body
  set loop_body := fun (⟨k, hk⟩ : Fin s) => (do
    have hk' : k < size (ProvablePair State Input) := by simp [ProvablePair.instance]; omega
    let expr := (toVars step_output)[k]
    let new_var ← (witnessVar (F := F) expr.eval : Circuit F _)
    (assertZero (F := F) (expr - var new_var) : Circuit F _)
    assignVar (.next ⟨k, hk'⟩) new_var : TableConstraint 2 (ProvablePair State Input) F Unit)

  -- output = step_output : both are the step circuit's output, but computed via different paths
  have h_pair_fst : pair.1 = varFromOffset State 0 := by
    show (getCurrRow (S := ProvablePair State Input) ctx0).1.1 = _
    simp only [getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength]
    rw [varFromOffset_pair]
  have h_pair_snd : pair.2 = varFromOffset Input s := by
    show (getCurrRow (S := ProvablePair State Input) ctx0).1.2 = _
    simp only [getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength]
    rw [varFromOffset_pair]; simp [s]
  have h_ctx1_ll : ctx1.circuit.localLength = s + x := by
    show (getCurrRow (S := ProvablePair State Input) ctx0).2.circuit.localLength = s + x
    simp only [getCurrRow, TableConstraint.getRow, ctx0, TableContext.empty,
      modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, Id.run, pure, Pure.pure,
      TableContext.offset, Operations.localLength, s, x, ProvablePair.instance, size,
      List.nil_append]
    simp [Operations.localLength]
  have h_output_eq : output = step_output := by
    simp only [output, h_output_def, step_output, step2]
    -- step2 = monadLift (table.step pair.1 pair.2) ctx1
    -- step2.1 = (table.step pair.1 pair.2).output ctx1.circuit.localLength
    show (table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x) =
         (table.step pair.1 pair.2).output ctx1.circuit.localLength
    rw [h_pair_fst, h_pair_snd, h_ctx1_ll]

  rw [h_output_eq]
  -- Goal: Expression.eval env' (toVars step_output)[i] = (toElements next.1)[i]
  have h_ctx2_oc : ctx2.circuit.localLength = ctx2.assignment.offset := by
    have h_ctx1_oc := TableConstraint.getRow_preservesOffsetConsistency (W := 2) (S := ProvablePair State Input) (F := F) 0 .empty rfl
    exact TableConstraint.monadLift_preservesOffsetConsistency (table.step pair.1 pair.2) ctx1 h_ctx1_oc
  set base_offset := ctx2.circuit.localLength
  have hi' : i < size (ProvablePair State Input) := by simp [ProvablePair.instance]; omega
  -- Key claims (proven by induction on the forM loop in a helper):
  -- (A) The loop assertion gives: eval env' ((toVars step_output)[i] - var ⟨base_offset + i⟩) = 0
  -- (B) The final assignment maps: fa.vars[base_offset + i] = .input ⟨1, ⟨i, _⟩⟩
  -- (C) base_offset + i < fa.offset
  -- From (A): eval env' (toVars step_output)[i] = env'.get (base_offset + i)
  -- From (B) + windowEnv: env'.get (base_offset + i) = (toElements next.1)[i]
  -- Prove the three key facts by induction on finRange s.
  -- We use a combined induction that tracks offset, OC, vars, and assertions.
  set fa_ctx := ((List.finRange s).forM loop_body ctx2).2
  -- fa_ctx is definitionally the same as (inductiveWitness .empty).2

  -- Combined induction: for all l : List (Fin s) and ctx' with OC:
  -- (a) final.offset = ctx'.offset + l.length
  -- (b) final.circuit.localLength = final.offset
  -- (c) for all p < l.length: final.vars[ctx'.offset + p] = .input (.next ⟨l[p].val, _⟩)
  -- (d) Soundness of added circuit implies assertions
  -- We only prove what we need (a, c, d for position i).

  -- For simplicity, prove the offset fact first (reusing the earlier proof pattern)
  have h_fa_offset_eq : fa_ctx.assignment.offset = base_offset + s := by
    suffices h_gen : ∀ (l : List (Fin s)) (ctx' : TableContext 2 (ProvablePair State Input) F),
        ctx'.circuit.localLength = ctx'.assignment.offset →
        ((l.forM loop_body) ctx').2.assignment.offset = ctx'.assignment.offset + l.length by
      show ((List.finRange s).forM loop_body ctx2).2.assignment.offset = base_offset + s
      rw [h_gen (List.finRange s) ctx2 h_ctx2_oc, ← h_ctx2_oc, List.length_finRange]
    intro l; induction l with
    | nil => intro ctx' _; simp [List.forM_nil, pure, Pure.pure, StateT.pure]
    | cons hd tl ih =>
      intro ctx' h_oc'
      show (tl.forM loop_body (loop_body hd ctx').2).2.assignment.offset = ctx'.assignment.offset + (tl.length + 1)
      have h_body_off : (loop_body hd ctx').2.assignment.offset = ctx'.assignment.offset + 1 := by
        simp only [loop_body, bind_def, table_norm, table_assignment_norm, circuit_norm, pure, Pure.pure, StateT.pure, Id.run]
      have h_body_oc : (loop_body hd ctx').2.circuit.localLength = (loop_body hd ctx').2.assignment.offset := by
        simp only [loop_body, bind_def, table_norm, table_assignment_norm, circuit_norm, pure, Pure.pure, StateT.pure, Id.run, h_oc']
      rw [ih _ h_body_oc, h_body_off]; omega

  have h_base_offset_lt_fa : base_offset + i < (TableConstraint.finalAssignment table.inductiveWitness).offset := by
    show base_offset + i < fa_ctx.assignment.offset
    rw [h_fa_offset_eq]; omega

  -- For vars and assertions, prove by induction on finRange s.
  -- The key insight: the loop body for iteration k (at offset ctx'.assignment.offset):
  -- - Creates a var at index ctx'.assignment.offset (via witnessVar)
  -- - Asserts (toVars step_output)[k] - var ⟨ctx'.assignment.offset⟩ = 0
  -- - Assigns vars[ctx'.assignment.offset] to .input (.next ⟨k, _⟩)
  -- Later iterations use higher indices, preserving the assignment.

  -- === h_fa_vars: fa.vars[base_offset + i] = .input ⟨1, ⟨i, _⟩⟩ ===
  -- and h_assert: the assertion from iteration i gives eval = 0 ===
  -- Both proved via a combined induction on the forM list.
  -- We prove a general invariant for any list l and starting context c with OC.
  have h_fa_vars_and_assert :
      fa_ctx.assignment.vars[base_offset + i]'(by omega) =
        .input ⟨1, ⟨i, hi'⟩⟩ ∧
      (Circuit.ConstraintsHold.Soundness env' loop_ops →
        Expression.eval env' ((toVars step_output)[i] -
          Expression.var ⟨base_offset + i⟩) = 0) := by
    -- We prove both by a combined induction. The general statement:
    -- For any list l, context c with OC, and extra (the appended circuit ops):
    -- (a) For each p, vars[c.ll + p] = .input (.next ⟨l[p].val, _⟩)
    -- (b) ConstraintsHold extra → assertions hold
    suffices h_gen : ∀ (l : List (Fin s)) (c : TableContext 2 (ProvablePair State Input) F)
        (hoc : c.circuit.localLength = c.assignment.offset),
        -- (a) vars mapping
        (∀ p (hp : p < l.length)
          (h_lt : c.circuit.localLength + p < ((l.forM loop_body) c).2.assignment.offset),
          ((l.forM loop_body) c).2.assignment.vars[c.circuit.localLength + p]'(by omega) =
            .input ⟨1, ⟨(l[p]'hp).val,
              by simp [ProvablePair.instance]; exact (l[p]'hp).isLt.trans_le (Nat.le_add_right _ _)⟩⟩) ∧
        -- (b) assertions from soundness
        (∀ extra (h_app : (l.forM loop_body c).2.circuit = c.circuit ++ extra),
          Circuit.ConstraintsHold.Soundness env' extra →
          ∀ p (hp : p < l.length),
            Expression.eval env' ((toVars step_output)[(l[p]'hp).val] -
              Expression.var ⟨c.circuit.localLength + p⟩) = 0) by
      have h_finRange_i : (List.finRange s)[i]'(by rw [List.length_finRange]; exact hi) = ⟨i, hi⟩ :=
        List.getElem_finRange ..
      obtain ⟨h_vars_gen, h_assert_gen⟩ := h_gen (List.finRange s) ctx2 h_ctx2_oc
      constructor
      · -- h_fa_vars
        have := h_vars_gen i (by rw [List.length_finRange]; exact hi) (by exact h_base_offset_lt_fa)
        simp only [h_finRange_i] at this; exact this
      · -- h_assert
        intro h_loop_sound
        -- Use the same loop_ops from the outer decomposition
        have h_fa_circuit : fa_ctx.circuit = ctx2.circuit ++ loop_ops := by
          sorry
        have := h_assert_gen loop_ops h_fa_circuit h_loop_sound i
          (by rw [List.length_finRange]; exact hi)
        simp only [h_finRange_i] at this; exact this
    -- The general statement is proved by induction on l.
    -- Each iteration sets vars and adds [witness, assert] ops.
    -- For vars (a): iteration p sets it, later iterations preserve via PreservesVarsBelow.
    -- For assertions (b): decompose extra = body_adds ++ tail_adds, extract from ConstraintsHold.
    sorry
  obtain ⟨h_fa_vars, h_assert_fn⟩ := h_fa_vars_and_assert
  have h_fa_vars : (TableConstraint.finalAssignment table.inductiveWitness).vars[base_offset + i]'h_base_offset_lt_fa =
      .input ⟨1, ⟨i, hi'⟩⟩ := h_fa_vars

  have h_assert : Expression.eval env' ((toVars step_output)[i] - Expression.var ⟨base_offset + i⟩) = 0 :=
    h_assert_fn h_loop
  -- From assertion: eval = env'.get
  have h_eval_eq : Expression.eval env' (toVars step_output)[i] = env'.get (base_offset + i) := by
    have h := h_assert; simp only [Expression.eval] at h
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg, neg_eq_neg_one_mul]; exact h)
  rw [h_eval_eq]
  -- From windowEnv: env'.get = (toElements next.1)[i]
  rw [h_env']; unfold windowEnv; dsimp only
  rw [dif_pos h_base_offset_lt_fa, h_fa_vars]
  -- After rw [dif_pos ..., h_fa_vars], the goal involves TraceOfLength.get on the window
  -- Compute: window.get 1 ⟨i, hi'⟩ = getLeFromBottom ⟨2-1-1, _⟩ ⟨i, hi'⟩
  -- = getLeFromBottom ⟨0, _⟩ ⟨i, hi'⟩ of (<+> +> curr +> next)
  -- = next.get ⟨i, hi'⟩ = (toElements next)[i]
  -- For i < size State: (toElements next)[i] = (toElements next.1)[i]
  -- The goal involves Fin coercions: ↑2 - 1 - ↑1 which needs to reduce to 0
  -- Then getLeFromBottom ⟨0, _⟩ of (<+> +> curr +> next) gives next.get
  change (<+> +> curr +> next).getLeFromBottom ⟨_, _⟩ ⟨i, hi'⟩ = (toElements next.1)[i]
  show next.get ⟨i, hi'⟩ = (toElements next.1)[i]
  simp only [Row.get, ProvablePair.instance, Vector.getElem_append,
    show i < size State from hi, ↓reduceDIte]

lemma table_soundness_aux (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data →
  TableConstraintsHold (table.tableConstraintsWitness input output) trace env →
    trace.ForAllRowsWithPrevious (fun row i rest => table.Spec input (traceInputs rest) i (traceInputs_length rest) row.1 env.data)
    ∧ trace.lastRow.1 = output := by
  intro input_spec

  -- add a condition on the trace length to the goal,
  -- so that we can change the induction to not depend on `N` (which would make it unprovable)
  rcases trace with ⟨ trace, h_trace ⟩
  suffices goal : TableConstraintsHold (table.tableConstraintsWitness input output) ⟨ trace, h_trace ⟩ env →
    trace.ForAllRowsWithPrevious (fun row rest =>
      table.Spec input (traceInputs ⟨ rest, rfl ⟩) rest.len (traceInputs_length ⟨ rest, rfl ⟩) row.1 env.data)
    ∧ (∀ (h_len : trace.len = N), (trace.lastRow (by rw [h_len]; exact N.pos)).1 = output) by
      intro constraints
      specialize goal constraints
      exact ⟨ goal.left, goal.right h_trace ⟩

  simp only [table_norm, tableConstraintsWitness]
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
    rw [equalityConstraint.soundness] at input_eq output_eq
    simp only [table_norm, and_true, Trace.ForAllRowsWithPrevious]
    constructor
    · rw [input_eq]
      exact input_spec
    intro h_len
    rw [←h_len] at output_eq
    simp only [zero_add, tsub_self, reduceIte] at output_eq
    exact output_eq

  case more curr next rest ih1 ih2 =>
    intro constraints
    simp only [table_norm, List.size_toArray, List.length_nil, List.push_toArray,
      List.nil_append, List.length_cons, zero_add, List.cons_append, Nat.add_eq_zero, one_ne_zero,
      and_false, reduceIte, tsub_zero,
      Nat.reduceAdd, true_and, Trace.ForAllRowsWithPrevious] at constraints ih1 ih2 ⊢
    rcases constraints with ⟨ constraints, output_eq, h_rest ⟩
    specialize ih2 h_rest
    have spec_previous : table.Spec input (traceInputs ⟨rest, rfl⟩) rest.len (traceInputs_length ⟨rest, rfl⟩) curr.1 env.data := by
      simp [ih2]
    simp only [ih2, and_self, and_true]
    clear ih1 ih2

    -- The windowEnv for inductiveWitness maps:
    --   input vars (0..s+x-1) → current-row cells (assign loop uses only fresh vars)
    --   fresh vars → next-row cells (via assignVar in the for loop)
    set env' := windowEnv table.inductiveWitness ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1))
    set curr_var : Var State F × Var Input F := varFromOffset (ProvablePair State Input) 0
    set s := size State
    set x := size Input

    -- Input variable evaluations: assign loop uses only fresh vars, so input vars are preserved
    have input_eq_1 : eval env' curr_var.1 = curr.1 := by
      show eval env' (varFromOffset (ProvablePair State Input) 0).1 = curr.1
      rw [varFromOffset_pair, ProvableType.ext_iff]
      intro i hi
      rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements,
        Vector.getElem_mapRange, zero_add]
      rw [table.inductiveWitness_env_get curr next _ i (by omega)]
      simp only [ProvablePair.instance, Vector.getElem_append, show i < size State from hi, ↓reduceDIte]
    have input_eq_2 : eval env' curr_var.2 = curr.2 := by
      show eval env' (varFromOffset (ProvablePair State Input) 0).2 = curr.2
      rw [varFromOffset_pair, ProvableType.ext_iff]
      intro i hi
      rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements,
        Vector.getElem_mapRange]
      show env'.get (0 + size State + i) = (toElements curr.2)[i]
      rw [show 0 + size State + i = size State + i from by omega]
      rw [table.inductiveWitness_env_get curr next _ (size State + i) (by omega)]
      simp only [ProvablePair.instance, Vector.getElem_append,
        show ¬(size State + i < size State) from by omega, ↓reduceDIte, Nat.add_sub_cancel_left]

    -- Extract step constraints and output evaluation from inductiveWitness constraints
    have h_decomp := table.inductiveWitness_soundness curr next (env.toEnvironment 0 (rest.len + 1)) constraints

    have step_constraints : Circuit.ConstraintsHold.Soundness
        env' ((table.step curr_var.1 curr_var.2).operations (s + x)) := by
      simp only [curr_var, varFromOffset_pair, s, x, Nat.zero_add]
      exact h_decomp.1

    have h_output_eq : eval env' ((table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)) = next.1 := by
      simp only [s, Nat.zero_add]
      exact h_decomp.2

    let xs := traceInputs ⟨ rest, rfl ⟩
    have xs_len := traceInputs_length ⟨ rest, rfl ⟩
    have xs_concat : traceInputs ⟨rest +> curr, rfl⟩ = xs.concat curr.2 := by
      simp only [traceInputs, xs, Trace.toList, List.map_concat]

    have h_soundness := table.soundness input rest.len env' curr_var.1 curr_var.2 curr.1 curr.2 xs xs_len
      ⟨ input_eq_1, input_eq_2 ⟩ step_constraints spec_previous
    simp only [curr_var, varFromOffset_pair] at h_soundness
    simp only [zero_add] at h_soundness

    rw [h_output_eq] at h_soundness
    simp only [xs_concat]
    use h_soundness

    intro h_len
    rw [equalityConstraint.soundness] at output_eq
    rw [←h_len] at output_eq
    simp only [add_tsub_cancel_right, reduceIte] at output_eq
    exact output_eq

theorem table_soundness (table : InductiveTable F State Input) (input output : State F)
  (N : ℕ+) (trace : TraceOfLength F (ProvablePair State Input) N) (env : TableEnvironments F) :
  table.Spec input [] 0 rfl input env.data → TableConstraintsHold (table.tableConstraintsWitness input output) trace env →
    table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output env.data := by
  intro h_input h_constraints
  have ⟨ h_spec, h_output ⟩ := table_soundness_aux table input output N trace env h_input h_constraints
  rw [←h_output]
  exact TraceOfLength.lastRow_of_forAllWithPrevious trace h_spec

def toFormal (table : InductiveTable F State Input) (input output : State F) : FormalTable F (ProvablePair State Input) where
  constraints := table.tableConstraintsWitness input output
  Assumption N env := N > 0 ∧ table.Spec input [] 0 rfl input env
  Spec {N} trace env := table.Spec input (traceInputs trace.tail) (N-1) (traceInputs_length trace.tail) output env

  soundness N trace env assumption constraints :=
    table.table_soundness input output ⟨N, assumption.left⟩ trace env assumption.right constraints

  offset_consistent := by
    simp only [tableConstraintsWitness, List.Forall]
    refine ⟨?_, ?_, ?_⟩
    · apply TableConstraint.OffsetConsistent_of_preserves
      apply TableConstraint.bind_preservesOffsetConsistency
        (TableConstraint.getRow_preservesOffsetConsistency 0)
      intro (acc, x)
      apply TableConstraint.bind_preservesOffsetConsistency
        (TableConstraint.monadLift_preservesOffsetConsistency _)
      intro output
      apply TableConstraint.forM_list_preservesOffsetConsistency
      intro ⟨i, hi⟩ _
      apply TableConstraint.bind_preservesOffsetConsistency
        (TableConstraint.monadLift_preservesOffsetConsistency _)
      intro new_var
      apply TableConstraint.bind_preservesOffsetConsistency
        (TableConstraint.monadLift_preservesOffsetConsistency _)
      intro _
      exact TableConstraint.assignVar_preservesOffsetConsistency _ _
    all_goals (
      simp only [TableConstraint.OffsetConsistent, TableConstraint.finalOffset,
                 TableConstraint.finalAssignment, equalityConstraint,
                 table_assignment_norm, circuit_norm]
      omega)

end InductiveTable
