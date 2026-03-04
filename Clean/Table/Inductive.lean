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

  /-- Every element of the step output is a bare variable with index in
      `[size State + size Input, size State + size Input + localLength)`, and distinct output
      positions have distinct variable indices.
      This ensures `setVarInput` in `inductiveWitness` correctly maps output variables to
      next-row cells, and doesn't corrupt input variable mappings. -/
  outputFreshVars :
      let s := size State; let x := size Input
      let output := (step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)
      let n := (step (varFromOffset State 0) (varFromOffset Input s)).localLength (s + x)
      -- (1) Every output element is a bare variable with index in [s+x, s+x+n)
      (∀ (i : ℕ) (hi : i < s),
        ∃ (v : Variable F), (toVars output)[i] = .var v ∧ v.index ≥ s + x ∧ v.index < s + x + n) ∧
      -- (2) Distinct output positions have distinct variable indices
      (∀ (i j : ℕ) (hi : i < s) (hj : j < s), i ≠ j →
        ∀ (v w : Variable F), (toVars output)[i] = .var v → (toVars output)[j] = .var w →
          v.index ≠ w.index)
    := by
      constructor
      · intro i hi; simp only [circuit_norm]; exact ⟨_, rfl, by omega, by omega⟩
      · intros; simp_all [circuit_norm]; omega

/-- Derive `outputFreshVars` from explicit output variable indices.
    Apply after `simp only [circuit_norm, ...]` has reduced the output vector and bounds.
    The user supplies `indices` mapping each output position to its variable index,
    proves they match the reduced output (`h_eq`), and the rest follows automatically. -/
theorem InductiveTable.outputFreshVars_of_indices
    {F : Type} [Field F] {s : ℕ}
    (elems : Vector (Expression F) s)
    (lower upper : ℕ)
    (indices : Fin s → ℕ)
    (h_eq : ∀ (i : ℕ) (hi : i < s), elems[i] = .var ⟨indices ⟨i, hi⟩⟩)
    (h_fresh : ∀ i, indices i ≥ lower)
    (h_bound : ∀ i, indices i < upper)
    (h_injective : Function.Injective indices) :
    (∀ (i : ℕ) (hi : i < s),
      ∃ (v : Variable F), elems[i] = .var v ∧ v.index ≥ lower ∧ v.index < upper) ∧
    (∀ (i j : ℕ) (hi : i < s) (hj : j < s), i ≠ j →
      ∀ (v w : Variable F), elems[i] = .var v → elems[j] = .var w →
        v.index ≠ w.index) :=
  ⟨fun i hi => ⟨⟨indices ⟨i, hi⟩⟩, h_eq i hi, h_fresh ⟨i, hi⟩, h_bound ⟨i, hi⟩⟩,
   fun i j hi hj hij v w hv hw heq => by
    have h1 := (h_eq i hi).symm.trans hv
    have h2 := (h_eq j hj).symm.trans hw
    simp only [Expression.var.injEq] at h1 h2
    subst h1; subst h2
    exact hij (congrArg Fin.val (h_injective heq))⟩

/-- Specialization when output variables are consecutive: base, base+1, ..., base+s-1. -/
theorem InductiveTable.outputFreshVars_of_consecutive
    {F : Type} [Field F] {s : ℕ}
    (elems : Vector (Expression F) s)
    (lower upper : ℕ)
    (base : ℕ)
    (h_eq : ∀ (i : ℕ) (hi : i < s), elems[i] = .var ⟨base + i⟩)
    (h_ge : base ≥ lower)
    (h_lt : base + s ≤ upper) :
    (∀ (i : ℕ) (hi : i < s),
      ∃ (v : Variable F), elems[i] = .var v ∧ v.index ≥ lower ∧ v.index < upper) ∧
    (∀ (i j : ℕ) (hi : i < s) (hj : j < s), i ≠ j →
      ∀ (v w : Variable F), elems[i] = .var v → elems[j] = .var w →
        v.index ≠ w.index) :=
  outputFreshVars_of_indices elems lower upper (fun i => base + i.val)
    (fun i hi => by rw [h_eq i hi])
    (fun i => by show base + i.val ≥ _; omega)
    (fun i => by show base + i.val < _; have := i.isLt; omega)
    (fun a b h => by dsimp at h; ext; omega)

namespace InductiveTable
variable {F : Type} [Field F] {State Input : TypeMap} [ProvableType State] [ProvableType Input]

/-
we show that every `InductiveTable` can be used to define a `FormalTable`,
that encodes the following statement:

`table.Spec 0 input → table.Spec (N-1) output`

for any given public `input` and `ouput`.
-/

/-- The assignment pairs: maps each output element to its next-row cell offset and variable index -/
def inductiveWitnessPairs (table : InductiveTable F State Input) :
    List (CellOffset 2 (ProvablePair State Input) × ℕ) :=
  let s := size State; let x := size Input
  let output := (table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)
  let elems := toVars output
  (List.finRange s).map fun ⟨i, hi⟩ =>
    have hi' : i < s + x := Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
    (.next ⟨i, hi'⟩, (elems[i]'hi).toVar.index)

def inductiveWitness (table : InductiveTable F State Input) : TableConstraint 2 (ProvablePair State Input) F Unit := do
  let (acc, x) ← getCurrRow
  let _output ← table.step acc x
  modify fun ctx =>
    let assignment := table.inductiveWitnessPairs.foldl
      (fun a p => a.setVarInput p.1 p.2) ctx.assignment
    { ctx with assignment }

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

set_option maxHeartbeats 3200000 in
/-- windowEnv for inductiveWitness maps input variable indices to current-row elements.
    That is, for `i < size State + size Input`, `env'.get i = (toElements curr)[i]`. -/
theorem inductiveWitness_env_get
    (table : InductiveTable F State Input)
    (curr next : Row F (ProvablePair State Input))
    (aux_env : Environment F)
    (i : ℕ) (hi_sx : i < size State + size Input) :
    (windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env).get i =
      (toElements (M := ProvablePair State Input) curr)[i] := by

  have h_fresh := table.outputFreshVars
  have h_pairs_ne : ∀ pair ∈ table.inductiveWitnessPairs, pair.2 ≠ i := by
    intro ⟨off, idx⟩ h_mem
    simp only [InductiveTable.inductiveWitnessPairs, List.mem_map, List.mem_finRange] at h_mem
    obtain ⟨⟨j, hj⟩, _, h_eq⟩ := h_mem
    have h_eq' := congr_arg Prod.snd h_eq
    simp only at h_eq'
    obtain ⟨v, hv_eq, hv_ge, _⟩ := h_fresh.1 j hj
    have : (toVars ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
      (size State + size Input)))[j].toVar.index ≥ size State + size Input := by
      rw [hv_eq]; simp [Expression.toVar]; exact hv_ge
    omega

  simp only [windowEnv, TableConstraint.finalAssignment, InductiveTable.inductiveWitness,
    table_norm, circuit_norm, pure, Pure.pure,
    TableConstraint.getRow, TableConstraint.getCurrRow,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    modify, bind_def, liftM, monadLift, MonadLift.monadLift,
    CellAssignment.setVarInput_foldl_offset, CellAssignment.assignmentFromCircuit_offset,
    CellAssignment.pushRow, CellAssignment.empty, ProvablePair.instance]
  simp only [show i < 0 + (size State + size Input) +
    Operations.localLength (table.step (varFromOffset State 0) (varFromOffset Input (0 + size State))
      (size State + size Input)).2 from by omega, ↓reduceDIte]
  rw [CellAssignment.setVarInput_foldl_preserves _ _ _ (by
    rw [CellAssignment.assignmentFromCircuit_offset]
    simp only [CellAssignment.pushRow, CellAssignment.empty, ProvablePair.instance]; omega) h_pairs_ne]
  simp only [CellAssignment.assignmentFromCircuit_vars, Vector.getElem_cast,
    ProvablePair.instance, Vector.getElem_append,
    show i < 0 + (size State + size Input) from by omega,
    show ¬(i < 0) from by omega,
    ↓reduceDIte, Nat.sub_zero, Vector.getElem_mapFinRange]
  simp only [TraceOfLength.get, PNat.val_ofNat, Nat.reduceSub, Fin.val_zero,
    Trace.getLeFromBottom, Row.get, Vector.getElem_append]

/-- windowEnv for inductiveWitness maps output variables to next-row elements.
    For each output element `i < size State`, if `(toVars output)[i] = .var v`, then
    `env'.get v.index = (toElements next)[i]`. -/
theorem inductiveWitness_env_get_output
    (table : InductiveTable F State Input)
    (curr next : Row F (ProvablePair State Input))
    (aux_env : Environment F)
    (i : ℕ) (hi : i < size State) :
    let s := size State; let x := size Input
    let output := (table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)
    let v := (toVars output)[i]'(by show i < size State; exact hi)
    (windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env).get v.toVar.index =
      (toElements next.1)[i] := by
  -- introduce the let bindings
  simp only []
  -- get the output variable info from outputFreshVars
  obtain ⟨v, hv_eq, hv_ge, hv_lt⟩ := table.outputFreshVars.1 i hi
  -- rewrite using the variable equality
  show (windowEnv table.inductiveWitness ⟨<+> +> curr +> next, rfl⟩ aux_env).get
    ((toVars ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
      (size State + size Input)))[i]).toVar.index = (toElements next.1)[i]
  rw [hv_eq]; simp only [Expression.toVar]
  -- Now need: env'.get v.index = (toElements next.1)[i]
  -- Unfold windowEnv + finalAssignment
  simp only [windowEnv, TableConstraint.finalAssignment, InductiveTable.inductiveWitness,
    table_norm, circuit_norm, pure, Pure.pure,
    TableConstraint.getRow, TableConstraint.getCurrRow,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    modify, bind_def, liftM, monadLift, MonadLift.monadLift,
    CellAssignment.setVarInput_foldl_offset, CellAssignment.assignmentFromCircuit_offset,
    CellAssignment.pushRow, CellAssignment.empty, ProvablePair.instance]
  -- Show v.index < offset for the dite branch
  have h_bound : v.index < 0 + (size State + size Input) +
      Operations.localLength
        (table.1 (varFromOffset State 0) (varFromOffset Input (0 + size State))
          (size State + size Input)).2 := by
    simp only [Nat.zero_add, Circuit.localLength] at hv_lt ⊢
    exact hv_lt
  rw [dif_pos h_bound]
  -- Prove vars[v.index] = .input (.next ⟨i, _⟩) using setVarInput_foldl_at
  have h_pairs_len : table.inductiveWitnessPairs.length = size State := by
    simp [inductiveWitnessPairs, List.length_map, List.length_finRange]
  have h_pairs_i : (table.inductiveWitnessPairs[i]'(by omega)) =
      (CellOffset.next ⟨i, by show i < size State + size Input; omega⟩, v.index) := by
    simp only [inductiveWitnessPairs, List.getElem_map, List.getElem_finRange]
    exact Prod.ext rfl (by
      show ((toVars ((table.step (varFromOffset State 0) (varFromOffset Input (size State))).output
        (size State + size Input)))[i]).toVar.index = v.index
      rw [hv_eq]; simp [Expression.toVar])
  have h_nodup : ∀ (a b : ℕ) (ha : a < table.inductiveWitnessPairs.length)
      (hb : b < table.inductiveWitnessPairs.length),
      a ≠ b → (table.inductiveWitnessPairs[a]'ha).2 ≠ (table.inductiveWitnessPairs[b]'hb).2 := by
    intro a b ha hb hab
    have ha' : a < size State := by omega
    have hb' : b < size State := by omega
    obtain ⟨va, hva_eq, _, _⟩ := table.outputFreshVars.1 a ha'
    obtain ⟨vb, hvb_eq, _, _⟩ := table.outputFreshVars.1 b hb'
    have h_ne : va.index ≠ vb.index := table.outputFreshVars.2 a b ha' hb' hab va vb hva_eq hvb_eq
    simp only [inductiveWitnessPairs, List.getElem_map, List.getElem_finRange]
    simp only [Fin.coe_cast]
    rw [hva_eq, hvb_eq]; simp only [Expression.toVar]
    exact h_ne
  rw [CellAssignment.setVarInput_foldl_at table.inductiveWitnessPairs _
    (.next ⟨i, by show i < size State + size Input; omega⟩) v.index i
    (by omega) h_pairs_i h_nodup (by
      rw [CellAssignment.assignmentFromCircuit_offset]
      simp only [varFromOffset_pair, Nat.zero_add, Nat.add_zero]
      exact hv_lt)]
  simp only [TraceOfLength.get, CellOffset.next, Fin.val_one, PNat.val_ofNat, Nat.reduceSub,
    Trace.getLeFromBottom, Row.get, ProvablePair.instance, Vector.getElem_append,
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

    -- Use inductiveWitness instead of inductiveConstraint.
    -- The windowEnv for inductiveWitness maps:
    --   input vars (0..s+x-1) → current-row cells (preserved by outputFreshVars)
    --   output vars (≥ s+x) → next-row cells (via setVarInput in the for loop)
    set env' := windowEnv table.inductiveWitness ⟨<+> +> curr +> next, _⟩ (env.toEnvironment 0 (rest.len + 1))
    set curr_var : Var State F × Var Input F := varFromOffset (ProvablePair State Input) 0
    set s := size State
    set x := size Input

    -- Input variable evaluations: outputFreshVars ensures setVarInput doesn't corrupt input vars
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

    -- Step constraints: extractable from the inductiveWitness constraints
    -- (inductiveWitness.operations = getCurrRow witness op ++ step ops ++ assign ops,
    --  and ConstraintsHold on the full ops implies ConstraintsHold on the step ops)
    have step_constraints : Circuit.ConstraintsHold.Soundness
        env' ((table.step curr_var.1 curr_var.2).operations (s + x)) := by
      simp only [curr_var, varFromOffset_pair, s, x]
      simp only [table_norm, circuit_norm, inductiveWitness,
        TableConstraint.assignVar_circuit] at constraints
      exact constraints

    let xs := traceInputs ⟨ rest, rfl ⟩
    have xs_len := traceInputs_length ⟨ rest, rfl ⟩
    have xs_concat : traceInputs ⟨rest +> curr, rfl⟩ = xs.concat curr.2 := by
      simp only [traceInputs, xs, Trace.toList, List.map_concat]

    have h_soundness := table.soundness input rest.len env' curr_var.1 curr_var.2 curr.1 curr.2 xs xs_len
      ⟨ input_eq_1, input_eq_2 ⟩ step_constraints spec_previous
    simp only [curr_var, varFromOffset_pair] at h_soundness
    simp only [zero_add] at h_soundness

    -- Output mapping: step output evaluates to next-row values via setVarInput
    have h_output_eq : eval env' ((table.step (varFromOffset State 0) (varFromOffset Input s)).output (s + x)) = next.1 := by
      rw [ProvableType.ext_iff]
      intro i hi
      rw [← ProvableType.getElem_eval_toElements]
      obtain ⟨v, hv_eq, _, _⟩ := table.outputFreshVars.1 i hi
      -- rewrite the expression to .var v and reduce eval
      show Expression.eval env' (toVars _)[i] = _
      rw [hv_eq]; simp only [Expression.eval]
      -- now need: env'.get v.index = (toElements next.1)[i]
      have h_get := inductiveWitness_env_get_output table curr next (env.toEnvironment 0 (rest.len + 1)) i hi
      simp only [hv_eq, Expression.toVar] at h_get
      exact h_get

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
    · unfold TableConstraint.OffsetConsistent TableConstraint.finalOffset TableConstraint.finalAssignment
        InductiveTable.inductiveWitness getCurrRow TableConstraint.getRow
      dsimp only [modifyGet, MonadStateOf.modifyGet, Bind.bind, StateT.bind,
                  StateT.modifyGet, Id.pure_eq, modify]
      simp only [CellAssignment.setVarInput_foldl_offset,
                 CellAssignment.assignmentFromCircuit_offset, CellAssignment.pushRow_offset,
                 Operations.append_localLength, Operations.localLength]
      omega
    all_goals (
      simp only [TableConstraint.OffsetConsistent, TableConstraint.finalOffset,
                 TableConstraint.finalAssignment, equalityConstraint,
                 table_assignment_norm, circuit_norm]
      omega)

end InductiveTable
