module

public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Air.GenerationCompletenessProof

@[expose] public section

/-!
# Completeness of FemtoCairo witness generation

From memory values on which the program halts with the public registers, witness generation returns
a valid witness.
-/

namespace Examples.FemtoCairo.FlatAir.Witness

open Air.Flat Air.Flat.WitnessGeneration
open Examples.FemtoCairo Examples.FemtoCairo.Types

/-! ### Validation -/

lemma fetch_readsBelow {p : ℕ} [Fact p.Prime] {programSize : ℕ}
    (program : Fin programSize → F p) (h_programSize : programSize < p) (m n : ℕ) (hmn : m = n)
    (pc : Expression (F p)) (h : expressionReadsBelow n pc = true) :
    flatReadsBelow m (Operations.toFlat ((fetchInstruction program h_programSize).main pc n).2) =
      true := by
  subst m
  have hmono : ∀ m, n ≤ m → expressionReadsBelow m pc = true :=
    fun _ hm => expressionReadsBelow_mono hm h
  simp [fetchInstruction, flatReadsBelow, witgenReadsBelow, Witgen.WitgenIR.ofFExpr,
    vexprReadsBelow, fexprReadsBelow, u64exprReadsBelow,
    fexprListReadsBelow_map_const, circuit_norm, hmono]
  exact ⟨hmono _ (by omega), hmono _ (by omega)⟩

lemma decode_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n)
    (x : Expression (F p)) (h : expressionReadsBelow n x = true) :
    flatReadsBelow m (Operations.toFlat (Examples.FemtoCairo.decodeInstruction.main x n).2) =
      true := by
  subst m
  have hmono : ∀ m, n ≤ m → expressionReadsBelow m x = true :=
    fun _ hm => expressionReadsBelow_mono hm h
  simp [Examples.FemtoCairo.decodeInstruction, Examples.FemtoCairo.decodeInstructionMain,
    Gadgets.toBits, Gadgets.ToBits.main, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Utils.Bits.fieldFromBitsExpr,
    flatReadsBelow, witgenReadsBelow,
    vexprReadsBelow, fexprReadsBelow,
    circuit_norm, explicit_provable_type, hmono]

lemma dataGet_value {p : ℕ} (row : Witgen.U64Expr (F p)) :
    (Witgen.dataGet "memory" ProviderInput row).value = .dataGet "memory" 3 row 1 := by
  have h := congrArg (fun v => v[1]) (ProvableType.toElements_fromElements (M := ProviderInput)
    (Vector.mapFinRange (size ProviderInput) fun col =>
      Witgen.FExpr.dataGet (F := F p) "memory" (size ProviderInput) row col))
  simp only [Witgen.dataGet]
  simp [explicit_provable_type, circuit_norm, Vector.mapFinRange, Vector.finRange_succ,
    Vector.extract, Vector.map, Vector.toArray_mk,
    List.map_toArray]
  split
  rename_i x _ heq
  have := congrArg Vector.toList heq
  have hcols : ((#v[0] : Vector (Fin 3) 1) ++ (#v[1, 2] : Vector (Fin 3) 2)).toArray.toList =
      [0, 1, 2] := rfl
  simp [hcols] at this
  exact this.symm

lemma read_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n)
    (input : Var MemoryReadInput (F p))
    (h : ∀ e ∈ [input.state.pc, input.state.ap, input.state.fp, input.offset,
      input.mode.isDoubleAddressing, input.mode.isApRelative, input.mode.isFpRelative,
      input.mode.isImmediate], expressionReadsBelow n e = true) :
    flatReadsBelow m (Operations.toFlat (readFromMemory.main input n).2) = true := by
  subst m
  obtain ⟨⟨pc, ap, fp⟩, offset, ⟨m1, m2, m3, m4⟩⟩ := input
  have hmono : ∀ e ∈ [pc, ap, fp, offset, m1, m2, m3, m4], ∀ m, n ≤ m →
      expressionReadsBelow m e = true := fun e he _ hm => expressionReadsBelow_mono hm (h e he)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hmono
  obtain ⟨hpc, hap, hfp, hoffset, hm1, hm2, hm3, hm4⟩ := hmono
  simp [hap, hfp, hoffset, hm1, hm2, hm3,
    readFromMemory, flatReadsBelow, witgenReadsBelow, Witgen.WitgenIR.ofFExpr,
    Gadgets.Equality.circuit, Gadgets.Equality.main, FormalAssertion.toSubcircuit,
    Operations.toNested_toFlat, Circuit.forEach, vexprReadsBelow,
    fexprReadsBelow, u64exprReadsBelow, expressionReadsBelow, dataGet_value, circuit_norm,
    explicit_provable_type]
  and_intros <;> first
    | omega
    | exact hm1 _ (by omega) | exact hm2 _ (by omega) | exact hm3 _ (by omega)
    | exact hm4 _ (by omega) | exact hoffset _ (by omega)

lemma next_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n)
    (input : Var StateTransitionInput (F p))
    (h : ∀ e ∈ [input.state.pc, input.state.ap, input.state.fp,
      input.decoded.instrType.isLoadState, input.v1, input.v2, input.v3],
      expressionReadsBelow n e = true) :
    flatReadsBelow m (Operations.toFlat (Examples.FemtoCairo.nextState.main input n).2) = true := by
  subst m
  obtain ⟨⟨pc, ap, fp⟩, ⟨⟨_, _, _, load⟩, _, _, _⟩, v1, v2, v3⟩ := input
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨hpc, hap, hfp, hload, hv1, hv2, hv3⟩ := h
  simp [Examples.FemtoCairo.nextState, flatReadsBelow,
    witgenReadsBelow, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    circuit_norm,
    explicit_provable_type, Circuit.forEach]
  simp only [Witgen.M.toIRLiteral]
  rw [vexprReadsBelow, show ∀ pc ap fp : Witgen.FExpr (F p),
    toElements (State.mk pc ap fp) = #v[pc, ap, fp] from fun _ _ _ => rfl]
  simp only [List.all_nil, Bool.true_and]
  simp only [Vector.toList_mk]
  simp only [List.all_nil, List.all_cons, fexprReadsBelow,
    bexprReadsBelow]
  simp only [hload, hv1, hpc, hv2, hap, hv3, hfp, Bool.and_self]

/-! #### Data reads -/

lemma fetch_dataReads {p : ℕ} [Fact p.Prime] {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) (n : ℕ) :
    flatDataReads (Operations.toFlat ((fetchInstruction program h_programSize).main pc n).2) =
      [] := by
  simp [fetchInstruction, witnessDataReads, Witgen.WitgenIR.ofFExpr, vexprDataReads,
    fexprDataReads, u64exprDataReads, fexprListDataReads_map_const, circuit_norm]

lemma decode_dataReads {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (x : Expression (F p)) (n : ℕ) :
    flatDataReads (Operations.toFlat (Examples.FemtoCairo.decodeInstruction.main x n).2) = [] := by
  simp [Examples.FemtoCairo.decodeInstruction, Examples.FemtoCairo.decodeInstructionMain,
    Gadgets.toBits, Gadgets.ToBits.main, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach,
    Gadgets.Equality.circuit, Gadgets.Equality.main, witnessDataReads,
    vexprDataReads, fexprDataReads, circuit_norm,
    explicit_provable_type]

/-- A read of a memory value. -/
def memoryRead : DataRead := { key := "memory", width := 3, column := 1 }

lemma read_dataReads {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (input : Var MemoryReadInput (F p))
    (n : ℕ) :
    flatDataReads (Operations.toFlat (readFromMemory.main input n).2) =
      [memoryRead, memoryRead] := by
  simp [readFromMemory, witnessDataReads, Witgen.WitgenIR.ofFExpr, Gadgets.Equality.circuit,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Circuit.forEach, vexprDataReads, fexprDataReads, u64exprDataReads, dataGet_value,
    memoryRead, circuit_norm, explicit_provable_type]

lemma next_dataReads {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
    (input : Var StateTransitionInput (F p))
    (n : ℕ) :
    flatDataReads (Operations.toFlat (Examples.FemtoCairo.nextState.main input n).2) = [] := by
  simp only [Examples.FemtoCairo.nextState, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach, circuit_norm,
    explicit_provable_type, flatDataReads_append, flatDataReads_witness,
    Witgen.M.toIRLiteral, witnessDataReads]
  simp only [List.flatMap_nil, List.nil_append, vexprDataReads, Vector.toList_mk, List.flatMap_cons,
    fexprDataReads, bexprDataReads, List.append_nil,
    ]
  simp [circuit_norm, explicit_provable_type]

/-! #### Interaction counts -/

lemma fetch_interactions {p : ℕ} [Fact p.Prime] {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) (n : ℕ) :
    (Operations.interactions ((fetchInstruction program h_programSize).main pc n).2).length =
      4 := by
  simp [fetchInstruction, circuit_norm]

lemma decode_interactions {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (x : Expression (F p)) (n : ℕ) :
    (Operations.interactions (Examples.FemtoCairo.decodeInstruction.main x n).2).length = 0 := by
  simp [Examples.FemtoCairo.decodeInstruction, Examples.FemtoCairo.decodeInstructionMain,
    Gadgets.toBits, Gadgets.ToBits.main, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach,
    Gadgets.Equality.circuit, Gadgets.Equality.main, FlatOperation.interactions, circuit_norm,
    explicit_provable_type]

lemma read_interactions {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (input : Var MemoryReadInput (F p))
    (n : ℕ) : (Operations.interactions (readFromMemory.main input n).2).length = 2 := by
  simp [readFromMemory, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Circuit.forEach, FlatOperation.interactions, circuit_norm,
    explicit_provable_type]

lemma next_interactions {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
    (input : Var StateTransitionInput (F p)) (n : ℕ) :
    (Operations.interactions (Examples.FemtoCairo.nextState.main input n).2).length = 0 := by
  simp [Examples.FemtoCairo.nextState, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Circuit.forEach, FlatOperation.interactions, circuit_norm,
    explicit_provable_type]

/-! #### Pulls of the step -/

/-- A single pull of a program word or memory cell. -/
def StepPull {p : ℕ} [Fact p.Prime] {programSize : ℕ} (program : Fin programSize → F p)
    (interaction : AbstractInteraction (F p)) : Prop :=
  (interaction.channel = (ProgramChannel program).toRaw ∨
      interaction.channel = MemoryChannel.toRaw) ∧
    interaction.mult = -1 ∧ interaction.assumeGuarantees = true

lemma fetch_pulls {p : ℕ} [Fact p.Prime] {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) (n : ℕ) :
    ∀ interaction ∈ Operations.interactions ((fetchInstruction program h_programSize).main pc n).2,
      StepPull program interaction := by
  simp [fetchInstruction, StepPull, circuit_norm]

lemma read_pulls {p : ℕ} [Fact p.Prime] [Fact (p > 512)] {programSize : ℕ}
    (program : Fin programSize → F p) (input : Var MemoryReadInput (F p)) (n : ℕ) :
    ∀ interaction ∈ Operations.interactions (readFromMemory.main input n).2,
      StepPull program interaction := by
  simp [readFromMemory, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Circuit.forEach, FlatOperation.interactions, StepPull,
    circuit_norm, explicit_provable_type]

/-- The step only pulls program words and memory cells. -/
lemma step_pulls {p : ℕ} [Fact p.Prime] [Fact (p > 512)] {programSize : ℕ}
    (program : Fin programSize → F p) (h_programSize : programSize < p) (state : Var State (F p))
    (n : ℕ) :
    ∀ interaction ∈ FlatOperation.interactions
      ((femtoCairoStep program h_programSize).toSubcircuit n state).ops.toFlat,
      StepPull program interaction := by
  rw [GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [femtoCairoStep, femtoCairoStepMain, GeneralFormalCircuit.WithHint.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.toSubcircuit, circuit_norm]
  rintro interaction (h | h | h | h | h | h)
  · exact fetch_pulls program h_programSize _ _ _ h
  · simp [List.eq_nil_of_length_eq_zero (decode_interactions _ _)] at h
  · exact read_pulls program _ _ _ h
  · exact read_pulls program _ _ _ h
  · exact read_pulls program _ _ _ h
  · simp [List.eq_nil_of_length_eq_zero (next_interactions _ _)] at h

section Shapes
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

lemma size_executionInput : size ExecutionInput = 4 := rfl

lemma executionInputVar {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    @varFromOffset (F p) ExecutionInput
      (instProvableTypeInput (executionComponent program h_programSize initialState)) 0 =
      { enabled := var ⟨0⟩, state := { pc := var ⟨1⟩, ap := var ⟨2⟩, fp := var ⟨3⟩ } } := by
  with_unfolding_all rfl

omit [Fact (p > 512)] in
lemma fetch_localLength {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) :
    (fetchInstruction program h_programSize).localLength pc = 4 := rfl

omit [Fact (p > 512)] in
lemma fetch_output {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) (n : ℕ) :
    (fetchInstruction program h_programSize).output pc n =
      { rawInstrType := var ⟨n⟩, op1 := var ⟨n + 1⟩, op2 := var ⟨n + 2⟩, op3 := var ⟨n + 3⟩ } := by
  with_unfolding_all rfl

lemma decode_localLength (x : Expression (F p)) :
    Examples.FemtoCairo.decodeInstruction.localLength x = 8 := rfl

omit [Fact (p > 512)] in
lemma read_localLength (input : Var MemoryReadInput (F p)) :
    readFromMemory.localLength input = 5 := rfl

omit [Fact (p > 512)] in
lemma read_output (input : Var MemoryReadInput (F p)) (n : ℕ) :
    readFromMemory.output input n = var ⟨n + 4⟩ := by
  with_unfolding_all rfl

omit [Fact (p > 512)] in
lemma ops_localLength {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (F p) Input Output) (input : Var Input (F p)) (n : ℕ) :
    Operations.localLength (circuit.main input n).2 = circuit.localLength input :=
  circuit.localLength_eq input n

/-- The decoded instruction is computed from the cells of its bits. -/
lemma decode_output_readsBelow (x : Expression (F p)) (n m : ℕ) (h : n + 8 ≤ m) :
    let decoded := Examples.FemtoCairo.decodeInstruction.output x n
    ∀ e ∈ [decoded.mode1.isDoubleAddressing, decoded.mode1.isApRelative,
      decoded.mode1.isFpRelative, decoded.mode1.isImmediate, decoded.mode2.isDoubleAddressing,
      decoded.mode2.isApRelative, decoded.mode2.isFpRelative, decoded.mode2.isImmediate,
      decoded.mode3.isDoubleAddressing, decoded.mode3.isApRelative, decoded.mode3.isFpRelative,
      decoded.mode3.isImmediate, decoded.instrType.isLoadState],
      expressionReadsBelow m e = true := by
  simp only [Examples.FemtoCairo.decodeInstruction, Examples.FemtoCairo.decodeInstructionMain,
    Gadgets.toBits, circuit_norm, explicit_provable_type]
  simp only [expressionReadsBelow_add, expressionReadsBelow_sub, expressionReadsBelow_mul,
    expressionReadsBelow_one, expressionReadsBelow_var, Bool.and_eq_true, decide_eq_true_eq,
    true_and]
  omega

end Shapes

/-- An execution row computes each witness from earlier cells. -/
lemma execution_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] {programSize : ℕ}
    (program : Fin programSize → F p) (h_programSize : programSize < p)
    (initialState : State (F p)) :
    flatReadsBelow (executionComponent program h_programSize initialState).rowOffset
      (executionComponent program h_programSize initialState).rowOperations.toFlat = true := by
  simp only [Component.rowOperations, Component.rowOffset, executionComponent, executeStep,
    femtoCairoStep]
  simp only [femtoCairoStepMain, GeneralFormalCircuit.WithHint.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.toSubcircuit, circuit_norm]
  simp only [flatReadsBelow, flatReadsBelow_append, Bool.and_eq_true,
    FlatOperation.localLength_toFlat, ops_localLength, fetch_localLength, decode_localLength,
    read_localLength, executionInputVar, fetch_output, read_output]
  have hsize : @size ExecutionInput
      (instProvableTypeInput (executionComponent program h_programSize initialState)) = 4 := rfl
  have hdecode := decode_output_readsBelow (p := p) (var ⟨@size ExecutionInput
    (instProvableTypeInput (executionComponent program h_programSize initialState))⟩)
    (@size ExecutionInput (instProvableTypeInput
      (executionComponent program h_programSize initialState)) + 4)
  and_intros
  · exact fetch_readsBelow _ _ _ _ rfl _ rfl
  · exact decode_readsBelow _ _ rfl _ rfl
  · refine read_readsBelow _ _ rfl _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals (simp only [expressionReadsBelow_var, decide_eq_true_eq]; omega)
    all_goals exact hdecode _ (by omega) _ (by simp)
  · refine read_readsBelow _ _ rfl _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals (simp only [expressionReadsBelow_var, decide_eq_true_eq]; omega)
    all_goals exact hdecode _ (by omega) _ (by simp)
  · refine read_readsBelow _ _ rfl _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals (simp only [expressionReadsBelow_var, decide_eq_true_eq]; omega)
    all_goals exact hdecode _ (by omega) _ (by simp)
  · refine next_readsBelow _ _ rfl _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals (simp only [expressionReadsBelow_var, decide_eq_true_eq]; omega)
    all_goals exact hdecode _ (by omega) _ (by simp)
  · trivial

/-- An execution row reads only memory values. -/
lemma execution_dataReads {p : ℕ} [Fact p.Prime] [Fact (p > 512)] {programSize : ℕ}
    (program : Fin programSize → F p) (h_programSize : programSize < p)
    (initialState : State (F p)) :
    flatDataReads (executionComponent program h_programSize initialState).rowOperations.toFlat =
      List.replicate 6 memoryRead := by
  simp only [Component.rowOperations, executionComponent, executeStep, femtoCairoStep]
  simp only [femtoCairoStepMain, GeneralFormalCircuit.WithHint.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.toSubcircuit, circuit_norm]
  simp only [flatDataReads_append, flatDataReads_assert, flatDataReads_interact, flatDataReads_nil,
    fetch_dataReads, decode_dataReads, read_dataReads, next_dataReads, List.nil_append,
    List.append_nil, List.cons_append]
  rfl

variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]
variable {programSize memorySize : UInt64} (program : Fin programSize.toNat → F p)
  (h_programSize : programSize.toNat < p) (h_memorySize : memorySize.toNat < p)
  (initialState : State (F p))

lemma tables_eq : (formalEnsemble program h_programSize h_memorySize initialState).ensemble.tables =
    [executionComponent program h_programSize initialState,
      memoryComponent memorySize h_memorySize, programComponent program h_programSize] := by
  with_unfolding_all rfl

lemma channels_eq :
    (formalEnsemble program h_programSize h_memorySize initialState).ensemble.channels =
      [(StateChannel program initialState).toRaw, MemoryChannel.toRaw,
        (ProgramChannel program).toRaw] := by
  with_unfolding_all rfl

/-- The row plans of the generation plan, in ensemble order. -/
abbrev rowPlans :=
  (plan (memorySize := memorySize) program h_programSize initialState).components.map (·.2)

lemma rowPlanErrors_none (hprogram : 2 ^ Nat.clog 2 programSize.toNat = programSize.toNat)
    (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat) :
    ([executionComponent program h_programSize initialState,
        memoryComponent memorySize h_memorySize, programComponent program h_programSize].zip
      (rowPlans (memorySize := memorySize) program h_programSize initialState)).findSome?
      (fun (component, rowPlan) => rowPlanError component rowPlan) = none := by
  simp [rowPlans, plan, rowPlanError, check, executionMode, memoryMode, programMode,
    executionComponent, memoryComponent, programComponent, memoryFixedColumns, programFixedColumns,
    Padding.targetHeight, Component.rowOffset, Component.fixedWidth, Component.rowOperations,
    executeStep, provideMemory, provideProgram, StateChannel, MemoryChannel, ProgramChannel,
    FixedColumns.width, Witgen.RowProgram.ofFExprs, hprogram, hmemory, circuit_norm,
    explicit_provable_type]

/-- The components of the ensemble. -/
abbrev components := [executionComponent program h_programSize initialState,
  memoryComponent memorySize h_memorySize, programComponent program h_programSize]

lemma handlersError_none :
    handlersError (components program h_programSize h_memorySize initialState)
      (rowPlans (memorySize := memorySize) program h_programSize initialState) = none := by
  simp [handlersError, check, rowPlans, plan, executionMode, memoryMode, programMode,
    Mode.handled, handlerDirection, executionComponent, memoryComponent, programComponent,
    Component.rowOperations, executeStep, provideMemory, provideProgram, StateChannel,
    MemoryChannel, ProgramChannel, circuit_norm, explicit_provable_type]

lemma dataReadsError_none (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat) :
    dataReadsError (components program h_programSize h_memorySize initialState)
      (rowPlans (memorySize := memorySize) program h_programSize initialState) = none := by
  apply dataReadsError_eq_none
  simp only [components, rowPlans, plan, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    execution_dataReads, List.mem_replicate]
  simp [dataReadError, check, memoryRead, executionMode, memoryMode, programMode, Mode.lazyColumns,
    executionComponent, memoryComponent, programComponent, Component.rowOperations,
    Component.rowOffset, executeStep, provideMemory, provideProgram, Padding.targetHeight, hmemory,
    circuit_norm, explicit_provable_type]

lemma readsAheadError_none :
    readsAheadError (components program h_programSize h_memorySize initialState) = none := by
  simp only [readsAheadError, check, components, List.findSome?_cons, List.findSome?_nil,
    execution_readsBelow, if_true]
  simp [memoryComponent, programComponent, Component.rowOffset, Component.rowOperations,
    provideMemory, provideProgram, flatReadsBelow, circuit_norm, explicit_provable_type]

lemma valid (hprogram : ∃ k, programSize.toNat = 2 ^ k) (hmemory : ∃ k, memorySize.toNat = 2 ^ k) :
    ∃ validPlan, (plan (memorySize := memorySize) program h_programSize initialState).validate
      (formalEnsemble program h_programSize h_memorySize initialState).ensemble =
        .ok validPlan := by
  obtain ⟨kp, hkp⟩ := hprogram
  obtain ⟨km, hkm⟩ := hmemory
  have hprogramHeight : 2 ^ Nat.clog 2 programSize.toNat = programSize.toNat := by
    rw [hkp, Nat.clog_pow _ _ (by decide)]
  have hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat := by
    rw [hkm, Nat.clog_pow _ _ (by decide)]
  refine GenerationPlan.validate_ok (by rw [tables_eq]; rfl) ?_
  rw [planError, tables_eq, rowPlanErrors_none _ _ _ _ hprogramHeight hmemoryHeight,
    handlersError_none, dataReadsError_none _ _ _ _ hmemoryHeight, readsAheadError_none]
  rfl

/-! ### Stable prover data -/

lemma hint_memoryValues (memoryValues : fields memorySize.toNat (F p)) :
    (formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues
      memoryValuesKey 1 = Array.ofFn fun i : Fin memorySize.toNat => #v[memoryValues[i]] := by
  simp [FormalEnsemble.hint, HintTable.hint, formalEnsemble, FormalEnsemble.withProverInput,
    memoryValuesKey]
  congr 1
  funext i
  ext j hj
  simp only [Nat.lt_one_iff] at hj
  subst hj
  simp only [Vector.getElem_ofFn, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  show memoryValues[(i : ℕ)]?.getD 0 = _
  simp

/-- Row `row` of the memory table initially holds address `row`, its value and multiplicity
zero. -/
lemma memory_initial (memoryValues : fields memorySize.toNat (F p)) {row : ℕ}
    (hrow : row < memorySize.toNat) :
    preallocatedInput (memoryComponent memorySize h_memorySize) (memoryMode memorySize)
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) row =
      #[(row : F p), memoryValues[row], 0] := by
  have hrow' : row < 2 ^ 64 := lt_trans hrow (UInt64.toNat_lt_size memorySize)
  simp [preallocatedInput, fixedPrefix, memoryComponent, memoryFixedColumns, memoryMode,
    FixedColumns.row, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs, Witgen.VExpr.eval,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, hint_memoryValues, hrow, circuit_norm,
    explicit_provable_type]

omit p_large_enough in
lemma evalList_map_const (ctx : Witgen.Ctx (F p)) (values : List (F p)) (i : ℕ) :
    Witgen.FExpr.evalList ctx i (values.map .const) = values[i]?.getD 0 := by
  induction values generalizing i with
  | nil => simp [Witgen.FExpr.evalList]
  | cons _ _ ih => cases i <;> simp [Witgen.FExpr.evalList, Witgen.FExpr.eval, ih]

omit p_large_enough in
/-- Row `row` of the program table initially holds address `row`, its word and multiplicity
zero. -/
lemma program_initial (hint : ProverHint (F p)) {row : ℕ} (hrow : row < programSize.toNat) :
    preallocatedInput (programComponent program h_programSize) (programMode programSize) hint row =
      #[(row : F p), program ⟨row, hrow⟩, 0] := by
  have hrow' : row < 2 ^ 64 := lt_trans hrow (UInt64.toNat_lt_size programSize)
  simp [preallocatedInput, fixedPrefix, programComponent, programFixedColumns, programMode,
    FixedColumns.row, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs, Witgen.VExpr.eval,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, evalList_map_const, hrow, circuit_norm,
    explicit_provable_type]

omit [Fact p.Prime] p_large_enough in
lemma providerInput_fromElements (row : Vector (F p) (size ProviderInput)) :
    (fromElements row : ProviderInput (F p)) =
      { address := row[0], value := row[1], multiplicity := row[2] } := by
  obtain ⟨⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩⟩, h⟩ := row <;> change _ = 3 at h <;> simp at h
  symm
  simp [explicit_provable_type, circuit_norm]

/-- Stable prover data holds the memory values in the memory table. -/
lemma memory_stable (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat)
    (memoryValues : fields memorySize.toNat (F p)) {data : ProverData (F p)}
    (hstable : StableData (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState)
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) data) :
    ∃ hsize : (data.getRows "memory" ProviderInput).size = memorySize.toNat,
      ∀ i (hi : i < memorySize.toNat),
        (data.getRows "memory" ProviderInput)[i].address = (i : F p) ∧
          (data.getRows "memory" ProviderInput)[i].value = memoryValues[i] := by
  obtain ⟨hsize, hrows⟩ := hstable (memoryComponent memorySize h_memorySize)
    (by simp [tables_eq])
    { mode := .preallocated (memoryMode memorySize),
      padding := { input := #[0, 0, 0], minimumRows := memorySize } }
    (memoryMode memorySize) (by simp [plan, memoryComponent]) rfl
  simp only [Padding.targetHeight, memoryMode, max_self, hmemory] at hsize
  change (data "memory" (size ProviderInput)).size = memorySize.toNat at hsize
  refine ⟨by simpa [ProverData.getRows] using hsize, fun i hi => ?_⟩
  have h0 : (data "memory" (size ProviderInput))[i][0] = (i : F p) := by
    have := hrows i (by change i < (data "memory" (size ProviderInput)).size; omega) 0
      (by show 0 < 3; decide) (by simp [memoryMode])
    simp only [show (memoryMode (p := p) memorySize).rows = memorySize from rfl, hi, if_true,
      memory_initial _ _ _ _ _ hi] at this
    exact this
  have h1 : (data "memory" (size ProviderInput))[i][1] = memoryValues[i] := by
    have := hrows i (by change i < (data "memory" (size ProviderInput)).size; omega) 1
      (by show 1 < 3; decide) (by simp [memoryMode])
    simp only [show (memoryMode (p := p) memorySize).rows = memorySize from rfl, hi, if_true,
      memory_initial _ _ _ _ _ hi] at this
    exact this
  simp only [ProverData.getRows, Array.getElem_map, providerInput_fromElements]
  exact ⟨h0, h1⟩

/-- Stable prover data has the memory of the memory values. -/
lemma memory_eq_of_stable (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat)
    (memoryValues : fields memorySize.toNat (F p)) {data : ProverData (F p)}
    (hstable : StableData (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState)
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) data) :
    ∃ hsize : FlatAir.memorySize data = memorySize.toNat,
      memory data = fun i => memoryValues.get (Fin.cast hsize i) := by
  obtain ⟨hsize, hrows⟩ := memory_stable program h_programSize h_memorySize initialState hmemory
    memoryValues hstable
  exact ⟨hsize, funext fun i => (hrows i (hsize ▸ i.isLt)).2⟩

lemma memoryCompleteness_of_stable (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat)
    (memoryValues : fields memorySize.toNat (F p)) {data : ProverData (F p)}
    (hstable : StableData (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState)
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) data) :
    MemoryCompletenessAssumption data := by
  obtain ⟨hsize, hrows⟩ := memory_stable program h_programSize h_memorySize initialState hmemory
    memoryValues hstable
  have hpos : 0 < memorySize.toNat := by rw [← hmemory]; exact Nat.two_pow_pos _
  have hsize64 := UInt64.toNat_lt_size memorySize
  simp only [UInt64.size] at hsize64
  refine ⟨by omega, by omega, fun address ha => ?_⟩
  rw [(hrows _ (hsize ▸ ha)).1, ZMod.natCast_zmod_val]

omit p_large_enough in
/-- Memories that agree run the same. -/
lemma transition_congr {programSize n m : ℕ} (program : Fin programSize → F p)
    (memory : Fin n → F p) (memory' : Fin m → F p) (h : n = m)
    (hmemory : ∀ i, memory i = memory' (Fin.cast h i)) (state : State (F p)) :
    Spec.femtoCairoMachineTransition program memory state =
      Spec.femtoCairoMachineTransition program memory' state := by
  subst h
  rw [show memory = memory' from funext hmemory]

omit p_large_enough in
lemma execution_congr {programSize n m : ℕ} (program : Fin programSize → F p)
    (memory : Fin n → F p) (memory' : Fin m → F p) (h : n = m)
    (hmemory : ∀ i, memory i = memory' (Fin.cast h i)) (state : Option (State (F p))) (steps : ℕ) :
    Spec.femtoCairoMachineBoundedExecution program memory state steps =
      Spec.femtoCairoMachineBoundedExecution program memory' state steps := by
  subst h
  rw [show memory = memory' from funext hmemory]

/-! ### The VM and its run -/

/-- A state as a channel message. -/
def messageOf (state : State (F p)) : Array (F p) := #[state.pc, state.ap, state.fp]

/-- A channel message as a state. -/
def stateOf (message : Array (F p)) : State (F p) :=
  { pc := message[0]?.getD 0, ap := message[1]?.getD 0, fp := message[2]?.getD 0 }

/-- The state after a state, on the memory values; halted states stay. -/
def next (memoryValues : fields memorySize.toNat (F p)) (message : Array (F p)) : Array (F p) :=
  match Spec.femtoCairoMachineTransition program memoryValues.get (stateOf message) with
  | some state => messageOf state
  | none => message

def vm : Vm (formalEnsemble program h_programSize h_memorySize initialState)
    (plan (memorySize := memorySize) program h_programSize initialState) where
  channel := (StateChannel program initialState).toRaw
  component := executionComponent program h_programSize initialState
  mode := executionMode program initialState
  padding := { input := #[0, initialState.pc, initialState.ap, initialState.fp], minimumRows := 8 }
  declared := by simp [channels_eq]
  mem := by simp [tables_eq]
  planned := by simp [plan, executionComponent]
  mode_channel := rfl
  mode_direction := rfl
  mode_aggregation := rfl
  no_pull_handler := by
    intro other hother rowPlan hplanned
    simp only [tables_eq, List.mem_cons, List.not_mem_nil, or_false] at hother
    rcases hother with rfl | rfl | rfl <;>
      simp [plan, executionComponent, memoryComponent, programComponent, executeStep,
        provideMemory, provideProgram] at hplanned <;>
      subst hplanned <;>
      simp [Mode.handled, executionMode, memoryMode, programMode, handlerDirection, circuit_norm,
        Component.rowOperations, memoryComponent, programComponent, provideMemory, provideProgram,
        StateChannel, MemoryChannel, ProgramChannel]
  next := next program
  initial _ := messageOf initialState
  final | (ap, fp) => messageOf (haltedState programSize.toNat ap fp)

omit p_large_enough in
lemma stateOf_messageOf (state : State (F p)) : stateOf (messageOf state) = state := rfl

omit [Fact (Nat.Prime p)] p_large_enough in
lemma messageOf_injective : Function.Injective (messageOf (p := p)) := by
  intro state state' h
  simp only [messageOf, Array.mk.injEq, List.cons.injEq] at h
  obtain ⟨_, _, _⟩ := state
  obtain ⟨_, _, _⟩ := state'
  simp_all

/-- The `k`-th state of the run is the `k`-th state of the execution. -/
lemma vm_state (memoryValues : fields memorySize.toNat (F p)) (publicInput : fieldPair (F p))
    {k : ℕ} {state : State (F p)}
    (h : Spec.femtoCairoMachineBoundedExecution program memoryValues.get (some initialState) k =
      some state) :
    (vm program h_programSize h_memorySize initialState).state publicInput memoryValues k =
      messageOf state := by
  induction k generalizing state with
  | zero =>
    simp only [Spec.femtoCairoMachineBoundedExecution, Option.some.injEq] at h
    subst h
    rfl
  | succ k ih =>
    simp only [Spec.femtoCairoMachineBoundedExecution, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨previous, hprevious, hnext⟩ := h
    simp only [Vm.state, Function.iterate_succ_apply'] at ih ⊢
    rw [ih hprevious]
    show next program memoryValues (messageOf previous) = _
    rw [next, stateOf_messageOf, hnext]

omit p_large_enough in
/-- A successful execution succeeds at every earlier step. -/
lemma execution_isSome_of_le {programSize memorySize : ℕ} {program : Fin programSize → F p}
    {memory : Fin memorySize → F p} {state : Option (State (F p))} {k k' : ℕ} (hle : k ≤ k')
    (h : (Spec.femtoCairoMachineBoundedExecution program memory state k').isSome) :
    (Spec.femtoCairoMachineBoundedExecution program memory state k).isSome := by
  induction hle with
  | refl => exact h
  | step _ ih =>
    apply ih
    simp only [Spec.femtoCairoMachineBoundedExecution, Option.bind_eq_bind] at h
    cases hstate : Spec.femtoCairoMachineBoundedExecution program memory state _ <;>
      simp_all

omit p_large_enough in
/-- An execution that fails stays failed. -/
lemma execution_none_of_le {programSize memorySize : ℕ} {program : Fin programSize → F p}
    {memory : Fin memorySize → F p} {state : Option (State (F p))} {k k' : ℕ} (hle : k ≤ k')
    (h : Spec.femtoCairoMachineBoundedExecution program memory state k = none) :
    Spec.femtoCairoMachineBoundedExecution program memory state k' = none := by
  induction hle with
  | refl => exact h
  | step _ ih => simp [Spec.femtoCairoMachineBoundedExecution, ih]

lemma proverAssumptions_iff (registers : fieldPair (F p))
    (memoryValues : fields memorySize.toNat (F p)) :
    (formalEnsemble program h_programSize h_memorySize initialState).ProverAssumptions registers
      memoryValues ↔ ProverAssumptions program memorySize initialState registers memoryValues :=
  Iff.rfl

/-- Every component of the ensemble with its row plan. -/
lemma planned_cases {component : Component (F p)}
    (hmem : component ∈
      (formalEnsemble program h_programSize h_memorySize initialState).ensemble.tables)
    {rowPlan : RowPlan (F p)}
    (hplanned : (component.circuit.name, rowPlan) ∈
      (plan (memorySize := memorySize) program h_programSize initialState).components) :
    (component = executionComponent program h_programSize initialState ∧ rowPlan =
      { mode := .demand (executionMode program initialState),
        padding := (vm program h_programSize h_memorySize initialState).padding }) ∨
    (component = memoryComponent memorySize h_memorySize ∧ rowPlan =
      { mode := .preallocated (memoryMode memorySize),
        padding := { input := #[0, 0, 0], minimumRows := memorySize } }) ∨
    (component = programComponent program h_programSize ∧ rowPlan =
      { mode := .preallocated (programMode programSize),
        padding := { input := #[0, 0, 0], minimumRows := programSize } }) := by
  simp only [tables_eq, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;>
    simp [plan, executionComponent, memoryComponent, programComponent, executeStep, provideMemory,
      provideProgram] at hplanned <;>
    simp [hplanned, vm]

lemma verifier_eq :
    (formalEnsemble program h_programSize h_memorySize initialState).ensemble.verifier =
      verifier program initialState := by
  with_unfolding_all rfl

lemma execution_interactions_length :
    (executionComponent program h_programSize initialState).rowOperations.interactions.length =
      12 := by
  simp only [Component.rowOperations, executionComponent, executeStep, femtoCairoStep]
  simp only [femtoCairoStepMain, GeneralFormalCircuit.WithHint.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.toSubcircuit, circuit_norm]
  simp only [List.length_cons, List.length_append, List.length_nil, fetch_interactions,
    decode_interactions, read_interactions, next_interactions]

/-- The execution row answering a state is enabled at that state. -/
lemma vm_input (state : State (F p)) :
    inputOf (executionComponent program h_programSize initialState)
      ((vm program h_programSize h_memorySize initialState).input (messageOf state)) =
      { enabled := 1, state := state } := by
  obtain ⟨pc, ap, fp⟩ := state
  simp only [Vm.input, vm, executionMode, InputTemplate.eval, messageOf]
  rw [inputOf_of_size _ rfl]
  with_unfolding_all rfl

lemma answers_memory (preallocated : Bool) :
    Answers (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState) preallocated "memory" :=
  ⟨memoryComponent memorySize h_memorySize, by simp [tables_eq],
    { mode := .preallocated (memoryMode memorySize),
      padding := { input := #[0, 0, 0], minimumRows := memorySize } },
    by simp [plan, memoryComponent],
    by simp [Mode.handled, memoryMode, memoryComponent, provideMemory, handlerDirection,
      MemoryChannel, circuit_norm, Component.rowOperations],
    fun _ => ⟨_, rfl⟩⟩

lemma answers_program (preallocated : Bool) :
    Answers (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState) preallocated "program" :=
  ⟨programComponent program h_programSize, by simp [tables_eq],
    { mode := .preallocated (programMode programSize),
      padding := { input := #[0, 0, 0], minimumRows := programSize } },
    by simp [plan, programComponent],
    by simp [Mode.handled, programMode, programComponent, provideProgram, handlerDirection,
      ProgramChannel, circuit_norm, Component.rowOperations],
    fun _ => ⟨_, rfl⟩⟩

/-- An execution row answering `state` pulls it and pushes the next state; it also pulls program
words and memory cells. -/
lemma execution_row (hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat)
    (memoryValues : fields memorySize.toNat (F p)) (state : State (F p)) :
    RowInteractions (executeStep program h_programSize initialState) fun input env interactions =>
      env.hint =
        (formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues →
      StableData (formalEnsemble program h_programSize h_memorySize initialState).ensemble
        (plan (memorySize := memorySize) program h_programSize initialState) env.hint env.data →
      input = { enabled := 1, state := state } →
      (∀ message, netOfInteractions interactions "state" message =
        (if message = next program memoryValues (messageOf state) then 1 else 0) -
          (if message = messageOf state then 1 else 0)) ∧
      ∀ interaction ∈ interactions, interaction.channel.name ≠ "state" →
        SideInteraction (formalEnsemble program h_programSize h_memorySize initialState).ensemble
          (plan (memorySize := memorySize) program h_programSize initialState) "state" false
          interaction := by
  circuit_proof_start [executeStep, StateChannel]
  rintro hhint hstable ⟨rfl, rfl⟩
  simp only [List.map_append, List.map_cons, List.map_nil, netOfInteractions_cons,
    netOfInteractions_append, netOfInteractions_nil]
  obtain ⟨-, hstepAssumptions⟩ := h_assumptions
  have hspec := (h_env hstepAssumptions).1 trivial
  obtain ⟨hsize, hmemoryData⟩ := memory_eq_of_stable program h_programSize h_memorySize initialState
    hmemoryHeight memoryValues (hhint ▸ hstable)
  have hnext : next program memoryValues (messageOf input_state) = messageOf (eval env.toEnvironment
      ((femtoCairoStep program h_programSize).output input_var_state i₀)) := by
    simp only [femtoCairoStep, femtoCairoStepSpec] at hspec
    rw [transition_congr program _ _ hsize (fun i => by rw [hmemoryData])] at hspec
    simp [next, stateOf_messageOf, hspec]
    rfl
  have hside : ∀ interaction ∈ List.map (fun x => AbstractInteraction.eval env.toEnvironment x)
      (FlatOperation.interactions
        ((femtoCairoStep program h_programSize).toSubcircuit (i₀ + 0 + 0)
          input_var_state).ops.toFlat),
      (interaction.channel.name = "program" ∨ interaction.channel.name = "memory") ∧
        interaction.IsUnitPull := by
    intro interaction hinteraction
    obtain ⟨abstract, habstract, rfl⟩ := List.mem_map.mp hinteraction
    obtain ⟨hchannel, hmult, hassume⟩ := step_pulls program h_programSize _ _ abstract habstract
    refine ⟨?_, ?_⟩
    · rcases hchannel with h | h <;>
        simp [AbstractInteraction.eval, h, ProgramChannel, MemoryChannel, Channel.toRaw]
    · simp [Interaction.IsUnitPull, AbstractInteraction.eval, hmult, hassume, circuit_norm]
  have hzero := netOfInteractions_eq_zero (channel := "state")
    (fun interaction hinteraction hname => by
    rcases (hside interaction hinteraction).1 with h | h <;> rw [h] at hname <;>
      exact absurd hname (by decide))
  refine ⟨fun message => ?_, fun interaction hmem hname => ?_⟩
  · simp only [hzero, zero_add, add_zero, hnext]
    obtain ⟨henabled, hstate⟩ := h_input
    subst hstate
    generalize (femtoCairoStep program h_programSize).output input_var_state i₀ = output
    obtain ⟨_, _, _⟩ := output
    obtain ⟨_, _, _⟩ := input_var_state
    simp [AbstractInteraction.eval, ChannelInteraction.toRaw, henabled, Channel.toRaw, messageOf,
      circuit_norm, explicit_provable_type]
    simp only [eq_comm (a := message)]
    split_ifs <;> ring
  obtain ⟨abstract, habstract | rfl, rfl⟩ := hmem
  · obtain ⟨hchannel, hpull⟩ := hside _ (List.mem_map.mpr ⟨abstract, habstract, rfl⟩)
    refine .inr ⟨hpull, hname, ?_⟩
    rcases hchannel with h | h <;> rw [h]
    · exact answers_program program h_programSize h_memorySize initialState false
    · exact answers_memory program h_programSize h_memorySize initialState false
  · simp [AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.toRaw] at hname

/-- The verifier pushes the initial state and pulls the halted one, and does nothing else. -/
lemma verifier_row (ap fp : F p) (data : ProverData (F p)) :
    let interactions := (formalEnsemble program h_programSize h_memorySize
      initialState).ensemble.verifierOperations.interactionValues
      (Environment.fromInput (Input := fieldPair) (ap, fp) data)
    (∀ message, netOfInteractions interactions "state" message =
      (if message = messageOf initialState then 1 else 0) -
        (if message = messageOf (haltedState programSize.toNat ap fp) then 1 else 0)) ∧
    ∀ interaction ∈ interactions, interaction.channel.name ≠ "state" →
      SideInteraction (formalEnsemble program h_programSize h_memorySize initialState).ensemble
        (plan (memorySize := memorySize) program h_programSize initialState) "state" false
        interaction ∧ interaction.ProverGuarantees data := by
  simp [Ensemble.verifierOperations, verifier_eq, verifier, circuit_norm,
    Operations.interactionValues, Verifier.Program.circuitOperations, explicit_provable_type,
    netOfInteractions_cons, netOfInteractions_nil, AbstractInteraction.eval, StateChannel,
    messageOf, haltedState]
  intro message
  simp only [eq_comm (a := message)]
  split_ifs <;> ring

/-! ### Provider tables -/

/-- The interactions of a provider row: it pushes its address and value with its multiplicity. -/
def providerInteractions (channel : RawChannel (F p)) (harity : channel.arity = 2)
    (row : Array (F p)) : List (Interaction (F p)) :=
  [{ channel, mult := row[2]?.getD 0, msg := #[row[0]?.getD 0, row[1]?.getD 0],
     same_size := by simp [harity], assumeGuarantees := false }]

omit p_large_enough in
lemma inputOf_memory (row : Array (F p)) :
    inputOf (memoryComponent memorySize h_memorySize) row =
      { address := row[0]?.getD 0, value := row[1]?.getD 0, multiplicity := row[2]?.getD 0 } := by
  with_unfolding_all rfl

omit p_large_enough in
lemma inputOf_program (row : Array (F p)) :
    inputOf (programComponent program h_programSize) row =
      { address := row[0]?.getD 0, value := row[1]?.getD 0, multiplicity := row[2]?.getD 0 } := by
  with_unfolding_all rfl

omit [Fact p.Prime] p_large_enough in
lemma memoryEntry_toElements {α : Type} (address value : α) :
    (toElements ({ address, value } : MemoryEntry α)).toArray = #[address, value] := by
  with_unfolding_all rfl

omit p_large_enough in
lemma memory_row (row : Array (F p)) : RowInteractions (provideMemory (p := p))
    fun input _ interactions =>
    input = inputOf (memoryComponent memorySize h_memorySize) row →
      interactions = providerInteractions MemoryChannel.toRaw rfl row := by
  circuit_proof_start [provideMemory, MemoryChannel]
  intro hinput
  rw [inputOf_memory] at hinput
  simp only [ProviderInput.mk.injEq] at hinput
  obtain ⟨rfl, rfl, rfl⟩ := hinput
  simp [providerInteractions, AbstractInteraction.eval, circuit_norm, memoryEntry_toElements,
    h_input]

omit p_large_enough in
lemma program_row (row : Array (F p)) : RowInteractions (provideProgram program)
    fun input _ interactions =>
    input = inputOf (programComponent program h_programSize) row →
      interactions = providerInteractions (ProgramChannel program).toRaw rfl row := by
  circuit_proof_start [provideProgram, ProgramChannel]
  intro hinput
  rw [inputOf_program] at hinput
  simp only [ProviderInput.mk.injEq] at hinput
  obtain ⟨rfl, rfl, rfl⟩ := hinput
  simp [providerInteractions, AbstractInteraction.eval, circuit_norm, explicit_provable_type,
    h_input]

/-- A disabled execution row interacts on the state channel with multiplicity zero, and otherwise
pulls program words and memory cells. -/
lemma execution_padding : RowInteractions (executeStep program h_programSize initialState)
    fun input _ interactions => input.enabled = 0 →
      ∀ interaction ∈ interactions,
        SideInteraction (formalEnsemble program h_programSize h_memorySize initialState).ensemble
          (plan (memorySize := memorySize) program h_programSize initialState) "state" true
          interaction := by
  circuit_proof_start [executeStep, StateChannel]
  intro henabled
  have heval : Expression.eval env.toEnvironment input_var_enabled = 0 := h_input.1.trans henabled
  refine ⟨.inl (by simp [AbstractInteraction.eval, ChannelInteraction.toRaw, heval,
    circuit_norm]), ?_⟩
  rintro _ ⟨abstract, habstract | rfl, rfl⟩
  · obtain ⟨hchannel, hmult, hassume⟩ := step_pulls program h_programSize _ _ abstract habstract
    refine .inr ⟨by simp [Interaction.IsUnitPull, AbstractInteraction.eval, hmult, hassume,
      circuit_norm], ?_⟩
    rcases hchannel with h | h <;>
      simp only [AbstractInteraction.eval, h, ProgramChannel, MemoryChannel, Channel.toRaw]
    · exact ⟨by decide, answers_program program h_programSize h_memorySize initialState true⟩
    · exact ⟨by decide, answers_memory program h_programSize h_memorySize initialState true⟩
  · exact .inl (by simp [AbstractInteraction.eval, ChannelInteraction.toRaw, heval, circuit_norm])

/-- A state the execution reaches and steps from satisfies the step's prover assumptions on stable
data. -/
lemma step_assumptions (hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat)
    (memoryValues : fields memorySize.toNat (F p)) {data : ProverData (F p)}
    (hstable : StableData (formalEnsemble program h_programSize h_memorySize initialState).ensemble
      (plan (memorySize := memorySize) program h_programSize initialState)
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) data)
    (hprogramSize : programSize.toNat + 3 < p) {k : ℕ} {state : State (F p)}
    (hstate : Spec.femtoCairoMachineBoundedExecution program memoryValues.get
      (some initialState) k = some state)
    (hnext : (Spec.femtoCairoMachineBoundedExecution program memoryValues.get (some initialState)
      (k + 1)).isSome) :
    (femtoCairoStep program h_programSize).ProverAssumptions state data
      ((formalEnsemble program h_programSize h_memorySize initialState).hint memoryValues) := by
  obtain ⟨hsize, hmemoryData⟩ := memory_eq_of_stable program h_programSize h_memorySize
    initialState hmemoryHeight memoryValues hstable
  refine ⟨hprogramSize,
    by have := UInt64.toNat_lt_size programSize; simp only [UInt64.size] at this; omega,
    memoryCompleteness_of_stable program h_programSize h_memorySize initialState hmemoryHeight
      memoryValues hstable, ?_⟩
  rw [transition_congr program _ _ hsize (fun i => by rw [hmemoryData])]
  simpa [Spec.femtoCairoMachineBoundedExecution, hstate] using hnext

/-- Execution padding rows are disabled at the initial state. -/
lemma padding_input :
    inputOf (executionComponent program h_programSize initialState)
      (vm program h_programSize h_memorySize initialState).padding.input =
      { enabled := 0, state := initialState } := by
  obtain ⟨pc, ap, fp⟩ := initialState
  rw [inputOf_of_size _ rfl]
  with_unfolding_all rfl

def completePlan (hprogram : ∃ k, programSize.toNat = 2 ^ k)
    (hmemory : ∃ k, memorySize.toNat = 2 ^ k) :
    CompletePlan (formalEnsemble program h_programSize h_memorySize initialState)
      (plan (memorySize := memorySize) program h_programSize initialState) where
  valid := valid program h_programSize h_memorySize initialState hprogram hmemory
  no_lazy := by
    intro component hmem rowPlan mode hplanned hmode
    rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hmode
    all_goals
      simp only [Mode.preallocated.injEq] at hmode
      subst hmode
      rfl
  vm := vm program h_programSize h_memorySize initialState
  rowBound steps name :=
    if name = "execution" then
      (vm program h_programSize h_memorySize initialState).padding.targetHeight steps
    else if name = "memory" then memorySize.toNat else programSize.toNat
  rank _ := 0
  acyclic := by
    intro component hmem rowPlan mode hplanned hmode hvm
    rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hvm
    all_goals cases hmode
  run := by
    rintro ⟨ap, fp⟩ memoryValues ⟨steps, hhalt, hp, hsteps⟩
    have hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat := by
      obtain ⟨k, hk⟩ := hmemory
      rw [hk, Nat.clog_pow _ _ (by decide)]
    -- every state of the run is reached
    have hreached : ∀ k ≤ steps + 1, ∃ state,
        Spec.femtoCairoMachineBoundedExecution program memoryValues.get (some initialState) k =
          some state := fun k hk =>
      Option.isSome_iff_exists.mp (execution_isSome_of_le hk (by simp [hhalt]))
    refine ⟨steps + 1, ?_, fun k hk heq => ?_, fun k hk data hstable => ?_, ?_⟩
    · rw [vm_state program h_programSize h_memorySize initialState memoryValues _ hhalt]
      rfl
    · obtain ⟨state, hstate⟩ := hreached k hk.le
      rw [vm_state program h_programSize h_memorySize initialState memoryValues _ hstate] at heq
      obtain rfl := messageOf_injective heq
      have hstuck : Spec.femtoCairoMachineBoundedExecution program memoryValues.get
          (some initialState) (k + 1) = none := by
        simp [Spec.femtoCairoMachineBoundedExecution, hstate,
          femtoCairoMachineTransition_haltedState program h_programSize]
      simp [execution_none_of_le (show k + 1 ≤ steps + 1 by omega) hstuck] at hhalt
    · obtain ⟨state, hstate⟩ := hreached k hk.le
      obtain ⟨next, hnext⟩ := hreached (k + 1) hk
      rw [vm_state program h_programSize h_memorySize initialState memoryValues _ hstate]
      change (executeStep program h_programSize initialState).ProverAssumptions
        (inputOf (executionComponent program h_programSize initialState) _) data _
      rw [vm_input]
      simp only [executeStep, StateChannel]
      obtain ⟨hsize, hmemoryData⟩ := memory_eq_of_stable program h_programSize h_memorySize
        initialState hmemoryHeight memoryValues hstable
      refine ⟨.inr ⟨trivial, k, ?_⟩, step_assumptions program h_programSize h_memorySize
        initialState hmemoryHeight memoryValues hstable (by omega) hstate (by simp [hnext])⟩
      rw [execution_congr program _ _ hsize (fun i => by rw [hmemoryData]), hstate]
    · have hle := le_targetHeight (vm program h_programSize h_memorySize initialState).padding
        (steps + 1)
      have hle2 := targetHeight_le_two_mul
        (vm program h_programSize h_memorySize initialState).padding (steps + 1) (by simp)
      have hmin :
          (vm program h_programSize h_memorySize initialState).padding.minimumRows.toNat = 8 := rfl
      rw [hmin] at hle hle2
      have hsize : (vm program h_programSize h_memorySize initialState).padding.targetHeight
          (steps + 1) ≤ UInt64.size := by
        have : max (steps + 1) 8 < 2 ^ 63 := by
          have : steps + 1 < 2 ^ 63 := by omega
          omega
        simp only [UInt64.size]
        omega
      have hprogramSize := (UInt64.toNat_lt_size programSize).le
      have hmemorySize := (UInt64.toNat_lt_size memorySize).le
      refine ⟨by simpa [vm, executionComponent, executeStep] using hle.1, ?_, ?_⟩
      · intro component hmem rowPlan hplanned
        rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [show (executionComponent program h_programSize initialState).circuit.name =
            "execution" from rfl, if_true]
          exact ⟨⟨_, rfl⟩, hle.2, hsize, .inl rfl⟩
        · simp only [show (memoryComponent memorySize h_memorySize (p := p)).circuit.name =
            "memory" from rfl, if_neg (show "memory" ≠ "execution" by decide), if_true]
          exact ⟨hmemory, le_rfl, hmemorySize, le_rfl⟩
        · simp only [show (programComponent program h_programSize).circuit.name =
            "program" from rfl, if_neg (show "program" ≠ "execution" by decide),
            if_neg (show "program" ≠ "memory" by decide)]
          exact ⟨hprogram, le_rfl, hprogramSize, le_rfl⟩
      · have hverifier : (formalEnsemble program h_programSize h_memorySize
            initialState).ensemble.verifierOperations.interactions.length = 2 := by
          simp [Ensemble.verifierOperations, verifier_eq, verifier,
            Verifier.Program.circuitOperations, circuit_norm]
        have hmemoryLength :
            (memoryComponent memorySize h_memorySize (p := p)).rowOperations.interactions.length =
              1 := by
          simp [memoryComponent, provideMemory, Component.rowOperations, circuit_norm]
        have hprogramLength :
            (programComponent program h_programSize).rowOperations.interactions.length = 1 := by
          simp [programComponent, provideProgram, Component.rowOperations, circuit_norm]
        rw [hverifier, tables_eq]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (executionComponent program h_programSize initialState).circuit.name =
            "execution" from rfl,
          show (memoryComponent memorySize h_memorySize (p := p)).circuit.name = "memory" from rfl,
          show (programComponent program h_programSize).circuit.name = "program" from rfl, if_true,
          if_neg (show "memory" ≠ "execution" by decide),
          if_neg (show "program" ≠ "execution" by decide),
          if_neg (show "program" ≠ "memory" by decide),
          execution_interactions_length, hmemoryLength, hprogramLength, FiniteField.char_F]
        exact lt_of_le_of_lt (by omega) hp
  vm_row memoryValues state hsize := by
    have hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat := by
      obtain ⟨k, hk⟩ := hmemory
      rw [hk, Nat.clog_pow _ _ (by decide)]
    change state.size = 3 at hsize
    rcases state with ⟨_ | ⟨pc, _ | ⟨ap, _ | ⟨fp, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hsize
    exact (execution_row program h_programSize h_memorySize initialState hmemoryHeight memoryValues
      ⟨pc, ap, fp⟩).mono fun _ _ _ h hhint hstable hinput =>
        h hhint hstable (hinput.trans (vm_input program h_programSize h_memorySize initialState
          ⟨pc, ap, fp⟩))
  verifier := by
    rintro ⟨ap, fp⟩ memoryValues - data -
    exact verifier_row program h_programSize h_memorySize initialState ap fp data
  demand := by
    intro component hmem rowPlan mode hplanned hmode hvm
    rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hvm
    all_goals cases hmode
  preallocated := by
    have hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat := by
      obtain ⟨k, hk⟩ := hmemory
      rw [hk, Nat.clog_pow _ _ (by decide)]
    intro component hmem rowPlan mode hplanned hmode
    rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hmode
    · simp only [Mode.preallocated.injEq] at hmode
      subst hmode
      refine ⟨fun publicInput memoryValues _ data hstable => ⟨?_, ?_, ?_⟩,
        fun row _ _ => providerInteractions MemoryChannel.toRaw rfl row,
        fun row => memory_row h_memorySize row, ?_, ?_⟩
      · intro row hrow
        change row < memorySize.toNat at hrow
        obtain ⟨hsize, hrows⟩ := memory_stable program h_programSize h_memorySize initialState
          hmemoryHeight memoryValues hstable
        have hval : ((row : ℕ) : F p).val = row := ZMod.val_natCast_of_lt (by omega)
        rw [memory_initial program h_programSize h_memorySize initialState memoryValues hrow,
          inputOf_memory]
        simp only [memoryComponent, provideMemory, MemoryChannel]
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, hval]
        exact ⟨hsize ▸ hrow, (hrows row hrow).1.symm, (hrows row hrow).2.symm⟩
      · intro handler hhandler row hrow
        simp only [memoryMode, List.mem_singleton] at hhandler
        subst hhandler
        rw [memory_initial program h_programSize h_memorySize initialState memoryValues
          (show row < memorySize.toNat from hrow)]
        rfl
      · intro input handler hhandler value hassumptions
        simp only [memoryMode, List.mem_singleton] at hhandler
        subst hhandler
        rw [inputOf_memory] at hassumptions ⊢
        simpa [memoryComponent, provideMemory] using hassumptions
      · intro input data hint index hindex other hother
        simp only [memoryMode, List.map_cons, List.map_nil, List.mem_singleton] at hindex
        rcases index with _ | index
        · contradiction
        · simp [providerInteractions] at hother
      · intro handler hhandler
        simp only [memoryMode, List.mem_singleton] at hhandler
        subst hhandler
        refine ⟨MemoryChannel.toRaw, by simp [channels_eq],
          fun _ _ _ => by simp [providerInteractions],
          fun _ _ _ _ => by simp [providerInteractions], fun _ _ _ _ index hindex => ?_, ?_⟩
        · rcases index with _ | index
          · contradiction
          · simp [providerInteractions]
        rintro publicInput memoryValues - data hstable
          ⟨⟨_ | ⟨address, _ | ⟨value, _ | _⟩⟩⟩, hlength⟩ hguarantees <;>
          change _ = 2 at hlength <;> simp at hlength
        simp [Channel.toRaw, MemoryChannel, explicit_provable_type, circuit_norm] at hguarantees
        obtain ⟨hlt, haddress, hvalue⟩ := hguarantees
        obtain ⟨hsize, hrows⟩ := memory_stable program h_programSize h_memorySize initialState
          hmemoryHeight memoryValues hstable
        have hrow : address.val < memorySize.toNat := hsize ▸ hlt
        refine ⟨address.val, hrow, _, rfl, ?_⟩
        rw [memory_initial program h_programSize h_memorySize initialState memoryValues hrow]
        simp only [List.getElem?_toArray, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, ZMod.natCast_zmod_val]
        rw [hvalue, (hrows _ hrow).2]
    · simp only [Mode.preallocated.injEq] at hmode
      subst hmode
      refine ⟨fun publicInput memoryValues _ data hstable => ⟨?_, ?_, ?_⟩,
        fun row _ _ => providerInteractions (ProgramChannel program).toRaw rfl row,
        fun row => program_row program h_programSize row, ?_, ?_⟩
      · intro row hrow
        change row < programSize.toNat at hrow
        have hval : ((row : ℕ) : F p).val = row := ZMod.val_natCast_of_lt (by omega)
        rw [program_initial program h_programSize _ hrow, inputOf_program]
        simp only [programComponent, provideProgram, ProgramChannel]
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, hval]
        exact ⟨hrow, trivial⟩
      · intro handler hhandler row hrow
        simp only [programMode, List.mem_singleton] at hhandler
        subst hhandler
        rw [program_initial program h_programSize _ (show row < programSize.toNat from hrow)]
        rfl
      · intro input handler hhandler value hassumptions
        simp only [programMode, List.mem_singleton] at hhandler
        subst hhandler
        rw [inputOf_program] at hassumptions ⊢
        simpa [programComponent, provideProgram] using hassumptions
      · intro input data hint index hindex other hother
        simp only [programMode, List.map_cons, List.map_nil, List.mem_singleton] at hindex
        rcases index with _ | index
        · contradiction
        · simp [providerInteractions] at hother
      · intro handler hhandler
        simp only [programMode, List.mem_singleton] at hhandler
        subst hhandler
        refine ⟨(ProgramChannel program).toRaw, by simp [channels_eq],
          fun _ _ _ => by simp [providerInteractions],
          fun _ _ _ _ => by simp [providerInteractions], fun _ _ _ _ index hindex => ?_, ?_⟩
        · rcases index with _ | index
          · contradiction
          · simp [providerInteractions]
        rintro publicInput memoryValues - data -
          ⟨⟨_ | ⟨address, _ | ⟨value, _ | _⟩⟩⟩, hlength⟩ hguarantees <;>
          change _ = 2 at hlength <;> simp at hlength
        simp [Channel.toRaw, ProgramChannel, explicit_provable_type, circuit_norm] at hguarantees
        obtain ⟨hrow, hvalue⟩ := hguarantees
        refine ⟨address.val, hrow, _, rfl, ?_⟩
        rw [program_initial program h_programSize _ hrow]
        simp [hvalue]
  padding := by
    have hmemoryHeight : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat := by
      obtain ⟨k, hk⟩ := hmemory
      rw [hk, Nat.clog_pow _ _ (by decide)]
    have hprogramHeight : 2 ^ Nat.clog 2 programSize.toNat = programSize.toNat := by
      obtain ⟨k, hk⟩ := hprogram
      rw [hk, Nat.clog_pow _ _ (by decide)]
    intro component hmem rowPlan hplanned hpad
    rcases planned_cases program h_programSize h_memorySize initialState hmem hplanned with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨?_, (execution_padding program h_programSize h_memorySize initialState).mono
        fun _ _ _ h hinput => h (by rw [hinput, padding_input])⟩
      rintro ⟨ap, fp⟩ memoryValues ⟨steps, hhalt, hp, -⟩ data hstable
      change (executeStep program h_programSize initialState).ProverAssumptions
        (inputOf (executionComponent program h_programSize initialState) _) data _
      rw [padding_input]
      refine ⟨.inl rfl, step_assumptions program h_programSize h_memorySize initialState
        hmemoryHeight memoryValues hstable (by omega) (k := 0) rfl ?_⟩
      exact execution_isSome_of_le (k' := steps + 1) (by omega) (by simp [hhalt])
    · have := hpad (memoryMode memorySize) rfl
      simp [Padding.targetHeight, memoryMode, hmemoryHeight] at this
    · have := hpad (programMode programSize) rfl
      simp [Padding.targetHeight, programMode, hprogramHeight] at this

/-- FemtoCairo witness generation is complete: from memory values on which the program runs in at
least one step to completion with registers `(ap, fp)`, in a run that fits the field and the trace,
it returns a witness for these registers satisfying the constraints and balancing all channels. -/
theorem generate_complete (hprogram : ∃ k, programSize.toNat = 2 ^ k)
    (hmemory : ∃ k, memorySize.toNat = 2 ^ k) (memoryValues : fields memorySize.toNat (F p))
    (ap fp : F p) (steps : ℕ)
    (hrun : Spec.femtoCairoMachineBoundedExecution program memoryValues.get (some initialState)
      (steps + 1) = some (haltedState programSize.toNat ap fp))
    (hp : 64 * (steps + programSize.toNat + memorySize.toNat + 8) < p) (hsteps : steps < 2 ^ 62) :
    ∃ witness, generate program h_programSize h_memorySize memoryValues initialState (ap, fp) =
        .ok witness ∧ witness.publicInput = (ap, fp) ∧ witness.Constraints ∧
      witness.BalancedChannels :=
  Air.Flat.WitnessGeneration.generate_complete
    (completePlan program h_programSize h_memorySize initialState hprogram hmemory)
    ⟨steps, hrun, hp, hsteps⟩

end Examples.FemtoCairo.FlatAir.Witness
