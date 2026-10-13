module

public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Air.GenerationCompletenessProof
import Mathlib.Util.CountHeartbeats

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
    (program : Fin programSize → F p) (h_programSize : programSize < p) (m n : ℕ) (hmn : m = n) (pc : Expression (F p)) (h : expressionReadsBelow n pc = true) :
    flatReadsBelow m (Operations.toFlat ((fetchInstruction program h_programSize).main pc n).2) = true := by
  subst m
  have hmono : ∀ m, n ≤ m → expressionReadsBelow m pc = true :=
    fun _ hm => expressionReadsBelow_mono hm h
  simp [fetchInstruction, flatReadsBelow, witgenReadsBelow, Witgen.WitgenIR.ofFExpr,
    stepReadsBelow, vexprReadsBelow, fexprReadsBelow, u64exprReadsBelow,
    fexprListReadsBelow_map_const, circuit_norm, hmono]
  exact ⟨hmono _ (by omega), hmono _ (by omega)⟩

lemma decode_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n) (x : Expression (F p)) (h : expressionReadsBelow n x = true) :
    flatReadsBelow m (Operations.toFlat (Examples.FemtoCairo.decodeInstruction.main x n).2) = true := by
  subst m
  have hmono : ∀ m, n ≤ m → expressionReadsBelow m x = true :=
    fun _ hm => expressionReadsBelow_mono hm h
  simp [Examples.FemtoCairo.decodeInstruction, Examples.FemtoCairo.decodeInstructionMain,
    Gadgets.toBits, Gadgets.ToBits.main, GeneralFormalCircuit.toSubcircuit,
    GeneralFormalCircuit.toWithHint, GeneralFormalCircuit.WithHint.toSubcircuit,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach,
    Gadgets.Equality.circuit, Gadgets.Equality.main, Utils.Bits.fieldFromBitsExpr,
    flatReadsBelow, witgenReadsBelow, Witgen.WitgenIR.ofFExpr,
    stepReadsBelow, vexprReadsBelow, fexprReadsBelow, u64exprReadsBelow, expressionReadsBelow,
    circuit_norm, explicit_provable_type, hmono]

lemma dataGet_value {p : ℕ} (row : Witgen.U64Expr (F p)) :
    (Witgen.dataGet "memory" ProviderInput row).value = .dataGet "memory" 3 row 1 := by
  have h := congrArg (fun v => v[1]) (ProvableType.toElements_fromElements (M := ProviderInput)
    (Vector.mapFinRange (size ProviderInput) fun col =>
      Witgen.FExpr.dataGet (F := F p) "memory" (size ProviderInput) row col))
  simp only [Witgen.dataGet]
  simp [explicit_provable_type, circuit_norm, Vector.mapFinRange, Vector.finRange_succ,
    Vector.extract, Vector.pop, Vector.map, Vector.toArray_append, Vector.toArray_mk,
    List.append_toArray, List.map_toArray, List.extract_toArray, List.pop_toArray]
  split
  rename_i x _ heq
  have := congrArg Vector.toList heq
  have hcols : ((#v[0] : Vector (Fin 3) 1) ++ (#v[1, 2] : Vector (Fin 3) 2)).toArray.toList =
      [0, 1, 2] := rfl
  simp [hcols] at this
  exact this.symm

lemma read_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n) (input : Var MemoryReadInput (F p))
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
  simp [Vector.mapFinRange, Vector.extract, Vector.pop, hpc, hap, hfp, hoffset, hm1, hm2, hm3, hm4,
    readFromMemory, flatReadsBelow, witgenReadsBelow, Witgen.WitgenIR.ofFExpr,
    Gadgets.Equality.circuit, Gadgets.Equality.main, FormalAssertion.toSubcircuit,
    Operations.toNested_toFlat, Circuit.forEach, stepReadsBelow, vexprReadsBelow,
    fexprReadsBelow, u64exprReadsBelow, expressionReadsBelow, dataGet_value, circuit_norm,
    explicit_provable_type]
  and_intros <;> first
    | omega
    | exact hm1 _ (by omega) | exact hm2 _ (by omega) | exact hm3 _ (by omega)
    | exact hm4 _ (by omega) | exact hoffset _ (by omega)

lemma next_readsBelow {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (m n : ℕ) (hmn : m = n) (input : Var StateTransitionInput (F p))
    (h : ∀ e ∈ [input.state.pc, input.state.ap, input.state.fp,
      input.decoded.instrType.isLoadState, input.v1, input.v2, input.v3],
      expressionReadsBelow n e = true) :
    flatReadsBelow m (Operations.toFlat (Examples.FemtoCairo.nextState.main input n).2) = true := by
  subst m
  obtain ⟨⟨pc, ap, fp⟩, ⟨⟨_, _, _, load⟩, _, _, _⟩, v1, v2, v3⟩ := input
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨hpc, hap, hfp, hload, hv1, hv2, hv3⟩ := h
  simp [Examples.FemtoCairo.nextState, hpc, hap, hfp, hload, hv1, hv2, hv3, flatReadsBelow,
    witgenReadsBelow, Witgen.WitgenIR.ofFExpr, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, stepReadsBelow, vexprReadsBelow,
    fexprReadsBelow, u64exprReadsBelow, bexprReadsBelow, expressionReadsBelow, circuit_norm,
    explicit_provable_type, Circuit.forEach]
  simp only [Witgen.M.toIRLiteral]
  rw [vexprReadsBelow, show ∀ pc ap fp : Witgen.FExpr (F p),
    toElements (State.mk pc ap fp) = #v[pc, ap, fp] from fun _ _ _ => rfl]
  simp only [List.all_nil, Bool.true_and]
  simp only [List.all_nil, Bool.true_and, Vector.toList_mk]
  simp only [List.all_nil, Bool.true_and, Vector.toList_mk, List.all_cons, fexprReadsBelow,
    bexprReadsBelow, expressionReadsBelow]
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
    Gadgets.Equality.circuit, Gadgets.Equality.main, witnessDataReads, Witgen.WitgenIR.ofFExpr,
    vexprDataReads, fexprDataReads, u64exprDataReads, bexprDataReads, circuit_norm,
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

lemma next_dataReads {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (input : Var StateTransitionInput (F p))
    (n : ℕ) :
    flatDataReads (Operations.toFlat (Examples.FemtoCairo.nextState.main input n).2) = [] := by
  simp only [Examples.FemtoCairo.nextState, Gadgets.Equality.circuit, Gadgets.Equality.main,
    FormalAssertion.toSubcircuit, Operations.toNested_toFlat, Circuit.forEach, circuit_norm,
    explicit_provable_type, flatDataReads_append, flatDataReads_witness, flatDataReads_assert,
    flatDataReads_nil, Witgen.M.toIRLiteral, witnessDataReads]
  simp only [List.flatMap_nil, List.nil_append, vexprDataReads, Vector.toList_mk, List.flatMap_cons,
    fexprDataReads, bexprDataReads, fexprDataReads_ofNat, List.append_nil, Vector.toArray_mk,
    List.toList_toArray]
  simp [circuit_norm, Circuit.forEach, explicit_provable_type]

section Shapes
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

lemma size_executionInput : size ExecutionInput = 4 := rfl

lemma executionInputVar {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    @varFromOffset (F p) ExecutionInput
      (instProvableTypeInput (executionComponent program h_programSize initialState)) 0 =
      { enabled := var ⟨0⟩, state := { pc := var ⟨1⟩, ap := var ⟨2⟩, fp := var ⟨3⟩ } } := by
  with_unfolding_all rfl

lemma fetch_localLength {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) :
    (fetchInstruction program h_programSize).localLength pc = 4 := rfl

lemma fetch_output {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (pc : Expression (F p)) (n : ℕ) :
    (fetchInstruction program h_programSize).output pc n =
      { rawInstrType := var ⟨n⟩, op1 := var ⟨n + 1⟩, op2 := var ⟨n + 2⟩, op3 := var ⟨n + 3⟩ } := by
  with_unfolding_all rfl

lemma decode_localLength (x : Expression (F p)) :
    Examples.FemtoCairo.decodeInstruction.localLength x = 8 := rfl

lemma read_localLength (input : Var MemoryReadInput (F p)) :
    readFromMemory.localLength input = 5 := rfl

lemma read_output (input : Var MemoryReadInput (F p)) (n : ℕ) :
    readFromMemory.output input n = var ⟨n + 4⟩ := by
  with_unfolding_all rfl

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
    read_localLength, size_executionInput, executionInputVar, fetch_output, read_output]
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
abbrev rowPlans := (plan (memorySize := memorySize) program h_programSize initialState).components.map
  (·.2)

lemma rowPlanErrors_none (hprogram : 2 ^ Nat.clog 2 programSize.toNat = programSize.toNat)
    (hmemory : 2 ^ Nat.clog 2 memorySize.toNat = memorySize.toNat) :
    ([executionComponent program h_programSize initialState, memoryComponent memorySize h_memorySize,
        programComponent program h_programSize].zip
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
    witnessDataReads, circuit_norm, explicit_provable_type]

lemma readsAheadError_none :
    readsAheadError (components program h_programSize h_memorySize initialState) = none := by
  simp only [readsAheadError, check, components, List.findSome?_cons, List.findSome?_nil,
    execution_readsBelow, if_true]
  simp [memoryComponent, programComponent, Component.rowOffset, Component.rowOperations,
    provideMemory, provideProgram, flatReadsBelow, circuit_norm, explicit_provable_type]

lemma valid (hprogram : ∃ k, programSize.toNat = 2 ^ k) (hmemory : ∃ k, memorySize.toNat = 2 ^ k) :
    ∃ validPlan, (plan (memorySize := memorySize) program h_programSize initialState).validate
      (formalEnsemble program h_programSize h_memorySize initialState).ensemble = .ok validPlan := by
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

end Examples.FemtoCairo.FlatAir.Witness
