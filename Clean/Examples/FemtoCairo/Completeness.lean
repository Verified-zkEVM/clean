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
  simp [Nat.mod_eq_of_lt hrow', preallocatedInput, fixedPrefix, memoryComponent, memoryFixedColumns, memoryMode,
    FixedColumns.row, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs, Witgen.VExpr.eval,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, hint_memoryValues, hrow, circuit_norm,
    explicit_provable_type]

lemma evalList_map_const (ctx : Witgen.Ctx (F p)) (values : List (F p)) (i : ℕ) :
    Witgen.FExpr.evalList ctx i (values.map .const) = values[i]?.getD 0 := by
  induction values generalizing i with
  | nil => simp [Witgen.FExpr.evalList]
  | cons _ _ ih => cases i <;> simp [Witgen.FExpr.evalList, Witgen.FExpr.eval, ih]

/-- Row `row` of the program table initially holds address `row`, its word and multiplicity
zero. -/
lemma program_initial (hint : ProverHint (F p)) {row : ℕ} (hrow : row < programSize.toNat) :
    preallocatedInput (programComponent program h_programSize) (programMode programSize) hint row =
      #[(row : F p), program ⟨row, hrow⟩, 0] := by
  have hrow' : row < 2 ^ 64 := lt_trans hrow (UInt64.toNat_lt_size programSize)
  simp [Nat.mod_eq_of_lt hrow', preallocatedInput, fixedPrefix, programComponent, programFixedColumns, programMode,
    FixedColumns.row, Witgen.RowProgram.eval, Witgen.RowProgram.ofFExprs, Witgen.VExpr.eval,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, evalList_map_const, hrow, circuit_norm,
    explicit_provable_type]

omit [Fact p.Prime] p_large_enough in
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
  refine ⟨by omega, by have := UInt64.toNat_lt_size memorySize; simp only [UInt64.size] at this; omega,
    fun address ha => ?_⟩
  rw [(hrows _ (hsize ▸ ha)).1, ZMod.natCast_zmod_val]

/-- Memories that agree run the same. -/
lemma transition_congr {programSize n m : ℕ} (program : Fin programSize → F p)
    (memory : Fin n → F p) (memory' : Fin m → F p) (h : n = m)
    (hmemory : ∀ i, memory i = memory' (Fin.cast h i)) (state : State (F p)) :
    Spec.femtoCairoMachineTransition program memory state =
      Spec.femtoCairoMachineTransition program memory' state := by
  subst h
  rw [show memory = memory' from funext hmemory]

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

lemma stateOf_messageOf (state : State (F p)) : stateOf (messageOf state) = state := rfl

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

end Examples.FemtoCairo.FlatAir.Witness
