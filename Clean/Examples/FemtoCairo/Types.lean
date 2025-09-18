import Clean.Circuit.Provable

namespace Examples.FemtoCairo.Types

/--
  State of the femtoCairo machine, represented as a structure (pc, ap, fp).
-/
structure State (F : Type) where
  pc : F
  ap : F
  fp : F

/--
  Raw instruction that is fetched from the program memory,
  represented as a structure (instrType, op1, op2, op3).
-/
structure RawInstruction (F : Type) where
  rawInstrType : F
  op1 : F
  op2 : F
  op3 : F

/--
  Decoded instruction type, represented as a one-hot encoding in a vector of 4 field elements.
  The four possible instruction types are:
  - ADD
  - MUL
  - STORE_STATE
  - LOAD_STATE
-/
structure DecodedInstructionType (F : Type) where
  isAdd : F
  isMul : F
  isStoreState : F
  isLoadState : F

/--
  Decoded addressing mode, represented as a one-hot encoding in a vector of 4 field elements.
  The four possible addressing modes are:
  - Double addressing (i.e., dereference twice from ap)
  - ap-relative addressing (i.e., dereference once from ap)
  - fp-relative addressing (i.e., dereference once from fp)
  - immediate (i.e., no dereference)
-/
structure DecodedAddressingMode (F : Type) where
  isDoubleAddressing : F
  isApRelative : F
  isFpRelative : F
  isImmediate : F

/--
  Decoded instruction, containing the instruction type and the addressing modes for the three operands.
-/
structure DecodedInstruction (F : Type) where
  instrType : DecodedInstructionType F
  addr1 : DecodedAddressingMode F
  addr2 : DecodedAddressingMode F
  addr3 : DecodedAddressingMode F


/--
  Input structure for the memory read circuit.
  Contains the current machine state, the offset operand, and the addressing mode.
-/
structure MemoryReadInput (F : Type) where
  state : State F
  offset : F
  mode : DecodedAddressingMode F

/--
  Input structure for checking the validity of a state transition.
  Contains the current state, the next state, the decoded instruction, and the values read from memory.
-/
structure StateTransitionInput (F : Type) where
  state : State F
  decoded : DecodedInstruction F
  v1 : F
  v2 : F
  v3 : F



instance : ProvableType State where
  size := 3
  toElements := fun { pc, ap, fp } => #v[pc, ap, fp]
  fromElements := fun elements => {
    pc := elements[0],
    ap := elements[1],
    fp := elements[2]
  }

instance : ProvableType RawInstruction where
  size := 4
  toElements := fun { rawInstrType, op1, op2, op3 } => #v[rawInstrType, op1, op2, op3]
  fromElements := fun elements => {
    rawInstrType := elements[0],
    op1 := elements[1],
    op2 := elements[2],
    op3 := elements[3]
  }

instance : ProvableType DecodedInstructionType where
  size := 4
  toElements := fun { isAdd, isMul, isStoreState, isLoadState } => #v[isAdd, isMul, isStoreState, isLoadState]
  fromElements := fun elements => {
    isAdd := elements[0],
    isMul := elements[1],
    isStoreState := elements[2],
    isLoadState := elements[3]
  }

instance : ProvableType DecodedAddressingMode where
  size := 4
  toElements := fun { isDoubleAddressing, isApRelative, isFpRelative, isImmediate } => #v[isDoubleAddressing, isApRelative, isFpRelative,
    isImmediate]
  fromElements := fun elements => {
    isDoubleAddressing := elements[0],
    isApRelative := elements[1],
    isFpRelative := elements[2],
    isImmediate := elements[3]
  }

instance : ProvableStruct DecodedInstruction where
  components := [DecodedInstructionType, DecodedAddressingMode, DecodedAddressingMode, DecodedAddressingMode]
  toComponents := fun { instrType, addr1, addr2, addr3 } => .cons instrType (.cons addr1 (.cons addr2 (.cons addr3 .nil)))
  fromComponents := fun (.cons instrType (.cons addr1 (.cons addr2 (.cons addr3 .nil)))) => {
    instrType, addr1, addr2, addr3
  }

instance : ProvableStruct MemoryReadInput where
  components := [State, field, DecodedAddressingMode]
  toComponents := fun { state, offset, mode } => .cons state (.cons offset (.cons mode .nil))
  fromComponents := fun (.cons state (.cons offset (.cons mode .nil))) => {
    state, offset, mode
  }

instance : ProvableStruct StateTransitionInput where
  components := [State, DecodedInstruction, field, field, field]
  toComponents := fun { state, decoded, v1, v2, v3 } =>
    .cons state (.cons decoded (.cons v1 (.cons v2 (.cons v3 .nil))))
  fromComponents := fun (.cons state (.cons decoded (.cons v1 (.cons v2 (.cons v3 .nil))))) => {
    state, decoded, v1, v2, v3
  }

@[ext]
lemma State.ext {F : Type} {s1 s2 : State F} (h1 : s1.pc = s2.pc) (h2 : s1.ap = s2.ap) (h3 : s1.fp = s2.fp) : s1 = s2 := by
  cases s1; cases s2; simp_all only


end Examples.FemtoCairo.Types
