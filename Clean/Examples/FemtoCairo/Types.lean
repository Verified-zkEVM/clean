import Clean.Circuit
import Clean.Utils.Field
import Clean.Utils.Primes
namespace Examples.FemtoCairo.Types
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  State of the femtoCairo machine, represented as a structure (pc, ap, fp).
-/
structure State (F : Type) where
  pc : F
  ap : F
  fp : F

instance {α : Type} [Fintype α] : Fintype (State α) :=
  Fintype.ofEquiv (α × α × α) {
    toFun := fun (pc, ap, fp) => ⟨pc, ap, fp⟩
    invFun := fun s => (s.pc, s.ap, s.fp)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

instance : ProvableType State where
  size := 3
  toElements := fun { pc, ap, fp } => #v[pc, ap, fp]
  fromElements := fun elements => {
    pc := elements[0],
    ap := elements[1],
    fp := elements[2]
  }

/--
  Raw instruction that is fetched from the program memory,
  represented as a structure (instrType, op1, op2, op3).
-/
structure RawInstruction (F : Type) where
  rawInstrType : F
  op1 : F
  op2 : F
  op3 : F

instance : ProvableType RawInstruction where
  size := 4
  toElements := fun { rawInstrType, op1, op2, op3 } => #v[rawInstrType, op1, op2, op3]
  fromElements := fun elements => {
    rawInstrType := elements[0],
    op1 := elements[1],
    op2 := elements[2],
    op3 := elements[3]
  }

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

instance : ProvableType DecodedInstructionType where
  size := 4
  toElements := fun { isAdd, isMul, isStoreState, isLoadState } => #v[isAdd, isMul, isStoreState, isLoadState]
  fromElements := fun elements => {
    isAdd := elements[0],
    isMul := elements[1],
    isStoreState := elements[2],
    isLoadState := elements[3]
  }

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

/--
  Decoded instruction, containing the instruction type and the addressing modes for the three operands.
-/
structure DecodedInstruction (F : Type) where
  instrType : DecodedInstructionType F
  mode1 : DecodedAddressingMode F
  mode2 : DecodedAddressingMode F
  mode3 : DecodedAddressingMode F
deriving ProvableStruct

/--
  Input structure for the memory read circuit.
  Contains the current machine state, the offset operand, and the addressing mode.
-/
structure MemoryReadInput (F : Type) where
  state : State F
  offset : F
  mode : DecodedAddressingMode F
deriving ProvableStruct

/--
  Input structure for checking the validity of a state transition.
  Contains the current state, the decoded instruction, and the values read from memory.
-/
structure StateTransitionInput (F : Type) where
  state : State F
  decoded : DecodedInstruction F
  v1 : F
  v2 : F
  v3 : F
deriving ProvableStruct

/-! Constructor-keyed composite eval rules (see `U64.eval_mk`): decomposition fires only on
struct literals, and component evals commute into projections of the opaque composite eval,
which is the atom `grind`'s subcircuit composition rules pattern on. -/

section EvalLemmas
variable {F : Type} [FiniteField F] (env : Environment F)

/-- Decomposition into components (see `U64.eval_eq_components`): deliberately untagged,
supply as an explicit hint where a composite eval hypothesis must be split. -/
theorem State.eval_eq_components (x : State (Expression F)) :
    eval env x =
      ⟨Expression.eval env x.pc, Expression.eval env x.ap, Expression.eval env x.fp⟩ := by
  with_unfolding_all rfl

theorem RawInstruction.eval_eq_components (x : RawInstruction (Expression F)) :
    eval env x =
      ⟨Expression.eval env x.rawInstrType, Expression.eval env x.op1,
       Expression.eval env x.op2, Expression.eval env x.op3⟩ := by
  with_unfolding_all rfl

theorem DecodedInstructionType.eval_eq_components (x : DecodedInstructionType (Expression F)) :
    eval env x =
      ⟨Expression.eval env x.isAdd, Expression.eval env x.isMul,
       Expression.eval env x.isStoreState, Expression.eval env x.isLoadState⟩ := by
  with_unfolding_all rfl

theorem DecodedAddressingMode.eval_eq_components (x : DecodedAddressingMode (Expression F)) :
    eval env x =
      ⟨Expression.eval env x.isDoubleAddressing, Expression.eval env x.isApRelative,
       Expression.eval env x.isFpRelative, Expression.eval env x.isImmediate⟩ := by
  with_unfolding_all rfl

theorem DecodedInstruction.eval_eq_components (x : DecodedInstruction (Expression F)) :
    eval env x =
      ⟨eval env x.instrType, eval env x.mode1, eval env x.mode2, eval env x.mode3⟩ := by
  simp only [circuit_norm]

@[grind =]
theorem State.eval_mk (pc ap fp : Expression F) :
    eval env (⟨pc, ap, fp⟩ : State (Expression F)) =
      ⟨Expression.eval env pc, Expression.eval env ap, Expression.eval env fp⟩ := by
  with_unfolding_all rfl

@[grind =]
theorem RawInstruction.eval_mk (t o1 o2 o3 : Expression F) :
    eval env (⟨t, o1, o2, o3⟩ : RawInstruction (Expression F)) =
      ⟨Expression.eval env t, Expression.eval env o1,
       Expression.eval env o2, Expression.eval env o3⟩ := by
  with_unfolding_all rfl

@[grind =]
theorem DecodedInstructionType.eval_mk (a m s l : Expression F) :
    eval env (⟨a, m, s, l⟩ : DecodedInstructionType (Expression F)) =
      ⟨Expression.eval env a, Expression.eval env m,
       Expression.eval env s, Expression.eval env l⟩ := by
  with_unfolding_all rfl

@[grind =]
theorem DecodedInstructionType.eval_isAdd (x : DecodedInstructionType (Expression F)) :
    Expression.eval env x.isAdd = (eval env x).isAdd := by with_unfolding_all rfl

@[grind =]
theorem DecodedInstructionType.eval_isMul (x : DecodedInstructionType (Expression F)) :
    Expression.eval env x.isMul = (eval env x).isMul := by with_unfolding_all rfl

@[grind =]
theorem DecodedInstructionType.eval_isStoreState (x : DecodedInstructionType (Expression F)) :
    Expression.eval env x.isStoreState = (eval env x).isStoreState := by with_unfolding_all rfl

@[grind =]
theorem DecodedInstructionType.eval_isLoadState (x : DecodedInstructionType (Expression F)) :
    Expression.eval env x.isLoadState = (eval env x).isLoadState := by with_unfolding_all rfl

@[grind =]
theorem DecodedAddressingMode.eval_mk (d a f i : Expression F) :
    eval env (⟨d, a, f, i⟩ : DecodedAddressingMode (Expression F)) =
      ⟨Expression.eval env d, Expression.eval env a,
       Expression.eval env f, Expression.eval env i⟩ := by
  with_unfolding_all rfl

@[grind =]
theorem DecodedAddressingMode.eval_isDoubleAddressing (x : DecodedAddressingMode (Expression F)) :
    Expression.eval env x.isDoubleAddressing = (eval env x).isDoubleAddressing := by
  with_unfolding_all rfl

@[grind =]
theorem DecodedAddressingMode.eval_isApRelative (x : DecodedAddressingMode (Expression F)) :
    Expression.eval env x.isApRelative = (eval env x).isApRelative := by with_unfolding_all rfl

@[grind =]
theorem DecodedAddressingMode.eval_isFpRelative (x : DecodedAddressingMode (Expression F)) :
    Expression.eval env x.isFpRelative = (eval env x).isFpRelative := by with_unfolding_all rfl

@[grind =]
theorem DecodedAddressingMode.eval_isImmediate (x : DecodedAddressingMode (Expression F)) :
    Expression.eval env x.isImmediate = (eval env x).isImmediate := by with_unfolding_all rfl

@[grind =]
theorem DecodedInstruction.eval_mk (t : DecodedInstructionType (Expression F))
    (m1 m2 m3 : DecodedAddressingMode (Expression F)) :
    eval env ({ instrType := t, mode1 := m1, mode2 := m2, mode3 := m3 } :
        DecodedInstruction (Expression F)) =
      { instrType := eval env t, mode1 := eval env m1, mode2 := eval env m2,
        mode3 := eval env m3 } := by
  simp only [circuit_norm]

@[grind =]
theorem DecodedInstruction.eval_instrType (x : DecodedInstruction (Expression F)) :
    eval env x.instrType = (eval env x).instrType := by simp only [circuit_norm]

@[grind =]
theorem DecodedInstruction.eval_mode1 (x : DecodedInstruction (Expression F)) :
    eval env x.mode1 = (eval env x).mode1 := by simp only [circuit_norm]

@[grind =]
theorem DecodedInstruction.eval_mode2 (x : DecodedInstruction (Expression F)) :
    eval env x.mode2 = (eval env x).mode2 := by simp only [circuit_norm]

@[grind =]
theorem DecodedInstruction.eval_mode3 (x : DecodedInstruction (Expression F)) :
    eval env x.mode3 = (eval env x).mode3 := by simp only [circuit_norm]

end EvalLemmas

/--
  Convert the one-hot encoding of an instruction type back to its numeric representation.
-/
def DecodedInstructionType.val : DecodedInstructionType (F p) → ℕ := fun instrType =>
  if instrType.isAdd = 1 then 0
  else if instrType.isMul = 1 then 1
  else if instrType.isStoreState = 1 then 2
  else 3

/--
  Property that checks if the one-hot encoding of an instruction type is valid, i.e., only
  one of the four fields is set to 1 and the others are set to 0.
-/
def DecodedInstructionType.isEncodedCorrectly (instrType : DecodedInstructionType (F p)) : Prop :=
  (instrType.isAdd = 1 ∧ instrType.isMul = 0 ∧ instrType.isStoreState = 0 ∧ instrType.isLoadState = 0) ∨
  (instrType.isAdd = 0 ∧ instrType.isMul = 1 ∧ instrType.isStoreState = 0 ∧ instrType.isLoadState = 0) ∨
  (instrType.isAdd = 0 ∧ instrType.isMul = 0 ∧ instrType.isStoreState = 1 ∧ instrType.isLoadState = 0) ∨
  (instrType.isAdd = 0 ∧ instrType.isMul = 0 ∧ instrType.isStoreState = 0 ∧ instrType.isLoadState = 1)

/--
  Convert the one-hot encoding of an addressing mode back to its numeric representation.
-/
def DecodedAddressingMode.val : DecodedAddressingMode (F p) → ℕ := fun mode =>
  if mode.isDoubleAddressing = 1 then 0
  else if mode.isApRelative = 1 then 1
  else if mode.isFpRelative = 1 then 2
  else 3

/--
  Property that checks if the one-hot encoding of an addressing mode is valid, i.e., only
  one of the four fields is set to 1 and the others are set to 0.
-/
def DecodedAddressingMode.isEncodedCorrectly (mode : DecodedAddressingMode (F p)) : Prop :=
  (mode.isDoubleAddressing = 1 ∧ mode.isApRelative = 0 ∧ mode.isFpRelative = 0 ∧ mode.isImmediate = 0) ∨
  (mode.isDoubleAddressing = 0 ∧ mode.isApRelative = 1 ∧ mode.isFpRelative = 0 ∧ mode.isImmediate = 0) ∨
  (mode.isDoubleAddressing = 0 ∧ mode.isApRelative = 0 ∧ mode.isFpRelative = 1 ∧ mode.isImmediate = 0) ∨
  (mode.isDoubleAddressing = 0 ∧ mode.isApRelative = 0 ∧ mode.isFpRelative = 0 ∧ mode.isImmediate = 1)

end Examples.FemtoCairo.Types
