import Clean.Table.Inductive
import Clean.Gadgets.Bits
import Clean.Utils.Bits
import Clean.Utils.Field

namespace Examples.FemtoCairo
open Gadgets
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  Decode a femtoCairo instruction into its components.
  Each instruction is represented as a field element in `F p`.
-/
def decodeInstruction (instr : (F p)) : ℕ × ℕ × ℕ × ℕ :=
  let bits := fieldToBits 8 instr
  let type := bits[0].val + 2 * bits[1].val
  let addr1 := bits[2].val + 2 * bits[3].val
  let addr2 := bits[4].val + 2 * bits[5].val
  let addr3 := bits[6].val + 2 * bits[7].val
  (type, addr1, addr2, addr3)

/--
  State transition function for the femtoCairo machine.
  Returns the new (pc, ap, fp) triple if there is a valid transition,
  otherwise returns None.

  NOTE: a sequence of state transitions (i.e., a program execution) is considered valid
  if all individual transitions are valid.
-/
def femtoCairoMachineTransition (program : (F p) → (F p)) (memory : (F p) → (F p))
    (pc : (F p)) (ap : (F p)) (fp : (F p)) : Option ((F p) × (F p) × (F p)) :=

  -- read and decode the current instruction
  let instruction := program pc
  let (instr_type, addr1, addr2, addr3) := decodeInstruction instruction
  let op1 := memory (pc + 1)
  let op2 := memory (pc + 2)
  let op3 := memory (pc + 3)

  let v1 := match addr1 with
  | 0 => memory (memory (ap + op1))
  | 1 => memory (ap + op1)
  | 2 => memory (fp + op1)
  | _ => op1

  let v2 := match addr2 with
  | 0 => memory (memory (ap + op2))
  | 1 => memory (ap + op2)
  | 2 => memory (fp + op2)
  | _ => op2

  let v3 := match addr3 with
  | 0 => memory (memory (ap + op3))
  | 1 => memory (ap + op3)
  | 2 => memory (fp + op3)
  | _ => op3

  match instr_type with
  -- ADD
  | 0 => if v1 + v2 = v3 then
            some (pc + 4, ap, fp)
         else
            none
  -- MUL
  | 1 => if v1 * v2 = v3 then
            some (pc + 4, ap, fp)
          else
            none
  -- STORE_STATE
  | 2 => if v1 = pc ∧ v2 = ap ∧ v3 = fp then
            some (pc + 4, ap, fp)
          else
            none
  -- LOAD_STATE
  | 3 => some (v1, v2, v3)
  -- Invalid instruction type
  | _ => none

/--
  Executes the femtoCairo machine for a bounded number of steps `steps`.
  Returns the final (pc, ap, fp) triple if `steps` iteration of the state
  transition execution completed successfully, otherwise returns None.
-/
def femtoCairoMachineBoundedExecution (program : (F p) → (F p)) (memory : (F p) → (F p))
    (initial_pc : (F p)) (initial_ap : (F p)) (initial_fp : (F p)) (steps : Nat) :
    Option ((F p) × (F p) × (F p)) :=
  let rec aux (pc : (F p)) (ap : (F p)) (fp : (F p)) (steps_left : Nat) :
      Option ((F p) × (F p) × (F p)) :=
    if steps_left = 0 then
      some (pc, ap, fp)
    else
      match femtoCairoMachineTransition program memory pc ap fp with
      | some (new_pc, new_ap, new_fp) =>
          aux new_pc new_ap new_fp (steps_left - 1)
      | none => none
  aux initial_pc initial_ap initial_fp steps

/--
  Construct a table that represents a read-only memory containing all pairs (i, f(i)) for i in [0, length).
  - The **program table** it is OK, as it a fixed and public,
    so the verifier always has access to lookups into its table.
  - For the **memory table**, it is committed by the prover, and no constraints are enforced on it.
    For our formalization, we represent it also as a fixed table. This is without loss of generality,
    since we do not make any assumptions on its content, and its role is just to fix a function.

  To represent, e.g., a read-write memory we will need a more complex construction.
-/
def ReadOnlyTableFromFunction (f : (F p) → (F p)) (length : ℕ) (h : length < p) [NeZero length] : Table (F p) fieldPair := .fromStatic {
  name := "ReadOnlyMemory"
  length := length
  row i := (i, f i)
  index := fun (i, _) => i.val
  Spec := fun (i, v) => v = f i ∧ i.val < length
  contains_iff := by
    intro t
    constructor
    · rintro ⟨ i, h: t = _ ⟩
      simp_all
      sorry
    · intro h
      simp_all
      use Fin.ofNat length t.1.val
      sorry
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
  addr1 : DecodedAddressingMode F
  addr2 : DecodedAddressingMode F
  addr3 : DecodedAddressingMode F

instance : ProvableStruct DecodedInstruction where
  components := [DecodedInstructionType, DecodedAddressingMode, DecodedAddressingMode, DecodedAddressingMode]
  toComponents := fun { instrType, addr1, addr2, addr3 } => .cons instrType (.cons addr1 (.cons addr2 (.cons addr3 .nil)))
  fromComponents := fun (.cons instrType (.cons addr1 (.cons addr2 (.cons addr3 .nil)))) => {
    instrType, addr1, addr2, addr3
  }

def decodeInstructionCircuit : FormalCircuit (F p) field DecodedInstruction where
  main := fun instruction => do
    let bits ← Gadgets.ToBits.toBits 8 (by linarith [p_large_enough.elim]) instruction
    return {
      instrType := {
        isAdd := (1 : Expression _) - bits[0] - bits[1] + bits[0] * bits[1],
        isMul := bits[0] - bits[0] * bits[1],
        isStoreState := bits[1] - bits[0] * bits[1],
        isLoadState := bits[0] * bits[1]
      },
      addr1 := {
        isDoubleAddressing := (1 : Expression _) - bits[2] - bits[3] + bits[2] * bits[3],
        isApRelative := bits[2] - bits[2] * bits[3],
        isFpRelative := bits[3] - bits[2] * bits[3],
        isImmediate := bits[2] * bits[3]
      },
      addr2 := {
        isDoubleAddressing := (1 : Expression _) - bits[4] - bits[5] + bits[4] * bits[5],
        isApRelative := bits[4] - bits[4] * bits[5],
        isFpRelative := bits[5] - bits[4] * bits[5],
        isImmediate := bits[4] * bits[5]
      },
      addr3 := {
        isDoubleAddressing := (1 : Expression _) - bits[6] - bits[7] + bits[6] * bits[7],
        isApRelative := bits[6] - bits[6] * bits[7],
        isFpRelative := bits[7] - bits[6] * bits[7],
        isImmediate := bits[6] * bits[7]
      }
    }
  localLength _ := 8

  Assumptions | instruction => instruction.val < 256

  Spec
  | instruction, output =>
    let (instr_type, addr1, addr2, addr3) := decodeInstruction instruction
    (output.instrType.isAdd = if instr_type = 0 then 1 else 0) ∧
    (output.instrType.isMul = if instr_type = 1 then 1 else 0) ∧
    (output.instrType.isStoreState = if instr_type = 2 then 1 else 0) ∧
    (output.instrType.isLoadState = if instr_type = 3 then 1 else 0) ∧

    (output.addr1.isDoubleAddressing = if addr1 = 0 then 1 else 0) ∧
    (output.addr1.isApRelative = if addr1 = 1 then 1 else 0) ∧
    (output.addr1.isFpRelative = if addr1 = 2 then 1 else 0) ∧
    (output.addr1.isImmediate = if addr1 = 3 then 1 else 0) ∧

    (output.addr2.isDoubleAddressing = if addr2 = 0 then 1 else 0) ∧
    (output.addr2.isApRelative = if addr2 = 1 then 1 else 0) ∧
    (output.addr2.isFpRelative = if addr2 = 2 then 1 else 0) ∧
    (output.addr2.isImmediate = if addr2 = 3 then 1 else 0) ∧

    (output.addr3.isDoubleAddressing = if addr3 = 0 then 1 else 0) ∧
    (output.addr3.isApRelative = if addr3 = 1 then 1 else 0) ∧
    (output.addr3.isFpRelative = if addr3 = 2 then 1 else 0) ∧
    (output.addr3.isImmediate = if addr3 = 3 then 1 else 0)

  soundness := by
    sorry
  completeness := by
    sorry


/--
  State of the femtoCairo machine, represented as a triple (pc, ap, fp).
-/
structure State (F : Type) where
  pc : F
  ap : F
  fp : F

instance : ProvableType State where
  size := 3
  toElements := fun { pc, ap, fp } => #v[pc, ap, fp]
  fromElements := fun elements => {
    pc := elements[0],
    ap := elements[1],
    fp := elements[2]
  }

structure MemoryReadInput (F : Type) where
  state : State F
  offset : F
  mode : DecodedAddressingMode F

instance : ProvableStruct MemoryReadInput where
  components := [State, field, DecodedAddressingMode]
  toComponents := fun { state, offset, mode } => .cons state (.cons offset (.cons mode .nil))
  fromComponents := fun (.cons state (.cons offset (.cons mode .nil))) => {
    state, offset, mode
  }

def readFromMemory (memory : (F p) → (F p)) (memoryTable : Table (F p) fieldPair) : FormalCircuit (F p)
    MemoryReadInput field where
  main := fun { state, offset, mode } => do
    -- read into memory for all cases of addr1
    let v0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + offset)
    let v1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + offset)
    let v2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + offset)
    lookup memoryTable ⟨(state.ap + offset), v0⟩
    lookup memoryTable ⟨(state.ap + offset), v1⟩
    lookup memoryTable ⟨(state.fp + offset), v2⟩

    -- witness the actual value based on the addressing mode
    let value : Expression _ ← witness fun eval =>
      eval mode.isDoubleAddressing * eval v0 +
      eval mode.isApRelative * eval v1 +
      eval mode.isFpRelative * eval v2 +
      eval mode.isImmediate * eval offset

    -- enforce that value is correctly selected
    assertZero <|
      mode.isDoubleAddressing * (value - v0) +
      mode.isApRelative * (value - v1) +
      mode.isFpRelative * (value - v2) +
      mode.isImmediate * (value - offset)
    return value

  localLength _ := 4
  Assumptions := sorry
  Spec := sorry
  soundness := by
    sorry
  completeness := by
    sorry


def stateTransitionCircuit (program : (F p) → (F p)) (memory : (F p) → (F p))
    (len : ℕ) [NeZero len] (h_len : len < p) (state : Var State (F p)) :
    Circuit (F p) (Var State (F p)) := do
  let programTable := ReadOnlyTableFromFunction program len h_len
  let memoryTable := ReadOnlyTableFromFunction memory len h_len

  let instruction : Expression _ ← witness fun eval => program (eval state.pc)
  let op1 ← witness fun eval => memory (eval state.pc + 1)
  let op2 ← witness fun eval => memory (eval state.pc + 2)
  let op3 ← witness fun eval => memory (eval state.pc + 3)
  lookup programTable ⟨state.pc, instruction⟩
  lookup programTable ⟨state.pc + 1, op1⟩
  lookup programTable ⟨state.pc + 2, op2⟩
  lookup programTable ⟨state.pc + 3, op3⟩

  let decoded : DecodedInstruction (Expression (F p)) ← subcircuit decodeInstructionCircuit instruction

  let v1 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op1, mode := decoded.addr1 }
  let v2 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op2, mode := decoded.addr2 }
  let v3 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op3, mode := decoded.addr3 }

  let nextState : State _ ← ProvableType.witness fun eval => {
    pc := if eval decoded.instrType.isLoadState = 1 then eval v1 else eval state.pc + 4
    ap := if eval decoded.instrType.isLoadState = 1 then eval v2 else eval state.ap
    fp := if eval decoded.instrType.isLoadState = 1 then eval v3 else eval state.fp
  }

  assertZero (decoded.instrType.isAdd * (v3 - (v1 + v2)))

  assertZero (decoded.instrType.isMul * (v3 - (v1 * v2)))

  assertZero (decoded.instrType.isStoreState * (v1 - state.pc))
  assertZero (decoded.instrType.isStoreState * (v2 - state.ap))
  assertZero (decoded.instrType.isStoreState * (v3 - state.fp))

  assertZero (decoded.instrType.isLoadState * (nextState.pc - v1))
  assertZero (decoded.instrType.isLoadState * (nextState.ap - v2))
  assertZero (decoded.instrType.isLoadState * (nextState.fp - v3))
  assertZero ((1 - decoded.instrType.isLoadState) * (nextState.pc - (state.pc + 4)))

  return nextState

end Examples.FemtoCairo
