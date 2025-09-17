import Clean.Table.Inductive
import Clean.Gadgets.Bits
import Clean.Utils.Bits
import Clean.Utils.Field

import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.FemtoCairo.Types

namespace Examples.FemtoCairo
open Gadgets
open Utils.Bits
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

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
    let (instr_type, addr1, addr2, addr3) := Spec.decodeInstruction instruction
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

def fetchInstruction (program : (F p) → (F p)) (programTable : Table (F p) fieldPair) : FormalCircuit (F p)
    field RawInstruction where
  main := fun pc => do
    let rawInstrType : Expression _ ← witness fun eval => program (eval pc)
    let op1 ← witness fun eval => program (eval pc + 1)
    let op2 ← witness fun eval => program (eval pc + 2)
    let op3 ← witness fun eval => program (eval pc + 3)

    lookup programTable ⟨pc, rawInstrType⟩
    lookup programTable ⟨pc + 1, op1⟩
    lookup programTable ⟨pc + 2, op2⟩
    lookup programTable ⟨pc + 3, op3⟩

    return { rawInstrType, op1, op2, op3 }

  localLength _ := 4
  Assumptions := sorry
  Spec := sorry
  soundness := by
    sorry
  completeness := by
    sorry

def readFromMemory (memory : (F p) → (F p)) (memoryTable : Table (F p) fieldPair) : FormalCircuit (F p)
    MemoryReadInput field where
  main := fun { state, offset, mode } => do
    -- read into memory for all cases of addressing mode
    let v0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + offset)
    let v1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + offset)
    let v2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + offset)
    lookup memoryTable ⟨(state.ap + offset), v0⟩
    lookup memoryTable ⟨(state.ap + offset), v1⟩
    lookup memoryTable ⟨(state.fp + offset), v2⟩

    -- select the correct value based on the addressing mode
    let value <==
      mode.isDoubleAddressing * v0 +
      mode.isApRelative * v1 +
      mode.isFpRelative * v2 +
      mode.isImmediate * offset

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

  -- Fetch instruction
  let { rawInstrType, op1, op2, op3 } ← subcircuit (fetchInstruction program programTable) state.pc

  -- Decode instruction
  let decoded ← subcircuit decodeInstructionCircuit rawInstrType

  -- Perform relevant memory accesses
  let v1 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op1, mode := decoded.addr1 }
  let v2 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op2, mode := decoded.addr2 }
  let v3 ← subcircuit (readFromMemory memory memoryTable) { state, offset := op3, mode := decoded.addr3 }

  -- check state transition
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
  assertZero ((1 - decoded.instrType.isLoadState) * (nextState.ap - state.ap))
  assertZero ((1 - decoded.instrType.isLoadState) * (nextState.fp - state.fp))

  return nextState

end Examples.FemtoCairo
