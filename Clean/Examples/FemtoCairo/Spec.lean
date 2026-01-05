import Clean.Utils.Bits
import Clean.Utils.Field

import Clean.Examples.FemtoCairo.Types

namespace Examples.FemtoCairo.Spec
open Utils.Bits
open Examples.FemtoCairo.Types
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  Decode a femtoCairo instruction into its components.
  Each instruction is represented as a field element in `F p`.
-/
def decodeInstruction (instr : (F p)) : Option (ℕ × ℕ × ℕ × ℕ) :=
  if instr.val ≥ 256 then
    none
  else
  let bits := fieldToBits 8 instr
  let type := bits[0].val + 2 * bits[1].val
  let mode1 := bits[2].val + 2 * bits[3].val
  let mode2 := bits[4].val + 2 * bits[5].val
  let mode3 := bits[6].val + 2 * bits[7].val
  some (type, mode1, mode2, mode3)

/--
  Safe memory access function. Returns `some value` if the address is within bounds,
  otherwise returns `none`.
-/
def memoryAccess {n : ℕ} [NeZero n] (memory : Fin n → F p) (addr : F p) : Option (F p) :=
  if h : addr.val < n then
    some (memory ⟨addr.val, h⟩)
  else
    none

/--
  Fetch an instruction from the program memory at the given program counter (pc).
-/
def fetchInstruction
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    (pc : (F p)) : Option (RawInstruction (F p)) := do
  let type ← memoryAccess program pc
  let op1 ← memoryAccess program (pc + 1)
  let op2 ← memoryAccess program (pc + 2)
  let op3 ← memoryAccess program (pc + 3)
  some { rawInstrType := type, op1, op2, op3 }

/--
  Perform a memory access based on the addressing mode.
  - addr: the offset value from the instruction operand
  - mode: addressing mode (0=double, 1=ap-relative, 2=fp-relative, 3=immediate)
-/
def dataMemoryAccess
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (addr : (F p)) (mode : ℕ) (ap : F p) (fp : F p) : Option (F p) :=
  match mode with
  | 0 => do
      let addr' ← memoryAccess memory (ap + addr)
      memoryAccess memory addr'
  | 1 => memoryAccess memory (ap + addr)
  | 2 => memoryAccess memory (fp + addr)
  | _ => addr

/--
  Set of accessed addresses in the circuit. Current implementation
  accesses all addresses touched by all of the addressing modes.
-/
def dataMemoryAddresses
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (addr : (F p)) (ap : F p) (fp : F p) : Set (F p) :=
  {fp + addr, ap + addr, addr} ∪
  match memoryAccess memory (ap + addr) with
   | some addr' => {addr'}
   | none => ∅

/--
  Compute the next state of the femtoCairo machine based on the current state and instruction
  operands. Returns `some nextState` if the transition is valid, otherwise returns `none`.
-/
def computeNextState
    (instr_type : ℕ) (v1 : (F p)) (v2 : (F p)) (v3 : (F p))
    (state : State (F p)) :
    Option (State (F p)) :=
  match instr_type with
  -- ADD
  | 0 => if v1 + v2 = v3 then
            some { pc := state.pc + 4, ap := state.ap, fp := state.fp }
         else
            none
  -- MUL
  | 1 => if v1 * v2 = v3 then
            some { pc := state.pc + 4, ap := state.ap, fp := state.fp }
          else
            none
  -- STORE_STATE
  | 2 => if v1 = state.pc ∧ v2 = state.ap ∧ v3 = state.fp then
            some { pc := state.pc + 4, ap := state.ap, fp := state.fp }
          else
            none
  -- LOAD_STATE
  | 3 => some { pc := v1, ap := v2, fp := v3 }
  -- Invalid instruction type
  | _ => none

/--
  State transition function for the femtoCairo machine.
  Returns the new state if there is a valid transition,
  otherwise returns None.

  NOTE: a sequence of state transitions (i.e., a program execution) is considered valid
  if all individual transitions are valid.
-/
def femtoCairoMachineTransition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (state : State (F p)) : Option (State (F p)) := do
  -- fetch instruction
  let { rawInstrType, op1, op2, op3 } ← fetchInstruction program state.pc

  -- decode instruction
  let (instr_type, mode1, mode2, mode3) ← decodeInstruction rawInstrType

  -- perform relevant memory accesses
  let v1 ← dataMemoryAccess memory op1 mode1 state.ap state.fp
  let v2 ← dataMemoryAccess memory op2 mode2 state.ap state.fp
  let v3 ← dataMemoryAccess memory op3 mode3 state.ap state.fp

  -- return the next state
  computeNextState instr_type v1 v2 v3 state

/--
  Executes the femtoCairo machine for a bounded number of steps `steps`.
  Returns the final state if `steps` iteration of the state
  transition execution completed successfully, otherwise returns None.
-/
def femtoCairoMachineBoundedExecution
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (state : Option (State (F p))) (steps : Nat) :
    Option (State (F p)) := match steps with
  | 0 => state
  | i + 1 => do
    let reachedState ← femtoCairoMachineBoundedExecution program memory state i
    femtoCairoMachineTransition program memory reachedState

/--
  A program is valid if all instruction bytes in the program memory are < 256.
  This ensures that `decodeInstruction` will always succeed for any fetched instruction.
-/
def ValidProgram {programSize : ℕ} (program : Fin programSize → F p) : Prop :=
  ∀ (i : Fin programSize), (program i).val < 256

/--
  Program size is valid if `programSize + 3 < p`. This ensures no field arithmetic
  wraparound can occur when accessing consecutive instruction addresses (pc, pc+1, pc+2, pc+3).
  In practice, this is always satisfied since program sizes are much smaller than cryptographic primes.
-/
def ValidProgramSize (p : ℕ) (programSize : ℕ) : Prop := programSize + 3 < p

end Examples.FemtoCairo.Spec
