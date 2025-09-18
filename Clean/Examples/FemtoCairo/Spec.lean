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
  let addr1 := bits[2].val + 2 * bits[3].val
  let addr2 := bits[4].val + 2 * bits[5].val
  let addr3 := bits[6].val + 2 * bits[7].val
  some (type, addr1, addr2, addr3)

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
-/
def dataMemoryAccess
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (addr : (F p)) (mode : ℕ) (ap : F p) (fp : F p) : Option (F p) :=
  match mode with
  | 0 => do
      let addr' ← memoryAccess memory addr
      memoryAccess memory (ap + addr')
  | 1 => memoryAccess memory (ap + addr)
  | 2 => memoryAccess memory (fp + addr)
  | _ => addr

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
  -- read and decode the current instruction
  let { rawInstrType, op1, op2, op3 } ← fetchInstruction program state.pc
  let (instr_type, addr1, addr2, addr3) ← decodeInstruction rawInstrType

  let v1 ← dataMemoryAccess memory op1 addr1 state.ap state.fp
  let v2 ← dataMemoryAccess memory op2 addr2 state.ap state.fp
  let v3 ← dataMemoryAccess memory op3 addr3 state.ap state.fp

  computeNextState instr_type v1 v2 v3 state

/--
  Executes the femtoCairo machine for a bounded number of steps `steps`.
  Returns the final state if `steps` iteration of the state
  transition execution completed successfully, otherwise returns None.
-/
def femtoCairoMachineBoundedExecution
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (initial_pc : (F p)) (initial_ap : (F p)) (initial_fp : (F p)) (steps : Nat) :
    Option (State (F p)) :=
  let rec aux (curr_state : State (F p)) (steps_left : Nat) :
      Option (State (F p)) :=
    if steps_left = 0 then
      some curr_state
    else
      match femtoCairoMachineTransition program memory curr_state with
      | some new_state =>
          aux new_state (steps_left - 1)
      | none => none
  aux { pc := initial_pc, ap := initial_ap, fp := initial_fp } steps

end Examples.FemtoCairo.Spec
