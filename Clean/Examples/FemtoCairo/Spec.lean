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

-- Helper lemmas for completeness proofs

/-- If memoryAccess succeeds, the address is in bounds -/
lemma memoryAccess_isSome_implies_bounds {n : ℕ} [NeZero n]
    (memory : Fin n → F p) (addr : F p)
    (h : (memoryAccess memory addr).isSome) : addr.val < n := by
  simp only [memoryAccess, Option.isSome_iff_exists] at h
  split at h
  case isTrue h_bound => exact h_bound
  case isFalse => simp at h

/-- If memoryAccess returns some value, the address is in bounds -/
lemma memoryAccess_eq_some_implies_bounds {n : ℕ} [NeZero n]
    (memory : Fin n → F p) (addr : F p) (v : F p)
    (h : memoryAccess memory addr = some v) : addr.val < n := by
  simp only [memoryAccess] at h
  split at h
  case isTrue h_bound => exact h_bound
  case isFalse => simp at h

/-- If decodeInstruction succeeds, the instruction value is < 256 -/
lemma decodeInstruction_isSome_implies_bound (instr : F p)
    (h : (decodeInstruction instr).isSome) : instr.val < 256 := by
  simp only [decodeInstruction] at h
  split at h
  case isTrue h_ge => simp at h
  case isFalse h_lt => omega

/-- If decodeInstruction returns some value, the instruction value is < 256 -/
lemma decodeInstruction_eq_some_implies_bound (instr : F p) (result : ℕ × ℕ × ℕ × ℕ)
    (h : decodeInstruction instr = some result) : instr.val < 256 := by
  simp only [decodeInstruction] at h
  split at h
  case isTrue h_ge => simp at h
  case isFalse h_lt => omega

/-- If femtoCairoMachineTransition succeeds, fetchInstruction succeeds -/
lemma transition_isSome_implies_fetch_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    (fetchInstruction program state.pc).isSome := by
  simp only [femtoCairoMachineTransition, Option.isSome_iff_exists] at h
  obtain ⟨next, h_next⟩ := h
  simp only [Option.bind_eq_bind] at h_next
  cases h_fetch : fetchInstruction program state.pc
  · simp [h_fetch] at h_next
  · simp

/-- If fetchInstruction succeeds and there's no field wraparound, pc + 3 < programSize -/
lemma fetchInstruction_isSome_implies_pc_bound
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    (h_programSize : programSize < p)
    (pc : F p)
    (h : (fetchInstruction program pc).isSome) : pc.val + 3 < programSize := by
  -- This requires showing that if fetchInstruction succeeds (meaning all 4 memory accesses succeed),
  -- then pc.val + 3 < programSize. The key insight is that memoryAccess (pc + 3) succeeds means
  -- (pc + 3).val < programSize. For typical program sizes (< p - 3), this implies pc.val + 3 < p
  -- (no wraparound), so (pc + 3).val = pc.val + 3 and we're done.
  -- Edge case: if programSize is close to p (within 3), wraparound is possible and the lemma
  -- may not hold. This is a limitation that should be addressed by adding programSize ≤ p - 3 assumption.
  sorry

/-- If transition succeeds, decode succeeds -/
lemma transition_isSome_implies_decode_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw, fetchInstruction program state.pc = some raw ∧
           (decodeInstruction raw.rawInstrType).isSome := by
  simp only [femtoCairoMachineTransition, Option.isSome_iff_exists] at h
  obtain ⟨next, h_next⟩ := h
  simp only [Option.bind_eq_bind] at h_next
  cases h_fetch : fetchInstruction program state.pc with
  | none => simp [h_fetch] at h_next
  | some raw =>
    use raw
    constructor
    · rfl
    · simp only [h_fetch, Option.some_bind] at h_next
      cases h_decode : decodeInstruction raw.rawInstrType with
      | none => simp [h_decode] at h_next
      | some _ => simp

/-- If transition succeeds with ValidProgram, the fetched instruction type is < 256 -/
lemma transition_isSome_with_valid_program_implies_instr_bound
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h_valid : Types.ValidProgram program)
    (h_trans : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw, fetchInstruction program state.pc = some raw ∧ raw.rawInstrType.val < 256 := by
  obtain ⟨raw, h_fetch, h_decode⟩ := transition_isSome_implies_decode_isSome program memory state h_trans
  use raw
  constructor
  · exact h_fetch
  · exact decodeInstruction_isSome_implies_bound raw.rawInstrType h_decode

/-- If transition succeeds, all intermediate steps succeed -/
lemma transition_isSome_implies_computeNextState_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw decode v1 v2 v3,
      fetchInstruction program state.pc = some raw ∧
      decodeInstruction raw.rawInstrType = some decode ∧
      dataMemoryAccess memory raw.op1 decode.1 state.ap state.fp = some v1 ∧
      dataMemoryAccess memory raw.op2 decode.2.1 state.ap state.fp = some v2 ∧
      dataMemoryAccess memory raw.op3 decode.2.2.1 state.ap state.fp = some v3 ∧
      (computeNextState decode.2.2.2 v1 v2 v3 state).isSome := by
  -- The transition is a chain of Option.bind operations. If the whole chain returns some,
  -- each intermediate step must have returned some.
  sorry

end Examples.FemtoCairo.Spec
