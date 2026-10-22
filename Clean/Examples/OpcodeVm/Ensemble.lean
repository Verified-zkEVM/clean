/-
A toy VM with one table per opcode, as in modern zkVMs: the opcode tables share the VM's state
channel, and witness generation routes each state to the table of the opcode at its `pc`.
-/
module

public import Clean.Air.Vm
public import Clean.Air.Lookup
public import Clean.Air.WitnessGeneration

@[expose] public section

open Air.Flat

namespace OpcodeVm

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- The VM's opcodes. Each one updates the accumulator with the instruction's operand. -/
inductive Opcode where
  | add
  | mul

/-- The opcode's number in the program. Rows past the end of the program have opcode 0. -/
def Opcode.code : Opcode → ℕ
  | .add => 1
  | .mul => 2

def Opcode.name : Opcode → String
  | .add => "add"
  | .mul => "mul"

def Opcode.apply {α : Type} [Add α] [Mul α] : Opcode → α → α → α
  | .add, acc, operand => acc + operand
  | .mul, acc, operand => acc * operand

structure State (F : Type) where
  pc : F
  acc : F
deriving ProvableStruct

structure Instruction (F : Type) where
  pc : F
  opcode : F
  operand : F
deriving ProvableStruct

/-- A program is a list of instructions, the opcode and the operand. -/
abbrev Program := List (Opcode × ℕ)

/-- The program table has a power-of-two height. -/
def programHeight (program : Program) : UInt64 :=
  (WitnessGeneration.nextPowerOfTwo program.length).toUInt64

/-- The instruction at row `i` of the program table. -/
def programRow (program : Program) (i : Witgen.U64Expr (F p)) : Instruction (Witgen.FExpr (F p)) :=
  let opcodes := (program.map fun (opcode, _) => (opcode.code : F p)).toArray
  let operands := (program.map fun (_, operand) => (operand : F p)).toArray
  { pc := i.toField, opcode := opcodes[i], operand := operands[i] }

/-- The program, as a table of instructions. -/
def programLookup (program : Program) : Lookup (F p) Instruction where
  name := "program"
  height := programHeight program
  row i := pure (programRow program i)
  valid := by simp [circuit_norm, programRow, -List.map_map]
  Contains instruction := ∃ i < programHeight program,
    instruction = Witgen.M.evalRow (pure (programRow program .idx)) i
  contains_iff _ := .rfl

/-- A cell of the program table's row `pc`, as the prover reads it: column 1 holds the opcode,
column 2 the operand. -/
def programCell (pc : Expression (F p)) (column : Fin 4) : Witgen.FExpr (F p) :=
  .dataGet "program" 4 pc.val column

/-- The cell of prover data that `programCell` reads. -/
def programCellIn (data : ProverData (F p)) (pc : F p) (column : Fin 4) : F p :=
  ((data.tables "program" 4)[(UInt64.ofNat pc.val).toNat]?.getD default)[column]

def stateChannel : Channel (F p) State where
  name := "state"
  Guarantees _ _ := True

structure StepInput (F : Type) where
  enabled : F
  pc : F
  acc : F
deriving ProvableStruct

/-- One step of the VM that executes `opcode`: pull a state, check that the program has `opcode` at
its `pc`, and push the next state. -/
def step (program : Program) (opcode : Opcode) : GeneralFormalCircuit (F p) StepInput unit where
  name := opcode.name
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    stateChannel.pullIf input.enabled { pc := input.pc, acc := input.acc }
    let operand ← witness (programCell input.pc 2)
    (programLookup program).channel.pullIf input.enabled
      { pc := input.pc, opcode := .const (opcode.code : F p), operand }
    stateChannel.pushIf input.enabled { pc := input.pc + 1, acc := opcode.apply input.acc operand }

  exposedChannels
  | { enabled, pc, acc }, i₀ =>
    let operand := var ⟨ i₀ ⟩
    expose stateChannel [ pulledIf enabled { pc, acc },
      pushedIf enabled { pc := pc + 1, acc := opcode.apply acc operand } ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input
    simp [circuit_norm, stateChannel, programLookup]

  ProverAssumptions
  | { enabled, pc, .. }, data, _ => enabled = 0 ∨ enabled = 1 ∧
    (programLookup program).Contains
      { pc, opcode := opcode.code, operand := programCellIn data pc 2 }
  Spec _ _ _ := True

  channelsWithRequirements := [ stateChannel.toRaw ]
  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input_var
    simp only [circuit_norm, stateChannel, programLookup]
    intro env h_bool h_one h_zero
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel]
    obtain ⟨h_bool, -⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    rcases h_bool with rfl | rfl <;> simp
  completeness := by
    circuit_proof_start [stateChannel, programCell, programCellIn]
    rcases h_assumptions with h | ⟨h, h_contains⟩ <;> simp_all

/-- The table of `opcode`: one row per state whose `pc` holds `opcode`. Padding rows are
disabled. -/
abbrev stepComponent (program : Program) (opcode : Opcode) : Component (F p) where
  circuit := step program opcode
  generation := .demand {
    channel := stateChannel
    trigger := .push
    guard := some fun state => programCell state.pc 1 =? Witgen.FExpr.const (opcode.code : F p)
    aggregation := .perOccurrence
    input := [.const 1, .message 0, .message 1]
    padding := #[0, 0, 0]
  }

/-- The public input `(initial, final)` claims that running the program on the accumulator
`initial` ends with the accumulator `final`. -/
def verifier (program : Program) : Verifier.Program (F p) fieldPair where
  main | (initial, final) => do
    Verifier.pull stateChannel { pc := .const (program.length : F p), acc := final }
    Verifier.push stateChannel { pc := 0, acc := initial }
  Spec _ _ := True
  soundness := by simp [circuit_norm]

def vm (program : Program) : VmTables (F p) fieldPair where
  channel := stateChannel
  tables := [stepComponent program .add, stepComponent program .mul]
  unique_names := by simp [step, Opcode.name]
  verifier := verifier program
  tables_channel := by simp [circuit_norm, step, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, verifier]
  verifier_requirements data := by simp [circuit_norm, verifier, stateChannel]

def ensemble (program : Program) := SoundEnsemble.empty (F p) fieldPair
  |>.addLookup (programLookup program)
  |>.addVm (vm program)
    (by simp +instances [circuit_norm, vm, programLookup, stateChannel])
    (by simp +instances [circuit_norm, vm, step, verifier])
    (by simp [circuit_norm, vm, step, verifier, programLookup, stateChannel])
    (by simp [circuit_norm, vm, step, programLookup, Opcode.name])

/-- The program of the tests: `acc := ((((acc + 3) * 5 + 7) * 2 + 1 + 4) * 3 + 9) * 2 + 6`. -/
def exampleProgram : Program :=
  [(.add, 3), (.mul, 5), (.add, 7), (.mul, 2), (.add, 1), (.add, 4), (.mul, 3), (.add, 9),
    (.mul, 2), (.add, 6)]

/-- Run a program on an accumulator. -/
def run (program : Program) (acc : F p) : F p :=
  program.foldl (fun acc (opcode, operand) => opcode.apply acc (operand : F p)) acc

end OpcodeVm
