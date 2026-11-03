/-
A toy VM with one table per opcode, as in modern zkVMs: the opcode tables share the VM's state
channel, and witness generation routes each state to the table of the opcode at its `pc`. Two of the
opcodes load and store the accumulator in a read-write memory.
-/
module

public import Clean.Air.MemoryVm
public import Clean.Air.WitnessGeneration

@[expose] public section

open Air.Flat

namespace OpcodeVm

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- The opcodes that update the accumulator with the instruction's operand. -/
inductive Arithmetic where
  | add
  | mul

/-- The opcodes that access the memory at the instruction's operand: `load` loads the accumulator
from there, and `store` stores it there. -/
inductive Access where
  | load
  | store

/-- The VM's opcodes. -/
inductive Opcode where
  | arithmetic (op : Arithmetic)
  | access (op : Access)

@[match_pattern] abbrev Opcode.add : Opcode := .arithmetic .add
@[match_pattern] abbrev Opcode.mul : Opcode := .arithmetic .mul
@[match_pattern] abbrev Opcode.load : Opcode := .access .load
@[match_pattern] abbrev Opcode.store : Opcode := .access .store

/-- The opcode's number in the program. Rows past the end of the program have opcode 0. -/
def Opcode.code : Opcode → ℕ
  | .add => 1
  | .mul => 2
  | .load => 3
  | .store => 4

/-- Opcode numbers are small, so they are distinct and nonzero as field elements. -/
lemma Opcode.val_code (opcode : Opcode) : (opcode.code : F p).val = opcode.code := by
  have : p > 512 := Fact.out
  exact ZMod.val_cast_of_lt
    (by rcases opcode with (_ | _) | (_ | _) <;> simp [Opcode.code] <;> omega)

lemma Opcode.code_ne_zero (opcode : Opcode) : (opcode.code : F p) ≠ 0 := fun h => by
  have h := congrArg ZMod.val h
  rw [Opcode.val_code, ZMod.val_zero] at h
  rcases opcode with (_ | _) | (_ | _) <;> simp [Opcode.code] at h

lemma Opcode.code_injective {a b : Opcode} (h : (a.code : F p) = b.code) : a = b := by
  have h := congrArg ZMod.val h
  rw [Opcode.val_code, Opcode.val_code] at h
  rcases a with (_ | _) | (_ | _) <;> rcases b with (_ | _) | (_ | _) <;> simp_all [Opcode.code]

def Arithmetic.name : Arithmetic → String
  | .add => "add"
  | .mul => "mul"

def Arithmetic.apply {α : Type} [Add α] [Mul α] : Arithmetic → α → α → α
  | .add, acc, operand => acc + operand
  | .mul, acc, operand => acc * operand

omit [Fact (p > 512)] in
@[circuit_norm]
lemma Arithmetic.eval_apply (op : Arithmetic) (env : Environment (F p))
    (acc operand : Expression (F p)) :
    (op.apply acc operand).eval env = op.apply (acc.eval env) (operand.eval env) := by
  cases op <;> simp [Arithmetic.apply, circuit_norm]

/-- Execute an instruction on the accumulator and the memory. -/
def Opcode.exec : Opcode → F p → F p × (F p → F p) → F p × (F p → F p)
  | .arithmetic op, operand, (acc, mem) => (op.apply acc operand, mem)
  | .load, address, (_, mem) => (mem address, mem)
  | .store, address, (acc, mem) => (acc, Function.update mem address acc)

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

/-- Run a program on an accumulator and a memory. -/
def run (program : Program) (state : F p × (F p → F p)) : F p × (F p → F p) :=
  program.foldl (fun state (opcode, operand) => opcode.exec (operand : F p) state) state

omit [Fact (p > 512)] in
/-- Running one more instruction executes it. -/
lemma run_take_succ (program : Program) (state : F p × (F p → F p)) {n : ℕ}
    (h : n < program.length) :
    run (program.take (n + 1)) state =
      program[n].1.exec program[n].2 (run (program.take n) state) := by
  simp only [run, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The program table has a power-of-two height. -/
def programHeight (program : Program) : UInt64 :=
  (WitnessGeneration.nextPowerOfTwo program.length).toUInt64

/-- The instruction at row `i` of the program table. -/
def programRow (program : Program) (i : Witgen.U64Expr (F p)) : Instruction (Witgen.FExpr (F p)) :=
  let opcodes := (program.map fun (opcode, _) => (opcode.code : F p)).toArray
  let operands := (program.map fun (_, operand) => (operand : F p)).toArray
  { pc := i.toField, opcode := opcodes[i], operand := operands[i] }

/-- The program, as a table of instructions: the instruction at each `pc`, and rows with opcode 0
past the end of the program. -/
def programLookup (program : Program) : Lookup (F p) Instruction where
  name := "program"
  height := programHeight program
  row i := pure (programRow program i)
  rowOf instruction := instruction.pc.val
  Contains
  | { pc, opcode, operand } => ∃ i < programHeight program, pc = i.toNat ∧
      match program[i.toNat]? with
      | some (op, value) => opcode = op.code ∧ operand = value
      | none => opcode = 0 ∧ operand = 0
  contains_iff value := by
    obtain ⟨pc, opcode, operand⟩ := value
    simp only [circuit_norm, programRow, Instruction.mk.injEq, List.getElem?_map,
      Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    refine exists_congr fun i => and_congr_right fun _ => and_congr_right fun _ => ?_
    cases program[i.toNat]? <;> simp

/-- A cell of the program table's row `pc`, as the prover reads it: column 1 holds the opcode,
column 2 the operand. -/
def programCell (pc : Expression (F p)) (column : Fin 4) : Witgen.FExpr (F p) :=
  .dataGet "program" 4 pc.val column

/-- The cell of prover data that `programCell` reads. -/
def programCellIn (data : ProverData (F p)) (pc : F p) (column : Fin 4) : F p :=
  ((data.tables "program" 4)[(UInt64.ofNat pc.val).toNat]?.getD default)[column]

omit [Fact (p > 512)] in
/-- The `pc` of an instruction in the program table doesn't wrap around when it is incremented. -/
lemma val_lt_val_add_one {program : Program} (h_height : 4 * (programHeight program).toNat ≤ p)
    {pc opcode operand : F p}
    (h_instruction : (programLookup program).Contains { pc, opcode, operand }) :
    pc.val < (pc + 1).val := by
  obtain ⟨i, hi, rfl, -⟩ := h_instruction
  rw [UInt64.lt_iff_toNat_lt] at hi
  have h_val : ((i.toNat : ℕ) : F p).val = i.toNat := ZMod.val_cast_of_lt (by omega)
  rw [ZMod.val_add_of_lt (by rw [h_val, ZMod.val_one]; omega), h_val, ZMod.val_one]
  omega

/-- The number of memory addresses. -/
def memorySize : UInt64 := 8

/-- The memory, which is initially zero. An instruction accesses it at time `pc + 1`, which is less
than twice the height of the program table. -/
def memory (program : Program) (h_height : 4 * (programHeight program).toNat ≤ p) :
    ReadWriteMemory p where
  name := "memory"
  size := memorySize
  initial _ := 0
  timeBound := 2 * programHeight program
  size_le := by
    have : p > 512 := Fact.out
    have : memorySize.toNat = 8 := rfl
    omega
  timeBound_le := by
    have : (2 * programHeight program).toNat ≤ 2 * (programHeight program).toNat := by
      rw [UInt64.toNat_mul]
      exact Nat.mod_le _ _
    omega

/-- The public input: the accumulator the program starts with, and the one it ends with. -/
structure PublicInput (F : Type) where
  initial : F
  final : F
deriving ProvableStruct

/-- The state reached after running the first `k` instructions of the program on the public
initial accumulator and the zero memory, with the memory after these instructions. -/
def Reached (program : Program) (k : ℕ) (state : State (F p)) (mem : F p → F p)
    (data : ProverData (F p)) : Prop :=
  k ≤ program.length ∧ state.pc = k ∧
    (state.acc, mem) = run (program.take k) ((data.getPublicInput PublicInput).initial, 0)

/-- The states of the VM, which `Reached` describes. -/
def stateChannel : Channel (F p) State where
  name := "state"
  Guarantees _ _ := True

/-- Executing the program's instruction at `pc` takes the state reached after `k` instructions to
the state reached after `k + 1` instructions. -/
lemma reached_step {program : Program} (h_program : program.length < p)
    {opcode : Opcode} {k : ℕ} {pc acc operand : F p} {mem : F p → F p} {data : ProverData (F p)}
    (h_state : Reached program k { pc, acc } mem data)
    (h_instruction : (programLookup program).Contains { pc, opcode := opcode.code, operand }) :
    Reached program (k + 1) { pc := pc + 1, acc := (opcode.exec operand (acc, mem)).1 }
      (opcode.exec operand (acc, mem)).2 data := by
  obtain ⟨h_k, rfl, h_acc⟩ := h_state
  obtain ⟨i, -, h_pc, h_instruction⟩ := h_instruction
  rcases h_get : program[i.toNat]? with _ | ⟨op, value⟩ <;> simp only [h_get] at h_instruction
  · exact absurd h_instruction.1 opcode.code_ne_zero
  obtain ⟨h_code, rfl⟩ := h_instruction
  obtain rfl := Opcode.code_injective h_code
  obtain ⟨hi, h_instruction⟩ := List.getElem?_eq_some_iff.mp h_get
  have h_val (n : ℕ) (hn : n ≤ program.length) : (n : F p).val = n :=
    ZMod.val_cast_of_lt (by omega)
  obtain rfl : k = i.toNat := by
    have h_pc := congrArg ZMod.val h_pc
    rwa [h_val k h_k, h_val _ hi.le] at h_pc
  simp only [Reached] at h_acc ⊢
  rw [run_take_succ program _ hi, h_instruction, ← h_acc]
  exact ⟨hi, by push_cast; rfl, rfl⟩

structure StepInput (F : Type) where
  enabled : F
  pc : F
  acc : F
deriving ProvableStruct

/-- One step of the VM that executes an arithmetic opcode: pull a state, check that the program has
the opcode at its `pc`, and push the next state. -/
def step (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) (op : Arithmetic) :
    GeneralFormalCircuit (F p) StepInput field where
  name := op.name
  main input := do
    -- enabled flag is boolean
    assertZero (input.enabled * (input.enabled - 1))
    -- pull current state
    stateChannel.pullIf input.enabled { pc := input.pc, acc := input.acc }
    -- look up current operand in the program
    let operand ← witness (programCell input.pc 2)
    (programLookup program).channel.pullIf input.enabled
      ⟨ input.pc, .const (Opcode.arithmetic op).code, operand ⟩
    -- compute next accumulator (this statically branches the circuit layout based on the operand)
    let acc := op.apply input.acc operand
    -- push next state
    stateChannel.pushIf input.enabled { pc := input.pc + 1, acc }
    return operand

  exposedChannels
  | { enabled, pc, acc }, i₀ =>
    let operand := var ⟨ i₀ ⟩
    expose stateChannel [ pulledIf enabled { pc, acc },
      pushedIf enabled { pc := pc + 1, acc := op.apply acc operand } ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input
    simp [circuit_norm, stateChannel, programLookup]

  ProverAssumptions
  | { enabled, pc, acc }, data, _ => enabled = 0 ∨ enabled = 1 ∧
    (∃ k mem, Reached program k { pc, acc } mem data) ∧
    (programLookup program).Contains
      { pc, opcode := (Opcode.arithmetic op).code, operand := programCellIn data pc 2 }
  -- an enabled step increments the `pc`, and takes the state after `k` instructions to the state
  -- after `k + 1` instructions
  Spec
  | { enabled, pc, acc }, operand, data => enabled = 1 → pc.val < (pc + 1).val ∧
    ∀ k mem, Reached program k { pc, acc } mem data →
      Reached program (k + 1) { pc := pc + 1, acc := op.apply acc operand } mem data

  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input_var
    simp only [circuit_norm, stateChannel, programLookup]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel]
    obtain ⟨h_bool, h_instruction⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨?_, by simp [h_bool]⟩
    rintro rfl
    simp_all only [circuit_norm, forall_const]
    refine ⟨val_lt_val_add_one h_height h_instruction, fun k mem h_state => ?_⟩
    exact reached_step h_program h_state h_instruction
  completeness := by
    circuit_proof_start [stateChannel, programCell, programCellIn]
    rcases h_assumptions with h | ⟨h, h_state, h_contains⟩ <;> simp_all

/-- One step of the VM that executes `load`: pull a state, check that the program has `load` at
its `pc`, read the memory at the instruction's operand, and push the next state, with the value
read. Returns the memory record that the read pulls. -/
def load (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) :
    GeneralFormalCircuit (F p) StepInput MemoryRecord where
  name := "load"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    stateChannel.pullIf input.enabled { pc := input.pc, acc := input.acc }
    let address ← witness (programCell input.pc 2)
    (programLookup program).channel.pullIf input.enabled
      ⟨ input.pc, .const Opcode.load.code, address ⟩
    let previous ← (memory program h_height).read
      { enabled := input.enabled, address, time := input.pc + 1 }
    stateChannel.pushIf input.enabled { pc := input.pc + 1, acc := previous.value }
    return previous

  exposedChannels
  | { enabled, pc, acc }, i₀ =>
    let previous : Var MemoryRecord (F p) :=
      { address := var ⟨ i₀ ⟩, value := var ⟨ i₀ + 1 ⟩, time := var ⟨ i₀ + 1 + 1 ⟩ }
    expose stateChannel [ pulledIf enabled { pc, acc },
      pushedIf enabled { pc := pc + 1, acc := previous.value } ] ++
    expose (memory program h_height).channel [ pulledIf enabled previous,
      pushedIf enabled { previous with time := pc + 1 } ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input
    simp [circuit_norm, stateChannel, programLookup, memory]

  ProverAssumptions
  | { enabled, pc, acc }, data, hint => enabled = 0 ∨ enabled = 1 ∧
    (∃ k mem, Reached program k { pc, acc } mem data) ∧
    (programLookup program).Contains
      { pc, opcode := Opcode.load.code, operand := programCellIn data pc 2 } ∧
    (memory program h_height).InRange
      ((memory program h_height).previousCellIn hint (pc + 1) 1) (pc + 1)
  -- an enabled step increments the `pc`, comes after the record it reads, and takes the state after
  -- `k` instructions to the state after `k + 1` instructions, if it reads the value of the memory
  Spec
  | { enabled, pc, acc }, previous, data => enabled = 1 → pc.val < (pc + 1).val ∧
    (memory program h_height).Ordered previous.time (pc + 1) ∧
    ∀ k mem, Reached program k { pc, acc } mem data → previous.value = mem previous.address →
      Reached program (k + 1) { pc := pc + 1, acc := previous.value } mem data

  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input_var
    simp only [circuit_norm, stateChannel, programLookup]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel]
    obtain ⟨h_bool, h_instruction, h_read⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨?_, by simp [h_bool]⟩
    rintro rfl
    simp_all only [circuit_norm, forall_const]
    refine ⟨val_lt_val_add_one h_height h_instruction, fun k mem h_state h_value => ?_⟩
    have := reached_step h_program h_state h_instruction
    simp_all [Opcode.exec]
  completeness := by
    circuit_proof_start [stateChannel, programCell, programCellIn]
    rcases h_assumptions with h | ⟨h, h_state, h_contains, h_range⟩ <;> simp_all

/-- One step of the VM that executes `store`: pull a state, check that the program has `store` at
its `pc`, write the accumulator to the memory at the instruction's operand, and push the next state.
Returns the memory record that the write pulls. -/
def store (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) :
    GeneralFormalCircuit (F p) StepInput MemoryRecord where
  name := "store"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    stateChannel.pullIf input.enabled { pc := input.pc, acc := input.acc }
    let address ← witness (programCell input.pc 2)
    (programLookup program).channel.pullIf input.enabled
      ⟨ input.pc, .const Opcode.store.code, address ⟩
    let previous ← (memory program h_height).write
      { enabled := input.enabled, address, value := input.acc, time := input.pc + 1 }
    stateChannel.pushIf input.enabled { pc := input.pc + 1, acc := input.acc }
    return previous

  exposedChannels
  | { enabled, pc, acc }, i₀ =>
    let previous : Var MemoryRecord (F p) :=
      { address := var ⟨ i₀ ⟩, value := var ⟨ i₀ + 1 ⟩, time := var ⟨ i₀ + 1 + 1 ⟩ }
    expose stateChannel [ pulledIf enabled { pc, acc }, pushedIf enabled { pc := pc + 1, acc } ] ++
    expose (memory program h_height).channel [ pulledIf enabled previous,
      pushedIf enabled { previous with value := acc, time := pc + 1 } ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input
    simp [circuit_norm, stateChannel, programLookup, memory]

  ProverAssumptions
  | { enabled, pc, acc }, data, hint => enabled = 0 ∨ enabled = 1 ∧
    (∃ k mem, Reached program k { pc, acc } mem data) ∧
    (programLookup program).Contains
      { pc, opcode := Opcode.store.code, operand := programCellIn data pc 2 } ∧
    (memory program h_height).InRange
      ((memory program h_height).previousCellIn hint (pc + 1) 1) (pc + 1)
  -- an enabled step increments the `pc`, comes after the record it overwrites, and takes the state
  -- after `k` instructions to the state after `k + 1` instructions
  Spec
  | { enabled, pc, acc }, previous, data => enabled = 1 → pc.val < (pc + 1).val ∧
    (memory program h_height).Ordered previous.time (pc + 1) ∧
    ∀ k mem, Reached program k { pc, acc } mem data →
      Reached program (k + 1) { pc := pc + 1, acc } (Function.update mem previous.address acc) data

  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input_var
    simp only [circuit_norm, stateChannel, programLookup]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start [stateChannel]
    obtain ⟨h_bool, h_instruction, h_write⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    refine ⟨?_, by simp [h_bool]⟩
    rintro rfl
    simp_all only [circuit_norm, forall_const]
    refine ⟨val_lt_val_add_one h_height h_instruction, fun k mem h_state => ?_⟩
    have := reached_step h_program h_state h_instruction
    simp_all [Opcode.exec]
  completeness := by
    circuit_proof_start [stateChannel, programCell, programCellIn]
    rcases h_assumptions with h | ⟨h, h_state, h_contains, h_range⟩ <;> simp_all

/-- Witness generation of the table of `opcode`: whenever someone pushes to the state channel, the
table answers if the program has `opcode` at the state's `pc`. -/
def stepGeneration {Input : TypeMap} [ProvableType Input] (opcode : Opcode)
    (input : Var State (F p) → Witgen.M (F p) (Input (WitnessGeneration.Cell (F p)))) :
    WitnessGeneration.Generation (F p) Input :=
  .demand {
    channel := stateChannel
    trigger := .push
    guard state := programCell state.pc 1 =? Witgen.FExpr.const (opcode.code : F p)
    input
  }

/-- The table of an arithmetic opcode: one row per state whose `pc` holds the opcode. -/
abbrev stepComponent (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) (op : Arithmetic) : Component (F p) where
  circuit := step program h_program h_height op
  generation := stepGeneration (.arithmetic op) fun { pc, acc } => pure { enabled := 1, pc, acc }

/-- The table of `load`: one row per state whose `pc` holds `load`. -/
abbrev loadComponent (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) : Component (F p) where
  circuit := load program h_program h_height
  generation := stepGeneration .load fun { pc, acc } => pure { enabled := 1, pc, acc }

/-- The table of `store`: one row per state whose `pc` holds `store`. -/
abbrev storeComponent (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) : Component (F p) where
  circuit := store program h_program h_height
  generation := stepGeneration .store fun { pc, acc } => pure { enabled := 1, pc, acc }

/-- The public input claims that running the program on the initial accumulator ends with the final
accumulator. -/
def verifier (program : Program) : Verifier.Program (F p) PublicInput where
  main | { initial, final } => do
    Verifier.pull stateChannel { pc := .const (program.length : F p), acc := final }
    Verifier.push stateChannel { pc := 0, acc := initial }

def vm (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) : MemoryVmTables p PublicInput where
  channel := stateChannel
  channel_guarantees := by simp [stateChannel]
  memory := memory program h_height
  clock state := state.pc.val
  Reached := Reached program
  tables := [stepComponent program h_program h_height .add,
    stepComponent program h_program h_height .mul]
  accessTables := [loadComponent program h_program h_height,
    storeComponent program h_program h_height]
  unique_names := by simp [step, load, store, Arithmetic.name]
  verifier := verifier program
  final | { final, .. } => { pc := program.length, acc := final }
  tables_channel := by simp [circuit_norm, step, sub_eq_zero, memory, programLookup]
  accessTables_channel := by
    simp +contextual [circuit_norm, load, store, sub_eq_zero, AccessStep, memory, stateChannel]
  verifier_channel := by
    simp [circuit_norm, verifier, Reached, run, ProverData.getPublicInput_eq_eval, memory,
      ReadWriteMemory.initialMemory, ReadWriteMemory.initialValue, funext_iff]
  verifier_memory := by simp [circuit_norm, verifier, memory]

def soundEnsemble (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) :=
  SoundEnsemble.empty (F p) PublicInput .logUp
  |>.addLookup (programLookup program)
  |>.addMemoryVm (vm program h_program h_height)
    (by simp [circuit_norm, vm, programLookup, memory, ReadWriteMemory.range])
    (by simp [circuit_norm, vm, programLookup, memory, ReadWriteMemory.range])
    (by simp [circuit_norm, vm, programLookup, memory, ReadWriteMemory.range, stateChannel])
    (by simp +instances [circuit_norm, vm, step, load, store, verifier])
    (by simp +instances [circuit_norm, vm, step, load, store, verifier, programLookup, memory,
      ReadWriteMemory.range, stateChannel])
    (by simp [circuit_norm, vm, step, load, store, programLookup, memory, ReadWriteMemory.range,
      Arithmetic.name])
  |>.withProverInput (memory program h_height).ProverInput (memory program h_height).hintTables

/-- The public statement: running the program on the initial accumulator and the zero memory ends
with the final accumulator. -/
def Spec (program : Program) : PublicInput (F p) → Prop
  | { initial, final } => final = (run program (initial, 0)).1

def formalEnsemble (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p) :=
  (soundEnsemble program h_program h_height).toFormal (fun _ _ => True) (Spec program)
    (by simp [circuit_norm, soundEnsemble, vm])
    (by
      -- the final state is reached after `program.length` instructions
      rintro witness - - ⟨ k, -, mem, -, -, reached ⟩
      have h_input := witness.data_getPublicInput
      generalize witness.data = data at reached h_input
      generalize witness.publicInput = publicInput at reached h_input ⊢
      obtain ⟨ h_k, h_pc, h_acc ⟩ := reached
      simp only [vm, h_input] at h_pc h_acc
      obtain rfl : k = program.length := by
        have h_pc := congrArg ZMod.val h_pc
        rwa [ZMod.val_cast_of_lt h_program, ZMod.val_cast_of_lt (by omega), eq_comm] at h_pc
      rw [List.take_length] at h_acc
      simp [Spec, ← h_acc])

/-- End-to-end soundness: a valid proof for a public input shows that running the program on its
initial accumulator and the zero memory ends with its final accumulator. -/
theorem opcodeVm_soundness (program : Program) (h_program : program.length < p)
    (h_height : 4 * (programHeight program).toNat ≤ p)
    (publicInput : PublicInput (F p)) (heights : List ℕ) :
    (soundEnsemble program h_program h_height).ensemble.Statement .logUp publicInput heights →
      Spec program publicInput :=
  (formalEnsemble program h_program h_height).soundness publicInput heights trivial

/-- The records that the memory accesses of a run push, in time order: an instruction at `pc`
accesses the memory at time `pc + 1`. -/
def accesses (program : Program) (initial : F p) : List (MemoryRecord (F p)) :=
  (program.zipIdx.foldl (fun (state, records) ((opcode, operand), pc) =>
    let address : F p := operand
    let next := opcode.exec address state
    let time : F p := (pc + 1 : ℕ)
    match opcode with
    | .arithmetic _ => (next, records)
    | .load => (next, records ++ [{ address, value := state.2 address, time }])
    | .store => (next, records ++ [{ address, value := state.1, time }]))
    ((initial, 0), [])).2

/-- The program of the tests. It stores intermediate accumulators at addresses 1 and 4, overwrites
address 1, and loads both addresses back, so its result depends on reading the latest writes. -/
def exampleProgram : Program :=
  [(.add, 3), (.mul, 5), (.store, 1), (.add, 7), (.mul, 2), (.store, 4), (.load, 1), (.add, 1),
    (.store, 1), (.load, 4), (.add, 9), (.load, 1), (.mul, 2), (.add, 6)]

omit [Fact p.Prime] in
theorem exampleProgram_length : exampleProgram.length < p := by
  have : p > 512 := Fact.out
  simp only [exampleProgram, List.length_cons, List.length_nil]
  omega

omit [Fact p.Prime] in
theorem exampleProgram_height : 4 * (programHeight exampleProgram).toNat ≤ p := by
  have : p > 512 := Fact.out
  have : (programHeight exampleProgram).toNat = 16 := by decide
  omega

end OpcodeVm
