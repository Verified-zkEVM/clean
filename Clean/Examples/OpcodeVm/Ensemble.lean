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

/-- Opcode numbers are small, so they are distinct and nonzero as field elements. -/
lemma Opcode.val_code (opcode : Opcode) : (opcode.code : F p).val = opcode.code := by
  have : p > 512 := Fact.out
  exact ZMod.val_cast_of_lt (by cases opcode <;> simp [Opcode.code] <;> omega)

lemma Opcode.code_ne_zero (opcode : Opcode) : (opcode.code : F p) ≠ 0 := fun h => by
  have h := congrArg ZMod.val h
  rw [Opcode.val_code, ZMod.val_zero] at h
  cases opcode <;> simp [Opcode.code] at h

lemma Opcode.code_injective {a b : Opcode} (h : (a.code : F p) = b.code) : a = b := by
  have h := congrArg ZMod.val h
  rw [Opcode.val_code, Opcode.val_code] at h
  cases a <;> cases b <;> simp_all [Opcode.code]

def Opcode.name : Opcode → String
  | .add => "add"
  | .mul => "mul"

def Opcode.apply {α : Type} [Add α] [Mul α] : Opcode → α → α → α
  | .add, acc, operand => acc + operand
  | .mul, acc, operand => acc * operand

omit [Fact (p > 512)] in
@[circuit_norm]
lemma Opcode.eval_apply (opcode : Opcode) (env : Environment (F p))
    (acc operand : Expression (F p)) :
    (opcode.apply acc operand).eval env = opcode.apply (acc.eval env) (operand.eval env) := by
  cases opcode <;> simp [Opcode.apply, circuit_norm]

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

/-- Run a program on an accumulator. -/
def run (program : Program) (acc : F p) : F p :=
  program.foldl (fun acc (opcode, operand) => opcode.apply acc (operand : F p)) acc

omit [Fact (p > 512)] in
/-- Running one more instruction applies it to the accumulator. -/
lemma run_take_succ (program : Program) (acc : F p) {n : ℕ} (h : n < program.length) :
    run (program.take (n + 1)) acc =
      program[n].1.apply (run (program.take n) acc) (program[n].2 : F p) := by
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
  ((data "program" 4)[(UInt64.ofNat pc.val).toNat]?.getD default)[column]

/-- The state after running the first `pc` instructions of the program on the initial accumulator.
-/
def stateChannel (program : Program) (initial : F p) : Channel (F p) State where
  name := "state"
  Guarantees state _ :=
    state.pc.val ≤ program.length ∧ state.acc = run (program.take state.pc.val) initial

/-- Executing the program's instruction at `pc` takes a state reached after `pc` instructions to the
state reached after `pc + 1` instructions. -/
lemma stateChannel_guarantees_step {program : Program} (h_program : program.length < p)
    {initial : F p} {opcode : Opcode} {pc acc operand : F p} {data : ProverData (F p)}
    (h_state : (stateChannel program initial).Guarantees { pc, acc } data)
    (h_instruction : (programLookup program).Contains { pc, opcode := opcode.code, operand }) :
    (stateChannel program initial).Guarantees
      { pc := pc + 1, acc := opcode.apply acc operand } data := by
  obtain ⟨h_pc, h_acc⟩ := h_state
  obtain ⟨i, -, rfl, h_instruction⟩ := h_instruction
  rcases h_get : program[i.toNat]? with _ | ⟨op, value⟩ <;> simp only [h_get] at h_instruction
  · exact absurd h_instruction.1 opcode.code_ne_zero
  obtain ⟨h_code, rfl⟩ := h_instruction
  obtain rfl := Opcode.code_injective h_code
  obtain ⟨hi, h_instruction⟩ := List.getElem?_eq_some_iff.mp h_get
  have h_val (n : ℕ) (hn : n ≤ program.length) : (n : F p).val = n :=
    ZMod.val_cast_of_lt (by omega)
  simp only [stateChannel, h_val i.toNat hi.le] at h_acc ⊢
  rw [← Nat.cast_add_one, h_val _ hi, run_take_succ program initial hi, h_instruction, h_acc]
  exact ⟨hi, rfl⟩

structure StepInput (F : Type) where
  enabled : F
  pc : F
  acc : F
deriving ProvableStruct

/-- One step of the VM that executes `opcode`: pull a state, check that the program has `opcode` at
its `pc`, and push the next state. -/
def step (program : Program) (h_program : program.length < p) (initial : F p) (opcode : Opcode) :
    GeneralFormalCircuit (F p) StepInput unit where
  name := opcode.name
  main input := do
    -- enabled flag is boolean
    assertZero (input.enabled * (input.enabled - 1))
    -- pull current state
    (stateChannel program initial).pullIf input.enabled { pc := input.pc, acc := input.acc }
    -- look up current operand in the program
    let operand ← witness (programCell input.pc 2)
    (programLookup program).channel.pullIf input.enabled ⟨ input.pc, .const opcode.code, operand ⟩
    -- compute next accumulator (this statically branches the circuit layout based on the operand)
    let acc := opcode.apply input.acc operand
    -- push next state
    (stateChannel program initial).pushIf input.enabled { pc := input.pc + 1, acc }

  exposedChannels
  | { enabled, pc, acc }, i₀ =>
    let operand := var ⟨ i₀ ⟩
    expose (stateChannel program initial) [ pulledIf enabled { pc, acc },
      pushedIf enabled { pc := pc + 1, acc := opcode.apply acc operand } ]
  exposedChannels_eq input i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input
    simp [circuit_norm, stateChannel, programLookup]

  ProverAssumptions
  | { enabled, pc, acc }, data, _ => enabled = 0 ∨ enabled = 1 ∧
    (stateChannel program initial).Guarantees { pc, acc } data ∧
    (programLookup program).Contains
      { pc, opcode := opcode.code, operand := programCellIn data pc 2 }
  Spec _ _ _ := True

  channelsWithRequirements := [ (stateChannel program initial).toRaw ]
  requirementsChannelsLawful input_var i₀ := by
    obtain ⟨enabled, pc, acc⟩ := input_var
    simp only [circuit_norm, stateChannel, programLookup]
    intro env h_bool h_one h_zero
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]

  soundness := by
    circuit_proof_start
    obtain ⟨h_bool, h_state, h_instruction⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with rfl | h_one
    · simp
    rw [sub_eq_zero] at h_one
    subst h_one
    simp_all
    exact fun _ => stateChannel_guarantees_step h_program h_state h_instruction
  completeness := by
    circuit_proof_start [programCell, programCellIn]
    rcases h_assumptions with h | ⟨h, h_state, h_contains⟩ <;> simp_all

/-- The table of `opcode`: one row per state whose `pc` holds `opcode`. -/
abbrev stepComponent (program : Program) (h_program : program.length < p) (initial : F p)
    (opcode : Opcode) : Component (F p) where
  circuit := step program h_program initial opcode
  -- witness generation: whenever someone pushes to the state channel,
  generation := .demand {
    channel := stateChannel program initial
    trigger := .push
    -- we handle this message if the current program opcode matches the static opcode parameter
    guard state := programCell state.pc 1 =? Witgen.FExpr.const (opcode.code : F p)
    input | { pc, acc } => pure { enabled := 1, pc, acc }
  }

/-- The public input `final` claims that running the program on the initial accumulator ends with
the accumulator `final`. -/
def verifier (program : Program) (initial : F p) : Verifier.Program (F p) field where
  main final := do
    Verifier.pull (stateChannel program initial)
      { pc := .const (program.length : F p), acc := final }
    Verifier.push (stateChannel program initial) { pc := 0, acc := .const initial }
  Spec final data :=
    (stateChannel program initial).Guarantees { pc := program.length, acc := final } data
  soundness := by simp [circuit_norm]

def vm (program : Program) (h_program : program.length < p) (initial : F p) :
    VmTables (F p) field where
  channel := stateChannel program initial
  tables := [stepComponent program h_program initial .add,
    stepComponent program h_program initial .mul]
  unique_names := by simp [step, Opcode.name]
  verifier := verifier program initial
  tables_channel := by simp [circuit_norm, step, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, verifier]
  verifier_requirements data := by simp [circuit_norm, verifier, stateChannel, run]

def soundEnsemble (program : Program) (h_program : program.length < p) (initial : F p) :=
  SoundEnsemble.empty (F p) field
  |>.addLookup (programLookup program)
  |>.addVm (vm program h_program initial)
    (by simp +instances [circuit_norm, vm, programLookup, stateChannel])
    (by simp +instances [circuit_norm, vm, step, verifier])
    (by simp +instances [circuit_norm, vm, step, verifier, programLookup, stateChannel])
    (by simp [circuit_norm, vm, step, programLookup, Opcode.name])

/-- The public statement: running the program on the initial accumulator ends with `final`. -/
def Spec (program : Program) (initial final : F p) : Prop :=
  final = run program initial

def formalEnsemble (program : Program) (h_program : program.length < p) (initial : F p) :=
  (soundEnsemble program h_program initial).toFormal (fun _ => True) (Spec program initial)
    (by simp [circuit_norm, soundEnsemble, vm])
    (by simp [circuit_norm, soundEnsemble, vm, verifier, stateChannel, Spec,
      ZMod.val_cast_of_lt h_program])

/-- End-to-end soundness: a valid proof for the public input `final` shows that running the program
on the initial accumulator ends with `final`. -/
theorem opcodeVm_soundness (program : Program) (h_program : program.length < p)
    (initial final : F p) :
    (soundEnsemble program h_program initial).ensemble.Statement final →
      final = run program initial :=
  (formalEnsemble program h_program initial).soundness final trivial

/-- The program of the tests: `acc := ((((acc + 3) * 5 + 7) * 2 + 1 + 4) * 3 + 9) * 2 + 6`. -/
def exampleProgram : Program :=
  [(.add, 3), (.mul, 5), (.add, 7), (.mul, 2), (.add, 1), (.add, 4), (.mul, 3), (.add, 9),
    (.mul, 2), (.add, 6)]

omit [Fact p.Prime] in
theorem exampleProgram_length : exampleProgram.length < p := by
  have : p > 512 := Fact.out
  simp only [exampleProgram, List.length_cons, List.length_nil]
  omega

end OpcodeVm
