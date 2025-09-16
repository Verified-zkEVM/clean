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
  Construct a table that represents a read-only memory
  containing all pairs (i, f(i)) for i in [0, length)

  TODO: once we figure out proper lookups, switch to use formal tables.
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

def table
    (program : (F p) → (F p)) (memory : (F p) → (F p))
    (len : ℕ) [NeZero len] (h_len : len < p) :
    InductiveTable (F p) State unit where
  step state _ := do
    let programTable := ReadOnlyTableFromFunction program len h_len
    let memoryTable := ReadOnlyTableFromFunction memory len h_len

    let instruction ← witness fun eval => program (eval state.pc)
    let op1 ← witness fun eval => memory (eval state.pc + 1)
    let op2 ← witness fun eval => memory (eval state.pc + 2)
    let op3 ← witness fun eval => memory (eval state.pc + 3)
    lookup programTable ⟨state.pc, instruction⟩
    lookup programTable ⟨state.pc + 1, op1⟩
    lookup programTable ⟨state.pc + 2, op2⟩
    lookup programTable ⟨state.pc + 3, op3⟩

    let bits ← (Gadgets.ToBits.toBits 8 (by linarith [p_large_enough.elim]) instruction)

    -- read into memory for all cases of addr1
    let v1_0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + op1)
    let v1_1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + op1)
    let v1_2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + op1)
    lookup memoryTable ⟨(state.ap + op1), v1_0⟩
    lookup memoryTable ⟨(state.ap + op1), v1_1⟩
    lookup memoryTable ⟨(state.fp + op1), v1_2⟩

    -- witness the actual v1 based on bits[2] and bits[3]
    let v1 ← witness fun eval =>
      let addressing1 := eval bits[2] + 2 * eval bits[3]
      match addressing1.val with
      | 0 => eval v1_0
      | 1 => eval v1_1
      | 2 => eval v1_2
      | _ => eval op1

    -- enforce that v1 is correctly selected
    assertZero
      (((1 : Expression _) - bits[2]) * ((1 : Expression _) - bits[3]) * (v1 - v1_0) +
      bits[2] * ((1 : Expression _) - bits[3]) * (v1 - v1_1) +
      ((1 : Expression _) - bits[2]) * bits[3] * (v1 - v1_2) +
      bits[2] * bits[3] * (v1 - op1))

    let v2_0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + op2)
    let v2_1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + op2)
    let v2_2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + op2)
    lookup memoryTable ⟨(state.ap + op2), v2_0⟩
    lookup memoryTable ⟨(state.ap + op2), v2_1⟩
    lookup memoryTable ⟨(state.fp + op2), v2_2⟩

    let v2 ← witness fun eval =>
      let addressing2 := eval bits[4] + 2 * eval bits[5]
      match addressing2.val with
      | 0 => eval v2_0
      | 1 => eval v2_1
      | 2 => eval v2_2
      | _ => eval op2

    assertZero
      (((1 : Expression _) - bits[4]) * ((1 : Expression _) - bits[5]) * (v2 - v2_0) +
      bits[4] * ((1 : Expression _) - bits[5]) * (v2 - v2_1) +
      ((1 : Expression _) - bits[4]) * bits[5] * (v2 - v2_2) +
      bits[4] * bits[5] * (v2 - op2))

    let v3_0 : Expression _ ← witness fun eval => (memory ∘ memory ∘ eval) (state.ap + op3)
    let v3_1 : Expression _ ← witness fun eval => (memory ∘ eval) (state.ap + op3)
    let v3_2 : Expression _ ← witness fun eval => (memory ∘ eval) (state.fp + op3)
    lookup memoryTable ⟨(state.ap + op3), v3_0⟩
    lookup memoryTable ⟨(state.ap + op3), v3_1⟩
    lookup memoryTable ⟨(state.fp + op3), v3_2⟩

    let v3 ← witness fun eval =>
      let addressing3 := eval bits[6] + 2 * eval bits[7]
      match addressing3.val with
      | 0 => eval v3_0
      | 1 => eval v3_1
      | 2 => eval v3_2
      | _ => eval op3

    assertZero
      (((1 : Expression _) - bits[6]) * ((1 : Expression _) - bits[7]) * (v3 - v3_0) +
      bits[6] * ((1 : Expression _) - bits[7]) * (v3 - v3_1) +
      ((1 : Expression _) - bits[6]) * bits[7] * (v3 - v3_2) +
      bits[6] * bits[7] * (v3 - op3))

    let is_add := ((1 : F p) - bits[0]) * ((1 : F p) - bits[1])
    let is_mul := bits[0] * ((1 : F p) - bits[1])
    let is_store_state := ((1 : F p) - bits[0]) * bits[1]
    let is_load_state := bits[0] * bits[1]

    assertZero (is_add * (v3 - (v1 + v2)))
    assertZero (is_mul * (v3 - (v1 * v2)))
    assertZero (is_store_state * (v1 - state.pc))
    assertZero (is_store_state * (v2 - state.ap))
    assertZero (is_store_state * (v3 - state.fp))

    let pc_next : Expression _ ← witness fun eval => if eval is_load_state = 1 then eval v1 else eval state.pc + 4
    let ap_next : Expression _ ← witness fun eval => if eval is_load_state = 1 then eval v2 else eval state.ap
    let fp_next : Expression _ ← witness fun eval => if eval is_load_state = 1 then eval v3 else eval state.fp

    assertZero (is_load_state * (pc_next - v1))
    assertZero (is_load_state * (ap_next - v2))
    assertZero (is_load_state * (fp_next - v3))
    assertZero ((1 - is_load_state) * (pc_next - (state.pc + 4)))

    return { pc := pc_next, ap := ap_next, fp := fp_next }

  Spec _ _ i _ row : Prop := sorry
  soundness := sorry
  completeness := sorry

end Examples.FemtoCairo
