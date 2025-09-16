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

end Examples.FemtoCairo
