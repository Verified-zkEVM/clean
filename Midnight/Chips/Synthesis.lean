import Midnight.Field

/-!
Keygen-only synthesis schedule of the shared native chips, used by the SHA-256 circuit.
Advice witness values are erased. Source allocation sites, selector enables, fixed
values, constant caching and copy order are retained. No witness correctness claim
is attached to these operations.

This schedule assumes the pinned shared-chip architecture: native advice columns
0..4, arithmetic coefficient fixed columns 0..8, the constant-cache fixed column 9,
and public inputs in instance column 1. It is not a configurable gadget API.
-/

namespace Midnight.Chips.Synthesis
open Halo2

inductive Instruction where
  | advice : Nat → Nat → Instruction
  | fixed : Nat → Nat → F → Instruction
  | selector : Nat → Nat → Instruction
  | copy : Cell → Cell → Instruction

inductive Step where
  | region : String → Array Instruction → Step
  | publicInput : Cell → Nat → Step

structure BuildState where
  steps : Array Step := #[]
  nextRegion : Nat := 0
  constants : List (Nat × Cell) := []

abbrev Build := StateM BuildState
abbrev Region := ReaderT Nat (StateM (Array Instruction))

def putInstr (i : Instruction) : Region Unit := modify (·.push i)

def advice (col row : Nat) : Region Cell := do
  putInstr (.advice col row)
  return .of (← read) row (⟨col⟩ : Column .advice)

def fixed (col row : Nat) (value : F) : Region Cell := do
  putInstr (.fixed col row value)
  return .of (← read) row (⟨col⟩ : Column .fixed)

def enable (selector row : Nat) : Region Unit := putInstr (.selector selector row)
def equal (left right : Cell) : Region Unit := putInstr (.copy left right)

/-- Rust `AssignedCell.copy_advice`: new cell is the first copy endpoint. -/
def copyAdvice (source : Cell) (col row : Nat) : Region Cell := do
  let target ← advice col row
  equal target source
  return target

def region {α : Type} (name : String) (body : Region α) : Build α := do
  let st ← get
  let (value, instructions) := (body st.nextRegion).run #[]
  set { st with steps := st.steps.push (.region name instructions), nextRegion := st.nextRegion + 1 }
  return value

/-- NativeChip's first-encounter constant cache, including reuse across chips. -/
def constant (n : Nat) : Build Cell := do
  let key := (n : F).val
  if let some (_, cell) := (← get).constants.find? (fun entry => entry.1 == key) then
    return cell
  let cell ← region "Assign fixed" (fixed 9 0 (n : F))
  modify fun st => { st with constants := (key, cell) :: st.constants }
  return cell

/-- Native arithmetic coefficients: five advice columns, fixed 4..8.
Caller contract: `coeffs.size = 5`; coefficients are supplied in advice-column order. -/
def custom (coeffs : Array F) (next : F) (row : Nat) : Region Unit := do
  enable 0 row
  for i in [:5] do let _ ← fixed (4+i) row coeffs[i]!
  let _ ← fixed 0 row next
  for col in [1,2,3] do let _ ← fixed col row 0

/-- Native linear-combination auxiliary, iterative spelling of its Rust recursion.
Caller contract: `coefficients` is nonempty and `1 ≤ colsUsed ≤ 4`. Advice column 0
holds each result and columns 1 through `colsUsed` hold terms; coefficients use
the five-column arithmetic architecture documented above. The source callers
here use `colsUsed = 1` or `4` and satisfy these preconditions. -/
def linearAux (coefficients : Array F) (colsUsed : Nat) : Region (Cell × Array Cell) := do
  let mut terms := #[]
  let mut output := default
  let rows := (coefficients.size + colsUsed - 1) / colsUsed
  for row in [:rows] do
    let result ← advice 0 row
    if row == 0 then output := result
    let mut coeffs : Array F := #[-1, 0, 0, 0, 0]
    let count := min colsUsed (coefficients.size - row*colsUsed)
    for i in [:count] do
      terms := terms.push (← advice (i+1) row)
      coeffs := coeffs.set! (i+1) coefficients[row*colsUsed+i]!
    custom coeffs (if row+1 < rows then 1 else 0) row
  return (output, terms)

def linearCombination (input : Array (F × Cell)) : Build Cell := do
  let zero ← constant 0
  let terms := input.filter fun (coeff, cell) => coeff != 0 && cell != zero
  if terms.isEmpty then return zero
  if terms.size == 1 && terms[0]!.1 == 1 then return terms[0]!.2
  region "Linear combination" do
    let (result, assigned) ← linearAux (terms.map (·.1)) 4
    for i in [:terms.size] do equal assigned[i]! terms[i]!.2
    return result

/-- Only advice values are erased. All keygen-relevant operations become Clean ops.
`activate` must use the configured real gates / lookup selector capabilities. -/
def scheduleToOperations (schedule : Array Step) (activate : Nat → Nat → List (RegionOperation F)) : Operations F :=
  schedule.toList.map fun step => match step with
  | .region name instructions => .region name (instructions.toList.flatMap fun instruction =>
      match instruction with
      | .advice col row => [.assignAdvice ⟨col⟩ row (.ofFExpr (.const 0))]
      | .fixed col row value => [.assignFixed ⟨col⟩ row value]
      | .selector selector row => activate selector row
      | .copy left right => [.constrainEqual left right])
  | .publicInput cell row => .constrainInstance cell ⟨1⟩ row

end Midnight.Chips.Synthesis
