import Midnight.Chips.Synthesis
import Midnight.Math.Checkpoint

/-! Bounded, source-linked reduction checkpoints for the keygen schedule.
A checkpoint quantifies over the pre-existing operation priorTrace and proves the
actual action's returned cells, cache, region index, and appended structure.
Fixed values are omitted only from this proof index. They stay in the source
program; fixed-write agreement is established separately from unique addresses. -/
namespace Midnight.Chips.SynthesisCheckpoint
open Halo2 Synthesis

inductive Instruction where
  | advice : Nat → Nat → Instruction
  | fixed : Nat → Nat → Instruction
  | selector : Nat → Nat → Instruction
  | copy : Cell → Cell → Instruction
  deriving DecidableEq, Repr

inductive Step where
  | region : String → List Instruction → Step
  | publicInput : Cell → Nat → Step
  deriving DecidableEq, Repr

def instruction : Synthesis.Instruction → Instruction
  | .advice column row => .advice column row
  | .fixed column row _ => .fixed column row
  | .selector selector row => .selector selector row
  | .copy left right => .copy left right

def step : Synthesis.Step → Step
  | .region name instructions => .region name (instructions.toList.map instruction)
  | .publicInput cell row => .publicInput cell row

def shape (steps : Array Synthesis.Step) : List Step := steps.toList.map step

structure Cursor where
  next : Nat
  constants : List (Nat × Cell)
  deriving DecidableEq, Repr

def cursor (state : BuildState) : Cursor := ⟨state.nextRegion, state.constants⟩
def Cursor.state (position : Cursor) (steps : Array Synthesis.Step) : BuildState :=
  ⟨steps, position.next, position.constants⟩

def frame : Midnight.Math.Checkpoint.Frame BuildState Cursor (Array Synthesis.Step) where
  position := cursor
  trace := BuildState.steps
  assemble := Cursor.state
  position_assemble _ _ := rfl
  trace_assemble _ _ := rfl
  reconstruct state := by cases state; rfl

abbrev Checkpoint {α : Type} (action : Build α) (before : Cursor) (output : α)
    (after : Cursor) (chunk : List Step) : Prop :=
  Midnight.Math.Checkpoint.Checked frame shape action before output after chunk

theorem Checkpoint.empty {α : Type} (action : Build α) (before : Cursor) (output : α)
    (after : Cursor) (chunk : List Step) (checked : Checkpoint action before output after chunk) :
    let result := action (before.state #[])
    result.1 = output ∧ cursor result.2 = after ∧ shape result.2.steps = chunk := by
  simpa only [frame, shape, Array.toList_empty, List.map_nil, List.nil_append] using checked #[]

/-- Direct closed-trace projections avoid normalizing the concrete action while
instantiating a dependent conjunction. The proof is generic in the action. -/
theorem Checkpoint.observed {α : Type} (action : Build α) (next : Nat)
    (constants : List (Nat × Cell)) (output : α) (after : Cursor) (chunk : List Step)
    (checked : Checkpoint action ⟨next, constants⟩ output after chunk) :
    shape (action ⟨#[], next, constants⟩).2.steps = chunk :=
  (Checkpoint.empty action ⟨next, constants⟩ output after chunk checked).2.2

theorem Checkpoint.next {α : Type} (action : Build α) (next : Nat)
    (constants : List (Nat × Cell)) (output : α) (after : Cursor) (chunk : List Step)
    (checked : Checkpoint action ⟨next, constants⟩ output after chunk) :
    (action ⟨#[], next, constants⟩).2.nextRegion = after.next :=
  congrArg Cursor.next (Checkpoint.empty action ⟨next, constants⟩ output after chunk checked).2.1

namespace Reduction
/-- Only the cache's comparison key is normalized; all emitted source fixed
assignments retain their original field values. -/
def canonicalConstant (n : Nat) : Synthesis.Build Cell := do
  let key := n % BLS12_381.scalarFieldSize
  if let some (_, cell) := (← get).constants.find? (fun entry => entry.1 == key) then return cell
  let cell ← Synthesis.region "Assign fixed" (Synthesis.fixed 9 0 (n : F))
  modify fun state => { state with constants := (key, cell) :: state.constants }
  return cell

theorem constant_canonical (n : Nat) : Synthesis.constant n = canonicalConstant n := by
  unfold Synthesis.constant canonicalConstant
  rw [ZMod.val_natCast]
  rfl

theorem cast_val (n : Nat) : (n : F).val = n % BLS12_381.scalarFieldSize := ZMod.val_natCast _ _
theorem beq_val (a b : F) : (a == b) = (a.val == b.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, (ZMod.val_injective BLS12_381.scalarFieldSize).eq_iff]
theorem zero_val : (0 : F).val = 0 := rfl
theorem one_val : (1 : F).val = 1 := rfl

def castTerms (terms : Array (Nat × Cell)) : Array (F × Cell) :=
  terms.map fun (coefficient, cell) => ((coefficient : F), cell)

theorem cast_beq (n m : Nat) :
    ((n : F) == (m : F)) = (n % BLS12_381.scalarFieldSize == m % BLS12_381.scalarFieldSize) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact (ZMod.val_injective BLS12_381.scalarFieldSize).eq_iff.symm.trans
    (by simp only [ZMod.val_natCast])
theorem cast_beq_zero (n : Nat) : ((n : F) == 0) = (n % BLS12_381.scalarFieldSize == 0) := by
  simpa only [Nat.cast_zero, Nat.zero_mod] using cast_beq n 0
theorem cast_beq_one (n : Nat) : ((n : F) == 1) = (n % BLS12_381.scalarFieldSize == 1) := by
  simpa only [Nat.cast_one, Nat.one_mod_eq_one.mpr (by decide : BLS12_381.scalarFieldSize ≠ 1)] using cast_beq n 1

def natLinearCombination (input : Array (Nat × Cell)) : Synthesis.Build Cell := do
  let zero ← Synthesis.constant 0
  let terms := input.filter fun (coefficient, cell) =>
    coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero
  if terms.isEmpty then return zero
  if terms.size == 1 && terms[0]!.1 % BLS12_381.scalarFieldSize == 1 then return terms[0]!.2
  let casted := castTerms terms
  Synthesis.region "Linear combination" do
    let (result, assigned) ← Synthesis.linearAux (casted.map (·.1)) 4
    for i in [:casted.size] do Synthesis.equal assigned[i]! casted[i]!.2
    return result

theorem linearCombination_cast (input : Array (Nat × Cell)) :
    Synthesis.linearCombination (castTerms input) = natLinearCombination input := by
  unfold Synthesis.linearCombination natLinearCombination
  congr 1
  funext zero
  have filter : (castTerms input).filter (fun (coefficient, cell) => coefficient != 0 && cell != zero) =
      castTerms (input.filter fun (coefficient, cell) => coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero) := by
    simp only [castTerms, Array.filter_map, Function.comp_def, bne, cast_beq_zero]
  rw [filter]
  let terms := input.filter fun (coefficient, cell) => coefficient % BLS12_381.scalarFieldSize != 0 && cell != zero
  change (if (castTerms terms).isEmpty then _ else _) = (if terms.isEmpty then _ else _)
  simp only [castTerms, Array.isEmpty, Array.size_map]
  split
  · rfl
  · rename_i nonempty
    simp only [decide_eq_true_eq] at nonempty
    have bound : 0 < terms.size := by omega
    have first : (terms.map fun x => ((x.1 : F), x.2))[0]! = ((terms[0]!.1 : F), terms[0]!.2) := by
      rw [getElem!_pos (terms.map fun x => ((x.1 : F), x.2)) 0 (by simpa using bound), getElem!_pos terms 0 bound]
      exact Array.getElem_map _ _
    dsimp only [terms] at first
    rw [first, cast_beq_one]

end Reduction

end Midnight.Chips.SynthesisCheckpoint
