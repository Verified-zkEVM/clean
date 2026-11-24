import Midnight.Chips.SynthesisCheckpoint
import Clean.Halo2.Operations.Copy
import Clean.Halo2.Operations.FixedWrites

/-! Structural certificates for source schedules with fixed values erased only
from their proof observation. Copy provenance is insensitive to those values and
to enable-only activation lists. Fixed-value agreement is derived from unique
addresses, not from replacing the source's values by zero. -/
namespace Midnight.Chips.SynthesisShapeLawful
open Halo2
abbrev ShapeInstruction := SynthesisCheckpoint.Instruction
abbrev ShapeStep := SynthesisCheckpoint.Step

/-- The activation callback contributes only gates/lookups, never assignments or copies. -/
def IsEnable : RegionOperation F → Prop
  | .enableGate _ _ | .enableLookup _ _ _ => True
  | _ => False

def OnlyEnables (activate : Nat → Nat → RegionOperations F) : Prop :=
  ∀ selector row, (activate selector row).Forall IsEnable

def decodeInstruction : ShapeInstruction → RegionOperations F
  | .advice column row => [.assignAdvice ⟨column⟩ row (.ofFExpr (.const 0))]
  | .fixed column row => [.assignFixed ⟨column⟩ row 0]
  | .selector _ _ => []
  | .copy left right => [.constrainEqual left right]

def decodeRegion (instructions : List ShapeInstruction) : RegionOperations F :=
  instructions.flatMap decodeInstruction

def decode : List ShapeStep → Operations F
  | [] => []
  | .region name body :: rest => .region name (decodeRegion body) :: decode rest
  | .publicInput cell row :: rest => .constrainInstance cell ⟨1⟩ row :: decode rest

/-- Original source lowering, factored only for proofs. -/
def lowerInstruction (activate : Nat → Nat → RegionOperations F) :
    Synthesis.Instruction → RegionOperations F
  | .advice column row => [.assignAdvice ⟨column⟩ row (.ofFExpr (.const 0))]
  | .fixed column row value => [.assignFixed ⟨column⟩ row value]
  | .selector selector row => activate selector row
  | .copy left right => [.constrainEqual left right]

def lowerRegion (activate : Nat → Nat → RegionOperations F)
    (instructions : List Synthesis.Instruction) : RegionOperations F :=
  instructions.flatMap (lowerInstruction activate)

def lower (activate : Nat → Nat → RegionOperations F) : List Synthesis.Step → Operations F
  | [] => []
  | .region name body :: rest => .region name (lowerRegion activate body.toList) :: lower activate rest
  | .publicInput cell row :: rest => .constrainInstance cell ⟨1⟩ row :: lower activate rest

theorem lower_eq (schedule : Array Synthesis.Step) (activate : Nat → Nat → RegionOperations F) :
    lower activate schedule.toList = Synthesis.scheduleToOperations schedule activate := by
  unfold Synthesis.scheduleToOperations
  generalize schedule.toList = steps
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step <;> simp only [lower, List.map_cons, ih, lowerRegion]
    all_goals rfl

private theorem enables_after (ops : RegionOperations F) (enabled : ops.Forall IsEnable)
    (index : Nat) (available : List Cell) : ops.assignedCellsAfter index available = available := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨head,tail⟩ := (List.forall_cons _ _ _).mp enabled
    cases op <;> first
      | contradiction
      | simpa only [RegionOperations.assignedCellsAfter, List.foldl_cons,
          RegionOperation.assignedCells, List.nil_append] using ih tail

private theorem enables_copy (ops : RegionOperations F) (enabled : ops.Forall IsEnable)
    (index : Nat) (available : List Cell) : ops.CopyCellsAssignedFrom index available := by
  induction ops with
  | nil => exact .nil available
  | cons op rest ih =>
    obtain ⟨head,tail⟩ := (List.forall_cons _ _ _).mp enabled
    cases op <;> first
      | contradiction
      | exact .enableGate _ _ _ _ (ih tail)
      | exact .enableLookup _ _ _ _ _ (ih tail)

private theorem enables_copy_append (ops rest : RegionOperations F) (enabled : ops.Forall IsEnable)
    (index : Nat) (available : List Cell) :
    (ops ++ rest).CopyCellsAssignedFrom index available ↔ rest.CopyCellsAssignedFrom index available := by
  rw [RegionOperations.copyCellsAssignedFrom_append_iff, enables_after ops enabled]
  exact and_iff_right (enables_copy ops enabled index available)

theorem region_after (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (instructions : List Synthesis.Instruction) (index : Nat) (available : List Cell) :
    (lowerRegion activate instructions).assignedCellsAfter index available =
      (decodeRegion (instructions.map SynthesisCheckpoint.instruction)).assignedCellsAfter index available := by
  induction instructions generalizing available with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction with
    | selector selector row =>
      change ((activate selector row) ++ lowerRegion activate rest).assignedCellsAfter index available =
        (decodeRegion (rest.map SynthesisCheckpoint.instruction)).assignedCellsAfter index available
      rw [RegionOperations.assignedCellsAfter_append, enables_after _ (enabled selector row)]
      exact ih available
    | advice column row | fixed column row value | copy left right =>
      simpa only [lowerRegion, decodeRegion, List.flatMap_cons, List.map_cons,
        lowerInstruction, decodeInstruction, SynthesisCheckpoint.instruction,
        List.singleton_append, RegionOperations.assignedCellsAfter, List.foldl_cons,
        RegionOperation.assignedCells, List.singleton_append, List.nil_append] using ih _

theorem region_copy_iff (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (instructions : List Synthesis.Instruction) (index : Nat) (available : List Cell) :
    (lowerRegion activate instructions).CopyCellsAssignedFrom index available ↔
      (decodeRegion (instructions.map SynthesisCheckpoint.instruction)).CopyCellsAssignedFrom index available := by
  induction instructions generalizing available with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;>
      simp only [lowerRegion, decodeRegion, List.flatMap_cons, List.map_cons,
        lowerInstruction, decodeInstruction, SynthesisCheckpoint.instruction,
        List.singleton_append, List.nil_append]
    · simpa only [lowerRegion, decodeRegion, RegionOperations.copyCellsAssignedFrom_assignAdvice_iff] using ih _
    · simpa only [lowerRegion, decodeRegion, RegionOperations.copyCellsAssignedFrom_assignFixed_iff] using ih _
    · rw [enables_copy_append _ _ (enabled _ _)]
      exact ih _
    · simp only [RegionOperations.copyCellsAssignedFrom_constrainEqual_iff]
      exact and_congr Iff.rfl (and_congr Iff.rfl (ih available))

theorem lower_copy_iff (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (steps : List Synthesis.Step) (index : Nat) (available : List Cell) :
    (lower activate steps).CopyCellsAssignedFrom index available ↔
      (decode (steps.map SynthesisCheckpoint.step)).CopyCellsAssignedFrom index available := by
  induction steps generalizing index available with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | region name instructions =>
      simp only [lower, List.map_cons, SynthesisCheckpoint.step, decode,
        Operations.copyCellsAssignedFrom_region_iff, region_copy_iff _ enabled,
        region_after _ enabled, ih]
    | publicInput cell row =>
      simp only [lower, List.map_cons, SynthesisCheckpoint.step, decode,
        Operations.copyCellsAssignedFrom_constrainInstance_iff, ih]

/-- The dummy decoding is used for provenance only; source operations retain
all original fixed values and configured activations. -/
theorem copy_iff (schedule : Array Synthesis.Step) (activate : Nat → Nat → RegionOperations F)
    (enabled : OnlyEnables activate) (index : Nat) (available : List Cell) :
    (Synthesis.scheduleToOperations schedule activate).CopyCellsAssignedFrom index available ↔
      (decode (SynthesisCheckpoint.shape schedule)).CopyCellsAssignedFrom index available := by
  rw [← lower_eq]
  exact lower_copy_iff activate enabled schedule.toList index available

theorem copy_of_shape (schedule : Array Synthesis.Step) (activate : Nat → Nat → RegionOperations F)
    (enabled : OnlyEnables activate) (shape : List ShapeStep)
    (observed : SynthesisCheckpoint.shape schedule = shape) (index : Nat) (available : List Cell)
    (copied : (decode shape).CopyCellsAssignedFrom index available) :
    (Synthesis.scheduleToOperations schedule activate).CopyCellsAssignedFrom index available := by
  rw [copy_iff schedule activate enabled, observed]
  exact copied

/-- Relative fixed-cell addresses retained by a shape region. -/
def fixedAddresses : List ShapeInstruction → List (Nat × Nat)
  | [] => []
  | .fixed column row :: rest => (column,row) :: fixedAddresses rest
  | _ :: rest => fixedAddresses rest

/-- Every region has distinct fixed-cell addresses. This intentionally rejects
repeated equal-valued writes too, avoiding any need to inspect field values. -/
def UniqueFixed : List ShapeStep → Prop
  | [] => True
  | .region _ instructions :: rest => (fixedAddresses instructions).Nodup ∧ UniqueFixed rest
  | .publicInput _ _ :: rest => UniqueFixed rest

/-- Boolean reflection keeps a large source shape opaque during elaboration. -/
def uniqueFixedCheck : List ShapeStep → Bool
  | [] => true
  | .region _ instructions :: rest =>
      decide (fixedAddresses instructions).Nodup && uniqueFixedCheck rest
  | .publicInput _ _ :: rest => uniqueFixedCheck rest

theorem uniqueFixedCheck_iff (shape : List ShapeStep) :
    uniqueFixedCheck shape = true ↔ UniqueFixed shape := by
  induction shape with
  | nil => simp [uniqueFixedCheck, UniqueFixed]
  | cons step rest ih =>
    cases step <;> simp only [uniqueFixedCheck, UniqueFixed, Bool.and_eq_true,
      decide_eq_true_eq, ih]

private def entries : RegionOperations F → List ((Nat × Nat) × F)
  | [] => []
  | .assignFixed column row value :: rest => ((column.index,row),value) :: entries rest
  | _ :: rest => entries rest

private def sourceEntries : List Synthesis.Instruction → List ((Nat × Nat) × F)
  | [] => []
  | .fixed column row value :: rest => ((column,row),value) :: sourceEntries rest
  | _ :: rest => sourceEntries rest

private theorem entries_append (left right : RegionOperations F) :
    entries (left ++ right) = entries left ++ entries right := by
  induction left with
  | nil => rfl
  | cons op rest ih => cases op <;> simp only [List.cons_append, entries, ih, List.cons_append]

private theorem enables_entries (ops : RegionOperations F) (enabled : ops.Forall IsEnable) :
    entries ops = [] := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨head,tail⟩ := (List.forall_cons _ _ _).mp enabled
    cases op <;> first | contradiction | exact ih tail

private theorem region_entries (activate : Nat → Nat → RegionOperations F)
    (enabled : OnlyEnables activate) (instructions : List Synthesis.Instruction) :
    entries (lowerRegion activate instructions) = sourceEntries instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;>
      simp only [lowerRegion, List.flatMap_cons, entries_append, lowerInstruction,
        entries, List.nil_append, List.cons_append, sourceEntries] at *
    all_goals first | exact ih | rw [enables_entries _ (enabled _ _), List.nil_append, ih] | rw [ih]

private theorem sourceEntries_keys (instructions : List Synthesis.Instruction) :
    (sourceEntries instructions).map Prod.fst =
      fixedAddresses (instructions.map SynthesisCheckpoint.instruction) := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp only [sourceEntries, List.map_cons,
      SynthesisCheckpoint.instruction, fixedAddresses, ih]

private theorem entries_member (ops : RegionOperations F) (column : Column .fixed)
    (row : Nat) (value : F) :
    ((column.index,row),value) ∈ entries ops ↔ .assignFixed column row value ∈ ops := by
  induction ops with
  | nil => simp [entries]
  | cons op rest ih =>
    cases column with
    | mk index =>
      have column_eq (other : Column .fixed) : other = ⟨index⟩ ↔ index = other.index := by
        cases other
        simp [eq_comm]
      cases op <;> simp [entries, ih, column_eq, eq_comm, and_assoc]

private theorem unique_values {K V : Type} (pairs : List (K × V))
    (unique : (pairs.map Prod.fst).Nodup) (left right : K × V)
    (hl : left ∈ pairs) (hr : right ∈ pairs) (same : left.1 = right.1) : left = right := by
  induction pairs with
  | nil => contradiction
  | cons head rest ih =>
    obtain ⟨missing,tail⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp hl with hleft | hleft
    · subst left
      rcases List.mem_cons.mp hr with hright | hright
      · exact hright.symm
      · exact False.elim (missing (List.mem_map.mpr ⟨right,hright,same.symm⟩))
    · rcases List.mem_cons.mp hr with hright | hright
      · subst right
        exact False.elim (missing (List.mem_map.mpr ⟨left,hleft,same⟩))
      · exact ih tail hleft hright

private theorem entries_agree (ops : RegionOperations F) (unique : ((entries ops).map Prod.fst).Nodup) :
    ops.FixedAssignmentsAgree := by
  intro column row left right hl hr
  have same := unique_values (entries ops) unique ((column.index,row),left) ((column.index,row),right)
    ((entries_member ops column row left).mpr hl) ((entries_member ops column row right).mpr hr) rfl
  exact congrArg Prod.snd same

theorem region_fixed_agree (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (instructions : List Synthesis.Instruction)
    (unique : (fixedAddresses (instructions.map SynthesisCheckpoint.instruction)).Nodup) :
    (lowerRegion activate instructions).FixedAssignmentsAgree := by
  apply entries_agree
  rw [region_entries activate enabled, sourceEntries_keys]
  exact unique

theorem lower_fixed_agree (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (steps : List Synthesis.Step) (unique : UniqueFixed (steps.map SynthesisCheckpoint.step)) :
    (lower activate steps).Forall Operation.FixedAssignmentsAgree := by
  induction steps with
  | nil => simp [lower]
  | cons step rest ih =>
    cases step with
    | region name instructions =>
      exact (List.forall_cons _ _ _).mpr ⟨region_fixed_agree activate enabled instructions.toList unique.1,ih unique.2⟩
    | publicInput cell row => exact (List.forall_cons _ _ _).mpr ⟨trivial,ih unique⟩

/-- Distinct observed addresses imply agreement of the original source values. -/
theorem fixed_agree_of_shape (schedule : Array Synthesis.Step)
    (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (shape : List ShapeStep) (observed : SynthesisCheckpoint.shape schedule = shape)
    (unique : UniqueFixed shape) :
    (Synthesis.scheduleToOperations schedule activate).Forall Operation.FixedAssignmentsAgree := by
  rw [← lower_eq]
  apply lower_fixed_agree activate enabled
  simpa only [← observed, SynthesisCheckpoint.shape] using unique

/-- Source fixed columns, in write order, retained by the shape observation. -/
def fixedColumns : List ShapeStep → List (Column .fixed)
  | [] => []
  | .region _ instructions :: rest =>
      (fixedAddresses instructions).map (fun address => ⟨address.1⟩) ++ fixedColumns rest
  | .publicInput _ _ :: rest => fixedColumns rest

private theorem entries_columns (ops : RegionOperations F) :
    (entries ops).map (fun entry => (⟨entry.1.1⟩ : Column .fixed)) = ops.fixedColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [entries, RegionOperations.fixedColumns,
      List.filterMap_cons, List.map_cons] at *
    all_goals first | exact ih | rw [ih]

theorem region_fixedColumns (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (instructions : List Synthesis.Instruction) :
    (lowerRegion activate instructions).fixedColumns =
      (fixedAddresses (instructions.map SynthesisCheckpoint.instruction)).map (fun address => ⟨address.1⟩) := by
  rw [← entries_columns, region_entries activate enabled, ← sourceEntries_keys, List.map_map]
  rfl

theorem lower_fixedColumns (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate)
    (steps : List Synthesis.Step) :
    (lower activate steps).regionFixedColumns = fixedColumns (steps.map SynthesisCheckpoint.step) := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step <;>
      simp only [lower, Operations.regionFixedColumns, List.flatMap_cons, List.map_cons,
        SynthesisCheckpoint.step, fixedColumns, region_fixedColumns _ enabled,
        List.nil_append] at *
    all_goals first | exact ih | rw [ih]

theorem regionFixedColumns_eq (schedule : Array Synthesis.Step)
    (activate : Nat → Nat → RegionOperations F) (enabled : OnlyEnables activate) :
    (Synthesis.scheduleToOperations schedule activate).regionFixedColumns =
      fixedColumns (SynthesisCheckpoint.shape schedule) := by
  rw [← lower_eq]
  exact lower_fixedColumns activate enabled schedule.toList

theorem loadedTableColumns_nil (schedule : Array Synthesis.Step)
    (activate : Nat → Nat → RegionOperations F) :
    (Synthesis.scheduleToOperations schedule activate).loadedTableColumns = [] := by
  rw [← lower_eq]
  generalize schedule.toList = steps
  induction steps with
  | nil => rfl
  | cons step rest ih => cases step <;> exact ih

end Midnight.Chips.SynthesisShapeLawful
