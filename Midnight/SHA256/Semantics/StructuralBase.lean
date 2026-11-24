import Midnight.SHA256.Configure
import Midnight.SHA256.SynthesisLayout
import Midnight.Chips.CopyLawful
import Midnight.Chips.Relocation
import Midnight.Chips.SynthesisCheckpoint
import Midnight.SHA256.WitnessInitialTables
import Midnight.SHA256.Semantics.StructuralComposition
import Midnight.Chips.SynthesisShapeLawful
import Midnight.SHA256.Semantics.StructuralCopies

/-! Closed structural certificates for the independently ported native schedule.
The computational leaves are checked by Lean's kernel; source relocation and
advice erasure transport these certificates to the witness-bearing program. -/
namespace Midnight.SHA256.Semantics.StructuralBase
open Halo2

-- Keep the independent closed kernel checks sequential to bound elaborator resources.
set_option Elab.async false

abbrev source := Synthesis.operations activation

def fixedColumns : List (Column .fixed) := (List.range configured.numFixed).map (⟨·⟩)
def permutationColumns : List AnyColumn := configured.permutation.toList

attribute [local irreducible] Synthesis.schedule
attribute [local irreducible] cleanGates cleanLookups configured fixedColumns permutationColumns

private def instructionColumns : Chips.Synthesis.Instruction → Bool
  | .fixed column _ _ => decide ((⟨column⟩ : Column .fixed) ∈ fixedColumns)
  | .copy left right => decide (left.column ∈ permutationColumns ∧ right.column ∈ permutationColumns)
  | _ => true

private def stepColumns : Chips.Synthesis.Step → Bool
  | .region _ instructions => instructions.toList.all instructionColumns
  | .publicInput cell _ => decide (cell.column ∈ permutationColumns ∧
      (⟨1⟩ : Column .instance).toAny ∈ permutationColumns)

private theorem activation_registered (selector row : Nat) :
    (activation selector row).Forall
      (RegionOperation.KeygenRegistered cleanGates cleanLookups fixedColumns permutationColumns) := by
  apply List.forall_iff_forall_mem.mpr
  intro op member
  simp only [activation, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨gate,⟨hg,_⟩,rfl⟩ | ⟨lookup,⟨hl,_⟩,rfl⟩
  · exact hg
  · exact hl

private theorem schedule_registered (schedule : Array Chips.Synthesis.Step)
    (valid : schedule.toList.all stepColumns = true) :
    (Chips.Synthesis.scheduleToOperations schedule activation).KeygenRegistered
      cleanGates cleanLookups fixedColumns permutationColumns := by
  apply List.forall_iff_forall_mem.mpr
  intro op member
  obtain ⟨step,inSteps,rfl⟩ := List.mem_map.mp member
  have checked := (List.all_eq_true.mp valid) step inSteps
  cases step with
  | publicInput cell row =>
      change cell.column ∈ permutationColumns ∧ (⟨1⟩ : Column .instance).toAny ∈ permutationColumns
      exact of_decide_eq_true checked
  | region name instructions =>
      apply List.forall_iff_forall_mem.mpr
      intro entry inEntries
      obtain ⟨instruction,inInstructions,inLowered⟩ := List.mem_flatMap.mp inEntries
      have check := (List.all_eq_true.mp checked) instruction inInstructions
      cases instruction with
      | advice column row =>
          simp only [List.mem_singleton] at inLowered
          subst entry
          trivial
      | fixed column row value =>
          simp only [List.mem_singleton] at inLowered
          subst entry
          simp only [RegionOperation.KeygenRegistered]
          exact of_decide_eq_true check
      | copy left right =>
          simp only [List.mem_singleton] at inLowered
          subst entry
          simp only [RegionOperation.KeygenRegistered]
          exact of_decide_eq_true check
      | selector selector row =>
          exact List.forall_iff_forall_mem.mp (activation_registered selector row) entry inLowered

private def shapeInstructionColumns : Chips.SynthesisCheckpoint.Instruction → Bool
  | .fixed column _ => decide ((⟨column⟩ : Column .fixed) ∈ fixedColumns)
  | .copy left right => decide (left.column ∈ permutationColumns ∧ right.column ∈ permutationColumns)
  | _ => true

private def shapeStepColumns : Chips.SynthesisCheckpoint.Step → Bool
  | .region _ instructions => instructions.all shapeInstructionColumns
  | .publicInput cell _ => decide (cell.column ∈ permutationColumns ∧
      (⟨1⟩ : Column .instance).toAny ∈ permutationColumns)

private theorem shapeInstructionColumns_eq (instruction : Chips.Synthesis.Instruction) :
    shapeInstructionColumns (Chips.SynthesisCheckpoint.instruction instruction) = instructionColumns instruction := by
  cases instruction <;> rfl

private theorem shapeStepColumns_eq (step : Chips.Synthesis.Step) :
    shapeStepColumns (Chips.SynthesisCheckpoint.step step) = stepColumns step := by
  cases step with
  | publicInput cell row => rfl
  | region name instructions =>
    simp only [Chips.SynthesisCheckpoint.step, shapeStepColumns, stepColumns, List.all_map]
    congr 1
    funext instruction
    exact shapeInstructionColumns_eq instruction

private theorem columns_shape (schedule : Array Chips.Synthesis.Step) :
    (Chips.SynthesisCheckpoint.shape schedule).all shapeStepColumns = schedule.toList.all stepColumns := by
  simp only [Chips.SynthesisCheckpoint.shape, List.all_map]
  congr 1
  funext step
  exact shapeStepColumns_eq step

private theorem fixedColumns_eq : fixedColumns = (List.range 16).map (⟨·⟩) := by
  decide +kernel

private theorem permutationColumns_eq : permutationColumns =
    [(⟨9⟩ : Column .fixed).toAny, (⟨0⟩ : Column .advice).toAny,
     (⟨1⟩ : Column .advice).toAny, (⟨2⟩ : Column .advice).toAny,
     (⟨3⟩ : Column .advice).toAny, (⟨4⟩ : Column .advice).toAny,
     (⟨0⟩ : Column .instance).toAny, (⟨1⟩ : Column .instance).toAny,
     (⟨5⟩ : Column .advice).toAny] := by
  decide +kernel

private theorem activation_lookup (selector row : Nat) :
    RegionOperations.LookupActivationsWellFormed (activation selector row) := by
  apply List.forall_iff_forall_mem.mpr
  intro op member
  simp only [activation, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨gate,⟨_,_⟩,rfl⟩ | ⟨lookup,⟨_,same⟩,rfl⟩
  · trivial
  · have same : selector = lookup.masterSelector.index := (beq_iff_eq.mp same).symm
    simp [RegionOperation.LookupActivationWellFormed, SelectorEnabledAtIndex, same]

private theorem schedule_lookup (schedule : Array Chips.Synthesis.Step) :
    (Chips.Synthesis.scheduleToOperations schedule activation).LookupActivationsWellFormed := by
  apply List.forall_iff_forall_mem.mpr
  intro op member
  obtain ⟨step,inSteps,rfl⟩ := List.mem_map.mp member
  cases step with
  | publicInput cell row => trivial
  | region name instructions =>
    apply List.forall_iff_forall_mem.mpr
    intro entry inEntries
    obtain ⟨instruction,_,inLowered⟩ := List.mem_flatMap.mp inEntries
    cases instruction with
    | selector selector row =>
      exact List.forall_iff_forall_mem.mp (activation_lookup selector row) entry inLowered
    | advice column row | fixed column row value | copy left right =>
      simp only [List.mem_singleton] at inLowered
      subst entry
      trivial

private theorem tables_registered : Synthesis.tableOperations.KeygenRegistered
    cleanGates cleanLookups fixedColumns permutationColumns := by
  simp only [Synthesis.tableOperations, Operations.KeygenRegistered, List.forall_cons,
    List.forall_nil, Operation.KeygenRegistered, fixedColumns_eq]
  decide

private theorem tables_lookup : Synthesis.tableOperations.LookupActivationsWellFormed := by
  simp only [Synthesis.tableOperations, Operations.LookupActivationsWellFormed,
    List.forall_cons, List.forall_nil, Operation.LookupActivationsWellFormed, and_self]

private theorem tables_columns : Synthesis.tableOperations.loadedTableColumns =
    [⟨11⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] := by
  have range : byteRangeRows ≠ [] := by
    intro empty
    have size := WitnessInitial.range_length
    rw [empty] at size
    contradiction
  have spread : spreadRows ≠ [] := by
    intro empty
    have size := WitnessInitial.spread_length
    rw [empty] at size
    contradiction
  simp only [Synthesis.tableOperations, Operations.loadedTableColumns,
    List.filterMap_cons, List.filterMap_nil, List.map_eq_nil_iff,
    range, spread, ↓reduceIte]

private theorem tables_copies (index : Nat) (prior : List Cell) :
    Synthesis.tableOperations.CopyCellsAssigned index prior := by
  simp only [Synthesis.tableOperations, Operations.CopyCellsAssigned,
    Operations.copyCellsAssignedFrom_loadTable_iff, Operations.copyCellsAssignedFrom_nil_iff]

private theorem tables_fixed : Synthesis.tableOperations.Forall Operation.FixedAssignmentsAgree := by
  simp only [Synthesis.tableOperations, List.forall_cons, List.forall_nil,
    Operation.FixedAssignmentsAgree, and_self]

private theorem tables_no_fixed : Synthesis.tableOperations.regionFixedColumns = [] := rfl

private def shapeRegions (steps : List Chips.SynthesisCheckpoint.Step) : Nat :=
  (steps.map fun step => match step with | .region _ _ => 1 | .publicInput _ _ => 0).sum

private theorem schedule_regions (schedule : Array Chips.Synthesis.Step) :
    (Chips.Synthesis.scheduleToOperations schedule activation).regionCount =
      shapeRegions (Chips.SynthesisCheckpoint.shape schedule) := by
  unfold Chips.Synthesis.scheduleToOperations Chips.SynthesisCheckpoint.shape shapeRegions
  generalize schedule.toList = steps
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step <;> simp only [List.map_cons, Operations.regionCount, Chips.SynthesisCheckpoint.step,
      List.sum_cons, ih, Nat.zero_add]

set_option maxRecDepth 100000 in
private theorem columns_check : Synthesis.schedule.toList.all stepColumns = true := by
  rw [← columns_shape, StructuralComposition.sourceShape]
  unfold shapeStepColumns shapeInstructionColumns
  simp only [fixedColumns_eq, permutationColumns_eq]
  decide +kernel

theorem registered : source.KeygenRegistered cleanGates cleanLookups fixedColumns permutationColumns := by
  change (Synthesis.toOperations activation ++ Synthesis.tableOperations).KeygenRegistered
    cleanGates cleanLookups fixedColumns permutationColumns
  rw [Operations.KeygenRegistered.append]
  exact ⟨schedule_registered Synthesis.schedule columns_check, tables_registered⟩

theorem lookup : source.LookupActivationsWellFormed :=
  Operations.LookupActivationsWellFormed.append
    (schedule_lookup Synthesis.schedule) tables_lookup

set_option maxRecDepth 100000 in
theorem regions : source.regionCount = 690 := by
  change ((Chips.Synthesis.scheduleToOperations Synthesis.schedule activation) ++
    Synthesis.tableOperations).regionCount = 690
  rw [Operations.regionCount_append, schedule_regions, StructuralComposition.sourceShape]
  change shapeRegions StructuralComposition.fullChunk + 0 = 690
  decide +kernel

theorem noAuxiliary : ∀ lookup ∈ cleanLookups, lookup.auxiliarySelectorIndices = [] := by
  decide +kernel

private theorem activation_only_enables : Chips.SynthesisShapeLawful.OnlyEnables activation := by
  intro selector row
  apply List.forall_iff_forall_mem.mpr
  intro op member
  simp only [activation, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨gate,⟨_,_⟩,rfl⟩ | ⟨lookup,⟨_,_⟩,rfl⟩ <;> trivial

set_option maxRecDepth 100000 in
private theorem unique_fixed_check :
    Chips.SynthesisShapeLawful.uniqueFixedCheck StructuralComposition.fullChunk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem fixed_columns_disjoint :
    ([⟨11⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩] : List (Column .fixed)).Disjoint
      (Chips.SynthesisShapeLawful.fixedColumns StructuralComposition.fullChunk) := by
  rw [List.disjoint_left]
  decide +kernel

theorem copies : source.CopyCellsAssigned 0 [] := by
  change (Chips.Synthesis.scheduleToOperations Synthesis.schedule activation ++
    Synthesis.tableOperations).CopyCellsAssignedFrom 0 []
  apply Operations.CopyCellsAssignedFrom.append
  · exact Chips.SynthesisShapeLawful.copy_of_shape Synthesis.schedule activation
      activation_only_enables StructuralComposition.fullChunk StructuralComposition.sourceShape 0 []
      (Midnight.Math.Operations.RegionalCopy.sound StructuralCopyTable.table _ StructuralCopies.checked)
  · exact tables_copies _ _

theorem fixed : source.FixedWritesLawful [] := by
  change (Chips.Synthesis.scheduleToOperations Synthesis.schedule activation ++
    Synthesis.tableOperations).FixedWritesLawful []
  constructor
  · rw [List.forall_append]
    exact ⟨Chips.SynthesisShapeLawful.fixed_agree_of_shape Synthesis.schedule activation
      activation_only_enables StructuralComposition.fullChunk StructuralComposition.sourceShape
      ((Chips.SynthesisShapeLawful.uniqueFixedCheck_iff _).mp unique_fixed_check), tables_fixed⟩
  · rw [Operations.loadedTableColumns_append, Chips.SynthesisShapeLawful.loadedTableColumns_nil,
      List.nil_append, tables_columns]
    decide
  · rw [Operations.loadedTableColumns_append, Chips.SynthesisShapeLawful.loadedTableColumns_nil,
      List.nil_append, tables_columns, Operations.regionFixedColumns_append, tables_no_fixed,
      List.append_nil, Chips.SynthesisShapeLawful.regionFixedColumns_eq _ _ activation_only_enables,
      StructuralComposition.sourceShape]
    exact fixed_columns_disjoint
  · exact List.disjoint_nil_right _

end Midnight.SHA256.Semantics.StructuralBase
