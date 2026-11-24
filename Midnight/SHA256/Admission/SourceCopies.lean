import Midnight.SHA256.Admission.CopyBounds
import Midnight.SHA256.Admission.Operations
import Midnight.SHA256.Semantics.StructuralBase

/-! Actual native copy bounds: regional endpoints follow assigned source cells,
and the source-certified public-output rows are checked independently. -/
namespace Midnight.SHA256.Admission
open Halo2 Halo2.FloorPlanner Midnight.Chips
attribute [local irreducible] Synthesis.schedule configured cleanGates cleanLookups

private def publicStep : SynthesisCheckpoint.Step → Bool
  | .region _ _ => true
  | .publicInput _ row => decide (row < 8183)

set_option maxRecDepth 100000 in
private theorem publicRows_checked :
    Semantics.StructuralComposition.fullChunk.all publicStep = true := by decide +kernel

private theorem regionPublicRows (instructions : List Chips.Synthesis.Instruction) :
    CopyBounds.RegionPublicRows 8183 (SynthesisShapeLawful.lowerRegion activation instructions) := by
  intro cell column row member
  obtain ⟨instruction,_,lowered⟩ := List.mem_flatMap.mp member
  cases instruction with
  | advice column row | fixed column row value | copy left right =>
    simp [SynthesisShapeLawful.lowerInstruction] at lowered
  | selector selector atRow =>
    have enabled := List.forall_iff_forall_mem.mp (activation_onlyEnables selector atRow) _ lowered
    exact False.elim enabled

theorem source_publicRows :
    (Synthesis.operations activation).Forall (CopyBounds.PublicRows 8183) := by
  apply List.forall_iff_forall_mem.mpr
  intro operation member
  rcases List.mem_append.mp member with lowered | table
  · obtain ⟨step,source,rfl⟩ := List.mem_map.mp lowered
    cases step with
    | region name instructions => exact regionPublicRows instructions.toList
    | publicInput cell row =>
      have shape : SynthesisCheckpoint.step (.publicInput cell row) ∈
          SynthesisCheckpoint.shape Synthesis.schedule := List.mem_map.mpr ⟨_,source,rfl⟩
      rw [Semantics.StructuralComposition.sourceShape] at shape
      change row < 8183
      exact of_decide_eq_true (List.all_eq_true.mp publicRows_checked _ shape)
  · simp only [Synthesis.tableOperations, List.mem_cons, List.not_mem_nil] at table
    rcases table with rfl | rfl | rfl | rfl | rfl | impossible <;> trivial

theorem source_registered : (Synthesis.operations activation).KeygenRegistered cleanGates cleanLookups
    (CertifiedCircuit.fixedColumns configured)
    ((CertifiedCircuit.permutationColumns configured).map Halo2.Layout.ColRef.toAny) := by
  rw [permutationColumns]
  exact Semantics.StructuralBase.registered

def source_copies : CopyLawful.Lawful (Synthesis.operations activation) cleanGates cleanLookups
    (CertifiedCircuit.fixedColumns configured) (CertifiedCircuit.permutationColumns configured)
    (SimpleFloorPlanner.starts (Synthesis.operations activation)) 8183 none where
  registered := source_registered
  laidOut := CopyLawful.laidOut_of_assigned Semantics.StructuralBase.copies
  constants := source_noConstants
  endpoints := CopyBounds.from_provenance _ _ _ _ _ _ _ _ source_registered
    Semantics.StructuralBase.copies source_operations source_assignedRows source_publicRows

end Midnight.SHA256.Admission
