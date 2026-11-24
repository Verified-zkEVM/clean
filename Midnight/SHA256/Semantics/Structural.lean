import Midnight.SHA256.Semantics.StructuralBase
import Midnight.SHA256.Semantics.ErasureStructural
import Midnight.SHA256.Semantics.SourceRelocation

/-! Actual source-program structural obligations at every region start. The
closed independently ported schedule is connected by exact advice erasure and
kernel-proved relocation; no caller-supplied operation equality is assumed. -/
namespace Midnight.SHA256.Semantics.Structural
open Halo2

attribute [local irreducible] WitnessCircuit.preimageCircuit
  cleanGates cleanLookups StructuralBase.fixedColumns StructuralBase.permutationColumns
  Synthesis.operations Synthesis.toOperations Synthesis.schedule
  WitnessErasure.operations Chips.Relocation.operations Operations.KeygenRegistered

theorem registered (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).KeygenRegistered
      cleanGates cleanLookups StructuralBase.fixedColumns StructuralBase.permutationColumns := by
  apply (WitnessErasure.keygen ((WitnessCircuit.preimageCircuit input).operations self)
    cleanGates cleanLookups StructuralBase.fixedColumns StructuralBase.permutationColumns).mp
  rw [SourceRelocation.preimage_operations input self]
  exact (Chips.Relocation.keygen self (Synthesis.operations activation) cleanGates cleanLookups
    StructuralBase.fixedColumns StructuralBase.permutationColumns).mpr StructuralBase.registered

theorem copies (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).CopyCellsAssigned self [] := by
  apply (WitnessErasure.copyAssigned self [] _).mp
  rw [SourceRelocation.preimage_operations]
  simpa only [Nat.add_zero, List.map_nil] using
    Chips.Relocation.copyAssigned self 0 [] StructuralBase.source StructuralBase.copies

theorem fixed (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).FixedWritesLawful [] := by
  apply (WitnessErasure.fixedWrites _ []).mp
  rw [SourceRelocation.preimage_operations]
  exact (Chips.Relocation.fixedWrites _ _ []).mpr StructuralBase.fixed

theorem lookup (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).LookupActivationsWellFormed := by
  apply (WitnessErasure.lookup _).mp
  rw [SourceRelocation.preimage_operations]
  exact (Chips.Relocation.lookup _ _).mpr StructuralBase.lookup

theorem regions (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).regionCount = 690 := by
  rw [← WitnessErasure.regionCount, SourceRelocation.preimage_operations, Chips.Relocation.regionCount]
  exact StructuralBase.regions

theorem summary (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    FloorPlanner.synthesisSummary ((WitnessCircuit.preimageCircuit input).operations self) =
      FloorPlanner.synthesisSummary StructuralBase.source := by
  rw [← WitnessErasure.summary, SourceRelocation.preimage_operations, Chips.Relocation.summary]

theorem lookupAgreement (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    ((WitnessCircuit.preimageCircuit input).operations self).LookupSelectorAssignmentsAgree :=
  Operations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
    (registered input self) (List.forall_iff_forall_mem.mpr StructuralBase.noAuxiliary)

theorem lookupAnchors (input : Vector (WitgenIR F 1) 24) (self : RegionIndex)
    (anchor : Nat → FloorPlanner.RegionColumn) :
    ((WitnessCircuit.preimageCircuit input).operations self).LookupSelectorsAnchoredBy anchor :=
  Operations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
    (registered input self) (List.forall_iff_forall_mem.mpr StructuralBase.noAuxiliary) anchor

end Midnight.SHA256.Semantics.Structural
