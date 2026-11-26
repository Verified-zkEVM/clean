import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.SourceRelocationRules
import Midnight.SHA256.Semantics.StageUnfold

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local cbv_opaque] WitnessCircuit.blockFromBytes WitnessCircuit.constant
  BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing
  Midnight.SHA256.activation Midnight.SHA256.byteRangeRows Midnight.SHA256.spreadRows
  List.map List.append Nat.add WitnessErasure.regionOperation Chips.Relocation.regionOperation
attribute [local cbv_eval] LinearNormalization.blockFromBytes_eq LinearNormalization.constant_eq
  List.map_cons List.map_nil WitnessErasure.activation
  SourceRelocation.Rules.nat_add_assoc SourceRelocation.Rules.nat_add_zero
  SourceRelocation.Rules.map_append SourceRelocation.Rules.nil_append
  SourceRelocation.Rules.cons_append SourceRelocation.Rules.append_nil
  SourceRelocation.Rules.erase_apply SourceRelocation.Rules.relocate_apply
  SourceRelocation.Rules.activation_relocate SourceRelocation.Rules.assigned_eq
  SourceRelocation.Rules.nat_add_left_eq SourceRelocation.Rules.nat_add_self_eq
  SourceRelocation.Rules.nat_self_add_eq

theorem inputReturns (offset : Nat) :
    Returns (inputAction offset) (beginCursor offset) (inputOutput offset) (inputAfter offset) := by
  cbv; exact ⟨rfl,rfl⟩
theorem inputChecked (offset : Nat) :
    Checked id (inputAction offset) (beginCursor offset) (inputOutput offset) (inputAfter offset)
      (inputOperations offset) := checked _ _ _ _ (inputReturns offset)

theorem initialReturns (offset : Nat) :
    Returns (initialAction offset) (inputAfter offset) (initialOutput offset) (initialAfter offset) := by
  cbv; exact ⟨rfl,rfl⟩
theorem initialChecked (offset : Nat) :
    Checked id (initialAction offset) (inputAfter offset) (initialOutput offset) (initialAfter offset)
      (initialOperations offset) := checked _ _ _ _ (initialReturns offset)

theorem paddingReturns (offset : Nat) :
    Returns (paddingAction offset) (initialAfter offset) (paddingOutput offset) (paddingAfter offset) := by
  cbv; exact ⟨rfl,rfl⟩
theorem paddingChecked (offset : Nat) :
    Checked id (paddingAction offset) (initialAfter offset) (paddingOutput offset) (paddingAfter offset)
      (paddingOperations offset) := checked _ _ _ _ (paddingReturns offset)

theorem packingReturns (offset : Nat) :
    Returns (packingAction offset) (paddingAfter offset) (packingOutput offset) (packingAfter offset) := by
  cbv; exact ⟨rfl,rfl⟩
theorem packingChecked (offset : Nat) :
    Checked id (packingAction offset) (paddingAfter offset) (packingOutput offset) (packingAfter offset)
      (packingOperations offset) := checked _ _ _ _ (packingReturns offset)

theorem prepare0Returns (offset : Nat) :
    Returns (prepare0Action offset) (packingAfter offset) (prepare0Output offset) (prepare0After offset) := by
  cbv
theorem prepare0Checked (offset : Nat) :
    Checked id (prepare0Action offset) (packingAfter offset) (prepare0Output offset) (prepare0After offset)
      (prepare0Operations offset) := checked _ _ _ _ (prepare0Returns offset)

theorem prepare1Returns (offset : Nat) :
    Returns (prepare1Action offset) (prepare0After offset) (prepare1Output offset) (prepare1After offset) := by
  cbv
theorem prepare1Checked (offset : Nat) :
    Checked id (prepare1Action offset) (prepare0After offset) (prepare1Output offset) (prepare1After offset)
      (prepare1Operations offset) := checked _ _ _ _ (prepare1Returns offset)

theorem prepare2Returns (offset : Nat) :
    Returns (prepare2Action offset) (prepare1After offset) (prepare2Output offset) (prepare2After offset) := by
  cbv
theorem prepare2Checked (offset : Nat) :
    Checked id (prepare2Action offset) (prepare1After offset) (prepare2Output offset) (prepare2After offset)
      (prepare2Operations offset) := checked _ _ _ _ (prepare2Returns offset)

theorem prepare3Returns (offset : Nat) :
    Returns (prepare3Action offset) (prepare2After offset) (prepare3Output offset) (prepare3After offset) := by
  cbv
theorem prepare3Checked (offset : Nat) :
    Checked id (prepare3Action offset) (prepare2After offset) (prepare3Output offset) (prepare3After offset)
      (prepare3Operations offset) := checked _ _ _ _ (prepare3Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
