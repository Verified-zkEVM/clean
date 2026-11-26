import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group4
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.SourceRelocationRules

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

theorem expand36Returns (offset : Nat) :
    Returns (expand36Action offset) (expand35After offset) (expand36Output offset) (expand36After offset) := by
  sha256_witness_unfold expand36
  cbv; exact ⟨rfl,rfl⟩
theorem expand36Checked (offset : Nat) :
    Checked id (expand36Action offset) (expand35After offset) (expand36Output offset) (expand36After offset)
      (expand36Operations offset) := checked _ _ _ _ (expand36Returns offset)

theorem expand37Returns (offset : Nat) :
    Returns (expand37Action offset) (expand36After offset) (expand37Output offset) (expand37After offset) := by
  sha256_witness_unfold expand37
  cbv; exact ⟨rfl,rfl⟩
theorem expand37Checked (offset : Nat) :
    Checked id (expand37Action offset) (expand36After offset) (expand37Output offset) (expand37After offset)
      (expand37Operations offset) := checked _ _ _ _ (expand37Returns offset)

theorem expand38Returns (offset : Nat) :
    Returns (expand38Action offset) (expand37After offset) (expand38Output offset) (expand38After offset) := by
  sha256_witness_unfold expand38
  cbv; exact ⟨rfl,rfl⟩
theorem expand38Checked (offset : Nat) :
    Checked id (expand38Action offset) (expand37After offset) (expand38Output offset) (expand38After offset)
      (expand38Operations offset) := checked _ _ _ _ (expand38Returns offset)

theorem expand39Returns (offset : Nat) :
    Returns (expand39Action offset) (expand38After offset) (expand39Output offset) (expand39After offset) := by
  sha256_witness_unfold expand39
  cbv; exact ⟨rfl,rfl⟩
theorem expand39Checked (offset : Nat) :
    Checked id (expand39Action offset) (expand38After offset) (expand39Output offset) (expand39After offset)
      (expand39Operations offset) := checked _ _ _ _ (expand39Returns offset)

theorem expand40Returns (offset : Nat) :
    Returns (expand40Action offset) (expand39After offset) (expand40Output offset) (expand40After offset) := by
  sha256_witness_unfold expand40
  cbv; exact ⟨rfl,rfl⟩
theorem expand40Checked (offset : Nat) :
    Checked id (expand40Action offset) (expand39After offset) (expand40Output offset) (expand40After offset)
      (expand40Operations offset) := checked _ _ _ _ (expand40Returns offset)

theorem expand41Returns (offset : Nat) :
    Returns (expand41Action offset) (expand40After offset) (expand41Output offset) (expand41After offset) := by
  sha256_witness_unfold expand41
  cbv; exact ⟨rfl,rfl⟩
theorem expand41Checked (offset : Nat) :
    Checked id (expand41Action offset) (expand40After offset) (expand41Output offset) (expand41After offset)
      (expand41Operations offset) := checked _ _ _ _ (expand41Returns offset)

theorem expand42Returns (offset : Nat) :
    Returns (expand42Action offset) (expand41After offset) (expand42Output offset) (expand42After offset) := by
  sha256_witness_unfold expand42
  cbv; exact ⟨rfl,rfl⟩
theorem expand42Checked (offset : Nat) :
    Checked id (expand42Action offset) (expand41After offset) (expand42Output offset) (expand42After offset)
      (expand42Operations offset) := checked _ _ _ _ (expand42Returns offset)

theorem expand43Returns (offset : Nat) :
    Returns (expand43Action offset) (expand42After offset) (expand43Output offset) (expand43After offset) := by
  sha256_witness_unfold expand43
  cbv; exact ⟨rfl,rfl⟩
theorem expand43Checked (offset : Nat) :
    Checked id (expand43Action offset) (expand42After offset) (expand43Output offset) (expand43After offset)
      (expand43Operations offset) := checked _ _ _ _ (expand43Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
