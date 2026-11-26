import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group6
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

theorem expand52Returns (offset : Nat) :
    Returns (expand52Action offset) (expand51After offset) (expand52Output offset) (expand52After offset) := by
  sha256_witness_unfold expand52
  cbv; exact ⟨rfl,rfl⟩
theorem expand52Checked (offset : Nat) :
    Checked id (expand52Action offset) (expand51After offset) (expand52Output offset) (expand52After offset)
      (expand52Operations offset) := checked _ _ _ _ (expand52Returns offset)

theorem expand53Returns (offset : Nat) :
    Returns (expand53Action offset) (expand52After offset) (expand53Output offset) (expand53After offset) := by
  sha256_witness_unfold expand53
  cbv; exact ⟨rfl,rfl⟩
theorem expand53Checked (offset : Nat) :
    Checked id (expand53Action offset) (expand52After offset) (expand53Output offset) (expand53After offset)
      (expand53Operations offset) := checked _ _ _ _ (expand53Returns offset)

theorem expand54Returns (offset : Nat) :
    Returns (expand54Action offset) (expand53After offset) (expand54Output offset) (expand54After offset) := by
  sha256_witness_unfold expand54
  cbv; exact ⟨rfl,rfl⟩
theorem expand54Checked (offset : Nat) :
    Checked id (expand54Action offset) (expand53After offset) (expand54Output offset) (expand54After offset)
      (expand54Operations offset) := checked _ _ _ _ (expand54Returns offset)

theorem expand55Returns (offset : Nat) :
    Returns (expand55Action offset) (expand54After offset) (expand55Output offset) (expand55After offset) := by
  sha256_witness_unfold expand55
  cbv; exact ⟨rfl,rfl⟩
theorem expand55Checked (offset : Nat) :
    Checked id (expand55Action offset) (expand54After offset) (expand55Output offset) (expand55After offset)
      (expand55Operations offset) := checked _ _ _ _ (expand55Returns offset)

theorem expand56Returns (offset : Nat) :
    Returns (expand56Action offset) (expand55After offset) (expand56Output offset) (expand56After offset) := by
  sha256_witness_unfold expand56
  cbv; exact ⟨rfl,rfl⟩
theorem expand56Checked (offset : Nat) :
    Checked id (expand56Action offset) (expand55After offset) (expand56Output offset) (expand56After offset)
      (expand56Operations offset) := checked _ _ _ _ (expand56Returns offset)

theorem expand57Returns (offset : Nat) :
    Returns (expand57Action offset) (expand56After offset) (expand57Output offset) (expand57After offset) := by
  sha256_witness_unfold expand57
  cbv; exact ⟨rfl,rfl⟩
theorem expand57Checked (offset : Nat) :
    Checked id (expand57Action offset) (expand56After offset) (expand57Output offset) (expand57After offset)
      (expand57Operations offset) := checked _ _ _ _ (expand57Returns offset)

theorem expand58Returns (offset : Nat) :
    Returns (expand58Action offset) (expand57After offset) (expand58Output offset) (expand58After offset) := by
  sha256_witness_unfold expand58
  cbv; exact ⟨rfl,rfl⟩
theorem expand58Checked (offset : Nat) :
    Checked id (expand58Action offset) (expand57After offset) (expand58Output offset) (expand58After offset)
      (expand58Operations offset) := checked _ _ _ _ (expand58Returns offset)

theorem expand59Returns (offset : Nat) :
    Returns (expand59Action offset) (expand58After offset) (expand59Output offset) (expand59After offset) := by
  sha256_witness_unfold expand59
  cbv; exact ⟨rfl,rfl⟩
theorem expand59Checked (offset : Nat) :
    Checked id (expand59Action offset) (expand58After offset) (expand59Output offset) (expand59After offset)
      (expand59Operations offset) := checked _ _ _ _ (expand59Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
