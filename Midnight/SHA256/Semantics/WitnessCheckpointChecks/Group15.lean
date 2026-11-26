import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group14
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

theorem round52Returns (offset : Nat) :
    Returns (round52Action offset) (round51After offset) (round52Output offset) (round52After offset) := by
  sha256_witness_unfold round52
  cbv; exact ⟨rfl,rfl⟩
theorem round52Checked (offset : Nat) :
    Checked id (round52Action offset) (round51After offset) (round52Output offset) (round52After offset)
      (round52Operations offset) := checked _ _ _ _ (round52Returns offset)

theorem round53Returns (offset : Nat) :
    Returns (round53Action offset) (round52After offset) (round53Output offset) (round53After offset) := by
  sha256_witness_unfold round53
  cbv; exact ⟨rfl,rfl⟩
theorem round53Checked (offset : Nat) :
    Checked id (round53Action offset) (round52After offset) (round53Output offset) (round53After offset)
      (round53Operations offset) := checked _ _ _ _ (round53Returns offset)

theorem round54Returns (offset : Nat) :
    Returns (round54Action offset) (round53After offset) (round54Output offset) (round54After offset) := by
  sha256_witness_unfold round54
  cbv; exact ⟨rfl,rfl⟩
theorem round54Checked (offset : Nat) :
    Checked id (round54Action offset) (round53After offset) (round54Output offset) (round54After offset)
      (round54Operations offset) := checked _ _ _ _ (round54Returns offset)

theorem round55Returns (offset : Nat) :
    Returns (round55Action offset) (round54After offset) (round55Output offset) (round55After offset) := by
  sha256_witness_unfold round55
  cbv; exact ⟨rfl,rfl⟩
theorem round55Checked (offset : Nat) :
    Checked id (round55Action offset) (round54After offset) (round55Output offset) (round55After offset)
      (round55Operations offset) := checked _ _ _ _ (round55Returns offset)

theorem round56Returns (offset : Nat) :
    Returns (round56Action offset) (round55After offset) (round56Output offset) (round56After offset) := by
  sha256_witness_unfold round56
  cbv; exact ⟨rfl,rfl⟩
theorem round56Checked (offset : Nat) :
    Checked id (round56Action offset) (round55After offset) (round56Output offset) (round56After offset)
      (round56Operations offset) := checked _ _ _ _ (round56Returns offset)

theorem round57Returns (offset : Nat) :
    Returns (round57Action offset) (round56After offset) (round57Output offset) (round57After offset) := by
  sha256_witness_unfold round57
  cbv; exact ⟨rfl,rfl⟩
theorem round57Checked (offset : Nat) :
    Checked id (round57Action offset) (round56After offset) (round57Output offset) (round57After offset)
      (round57Operations offset) := checked _ _ _ _ (round57Returns offset)

theorem round58Returns (offset : Nat) :
    Returns (round58Action offset) (round57After offset) (round58Output offset) (round58After offset) := by
  sha256_witness_unfold round58
  cbv; exact ⟨rfl,rfl⟩
theorem round58Checked (offset : Nat) :
    Checked id (round58Action offset) (round57After offset) (round58Output offset) (round58After offset)
      (round58Operations offset) := checked _ _ _ _ (round58Returns offset)

theorem round59Returns (offset : Nat) :
    Returns (round59Action offset) (round58After offset) (round59Output offset) (round59After offset) := by
  sha256_witness_unfold round59
  cbv; exact ⟨rfl,rfl⟩
theorem round59Checked (offset : Nat) :
    Checked id (round59Action offset) (round58After offset) (round59Output offset) (round59After offset)
      (round59Operations offset) := checked _ _ _ _ (round59Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
