import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group10
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

theorem round20Returns (offset : Nat) :
    Returns (round20Action offset) (round19After offset) (round20Output offset) (round20After offset) := by
  sha256_witness_unfold round20
  cbv; exact ⟨rfl,rfl⟩
theorem round20Checked (offset : Nat) :
    Checked id (round20Action offset) (round19After offset) (round20Output offset) (round20After offset)
      (round20Operations offset) := checked _ _ _ _ (round20Returns offset)

theorem round21Returns (offset : Nat) :
    Returns (round21Action offset) (round20After offset) (round21Output offset) (round21After offset) := by
  sha256_witness_unfold round21
  cbv; exact ⟨rfl,rfl⟩
theorem round21Checked (offset : Nat) :
    Checked id (round21Action offset) (round20After offset) (round21Output offset) (round21After offset)
      (round21Operations offset) := checked _ _ _ _ (round21Returns offset)

theorem round22Returns (offset : Nat) :
    Returns (round22Action offset) (round21After offset) (round22Output offset) (round22After offset) := by
  sha256_witness_unfold round22
  cbv; exact ⟨rfl,rfl⟩
theorem round22Checked (offset : Nat) :
    Checked id (round22Action offset) (round21After offset) (round22Output offset) (round22After offset)
      (round22Operations offset) := checked _ _ _ _ (round22Returns offset)

theorem round23Returns (offset : Nat) :
    Returns (round23Action offset) (round22After offset) (round23Output offset) (round23After offset) := by
  sha256_witness_unfold round23
  cbv; exact ⟨rfl,rfl⟩
theorem round23Checked (offset : Nat) :
    Checked id (round23Action offset) (round22After offset) (round23Output offset) (round23After offset)
      (round23Operations offset) := checked _ _ _ _ (round23Returns offset)

theorem round24Returns (offset : Nat) :
    Returns (round24Action offset) (round23After offset) (round24Output offset) (round24After offset) := by
  sha256_witness_unfold round24
  cbv; exact ⟨rfl,rfl⟩
theorem round24Checked (offset : Nat) :
    Checked id (round24Action offset) (round23After offset) (round24Output offset) (round24After offset)
      (round24Operations offset) := checked _ _ _ _ (round24Returns offset)

theorem round25Returns (offset : Nat) :
    Returns (round25Action offset) (round24After offset) (round25Output offset) (round25After offset) := by
  sha256_witness_unfold round25
  cbv; exact ⟨rfl,rfl⟩
theorem round25Checked (offset : Nat) :
    Checked id (round25Action offset) (round24After offset) (round25Output offset) (round25After offset)
      (round25Operations offset) := checked _ _ _ _ (round25Returns offset)

theorem round26Returns (offset : Nat) :
    Returns (round26Action offset) (round25After offset) (round26Output offset) (round26After offset) := by
  sha256_witness_unfold round26
  cbv; exact ⟨rfl,rfl⟩
theorem round26Checked (offset : Nat) :
    Checked id (round26Action offset) (round25After offset) (round26Output offset) (round26After offset)
      (round26Operations offset) := checked _ _ _ _ (round26Returns offset)

theorem round27Returns (offset : Nat) :
    Returns (round27Action offset) (round26After offset) (round27Output offset) (round27After offset) := by
  sha256_witness_unfold round27
  cbv; exact ⟨rfl,rfl⟩
theorem round27Checked (offset : Nat) :
    Checked id (round27Action offset) (round26After offset) (round27Output offset) (round27After offset)
      (round27Operations offset) := checked _ _ _ _ (round27Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
