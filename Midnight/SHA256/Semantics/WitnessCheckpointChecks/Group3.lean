import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group2
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

theorem expand20Returns (offset : Nat) :
    Returns (expand20Action offset) (expand19After offset) (expand20Output offset) (expand20After offset) := by
  sha256_witness_unfold expand20
  cbv; exact ⟨rfl,rfl⟩
theorem expand20Checked (offset : Nat) :
    Checked id (expand20Action offset) (expand19After offset) (expand20Output offset) (expand20After offset)
      (expand20Operations offset) := checked _ _ _ _ (expand20Returns offset)

theorem expand21Returns (offset : Nat) :
    Returns (expand21Action offset) (expand20After offset) (expand21Output offset) (expand21After offset) := by
  sha256_witness_unfold expand21
  cbv; exact ⟨rfl,rfl⟩
theorem expand21Checked (offset : Nat) :
    Checked id (expand21Action offset) (expand20After offset) (expand21Output offset) (expand21After offset)
      (expand21Operations offset) := checked _ _ _ _ (expand21Returns offset)

theorem expand22Returns (offset : Nat) :
    Returns (expand22Action offset) (expand21After offset) (expand22Output offset) (expand22After offset) := by
  sha256_witness_unfold expand22
  cbv; exact ⟨rfl,rfl⟩
theorem expand22Checked (offset : Nat) :
    Checked id (expand22Action offset) (expand21After offset) (expand22Output offset) (expand22After offset)
      (expand22Operations offset) := checked _ _ _ _ (expand22Returns offset)

theorem expand23Returns (offset : Nat) :
    Returns (expand23Action offset) (expand22After offset) (expand23Output offset) (expand23After offset) := by
  sha256_witness_unfold expand23
  cbv; exact ⟨rfl,rfl⟩
theorem expand23Checked (offset : Nat) :
    Checked id (expand23Action offset) (expand22After offset) (expand23Output offset) (expand23After offset)
      (expand23Operations offset) := checked _ _ _ _ (expand23Returns offset)

theorem expand24Returns (offset : Nat) :
    Returns (expand24Action offset) (expand23After offset) (expand24Output offset) (expand24After offset) := by
  sha256_witness_unfold expand24
  cbv; exact ⟨rfl,rfl⟩
theorem expand24Checked (offset : Nat) :
    Checked id (expand24Action offset) (expand23After offset) (expand24Output offset) (expand24After offset)
      (expand24Operations offset) := checked _ _ _ _ (expand24Returns offset)

theorem expand25Returns (offset : Nat) :
    Returns (expand25Action offset) (expand24After offset) (expand25Output offset) (expand25After offset) := by
  sha256_witness_unfold expand25
  cbv; exact ⟨rfl,rfl⟩
theorem expand25Checked (offset : Nat) :
    Checked id (expand25Action offset) (expand24After offset) (expand25Output offset) (expand25After offset)
      (expand25Operations offset) := checked _ _ _ _ (expand25Returns offset)

theorem expand26Returns (offset : Nat) :
    Returns (expand26Action offset) (expand25After offset) (expand26Output offset) (expand26After offset) := by
  sha256_witness_unfold expand26
  cbv; exact ⟨rfl,rfl⟩
theorem expand26Checked (offset : Nat) :
    Checked id (expand26Action offset) (expand25After offset) (expand26Output offset) (expand26After offset)
      (expand26Operations offset) := checked _ _ _ _ (expand26Returns offset)

theorem expand27Returns (offset : Nat) :
    Returns (expand27Action offset) (expand26After offset) (expand27Output offset) (expand27After offset) := by
  sha256_witness_unfold expand27
  cbv; exact ⟨rfl,rfl⟩
theorem expand27Checked (offset : Nat) :
    Checked id (expand27Action offset) (expand26After offset) (expand27Output offset) (expand27After offset)
      (expand27Operations offset) := checked _ _ _ _ (expand27Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
