import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group11
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

theorem round28Returns (offset : Nat) :
    Returns (round28Action offset) (round27After offset) (round28Output offset) (round28After offset) := by
  sha256_witness_unfold round28
  cbv; exact ⟨rfl,rfl⟩
theorem round28Checked (offset : Nat) :
    Checked id (round28Action offset) (round27After offset) (round28Output offset) (round28After offset)
      (round28Operations offset) := checked _ _ _ _ (round28Returns offset)

theorem round29Returns (offset : Nat) :
    Returns (round29Action offset) (round28After offset) (round29Output offset) (round29After offset) := by
  sha256_witness_unfold round29
  cbv; exact ⟨rfl,rfl⟩
theorem round29Checked (offset : Nat) :
    Checked id (round29Action offset) (round28After offset) (round29Output offset) (round29After offset)
      (round29Operations offset) := checked _ _ _ _ (round29Returns offset)

theorem round30Returns (offset : Nat) :
    Returns (round30Action offset) (round29After offset) (round30Output offset) (round30After offset) := by
  sha256_witness_unfold round30
  cbv; exact ⟨rfl,rfl⟩
theorem round30Checked (offset : Nat) :
    Checked id (round30Action offset) (round29After offset) (round30Output offset) (round30After offset)
      (round30Operations offset) := checked _ _ _ _ (round30Returns offset)

theorem round31Returns (offset : Nat) :
    Returns (round31Action offset) (round30After offset) (round31Output offset) (round31After offset) := by
  sha256_witness_unfold round31
  cbv; exact ⟨rfl,rfl⟩
theorem round31Checked (offset : Nat) :
    Checked id (round31Action offset) (round30After offset) (round31Output offset) (round31After offset)
      (round31Operations offset) := checked _ _ _ _ (round31Returns offset)

theorem round32Returns (offset : Nat) :
    Returns (round32Action offset) (round31After offset) (round32Output offset) (round32After offset) := by
  sha256_witness_unfold round32
  cbv; exact ⟨rfl,rfl⟩
theorem round32Checked (offset : Nat) :
    Checked id (round32Action offset) (round31After offset) (round32Output offset) (round32After offset)
      (round32Operations offset) := checked _ _ _ _ (round32Returns offset)

theorem round33Returns (offset : Nat) :
    Returns (round33Action offset) (round32After offset) (round33Output offset) (round33After offset) := by
  sha256_witness_unfold round33
  cbv; exact ⟨rfl,rfl⟩
theorem round33Checked (offset : Nat) :
    Checked id (round33Action offset) (round32After offset) (round33Output offset) (round33After offset)
      (round33Operations offset) := checked _ _ _ _ (round33Returns offset)

theorem round34Returns (offset : Nat) :
    Returns (round34Action offset) (round33After offset) (round34Output offset) (round34After offset) := by
  sha256_witness_unfold round34
  cbv; exact ⟨rfl,rfl⟩
theorem round34Checked (offset : Nat) :
    Checked id (round34Action offset) (round33After offset) (round34Output offset) (round34After offset)
      (round34Operations offset) := checked _ _ _ _ (round34Returns offset)

theorem round35Returns (offset : Nat) :
    Returns (round35Action offset) (round34After offset) (round35Output offset) (round35After offset) := by
  sha256_witness_unfold round35
  cbv; exact ⟨rfl,rfl⟩
theorem round35Checked (offset : Nat) :
    Checked id (round35Action offset) (round34After offset) (round35Output offset) (round35After offset)
      (round35Operations offset) := checked _ _ _ _ (round35Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
