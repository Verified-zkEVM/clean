import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group8
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

theorem round4Returns (offset : Nat) :
    Returns (round4Action offset) (round3After offset) (round4Output offset) (round4After offset) := by
  sha256_witness_unfold round4
  cbv; exact ⟨rfl,rfl⟩
theorem round4Checked (offset : Nat) :
    Checked id (round4Action offset) (round3After offset) (round4Output offset) (round4After offset)
      (round4Operations offset) := checked _ _ _ _ (round4Returns offset)

theorem round5Returns (offset : Nat) :
    Returns (round5Action offset) (round4After offset) (round5Output offset) (round5After offset) := by
  sha256_witness_unfold round5
  cbv; exact ⟨rfl,rfl⟩
theorem round5Checked (offset : Nat) :
    Checked id (round5Action offset) (round4After offset) (round5Output offset) (round5After offset)
      (round5Operations offset) := checked _ _ _ _ (round5Returns offset)

theorem round6Returns (offset : Nat) :
    Returns (round6Action offset) (round5After offset) (round6Output offset) (round6After offset) := by
  sha256_witness_unfold round6
  cbv; exact ⟨rfl,rfl⟩
theorem round6Checked (offset : Nat) :
    Checked id (round6Action offset) (round5After offset) (round6Output offset) (round6After offset)
      (round6Operations offset) := checked _ _ _ _ (round6Returns offset)

theorem round7Returns (offset : Nat) :
    Returns (round7Action offset) (round6After offset) (round7Output offset) (round7After offset) := by
  sha256_witness_unfold round7
  cbv; exact ⟨rfl,rfl⟩
theorem round7Checked (offset : Nat) :
    Checked id (round7Action offset) (round6After offset) (round7Output offset) (round7After offset)
      (round7Operations offset) := checked _ _ _ _ (round7Returns offset)

theorem round8Returns (offset : Nat) :
    Returns (round8Action offset) (round7After offset) (round8Output offset) (round8After offset) := by
  sha256_witness_unfold round8
  cbv; exact ⟨rfl,rfl⟩
theorem round8Checked (offset : Nat) :
    Checked id (round8Action offset) (round7After offset) (round8Output offset) (round8After offset)
      (round8Operations offset) := checked _ _ _ _ (round8Returns offset)

theorem round9Returns (offset : Nat) :
    Returns (round9Action offset) (round8After offset) (round9Output offset) (round9After offset) := by
  sha256_witness_unfold round9
  cbv; exact ⟨rfl,rfl⟩
theorem round9Checked (offset : Nat) :
    Checked id (round9Action offset) (round8After offset) (round9Output offset) (round9After offset)
      (round9Operations offset) := checked _ _ _ _ (round9Returns offset)

theorem round10Returns (offset : Nat) :
    Returns (round10Action offset) (round9After offset) (round10Output offset) (round10After offset) := by
  sha256_witness_unfold round10
  cbv; exact ⟨rfl,rfl⟩
theorem round10Checked (offset : Nat) :
    Checked id (round10Action offset) (round9After offset) (round10Output offset) (round10After offset)
      (round10Operations offset) := checked _ _ _ _ (round10Returns offset)

theorem round11Returns (offset : Nat) :
    Returns (round11Action offset) (round10After offset) (round11Output offset) (round11After offset) := by
  sha256_witness_unfold round11
  cbv; exact ⟨rfl,rfl⟩
theorem round11Checked (offset : Nat) :
    Checked id (round11Action offset) (round10After offset) (round11Output offset) (round11After offset)
      (round11Operations offset) := checked _ _ _ _ (round11Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
