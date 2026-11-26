import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group7
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

theorem expand60Returns (offset : Nat) :
    Returns (expand60Action offset) (expand59After offset) (expand60Output offset) (expand60After offset) := by
  sha256_witness_unfold expand60
  cbv; exact ⟨rfl,rfl⟩
theorem expand60Checked (offset : Nat) :
    Checked id (expand60Action offset) (expand59After offset) (expand60Output offset) (expand60After offset)
      (expand60Operations offset) := checked _ _ _ _ (expand60Returns offset)

theorem expand61Returns (offset : Nat) :
    Returns (expand61Action offset) (expand60After offset) (expand61Output offset) (expand61After offset) := by
  sha256_witness_unfold expand61
  cbv; exact ⟨rfl,rfl⟩
theorem expand61Checked (offset : Nat) :
    Checked id (expand61Action offset) (expand60After offset) (expand61Output offset) (expand61After offset)
      (expand61Operations offset) := checked _ _ _ _ (expand61Returns offset)

theorem expand62Returns (offset : Nat) :
    Returns (expand62Action offset) (expand61After offset) (expand62Output offset) (expand62After offset) := by
  sha256_witness_unfold expand62
  cbv; exact ⟨rfl,rfl⟩
theorem expand62Checked (offset : Nat) :
    Checked id (expand62Action offset) (expand61After offset) (expand62Output offset) (expand62After offset)
      (expand62Operations offset) := checked _ _ _ _ (expand62Returns offset)

theorem expand63Returns (offset : Nat) :
    Returns (expand63Action offset) (expand62After offset) (expand63Output offset) (expand63After offset) := by
  sha256_witness_unfold expand63
  cbv; exact ⟨rfl,rfl⟩
theorem expand63Checked (offset : Nat) :
    Checked id (expand63Action offset) (expand62After offset) (expand63Output offset) (expand63After offset)
      (expand63Operations offset) := checked _ _ _ _ (expand63Returns offset)

theorem round0Returns (offset : Nat) :
    Returns (round0Action offset) (expand63After offset) (round0Output offset) (round0After offset) := by
  sha256_witness_unfold round0
  cbv; exact ⟨rfl,rfl⟩
theorem round0Checked (offset : Nat) :
    Checked id (round0Action offset) (expand63After offset) (round0Output offset) (round0After offset)
      (round0Operations offset) := checked _ _ _ _ (round0Returns offset)

theorem round1Returns (offset : Nat) :
    Returns (round1Action offset) (round0After offset) (round1Output offset) (round1After offset) := by
  sha256_witness_unfold round1
  cbv; exact ⟨rfl,rfl⟩
theorem round1Checked (offset : Nat) :
    Checked id (round1Action offset) (round0After offset) (round1Output offset) (round1After offset)
      (round1Operations offset) := checked _ _ _ _ (round1Returns offset)

theorem round2Returns (offset : Nat) :
    Returns (round2Action offset) (round1After offset) (round2Output offset) (round2After offset) := by
  sha256_witness_unfold round2
  cbv; exact ⟨rfl,rfl⟩
theorem round2Checked (offset : Nat) :
    Checked id (round2Action offset) (round1After offset) (round2Output offset) (round2After offset)
      (round2Operations offset) := checked _ _ _ _ (round2Returns offset)

theorem round3Returns (offset : Nat) :
    Returns (round3Action offset) (round2After offset) (round3Output offset) (round3After offset) := by
  sha256_witness_unfold round3
  cbv; exact ⟨rfl,rfl⟩
theorem round3Checked (offset : Nat) :
    Checked id (round3Action offset) (round2After offset) (round3Output offset) (round3After offset)
      (round3Operations offset) := checked _ _ _ _ (round3Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
