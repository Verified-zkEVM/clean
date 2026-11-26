import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group9
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

theorem round12Returns (offset : Nat) :
    Returns (round12Action offset) (round11After offset) (round12Output offset) (round12After offset) := by
  sha256_witness_unfold round12
  cbv; exact ⟨rfl,rfl⟩
theorem round12Checked (offset : Nat) :
    Checked id (round12Action offset) (round11After offset) (round12Output offset) (round12After offset)
      (round12Operations offset) := checked _ _ _ _ (round12Returns offset)

theorem round13Returns (offset : Nat) :
    Returns (round13Action offset) (round12After offset) (round13Output offset) (round13After offset) := by
  sha256_witness_unfold round13
  cbv; exact ⟨rfl,rfl⟩
theorem round13Checked (offset : Nat) :
    Checked id (round13Action offset) (round12After offset) (round13Output offset) (round13After offset)
      (round13Operations offset) := checked _ _ _ _ (round13Returns offset)

theorem round14Returns (offset : Nat) :
    Returns (round14Action offset) (round13After offset) (round14Output offset) (round14After offset) := by
  sha256_witness_unfold round14
  cbv; exact ⟨rfl,rfl⟩
theorem round14Checked (offset : Nat) :
    Checked id (round14Action offset) (round13After offset) (round14Output offset) (round14After offset)
      (round14Operations offset) := checked _ _ _ _ (round14Returns offset)

theorem round15Returns (offset : Nat) :
    Returns (round15Action offset) (round14After offset) (round15Output offset) (round15After offset) := by
  sha256_witness_unfold round15
  cbv; exact ⟨rfl,rfl⟩
theorem round15Checked (offset : Nat) :
    Checked id (round15Action offset) (round14After offset) (round15Output offset) (round15After offset)
      (round15Operations offset) := checked _ _ _ _ (round15Returns offset)

theorem round16Returns (offset : Nat) :
    Returns (round16Action offset) (round15After offset) (round16Output offset) (round16After offset) := by
  sha256_witness_unfold round16
  cbv; exact ⟨rfl,rfl⟩
theorem round16Checked (offset : Nat) :
    Checked id (round16Action offset) (round15After offset) (round16Output offset) (round16After offset)
      (round16Operations offset) := checked _ _ _ _ (round16Returns offset)

theorem round17Returns (offset : Nat) :
    Returns (round17Action offset) (round16After offset) (round17Output offset) (round17After offset) := by
  sha256_witness_unfold round17
  cbv; exact ⟨rfl,rfl⟩
theorem round17Checked (offset : Nat) :
    Checked id (round17Action offset) (round16After offset) (round17Output offset) (round17After offset)
      (round17Operations offset) := checked _ _ _ _ (round17Returns offset)

theorem round18Returns (offset : Nat) :
    Returns (round18Action offset) (round17After offset) (round18Output offset) (round18After offset) := by
  sha256_witness_unfold round18
  cbv; exact ⟨rfl,rfl⟩
theorem round18Checked (offset : Nat) :
    Checked id (round18Action offset) (round17After offset) (round18Output offset) (round18After offset)
      (round18Operations offset) := checked _ _ _ _ (round18Returns offset)

theorem round19Returns (offset : Nat) :
    Returns (round19Action offset) (round18After offset) (round19Output offset) (round19After offset) := by
  sha256_witness_unfold round19
  cbv; exact ⟨rfl,rfl⟩
theorem round19Checked (offset : Nat) :
    Checked id (round19Action offset) (round18After offset) (round19Output offset) (round19After offset)
      (round19Operations offset) := checked _ _ _ _ (round19Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
