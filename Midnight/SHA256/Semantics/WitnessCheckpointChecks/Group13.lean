import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group12
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

theorem round36Returns (offset : Nat) :
    Returns (round36Action offset) (round35After offset) (round36Output offset) (round36After offset) := by
  sha256_witness_unfold round36
  cbv; exact ⟨rfl,rfl⟩
theorem round36Checked (offset : Nat) :
    Checked id (round36Action offset) (round35After offset) (round36Output offset) (round36After offset)
      (round36Operations offset) := checked _ _ _ _ (round36Returns offset)

theorem round37Returns (offset : Nat) :
    Returns (round37Action offset) (round36After offset) (round37Output offset) (round37After offset) := by
  sha256_witness_unfold round37
  cbv; exact ⟨rfl,rfl⟩
theorem round37Checked (offset : Nat) :
    Checked id (round37Action offset) (round36After offset) (round37Output offset) (round37After offset)
      (round37Operations offset) := checked _ _ _ _ (round37Returns offset)

theorem round38Returns (offset : Nat) :
    Returns (round38Action offset) (round37After offset) (round38Output offset) (round38After offset) := by
  sha256_witness_unfold round38
  cbv; exact ⟨rfl,rfl⟩
theorem round38Checked (offset : Nat) :
    Checked id (round38Action offset) (round37After offset) (round38Output offset) (round38After offset)
      (round38Operations offset) := checked _ _ _ _ (round38Returns offset)

theorem round39Returns (offset : Nat) :
    Returns (round39Action offset) (round38After offset) (round39Output offset) (round39After offset) := by
  sha256_witness_unfold round39
  cbv; exact ⟨rfl,rfl⟩
theorem round39Checked (offset : Nat) :
    Checked id (round39Action offset) (round38After offset) (round39Output offset) (round39After offset)
      (round39Operations offset) := checked _ _ _ _ (round39Returns offset)

theorem round40Returns (offset : Nat) :
    Returns (round40Action offset) (round39After offset) (round40Output offset) (round40After offset) := by
  sha256_witness_unfold round40
  cbv; exact ⟨rfl,rfl⟩
theorem round40Checked (offset : Nat) :
    Checked id (round40Action offset) (round39After offset) (round40Output offset) (round40After offset)
      (round40Operations offset) := checked _ _ _ _ (round40Returns offset)

theorem round41Returns (offset : Nat) :
    Returns (round41Action offset) (round40After offset) (round41Output offset) (round41After offset) := by
  sha256_witness_unfold round41
  cbv; exact ⟨rfl,rfl⟩
theorem round41Checked (offset : Nat) :
    Checked id (round41Action offset) (round40After offset) (round41Output offset) (round41After offset)
      (round41Operations offset) := checked _ _ _ _ (round41Returns offset)

theorem round42Returns (offset : Nat) :
    Returns (round42Action offset) (round41After offset) (round42Output offset) (round42After offset) := by
  sha256_witness_unfold round42
  cbv; exact ⟨rfl,rfl⟩
theorem round42Checked (offset : Nat) :
    Checked id (round42Action offset) (round41After offset) (round42Output offset) (round42After offset)
      (round42Operations offset) := checked _ _ _ _ (round42Returns offset)

theorem round43Returns (offset : Nat) :
    Returns (round43Action offset) (round42After offset) (round43Output offset) (round43After offset) := by
  sha256_witness_unfold round43
  cbv; exact ⟨rfl,rfl⟩
theorem round43Checked (offset : Nat) :
    Checked id (round43Action offset) (round42After offset) (round43Output offset) (round43After offset)
      (round43Operations offset) := checked _ _ _ _ (round43Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
