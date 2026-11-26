import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group1
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

theorem prepare12Returns (offset : Nat) :
    Returns (prepare12Action offset) (prepare11After offset) (prepare12Output offset) (prepare12After offset) := by
  cbv
theorem prepare12Checked (offset : Nat) :
    Checked id (prepare12Action offset) (prepare11After offset) (prepare12Output offset) (prepare12After offset)
      (prepare12Operations offset) := checked _ _ _ _ (prepare12Returns offset)

theorem prepare13Returns (offset : Nat) :
    Returns (prepare13Action offset) (prepare12After offset) (prepare13Output offset) (prepare13After offset) := by
  cbv
theorem prepare13Checked (offset : Nat) :
    Checked id (prepare13Action offset) (prepare12After offset) (prepare13Output offset) (prepare13After offset)
      (prepare13Operations offset) := checked _ _ _ _ (prepare13Returns offset)

theorem prepare14Returns (offset : Nat) :
    Returns (prepare14Action offset) (prepare13After offset) (prepare14Output offset) (prepare14After offset) := by
  cbv
theorem prepare14Checked (offset : Nat) :
    Checked id (prepare14Action offset) (prepare13After offset) (prepare14Output offset) (prepare14After offset)
      (prepare14Operations offset) := checked _ _ _ _ (prepare14Returns offset)

theorem prepare15Returns (offset : Nat) :
    Returns (prepare15Action offset) (prepare14After offset) (prepare15Output offset) (prepare15After offset) := by
  cbv
theorem prepare15Checked (offset : Nat) :
    Checked id (prepare15Action offset) (prepare14After offset) (prepare15Output offset) (prepare15After offset)
      (prepare15Operations offset) := checked _ _ _ _ (prepare15Returns offset)

theorem expand16Returns (offset : Nat) :
    Returns (expand16Action offset) (prepare15After offset) (expand16Output offset) (expand16After offset) := by
  sha256_witness_unfold expand16
  cbv; exact ⟨rfl,rfl⟩
theorem expand16Checked (offset : Nat) :
    Checked id (expand16Action offset) (prepare15After offset) (expand16Output offset) (expand16After offset)
      (expand16Operations offset) := checked _ _ _ _ (expand16Returns offset)

theorem expand17Returns (offset : Nat) :
    Returns (expand17Action offset) (expand16After offset) (expand17Output offset) (expand17After offset) := by
  sha256_witness_unfold expand17
  cbv; exact ⟨rfl,rfl⟩
theorem expand17Checked (offset : Nat) :
    Checked id (expand17Action offset) (expand16After offset) (expand17Output offset) (expand17After offset)
      (expand17Operations offset) := checked _ _ _ _ (expand17Returns offset)

theorem expand18Returns (offset : Nat) :
    Returns (expand18Action offset) (expand17After offset) (expand18Output offset) (expand18After offset) := by
  sha256_witness_unfold expand18
  cbv; exact ⟨rfl,rfl⟩
theorem expand18Checked (offset : Nat) :
    Checked id (expand18Action offset) (expand17After offset) (expand18Output offset) (expand18After offset)
      (expand18Operations offset) := checked _ _ _ _ (expand18Returns offset)

theorem expand19Returns (offset : Nat) :
    Returns (expand19Action offset) (expand18After offset) (expand19Output offset) (expand19After offset) := by
  sha256_witness_unfold expand19
  cbv; exact ⟨rfl,rfl⟩
theorem expand19Checked (offset : Nat) :
    Checked id (expand19Action offset) (expand18After offset) (expand19Output offset) (expand19After offset)
      (expand19Operations offset) := checked _ _ _ _ (expand19Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
