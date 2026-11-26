import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group5
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

theorem expand44Returns (offset : Nat) :
    Returns (expand44Action offset) (expand43After offset) (expand44Output offset) (expand44After offset) := by
  sha256_witness_unfold expand44
  cbv; exact ⟨rfl,rfl⟩
theorem expand44Checked (offset : Nat) :
    Checked id (expand44Action offset) (expand43After offset) (expand44Output offset) (expand44After offset)
      (expand44Operations offset) := checked _ _ _ _ (expand44Returns offset)

theorem expand45Returns (offset : Nat) :
    Returns (expand45Action offset) (expand44After offset) (expand45Output offset) (expand45After offset) := by
  sha256_witness_unfold expand45
  cbv; exact ⟨rfl,rfl⟩
theorem expand45Checked (offset : Nat) :
    Checked id (expand45Action offset) (expand44After offset) (expand45Output offset) (expand45After offset)
      (expand45Operations offset) := checked _ _ _ _ (expand45Returns offset)

theorem expand46Returns (offset : Nat) :
    Returns (expand46Action offset) (expand45After offset) (expand46Output offset) (expand46After offset) := by
  sha256_witness_unfold expand46
  cbv; exact ⟨rfl,rfl⟩
theorem expand46Checked (offset : Nat) :
    Checked id (expand46Action offset) (expand45After offset) (expand46Output offset) (expand46After offset)
      (expand46Operations offset) := checked _ _ _ _ (expand46Returns offset)

theorem expand47Returns (offset : Nat) :
    Returns (expand47Action offset) (expand46After offset) (expand47Output offset) (expand47After offset) := by
  sha256_witness_unfold expand47
  cbv; exact ⟨rfl,rfl⟩
theorem expand47Checked (offset : Nat) :
    Checked id (expand47Action offset) (expand46After offset) (expand47Output offset) (expand47After offset)
      (expand47Operations offset) := checked _ _ _ _ (expand47Returns offset)

theorem expand48Returns (offset : Nat) :
    Returns (expand48Action offset) (expand47After offset) (expand48Output offset) (expand48After offset) := by
  sha256_witness_unfold expand48
  cbv; exact ⟨rfl,rfl⟩
theorem expand48Checked (offset : Nat) :
    Checked id (expand48Action offset) (expand47After offset) (expand48Output offset) (expand48After offset)
      (expand48Operations offset) := checked _ _ _ _ (expand48Returns offset)

theorem expand49Returns (offset : Nat) :
    Returns (expand49Action offset) (expand48After offset) (expand49Output offset) (expand49After offset) := by
  sha256_witness_unfold expand49
  cbv; exact ⟨rfl,rfl⟩
theorem expand49Checked (offset : Nat) :
    Checked id (expand49Action offset) (expand48After offset) (expand49Output offset) (expand49After offset)
      (expand49Operations offset) := checked _ _ _ _ (expand49Returns offset)

theorem expand50Returns (offset : Nat) :
    Returns (expand50Action offset) (expand49After offset) (expand50Output offset) (expand50After offset) := by
  sha256_witness_unfold expand50
  cbv; exact ⟨rfl,rfl⟩
theorem expand50Checked (offset : Nat) :
    Checked id (expand50Action offset) (expand49After offset) (expand50Output offset) (expand50After offset)
      (expand50Operations offset) := checked _ _ _ _ (expand50Returns offset)

theorem expand51Returns (offset : Nat) :
    Returns (expand51Action offset) (expand50After offset) (expand51Output offset) (expand51After offset) := by
  sha256_witness_unfold expand51
  cbv; exact ⟨rfl,rfl⟩
theorem expand51Checked (offset : Nat) :
    Checked id (expand51Action offset) (expand50After offset) (expand51Output offset) (expand51After offset)
      (expand51Operations offset) := checked _ _ _ _ (expand51Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
