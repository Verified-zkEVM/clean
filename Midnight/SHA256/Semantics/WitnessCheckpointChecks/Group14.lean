import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group13
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

theorem round44Returns (offset : Nat) :
    Returns (round44Action offset) (round43After offset) (round44Output offset) (round44After offset) := by
  sha256_witness_unfold round44
  cbv; exact ⟨rfl,rfl⟩
theorem round44Checked (offset : Nat) :
    Checked id (round44Action offset) (round43After offset) (round44Output offset) (round44After offset)
      (round44Operations offset) := checked _ _ _ _ (round44Returns offset)

theorem round45Returns (offset : Nat) :
    Returns (round45Action offset) (round44After offset) (round45Output offset) (round45After offset) := by
  sha256_witness_unfold round45
  cbv; exact ⟨rfl,rfl⟩
theorem round45Checked (offset : Nat) :
    Checked id (round45Action offset) (round44After offset) (round45Output offset) (round45After offset)
      (round45Operations offset) := checked _ _ _ _ (round45Returns offset)

theorem round46Returns (offset : Nat) :
    Returns (round46Action offset) (round45After offset) (round46Output offset) (round46After offset) := by
  sha256_witness_unfold round46
  cbv; exact ⟨rfl,rfl⟩
theorem round46Checked (offset : Nat) :
    Checked id (round46Action offset) (round45After offset) (round46Output offset) (round46After offset)
      (round46Operations offset) := checked _ _ _ _ (round46Returns offset)

theorem round47Returns (offset : Nat) :
    Returns (round47Action offset) (round46After offset) (round47Output offset) (round47After offset) := by
  sha256_witness_unfold round47
  cbv; exact ⟨rfl,rfl⟩
theorem round47Checked (offset : Nat) :
    Checked id (round47Action offset) (round46After offset) (round47Output offset) (round47After offset)
      (round47Operations offset) := checked _ _ _ _ (round47Returns offset)

theorem round48Returns (offset : Nat) :
    Returns (round48Action offset) (round47After offset) (round48Output offset) (round48After offset) := by
  sha256_witness_unfold round48
  cbv; exact ⟨rfl,rfl⟩
theorem round48Checked (offset : Nat) :
    Checked id (round48Action offset) (round47After offset) (round48Output offset) (round48After offset)
      (round48Operations offset) := checked _ _ _ _ (round48Returns offset)

theorem round49Returns (offset : Nat) :
    Returns (round49Action offset) (round48After offset) (round49Output offset) (round49After offset) := by
  sha256_witness_unfold round49
  cbv; exact ⟨rfl,rfl⟩
theorem round49Checked (offset : Nat) :
    Checked id (round49Action offset) (round48After offset) (round49Output offset) (round49After offset)
      (round49Operations offset) := checked _ _ _ _ (round49Returns offset)

theorem round50Returns (offset : Nat) :
    Returns (round50Action offset) (round49After offset) (round50Output offset) (round50After offset) := by
  sha256_witness_unfold round50
  cbv; exact ⟨rfl,rfl⟩
theorem round50Checked (offset : Nat) :
    Checked id (round50Action offset) (round49After offset) (round50Output offset) (round50After offset)
      (round50Operations offset) := checked _ _ _ _ (round50Returns offset)

theorem round51Returns (offset : Nat) :
    Returns (round51Action offset) (round50After offset) (round51Output offset) (round51After offset) := by
  sha256_witness_unfold round51
  cbv; exact ⟨rfl,rfl⟩
theorem round51Checked (offset : Nat) :
    Checked id (round51Action offset) (round50After offset) (round51Output offset) (round51After offset)
      (round51Operations offset) := checked _ _ _ _ (round51Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
