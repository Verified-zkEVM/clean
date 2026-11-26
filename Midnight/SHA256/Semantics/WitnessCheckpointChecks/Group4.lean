import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group3
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

theorem expand28Returns (offset : Nat) :
    Returns (expand28Action offset) (expand27After offset) (expand28Output offset) (expand28After offset) := by
  sha256_witness_unfold expand28
  cbv; exact ⟨rfl,rfl⟩
theorem expand28Checked (offset : Nat) :
    Checked id (expand28Action offset) (expand27After offset) (expand28Output offset) (expand28After offset)
      (expand28Operations offset) := checked _ _ _ _ (expand28Returns offset)

theorem expand29Returns (offset : Nat) :
    Returns (expand29Action offset) (expand28After offset) (expand29Output offset) (expand29After offset) := by
  sha256_witness_unfold expand29
  cbv; exact ⟨rfl,rfl⟩
theorem expand29Checked (offset : Nat) :
    Checked id (expand29Action offset) (expand28After offset) (expand29Output offset) (expand29After offset)
      (expand29Operations offset) := checked _ _ _ _ (expand29Returns offset)

theorem expand30Returns (offset : Nat) :
    Returns (expand30Action offset) (expand29After offset) (expand30Output offset) (expand30After offset) := by
  sha256_witness_unfold expand30
  cbv; exact ⟨rfl,rfl⟩
theorem expand30Checked (offset : Nat) :
    Checked id (expand30Action offset) (expand29After offset) (expand30Output offset) (expand30After offset)
      (expand30Operations offset) := checked _ _ _ _ (expand30Returns offset)

theorem expand31Returns (offset : Nat) :
    Returns (expand31Action offset) (expand30After offset) (expand31Output offset) (expand31After offset) := by
  sha256_witness_unfold expand31
  cbv; exact ⟨rfl,rfl⟩
theorem expand31Checked (offset : Nat) :
    Checked id (expand31Action offset) (expand30After offset) (expand31Output offset) (expand31After offset)
      (expand31Operations offset) := checked _ _ _ _ (expand31Returns offset)

theorem expand32Returns (offset : Nat) :
    Returns (expand32Action offset) (expand31After offset) (expand32Output offset) (expand32After offset) := by
  sha256_witness_unfold expand32
  cbv; exact ⟨rfl,rfl⟩
theorem expand32Checked (offset : Nat) :
    Checked id (expand32Action offset) (expand31After offset) (expand32Output offset) (expand32After offset)
      (expand32Operations offset) := checked _ _ _ _ (expand32Returns offset)

theorem expand33Returns (offset : Nat) :
    Returns (expand33Action offset) (expand32After offset) (expand33Output offset) (expand33After offset) := by
  sha256_witness_unfold expand33
  cbv; exact ⟨rfl,rfl⟩
theorem expand33Checked (offset : Nat) :
    Checked id (expand33Action offset) (expand32After offset) (expand33Output offset) (expand33After offset)
      (expand33Operations offset) := checked _ _ _ _ (expand33Returns offset)

theorem expand34Returns (offset : Nat) :
    Returns (expand34Action offset) (expand33After offset) (expand34Output offset) (expand34After offset) := by
  sha256_witness_unfold expand34
  cbv; exact ⟨rfl,rfl⟩
theorem expand34Checked (offset : Nat) :
    Checked id (expand34Action offset) (expand33After offset) (expand34Output offset) (expand34After offset)
      (expand34Operations offset) := checked _ _ _ _ (expand34Returns offset)

theorem expand35Returns (offset : Nat) :
    Returns (expand35Action offset) (expand34After offset) (expand35Output offset) (expand35After offset) := by
  sha256_witness_unfold expand35
  cbv; exact ⟨rfl,rfl⟩
theorem expand35Checked (offset : Nat) :
    Checked id (expand35Action offset) (expand34After offset) (expand35Output offset) (expand35After offset)
      (expand35Operations offset) := checked _ _ _ _ (expand35Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
