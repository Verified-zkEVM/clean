import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group15
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

theorem round60Returns (offset : Nat) :
    Returns (round60Action offset) (round59After offset) (round60Output offset) (round60After offset) := by
  sha256_witness_unfold round60
  cbv; exact ⟨rfl,rfl⟩
theorem round60Checked (offset : Nat) :
    Checked id (round60Action offset) (round59After offset) (round60Output offset) (round60After offset)
      (round60Operations offset) := checked _ _ _ _ (round60Returns offset)

theorem round61Returns (offset : Nat) :
    Returns (round61Action offset) (round60After offset) (round61Output offset) (round61After offset) := by
  sha256_witness_unfold round61
  cbv; exact ⟨rfl,rfl⟩
theorem round61Checked (offset : Nat) :
    Checked id (round61Action offset) (round60After offset) (round61Output offset) (round61After offset)
      (round61Operations offset) := checked _ _ _ _ (round61Returns offset)

theorem round62Returns (offset : Nat) :
    Returns (round62Action offset) (round61After offset) (round62Output offset) (round62After offset) := by
  sha256_witness_unfold round62
  cbv; exact ⟨rfl,rfl⟩
theorem round62Checked (offset : Nat) :
    Checked id (round62Action offset) (round61After offset) (round62Output offset) (round62After offset)
      (round62Operations offset) := checked _ _ _ _ (round62Returns offset)

theorem round63Returns (offset : Nat) :
    Returns (round63Action offset) (round62After offset) (round63Output offset) (round63After offset) := by
  sha256_witness_unfold round63
  cbv; exact ⟨rfl,rfl⟩
theorem round63Checked (offset : Nat) :
    Checked id (round63Action offset) (round62After offset) (round63Output offset) (round63After offset)
      (round63Operations offset) := checked _ _ _ _ (round63Returns offset)

theorem feedforwardReturns (offset : Nat) :
    Returns (feedforwardAction offset) (round63After offset) (feedforwardOutput offset) (feedforwardAfter offset) := by
  cbv; exact ⟨rfl,rfl⟩
theorem feedforwardChecked (offset : Nat) :
    Checked id (feedforwardAction offset) (round63After offset) (feedforwardOutput offset) (feedforwardAfter offset)
      (feedforwardOperations offset) := checked _ _ _ _ (feedforwardReturns offset)

theorem serialize0Returns (offset : Nat) :
    Returns (serialize0Action offset) (feedforwardAfter offset) (serialize0Output offset) (serialize0After offset) := by
  cbv
theorem serialize0Checked (offset : Nat) :
    Checked id (serialize0Action offset) (feedforwardAfter offset) (serialize0Output offset) (serialize0After offset)
      (serialize0Operations offset) := checked _ _ _ _ (serialize0Returns offset)

theorem serialize1Returns (offset : Nat) :
    Returns (serialize1Action offset) (serialize0After offset) (serialize1Output offset) (serialize1After offset) := by
  cbv
theorem serialize1Checked (offset : Nat) :
    Checked id (serialize1Action offset) (serialize0After offset) (serialize1Output offset) (serialize1After offset)
      (serialize1Operations offset) := checked _ _ _ _ (serialize1Returns offset)

theorem serialize2Returns (offset : Nat) :
    Returns (serialize2Action offset) (serialize1After offset) (serialize2Output offset) (serialize2After offset) := by
  cbv
theorem serialize2Checked (offset : Nat) :
    Checked id (serialize2Action offset) (serialize1After offset) (serialize2Output offset) (serialize2After offset)
      (serialize2Operations offset) := checked _ _ _ _ (serialize2Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
