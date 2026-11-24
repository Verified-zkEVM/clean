import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group16
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

theorem serialize3Returns (offset : Nat) :
    Returns (serialize3Action offset) (serialize2After offset) (serialize3Output offset) (serialize3After offset) := by
  cbv
theorem serialize3Checked (offset : Nat) :
    Checked id (serialize3Action offset) (serialize2After offset) (serialize3Output offset) (serialize3After offset)
      (serialize3Operations offset) := checked _ _ _ _ (serialize3Returns offset)

theorem serialize4Returns (offset : Nat) :
    Returns (serialize4Action offset) (serialize3After offset) (serialize4Output offset) (serialize4After offset) := by
  cbv
theorem serialize4Checked (offset : Nat) :
    Checked id (serialize4Action offset) (serialize3After offset) (serialize4Output offset) (serialize4After offset)
      (serialize4Operations offset) := checked _ _ _ _ (serialize4Returns offset)

theorem serialize5Returns (offset : Nat) :
    Returns (serialize5Action offset) (serialize4After offset) (serialize5Output offset) (serialize5After offset) := by
  cbv
theorem serialize5Checked (offset : Nat) :
    Checked id (serialize5Action offset) (serialize4After offset) (serialize5Output offset) (serialize5After offset)
      (serialize5Operations offset) := checked _ _ _ _ (serialize5Returns offset)

theorem serialize6Returns (offset : Nat) :
    Returns (serialize6Action offset) (serialize5After offset) (serialize6Output offset) (serialize6After offset) := by
  cbv
theorem serialize6Checked (offset : Nat) :
    Checked id (serialize6Action offset) (serialize5After offset) (serialize6Output offset) (serialize6After offset)
      (serialize6Operations offset) := checked _ _ _ _ (serialize6Returns offset)

theorem serialize7Returns (offset : Nat) :
    Returns (serialize7Action offset) (serialize6After offset) (serialize7Output offset) (serialize7After offset) := by
  cbv
theorem serialize7Checked (offset : Nat) :
    Checked id (serialize7Action offset) (serialize6After offset) (serialize7Output offset) (serialize7After offset)
      (serialize7Operations offset) := checked _ _ _ _ (serialize7Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
