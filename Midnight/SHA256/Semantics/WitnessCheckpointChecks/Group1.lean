import Midnight.SHA256.Semantics.WitnessCheckpointChecks.Group0
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

theorem prepare4Returns (offset : Nat) :
    Returns (prepare4Action offset) (prepare3After offset) (prepare4Output offset) (prepare4After offset) := by
  cbv
theorem prepare4Checked (offset : Nat) :
    Checked id (prepare4Action offset) (prepare3After offset) (prepare4Output offset) (prepare4After offset)
      (prepare4Operations offset) := checked _ _ _ _ (prepare4Returns offset)

theorem prepare5Returns (offset : Nat) :
    Returns (prepare5Action offset) (prepare4After offset) (prepare5Output offset) (prepare5After offset) := by
  cbv
theorem prepare5Checked (offset : Nat) :
    Checked id (prepare5Action offset) (prepare4After offset) (prepare5Output offset) (prepare5After offset)
      (prepare5Operations offset) := checked _ _ _ _ (prepare5Returns offset)

theorem prepare6Returns (offset : Nat) :
    Returns (prepare6Action offset) (prepare5After offset) (prepare6Output offset) (prepare6After offset) := by
  cbv
theorem prepare6Checked (offset : Nat) :
    Checked id (prepare6Action offset) (prepare5After offset) (prepare6Output offset) (prepare6After offset)
      (prepare6Operations offset) := checked _ _ _ _ (prepare6Returns offset)

theorem prepare7Returns (offset : Nat) :
    Returns (prepare7Action offset) (prepare6After offset) (prepare7Output offset) (prepare7After offset) := by
  cbv
theorem prepare7Checked (offset : Nat) :
    Checked id (prepare7Action offset) (prepare6After offset) (prepare7Output offset) (prepare7After offset)
      (prepare7Operations offset) := checked _ _ _ _ (prepare7Returns offset)

theorem prepare8Returns (offset : Nat) :
    Returns (prepare8Action offset) (prepare7After offset) (prepare8Output offset) (prepare8After offset) := by
  cbv
theorem prepare8Checked (offset : Nat) :
    Checked id (prepare8Action offset) (prepare7After offset) (prepare8Output offset) (prepare8After offset)
      (prepare8Operations offset) := checked _ _ _ _ (prepare8Returns offset)

theorem prepare9Returns (offset : Nat) :
    Returns (prepare9Action offset) (prepare8After offset) (prepare9Output offset) (prepare9After offset) := by
  cbv
theorem prepare9Checked (offset : Nat) :
    Checked id (prepare9Action offset) (prepare8After offset) (prepare9Output offset) (prepare9After offset)
      (prepare9Operations offset) := checked _ _ _ _ (prepare9Returns offset)

theorem prepare10Returns (offset : Nat) :
    Returns (prepare10Action offset) (prepare9After offset) (prepare10Output offset) (prepare10After offset) := by
  cbv
theorem prepare10Checked (offset : Nat) :
    Checked id (prepare10Action offset) (prepare9After offset) (prepare10Output offset) (prepare10After offset)
      (prepare10Operations offset) := checked _ _ _ _ (prepare10Returns offset)

theorem prepare11Returns (offset : Nat) :
    Returns (prepare11Action offset) (prepare10After offset) (prepare11Output offset) (prepare11After offset) := by
  cbv
theorem prepare11Checked (offset : Nat) :
    Checked id (prepare11Action offset) (prepare10After offset) (prepare11Output offset) (prepare11After offset)
      (prepare11Operations offset) := checked _ _ _ _ (prepare11Returns offset)

end Midnight.SHA256.Semantics.WitnessCheckpoints
