import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.SourceRelocationRules
import Lean
import Midnight.SHA256.Semantics.StageUnfold

/-! `sha256_relocation_reduction in` elaborates one declaration under the local `cbv`
configuration (opaque/eval sets and limits) shared by the source relocation leaves. -/
namespace Midnight.SHA256.Semantics.RelocationReduction
open Halo2 Lean Elab Command

elab "sha256_relocation_reduction" " in " declaration:command : command => do
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| set_option Elab.async false))
    elabCommand (← `(command| set_option maxRecDepth 10000))
    elabCommand (← `(command| attribute [local cbv_opaque] WitnessCircuit.blockFromBytes WitnessCircuit.constant
        BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing
        Midnight.SHA256.activation Midnight.SHA256.byteRangeRows Midnight.SHA256.spreadRows
        List.map List.append Nat.add WitnessErasure.regionOperation Chips.Relocation.regionOperation
        Witgen.WitgenIROver.ofFExpr WitnessIR.program WitnessIR.readNat WitnessIR.spread32
        WitnessIR.compactEven WitnessIR.evenBits WitnessIR.oddBits WitnessIR.negateSpread
        WitnessIR.limb WitnessIR.limbs WitnessIR.weighted WitnessIR.sum WitnessIR.sum32
        WitnessIR.carry32 UInt64.ofNat))
    elabCommand (← `(command| attribute [local cbv_eval] LinearNormalization.blockFromBytes_eq LinearNormalization.constant_eq
        List.map_cons List.map_nil WitnessErasure.activation
        SourceRelocation.Rules.nat_add_assoc SourceRelocation.Rules.nat_add_zero
        SourceRelocation.Rules.map_append SourceRelocation.Rules.nil_append
        SourceRelocation.Rules.cons_append SourceRelocation.Rules.append_nil
        SourceRelocation.Rules.erase_apply SourceRelocation.Rules.relocate_apply
        SourceRelocation.Rules.activation_relocate SourceRelocation.Rules.assigned_eq
        SourceRelocation.Rules.nat_add_left_eq SourceRelocation.Rules.nat_add_self_eq
        SourceRelocation.Rules.nat_self_add_eq))
    elabCommand declaration
  finally
    elabCommand (← `(command| end))

end Midnight.SHA256.Semantics.RelocationReduction
