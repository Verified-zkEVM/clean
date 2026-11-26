import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Basic
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.StructuralCheckpoints
import Midnight.SHA256.Semantics.StageUnfold
import Lean

/-! `sha256_erasure_reduction in` elaborates one declaration under the local `cbv`
configuration (opaque/eval sets and limits) shared by the erasure checkpoint leaves. -/
namespace Midnight.SHA256.Semantics.ErasureReduction
open Halo2 Lean Elab Command

elab "sha256_erasure_reduction" " in " declaration:command : command => do
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| set_option Elab.async false))
    elabCommand (← `(command| set_option maxRecDepth 10000))
    elabCommand (← `(command| set_option maxHeartbeats 2000000))
    elabCommand (← `(command| set_option cbv.maxSteps 2000000))
    elabCommand (← `(command| attribute [local cbv_opaque] BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing
        Chips.Synthesis.constant Synthesis.blockFromBytes WitnessCircuit.constant WitnessCircuit.blockFromBytes
        SHA256.activation byteRangeRows spreadRows List.map List.append List.concat
        Witgen.WitgenIROver.ofFExpr WitnessIR.program WitnessIR.readNat WitnessIR.spread32
        WitnessIR.compactEven WitnessIR.evenBits WitnessIR.oddBits WitnessIR.negateSpread
        WitnessIR.limb WitnessIR.limbs WitnessIR.weighted WitnessIR.sum WitnessIR.sum32
        WitnessIR.carry32 UInt64.ofNat))
    elabCommand (← `(command| attribute [local cbv_eval] StructuralNormalization.blockFromBytes_eq
        Chips.SynthesisCheckpoint.Reduction.constant_canonical
        LinearNormalization.blockFromBytes_eq LinearNormalization.constant_eq
        List.map_cons List.map_nil
        Midnight.Math.Checkpoint.Reduction.map_append Midnight.Math.Checkpoint.Reduction.nil_append
        Midnight.Math.Checkpoint.Reduction.cons_append Midnight.Math.Checkpoint.Reduction.append_nil
        Midnight.Math.Checkpoint.Reduction.append_assoc Midnight.Math.Checkpoint.Reduction.concat_append))
    elabCommand declaration
  finally
    elabCommand (← `(command| end))

/-- `sha256_structural_unfold roundN` (or `expandN`) unfolds that stage's
`StructuralCheckpoints` action down to the keygen synthesis gadgets. -/
macro "sha256_structural_unfold " stage:ident : tactic => do
  let .str .anonymous name := stage.getId | Lean.Macro.throwError "expected a stage name"
  let act := Lean.mkIdentFrom stage
    (.str `Midnight.SHA256.Semantics.StructuralCheckpoints (name ++ "Action"))
  if name.startsWith "round" then
    `(tactic| dsimp only [$act:ident, Midnight.SHA256.Synthesis.compressionRound,
      Midnight.SHA256.Synthesis.majority, Midnight.SHA256.Synthesis.choice,
      Midnight.SHA256.Synthesis.prepareA, Midnight.SHA256.Synthesis.prepareE,
      Midnight.SHA256.Synthesis.prepare, Midnight.SHA256.Synthesis.bigSigma0,
      Midnight.SHA256.Synthesis.bigSigma1, Midnight.SHA256.Synthesis.sigma0,
      Midnight.SHA256.Synthesis.sigma1, Midnight.SHA256.Synthesis.sigma,
      Midnight.SHA256.Synthesis.spread111110, Midnight.SHA256.Synthesis.plainAndSpread,
      Midnight.SHA256.Synthesis.scopy, Midnight.SHA256.Synthesis.sa])
  else if name.startsWith "expand" then
    `(tactic| dsimp only [$act:ident, Midnight.SHA256.Synthesis.compressionRound,
      Midnight.SHA256.Synthesis.bigSigma0, Midnight.SHA256.Synthesis.bigSigma1,
      Midnight.SHA256.Synthesis.sigma0, Midnight.SHA256.Synthesis.sigma1,
      Midnight.SHA256.Synthesis.sigma, Midnight.SHA256.Synthesis.spread111110,
      Midnight.SHA256.Synthesis.plainAndSpread, Midnight.SHA256.Synthesis.scopy,
      Midnight.SHA256.Synthesis.sa])
  else
    Lean.Macro.throwError "expected an expandN or roundN stage"

end Midnight.SHA256.Semantics.ErasureReduction
