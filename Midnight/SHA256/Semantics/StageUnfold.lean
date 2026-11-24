import Midnight.SHA256.Semantics.WitnessCheckpointModel

/-! Shared unfolding for the generated per-stage proofs. -/
namespace Midnight.SHA256.Semantics.StageUnfold

/-- `sha256_witness_unfold roundN` (or `expandN`) unfolds that stage's
`WitnessCheckpoints` operations and action down to the witness gadgets. -/
macro "sha256_witness_unfold " stage:ident : tactic => do
  let .str .anonymous name := stage.getId | Lean.Macro.throwError "expected a stage name"
  let ns := `Midnight.SHA256.Semantics.WitnessCheckpoints
  let ops := Lean.mkIdentFrom stage (.str ns (name ++ "Operations"))
  let act := Lean.mkIdentFrom stage (.str ns (name ++ "Action"))
  if name.startsWith "round" then
    `(tactic| dsimp only [$ops:ident, $act:ident,
      Midnight.SHA256.Semantics.WitnessCheckpointModel.operations,
      Midnight.SHA256.WitnessCircuit.compressionRound, Midnight.SHA256.WitnessCircuit.majority,
      Midnight.SHA256.WitnessCircuit.choice, Midnight.SHA256.WitnessCircuit.prepareA,
      Midnight.SHA256.WitnessCircuit.prepareE, Midnight.SHA256.WitnessCircuit.prepare,
      Midnight.SHA256.WitnessCircuit.bigSigma0, Midnight.SHA256.WitnessCircuit.bigSigma1,
      Midnight.SHA256.WitnessCircuit.sigma0, Midnight.SHA256.WitnessCircuit.sigma1,
      Midnight.SHA256.WitnessCircuit.sigma, Midnight.SHA256.WitnessCircuit.spread111110,
      Midnight.SHA256.WitnessCircuit.plainAndSpread, Midnight.SHA256.WitnessCircuit.scopy,
      Midnight.SHA256.WitnessCircuit.sa])
  else if name.startsWith "expand" then
    `(tactic| dsimp only [$ops:ident, $act:ident,
      Midnight.SHA256.Semantics.WitnessCheckpointModel.operations,
      Midnight.SHA256.WitnessCircuit.compressionRound,
      Midnight.SHA256.WitnessCircuit.bigSigma0, Midnight.SHA256.WitnessCircuit.bigSigma1,
      Midnight.SHA256.WitnessCircuit.sigma0, Midnight.SHA256.WitnessCircuit.sigma1,
      Midnight.SHA256.WitnessCircuit.sigma, Midnight.SHA256.WitnessCircuit.spread111110,
      Midnight.SHA256.WitnessCircuit.plainAndSpread, Midnight.SHA256.WitnessCircuit.scopy,
      Midnight.SHA256.WitnessCircuit.sa])
  else
    Lean.Macro.throwError "expected an expandN or roundN stage"

end Midnight.SHA256.Semantics.StageUnfold
