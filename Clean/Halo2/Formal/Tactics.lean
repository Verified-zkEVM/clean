import Clean.Halo2.FormalRegion.ToFormal

namespace Halo2

open Lean Meta Simp in
/-- Reduce a concrete circuit's declared output metadata without adding a projection
lemma for every circuit bundle. Circuits with a reduced elaborated `output` field stop
at that field; opaque or still-symbolic bundles are left unchanged. -/
def foldDeclaredOutputProc : Simproc := fun expression => do
  let isRegion := expression.isAppOf ``FormalRegionCircuit.output
  unless expression.isAppOf ``FormalCircuit.output || isRegion do
    return .continue
  try
    let arguments := expression.getAppArgs
    let explicitArity := if isRegion then 5 else 4
    unless explicitArity ≤ arguments.size do
      return .continue
    let self := arguments[arguments.size - explicitArity]!
    let some unfoldedSelf ← withTransparency .default <| unfoldDefinition? self
      | return .continue
    let some unfoldedOutput ←
        withTransparency .default <| unfoldDefinition? expression
      | return .continue
    let withBundle := unfoldedOutput.replace fun candidate =>
      if candidate == self then some unfoldedSelf else none
    let withBundle ← withTransparency .reducible <| whnf withBundle
    let elaboratedOutput :=
      if isRegion then ``ElaboratedRegionCircuit.output else ``ElaboratedCircuit.output
    let some outputProjection := withBundle.find? fun candidate =>
        candidate.getAppFn.isConstOf elaboratedOutput
      | return .continue
    let some projectionInfo ← getProjectionFnInfo? elaboratedOutput
      | return .continue
    let projectionArguments := outputProjection.getAppArgs
    unless projectionInfo.numParams < projectionArguments.size do
      return .continue
    let elaborated := projectionArguments[projectionInfo.numParams]!
    let reducedElaborated ← withTransparency .default <| whnf elaborated
    let reducedElaborated ←
      if reducedElaborated != elaborated then
        pure reducedElaborated
      else
        match ← withTransparency .default <| unfoldDefinition? elaborated with
        | some unfoldedElaborated => pure unfoldedElaborated
        | none => pure elaborated
    let withElaborated := withBundle.replace fun candidate =>
      if candidate == elaborated then some reducedElaborated else none
    let reduced ← withTransparency .reducible <| whnf withElaborated
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldFormalCircuitDeclaredOutput
    (FormalCircuit.output _ _ _ _) := foldDeclaredOutputProc

simproc foldFormalRegionCircuitDeclaredOutput
    (FormalRegionCircuit.output _ _ _ _ _) := foldDeclaredOutputProc

attribute [keygen_output_norm]
  foldFormalCircuitDeclaredOutput
  foldFormalRegionCircuitDeclaredOutput

open Lean Meta Simp in
/-- Reduce a configured circuit's declared input-dependent equality requirements.
This is the keygen analogue of `foldDeclaredOutputProc`: it exposes only the small
`KeygenRequirements.inputPermutationColumns` field and never unfolds synthesis. -/
def foldDeclaredInputPermutationColumnsProc : Simproc := fun expression => do
  let isRegion :=
    expression.isAppOf ``FormalRegionCircuit.Configured.inputPermutationColumns
  unless expression.isAppOf ``FormalCircuit.Configured.inputPermutationColumns ||
      isRegion do
    return .continue
  try
    let arguments := expression.getAppArgs
    unless 4 ≤ arguments.size do
      return .continue
    let self := arguments[arguments.size - 4]!
    let some unfoldedSelf ← withTransparency .default <| unfoldDefinition? self
      | return .continue
    let some unfoldedProjection ←
        withTransparency .default <| unfoldDefinition? expression
      | return .continue
    let withBundle := unfoldedProjection.replace fun candidate =>
      if candidate == self then some unfoldedSelf else none
    let withBundle ← withTransparency .default <| whnf withBundle
    let some requirementProjection := withBundle.find? fun candidate =>
        candidate.getAppFn.isConstOf ``KeygenRequirements.inputPermutationColumns
      | if withBundle == expression then
          return .continue
        let proof ← mkExpectedTypeHint
          (← mkEqRefl expression) (← mkEq expression withBundle)
        return .visit { expr := withBundle, proof? := some proof }
    let requirementArguments := requirementProjection.getAppArgs
    unless 3 < requirementArguments.size do
      return .continue
    let requirements := requirementArguments[3]!
    let reducedRequirements ← withTransparency .default <| whnf requirements
    let reducedRequirements ←
      if reducedRequirements != requirements then
        pure reducedRequirements
      else
        match ← withTransparency .default <| unfoldDefinition? requirements with
        | some unfoldedRequirements => pure unfoldedRequirements
        | none => pure requirements
    let withRequirements := withBundle.replace fun candidate =>
      if candidate == requirements then some reducedRequirements else none
    let reduced ← withTransparency .reducible <| whnf withRequirements
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldFormalCircuitDeclaredInputPermutationColumns
    (FormalCircuit.Configured.inputPermutationColumns _ _) :=
  foldDeclaredInputPermutationColumnsProc

simproc foldFormalRegionCircuitDeclaredInputPermutationColumns
    (FormalRegionCircuit.Configured.inputPermutationColumns _ _) :=
  foldDeclaredInputPermutationColumnsProc

attribute [keygen_norm]
  foldFormalCircuitDeclaredInputPermutationColumns
  foldFormalRegionCircuitDeclaredInputPermutationColumns

end Halo2
