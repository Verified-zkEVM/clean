import Lean
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructSimp

open Lean Elab Tactic Meta
open Circuit

namespace CircuitProofStart

/-- If `name` is a generated view structure name like `Input.Var`, return `Input`. -/
private def baseNameOfVarView? (name : Name) : Option Name :=
  match name with
  | .str base "Var" => some base
  | _ => none

/-- Extract the underlying circuit type from a type like `Var Input F`, if present. -/
private def circuitTypeOfVarProjection? (type : Expr) : Option Name :=
  if type.getAppFn.isConstOf ``CircuitType.Var then
    match type.getAppArgs[0]? with
    | some e =>
      match e with
      | Expr.const name _ => some name
      | _ => none
    | _ => none
  else
    none

/--
Find generated eval-exposure lemmas for the `h_input` variable, if it is a
derived record-shaped `CircuitType` input.

For a derived input `Input`, the `CircuitType` deriver generates
`Input.Var` and lemmas `Input.eval_verifier` / `Input.eval_prover`. We detect
that shape from the type of the final argument of `eval env input_var`.
-/
private def generatedEvalLemmasForHInput : TacticM (Array Name) := do
  withMainContext do
    let hInput ← getLocalDeclFromUserName `h_input
    let hType ← instantiateMVars hInput.type
    unless hType.isAppOf ``Eq do
      return #[]
    let some lhs := hType.getArg? 1
      | return #[]
    let some inputVar := lhs.getAppArgs.back?
      | return #[]
    let inputVarType ← inferType inputVar
    let inputVarType ← withTransparency .reducible (whnf inputVarType)
    let some baseName := circuitTypeOfVarProjection? inputVarType <|>
        (inputVarType.getAppFn.constName?.bind baseNameOfVarView?)
      | return #[]
    let env ← getEnv
    let candidates := #[baseName ++ `eval_verifier, baseName ++ `eval_prover]
    return candidates.filter env.contains

/--
Expose `h_input` using generated record `CircuitType` eval lemmas only.

This intentionally does not rewrite with generic `CircuitType.eval_verifier` /
`CircuitType.eval_prover`: hand-written `CircuitType`s may be abstract and should
not be unfolded unless they provide an explicit lemma with this shape.
-/
private def exposeGeneratedCircuitTypeHInput : TacticM Unit := do
  let lemmas ← generatedEvalLemmasForHInput
  if lemmas.isEmpty then
    throwError "no generated CircuitType eval lemma found for h_input"
  let mut progressed := false
  for lemmaName in lemmas do
    try
      evalTactic (← `(tactic| rw [$(mkIdent lemmaName):ident] at $(mkIdent `h_input):ident))
      progressed := true
    catch _ =>
      pure ()
  unless progressed do
    throwError "generated CircuitType eval lemmas did not rewrite h_input"

end CircuitProofStart

/--
  Introduce all standard parameters and hypotheses for Soundness or Completeness.
-/
partial def circuitProofStartCore : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType

    -- First check if this is a Soundness or Completeness type that needs unfolding
    -- We need to check the head constant of the expression
    let headConst? := goalType.getAppFn.constName?
    let isSoundness := headConst? == some ``Soundness ||
                       headConst? == some ``FormalAssertion.Soundness ||
                       headConst? == some ``GeneralFormalCircuit.Soundness ||
                       headConst? == some ``GeneralFormalCircuit.WithHint.Soundness
    let isCompleteness := headConst? == some ``Completeness ||
                          headConst? == some ``FormalAssertion.Completeness ||
                          headConst? == some ``GeneralFormalCircuit.Completeness ||
                          headConst? == some ``GeneralFormalCircuit.WithHint.Completeness

    if isSoundness then
      match headConst? with
      | some ``Soundness =>
        evalTactic (← `(tactic| unfold Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``FormalAssertion.Soundness =>
        evalTactic (← `(tactic| unfold FormalAssertion.Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.Soundness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.WithHint.Soundness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.WithHint.Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | _ => pure ()
      return
    else if isCompleteness then
      -- Unfold the appropriate Completeness definition and introduce the correct parameters
      match headConst? with
      | some ``Completeness =>
        evalTactic (← `(tactic| unfold Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``FormalAssertion.Completeness =>
        evalTactic (← `(tactic| unfold FormalAssertion.Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions, `h_spec]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.Completeness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.WithHint.Completeness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.WithHint.Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | _ => pure ()
      return
    else
      -- Goal is not a supported Soundness or Completeness type
      throwError "circuit_proof_start can only be used on Soundness, Completeness and variants"

/--
  Standard tactic for starting soundness and completeness proofs.

  This tactic:
  1. Automatically introduces all parameters for `Soundness` or `Completeness` goals
  2. Unfolds `main`, `Assumptions`, and `Spec` definitions
  3. Normalizes the goal state using circuit_norm
  4. Applies provable_struct_simp to decompose structs and decompose eval that mention struct components
  5. Additionally simplifies h_holds henv and the goal with circuit_norm and h_input

  **Supported goal types**: This tactic works on `Soundness`, `Completeness`,
  `FormalAssertion.Soundness`, `FormalAssertion.Completeness`,
  `GeneralFormalCircuit.Soundness`, or `GeneralFormalCircuit.Completeness` goals.

  **Optional argument**: You can provide additional lemmas for simplification by using square brackets:
  `circuit_proof_start [lemma1, lemma2, ...]`. These lemmas will be used alongside `circuit_norm`
  to simplify the goal and the hypotheses.

  Example usage:
  ```lean
  theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start
    -- The assumptions in Soundness are introduced. All provable structs are decomposed when their components are mentioned

  theorem soundness_with_lemmas : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start [my_custom_lemma, another_lemma]
    -- Same as above but also uses my_custom_lemma and another_lemma in simplifications

  theorem completeness : Completeness (F p) elaborated Assumptions := by
    circuit_proof_start
    -- The assumptions in Completeness are introduced. All provable structs are decomposed when their components are mentioned
  ```
-/
syntax "circuit_proof_start" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_start $[[$terms:term,*]]?) => do
  -- intro all hypotheses
  circuitProofStartCore
  try (evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `input_var):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `h_input):ident))) catch _ => pure ()

  -- try to unfold main, Assumptions and Spec as local definitions
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Assumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Spec):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `ProverAssumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `ProverSpec):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `elaborated):ident] at *)) -- sometimes `main` is hidden behind `elaborated`
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `main):ident] at *))

  -- simplify structs / eval first
  try (evalTactic (← `(tactic| provable_struct_simp))) catch _ => pure ()
  try CircuitProofStart.exposeGeneratedCircuitTypeHInput catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm] at $(mkIdent `h_input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| provable_struct_simp))) catch _ => pure ()

  -- Additional simplification for common patterns in soundness/completeness proofs
  -- Convert optional terms to simpLemma syntax
  let extraLemmas := match terms with
    | some terms => terms.getElems.map fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    | none => #[]
  let lemmasArray ← extraLemmas.mapM id

  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_assumptions):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_holds):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_env):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*]))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_spec):ident))) catch _ => pure ()

-- core version only, for experimentation with variants of this tactic
elab "circuit_proof_start_core" : tactic => do
  circuitProofStartCore

-- version of circuit_proof_start that attempts to close the goal with `simp_all`
syntax "circuit_proof_all" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_all $[[$terms:term,*]]?) => do
  let lemmas := terms.getD (.mk #[])
  evalTactic (← `(tactic| circuit_proof_start [$lemmas,*]))
  evalTactic (← `(tactic| try first | simp_all | grind))
  evalTactic (← `(tactic| done))
