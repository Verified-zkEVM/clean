import Lean
import Clean.Circuit.Formal
import Clean.Utils.Tactics.ProvableStructSimp

open Lean Elab Tactic Meta
open Circuit

/-- Whether an output projection contains a literal, rather than named, circuit body. -/
private def isInlineCircuitOutput (e : Expr) : Bool :=
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``ElaboratedCircuit.output then
    (args[args.size - 4]?.map (·.isLambda)).getD false
  else if e.getAppFn.isConstOf ``FormalCircuitBase.output then
    match args[args.size - 3]? with
    | some circuit =>
      circuit.getAppFn.isConstOf ``FormalCircuitBase.mk &&
        (circuit.getAppArgs[7]?.map (·.isLambda)).getD false
    | none => false
  else false

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
  `GeneralFormalCircuit.Soundness`, `GeneralFormalCircuit.Completeness`,
  `GeneralFormalCircuit.WithHint.Soundness`, `GeneralFormalCircuit.WithHint.Completeness`.

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
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `input_var):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm] at $(mkIdent `h_input):ident))) catch _ => pure ()

  -- try to unfold main, Assumptions and Spec as local definitions
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Assumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Spec):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `ProverAssumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `ProverSpec):ident] at *))
  evalTactic (← `(tactic| try dsimp +instances only [$(mkIdent `elaborated):ident] at *)) -- sometimes `main` is hidden behind `elaborated`
  evalTactic (← `(tactic| try dsimp +instances only [$(mkIdent `main):ident] at *))

  -- needed because struct-var destructuring would time out on `(ElaboratedCircuit.WithData ...).output` like terms
  try (evalTactic (← `(tactic| dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output]))) catch _ => pure ()

  -- collapse the `field`/`id` type synonym everywhere, so that hypotheses and goals
  -- are stated at the underlying field type with canonical instances.
  -- Since Lean 4.29, automation (simp matching, grind e-matching/ring) no longer
  -- identifies `field F`-instance applications with canonical `F` ones up to defeq.
  try (evalTactic (← `(tactic| dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))) catch _ => pure ()

  -- simplify structs / eval first
  try (evalTactic (← `(tactic| provable_struct_simp))) catch _ => pure ()

  -- Additional simplification for common patterns in soundness/completeness proofs
  -- Convert optional terms to simpLemma syntax
  let extraLemmas := match terms with
    | some terms => terms.getElems.map fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    | none => #[]
  let lemmasArray ← extraLemmas.mapM id

  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_assumptions):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_holds):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_env):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*]))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp +instances only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_spec):ident))) catch _ => pure ()

  -- A child unfolded above may leave behind the output projection of its inline body.
  if (← getGoals).isEmpty then return
  let hasInlineOutput ← withMainContext do
    let some hHolds := (← getLCtx).findFromUserName? `h_holds | pure false
    pure ((← instantiateMVars hHolds.type).find? isInlineCircuitOutput).isSome
  if hasInlineOutput then
    try (evalTactic (← `(tactic| simp only [FormalCircuitBase.output,
      ElaboratedCircuit.output] at $(mkIdent `h_holds):ident))) catch _ => pure ()
    try (evalTactic (← `(tactic| simp only [circuit_norm]
      at $(mkIdent `h_holds):ident))) catch _ => pure ()

  -- collapse the field/id synonym again: the simp passes above can reintroduce
  -- `field F`-typed statements (e.g. from unfolded Specs)
  try (evalTactic (← `(tactic| dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))) catch _ => pure ()

-- core version only, for experimentation with variants of this tactic
elab "circuit_proof_start_core" : tactic => do
  circuitProofStartCore

-- version of circuit_proof_start that attempts to close the goal with `simp_all`
syntax "circuit_proof_all" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_all $[[$terms:term,*]]?) => do
  let lemmas := terms.getD (.mk #[])
  evalTactic (← `(tactic| circuit_proof_start [$lemmas,*]))
  evalTactic (← `(tactic| try simp_all))
  evalTactic (← `(tactic| try grind))
  evalTactic (← `(tactic| done))
