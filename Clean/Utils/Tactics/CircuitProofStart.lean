import Lean
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructSimp

open Lean Elab Tactic Meta
open Circuit

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
                       headConst? == some ``GeneralFormalCircuit.Soundness
    let isCompleteness := headConst? == some ``Completeness ||
                          headConst? == some ``FormalAssertion.Completeness ||
                          headConst? == some ``GeneralFormalCircuit.Completeness

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
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_holds]
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
      | _ => pure ()
      return
    else
      -- Goal is not a supported Soundness or Completeness type
      throwError "circuitProofStartCore can only be used on Soundness, Completeness, FormalAssertion.Soundness, FormalAssertion.Completeness, GeneralFormalCircuit.Soundness, or GeneralFormalCircuit.Completeness goals"

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

  -- try to unfold main, Assumptions and Spec as local definitions
  try (evalTactic (← `(tactic| unfold $(mkIdent `Assumptions):ident at *))) catch _ => pure ()
  try (evalTactic (← `(tactic| unfold $(mkIdent `Spec):ident at *))) catch _ => pure ()
  try (evalTactic (← `(tactic| unfold $(mkIdent `elaborated):ident at *))) catch _ => pure () -- sometimes `main` is hidden behind `elaborated`
  try (evalTactic (← `(tactic| unfold $(mkIdent `main):ident at *))) catch _ => pure ()
  -- simplify structs / eval first
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
  evalTactic (← `(tactic| simp_all))
  evalTactic (← `(tactic| done))
