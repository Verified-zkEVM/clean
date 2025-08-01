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
    let isSoundness := headConst? == some ``Soundness
    let isCompleteness := headConst? == some ``Completeness

    if isSoundness then
      evalTactic (← `(tactic| unfold Soundness))
      let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      return
    else if isCompleteness then
      evalTactic (← `(tactic| unfold Completeness))
      let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      return
    else
      -- Goal is neither Soundness nor Completeness
      throwError "circuitProofStartCore can only be used on direct Soundness or Completeness goals"

/--
  Standard tactic for starting soundness and completeness proofs.

  This tactic:
  1. Automatically introduces all parameters for `Soundness` or `Completeness` goals
  2. Unfolds `main`, `Assumptions`, and `Spec` definitions
  3. Normalizes the goal state using circuit_norm
  4. Applies provable_struct_simp to decompose structs and decompose eval that mention struct components
  5. Additionally simplifies h_holds henv and the goal with circuit_norm and h_input

  **Limitation**: This tactic only works on direct `Soundness` or `Completeness` goals.
  It will fail with an error if the goal type is neither `Soundness` nor `Completeness`.

  **Optional argument**: You can provide additional lemmas for simplification by using square brackets:
  `circuit_proof_start [lemma1, lemma2, ...]`. These lemmas will be used alongside `circuit_norm`
  in all simplification steps.

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
  
  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_assumptions):ident $(mkIdent `h_input):ident ⊢))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_holds):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_env):ident))) catch _ => pure ()

-- core version only, for experimentation with variants of this tactic
elab "circuit_proof_start_core" : tactic => do
  circuitProofStartCore
