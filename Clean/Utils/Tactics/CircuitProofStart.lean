import Lean
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableSimp

open Lean Elab Tactic Meta
open Circuit

/--
  Apply intro until we've introduced all the standard parameters for
  soundness or completeness proofs, then apply additional simplifications
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
      let names := [`i₀, `env, `input_var, `henv, `input, `h_input, `h_assumptions]
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
  2. Applies provable_simp to decompose structs and decompose eval that mention struct components
  3. Unfolds local Assumptions and Spec definitions
  4. Normalized the goal state using circuit_norm

  **Limitation**: This tactic only works on direct `Soundness` or `Completeness` goals.
  It will fail with an error if the goal type is neither `Soundness` nor `Completeness`.

  Example usage:
  ```lean
  theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start
    -- The assumptions in Soundness are introduced. All provable structs are decomposed when their components are mentioned

  theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) Assumptions (Spec offset) := by
    circuit_proof_start
    -- The assumptions in Completeness are introduced. All provable structs are decomposed when their components are mentioned
  ```
-/
elab "circuit_proof_start" : tactic => do
  -- First run the core logic which handles intro and unfolding
  circuitProofStartCore
  -- Try to unfold Assumptions and Spec as local definitions
  try (evalTactic (← `(tactic| unfold $(mkIdent `Assumptions):ident at *))) catch _ => pure ()
  try (evalTactic (← `(tactic| unfold $(mkIdent `Spec):ident at *))) catch _ => pure ()
  try (evalTactic (← `(tactic| provable_struct_simp))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm] at *))) catch _ => pure ()
