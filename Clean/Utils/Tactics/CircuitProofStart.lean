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

    -- Check if this is a Soundness or Completeness proof
    let isSoundness := headConst? == some ``Soundness
    let isCompleteness := headConst? == some ``Completeness

    if isSoundness then
      -- This is a Soundness proof, unfold it and introduce all parameters with names
      evalTactic (← `(tactic| unfold Soundness))
      -- Introduce parameters with explicit names using introN
      let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      return
    else if isCompleteness then
      -- This is a Completeness proof, unfold it and introduce all parameters with names
      evalTactic (← `(tactic| unfold Completeness))
      -- Introduce parameters one by one
      let names := [`i₀, `env, `input_var, `henv, `input, `h_input, `h_assumptions]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      return

/--
  Standard tactic for starting soundness and completeness proofs.

  This tactic:
  1. Automatically introduces all parameters for `Soundness` or `Completeness` goals
  2. Applies provable_simp to decompose structs/pairs and simplify eval
  3. Unfolds circuit definitions using circuit_norm
  4. Unfolds local Assumptions and Spec definitions

  For soundness proofs, it introduces:
  - Any theorem parameters
  - i₀ (offset in the environment)
  - env (environment)
  - input_var (variable)
  - input (value)
  - h_input (eval env input_var = input)
  - h_assumptions (Assumptions input)
  - h_holds (ConstraintsHold.Soundness ...)

  For completeness proofs, it introduces:
  - Any theorem parameters
  - i₀ (offset in the environment)
  - env (environment)
  - input_var (variable)
  - henv (UsesLocalWitnessesCompleteness ...)
  - input (value)
  - h_input (eval env input_var = input)
  - h_assumptions (Assumptions input)

  Example usage:
  ```lean
  theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start
    -- Goal is now unfolded with all struct equalities split

  theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) Assumptions (Spec offset) := by
    circuit_proof_start
    -- offset is introduced first, then standard soundness parameters
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
