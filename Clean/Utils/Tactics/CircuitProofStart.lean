import Lean
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableSimp

namespace ProvenZK

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
      let names := [`offset, `env, `input_var, `input, `h_input, `h_asm, `h_holds]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      evalTactic (← `(tactic| provable_simp))
      evalTactic (← `(tactic| simp only [circuit_norm] at *))
      return
    else if isCompleteness then
      -- This is a Completeness proof, unfold it and introduce all parameters with names
      evalTactic (← `(tactic| unfold Completeness))
      -- Introduce parameters one by one
      let names1 := [`offset, `env, `input_var, `henv, `input, `h_input, `h_asm]
      for name in names1 do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      -- Use rintro for the remaining parameters
      evalTactic (← `(tactic| provable_simp))
      evalTactic (← `(tactic| simp only [circuit_norm] at *))
      return

    -- Otherwise, continue with the original logic for parametrized theorems
    let goalType' ← whnf goalType

    match goalType' with
    | .forallE _ _ body _ =>
      -- Look ahead to see if this is the last intro before the implication
      let body' ← whnf body
      match body' with
      | .forallE _ _ _ _ =>
        -- More foralls to go, just intro
        evalTactic (← `(tactic| intro))
        circuitProofStartCore
      | _ =>
        -- Check if this is an implication (non-dependent forall)
        if !body.hasLooseBVars then
          -- This is an implication, check if the premise is what we're looking for
          let premise' ← whnf goalType'.bindingDomain!
          match premise' with
          | .app (.app (.const ``ConstraintsHold.Soundness _) _) _ =>
            -- This is the h_holds parameter in soundness
            evalTactic (← `(tactic| intro h_holds))
            -- Now apply provable_struct_simp and unfold
            evalTactic (← `(tactic| provable_simp))
            try (evalTactic (← `(tactic| simp only [circuit_norm] at *))) catch _ => pure ()
            return
          | .app (.app (.app (.const ``Environment.UsesLocalWitnessesCompleteness _) _) _) _ =>
            -- This is the henv parameter in completeness
            evalTactic (← `(tactic| intro henv))
            -- Continue with the remaining intros for completeness
            evalTactic (← `(tactic| rintro input h_input h_normalized))
            evalTactic (← `(tactic| provable_simp))
            try (evalTactic (← `(tactic| simp only [circuit_norm] at *))) catch _ => pure ()
            return
          | _ =>
            -- Regular implication, just intro
            evalTactic (← `(tactic| intro))
            circuitProofStartCore
        else
          -- Not an implication, just intro
          evalTactic (← `(tactic| intro))
          circuitProofStartCore
    | _ =>
      -- No more foralls, we're done
      evalTactic (← `(tactic| provable_simp))
      try (evalTactic (← `(tactic| simp only [circuit_norm] at *))) catch _ => pure ()

/--
  Try to unfold local definitions by looking them up in the context
-/
def tryUnfoldLocalDefs (names : List Name) : TacticM Unit := do
  withMainContext do
    for name in names do
      -- Try both the simple name and with current namespace
      let candidates := [name, (← getCurrNamespace) ++ name]
      for candidate in candidates do
        try
          -- Check if this constant exists and is a definition
          let info ← getConstInfo candidate
          match info with
          | .defnInfo _ =>
            -- It's a definition, try to unfold it
            let ident := mkIdent candidate
            try (evalTactic (← `(tactic| simp only [$ident:ident] at *))) catch _ => pure ()
          | _ => pure ()
        catch _ => pure ()

/--
  Standard tactic for starting soundness and completeness proofs.

  This tactic:
  1. Automatically introduces all parameters until reaching the proof obligations
  2. Applies provable_simp to decompose structs/pairs and simplify eval
  3. Unfolds circuit definitions using circuit_norm
  4. Unfolds local Assumptions and Spec definitions

  For soundness proofs, it introduces:
  - Any theorem parameters (like offset)
  - offset (offset parameter)
  - env (environment)
  - input_var (variable)
  - input (value)
  - h_input (eval env input_var = input)
  - h_normalized (Assumptions input)
  - h_holds (ConstraintsHold.Soundness ...)

  For completeness proofs, it introduces:
  - Any theorem parameters
  - offset (offset parameter)
  - env (environment)
  - input_var (variable)
  - henv (UsesLocalWitnessesCompleteness ...)
  - input (value)
  - h_input (eval env input_var = input)
  - h_normalized (Assumptions input)

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
  -- Then apply additional unfolding and simplification
  -- Unfold the circuit definition and common definitions
  try (evalTactic (← `(tactic| dsimp only [ElaboratedCircuit.main, Circuit.bind_def, Circuit.output, main] at *))) catch _ => pure ()
  -- Try to unfold Assumptions and Spec as local definitions
  tryUnfoldLocalDefs [`Assumptions, `Spec]
  -- Also try with delta reduction which is more aggressive
  try (evalTactic (← `(tactic| delta Assumptions Spec))) catch _ => pure ()
  -- Unfold the elaborated circuit definition
  try (evalTactic (← `(tactic| unfold elaborated at *))) catch _ => pure ()

end ProvenZK
