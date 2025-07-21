import Lean
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructSimp

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
    
    -- Check if we're done by looking for ConstraintsHold.Soundness or UsesLocalWitnessesCompleteness
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
            evalTactic (← `(tactic| provable_struct_simp))
            evalTactic (← `(tactic| simp only [circuit_norm] at *))
            return
          | .app (.app (.app (.const ``Environment.UsesLocalWitnessesCompleteness _) _) _) _ =>
            -- This is the henv parameter in completeness
            evalTactic (← `(tactic| intro henv))
            -- Continue with the remaining intros for completeness
            evalTactic (← `(tactic| rintro input h_input h_normalized))
            evalTactic (← `(tactic| provable_struct_simp))
            evalTactic (← `(tactic| simp only [circuit_norm] at *))
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
      evalTactic (← `(tactic| provable_struct_simp))
      evalTactic (← `(tactic| simp only [circuit_norm] at *))

/--
  Standard tactic for starting soundness and completeness proofs.
  
  This tactic:
  1. Automatically introduces all parameters until reaching the proof obligations
  2. Applies provable_struct_simp to decompose structs and simplify eval
  3. Unfolds circuit definitions using circuit_norm
  
  For soundness proofs, it introduces:
  - Any theorem parameters (like offset)
  - i0 (offset)
  - env (environment)
  - input_var (variable)
  - input (value)
  - h_input (eval env input_var = input)
  - h_normalized (Assumptions input)
  - h_holds (ConstraintsHold.Soundness ...)
  
  For completeness proofs, it introduces:
  - Any theorem parameters
  - i0 (offset)
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
  circuitProofStartCore
  -- Additional unfolding that's commonly needed
  try (evalTactic (← `(tactic| dsimp only [ElaboratedCircuit.main, Circuit.bind_def, Circuit.output, main, elaborated, Assumptions, Spec] at *))) catch _ => pure ()
  -- Try to obtain struct fields from hypotheses if they exist
  try (evalTactic (← `(tactic| obtain ⟨_, _⟩ := h_normalized))) catch _ => pure ()
  try (evalTactic (← `(tactic| obtain ⟨_, _⟩ := h_input))) catch _ => pure ()

end ProvenZK