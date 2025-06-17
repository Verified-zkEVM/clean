import Clean.Circuit.SubCircuit
import Clean.Circuit.Foundations
variable {F : Type} [Field F] {α β : TypeMap} [ProvableType α] [ProvableType β]

def FormalCircuit.constantOutput (circuit : FormalCircuit F α β) (proverEnv : (input: α F) → Environment F) (input : α F) (offset := 0) : β F :=
  circuit.output (const input) offset |> eval (proverEnv input)

def FormalCircuit.toTable (circuit : FormalCircuit F α β) (name : String)
  (proverEnv : (input: α F) → Environment F)
  (henv : ∀ input, (proverEnv input).uses_local_witnesses 0 (circuit.main (const input) |>.operations 0)) :
    TypedTable F (ProvablePair α β) where
  name

  valid := fun (input, output) => circuit.assumptions input ∧ output = circuit.constantOutput proverEnv input
  contains := fun (input, output) => circuit.spec input output

  implies := by
    intro (input, output) ⟨h_assumptions, h_output⟩
    simp only [h_output, constantOutput]
    set env := proverEnv input with env_def
    apply circuit.original_soundness 0 env (const input) input ProvableType.eval_const h_assumptions
    apply circuit.original_completeness 0 env (const input) input ProvableType.eval_const h_assumptions
    exact henv input
