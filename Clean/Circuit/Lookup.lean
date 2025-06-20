import Clean.Circuit.SubCircuit
import Clean.Circuit.Foundations
variable {F : Type} [Field F] {α β : TypeMap} [ProvableType α] [ProvableType β]

def FormalCircuit.proverEnvironment (circuit : FormalCircuit F α β) (input : α F) : Environment F :=
  circuit.main (const input) |>.proverEnvironment

def FormalCircuit.computable_witnesses (circuit : FormalCircuit F α β) : Prop :=
    ∀ (input : α F), (circuit.main (const input)).computable_witnesses

theorem FormalCircuit.proverEnvironment_uses_local_witnesses (circuit : FormalCircuit F α β)
  (h_computable : circuit.computable_witnesses) (input : α F) :
    (circuit.proverEnvironment input).uses_local_witnesses 0 ((circuit.main (const input)).operations 0) :=
  Circuit.proverEnvironment_uses_local_witnesses _ _ (h_computable input)

def FormalCircuit.constantOutput (circuit : FormalCircuit F α β) (input : α F) : β F :=
  circuit.output (const input) 0 |> eval (circuit.proverEnvironment input)

def FormalCircuit.toTable (circuit : FormalCircuit F α β) (name : String) (h_computable : circuit.computable_witnesses) :
    TypedTable F (ProvablePair α β) where
  name

  contains := fun (input, output) => ∃ n env,
    -- the circuit constraints hold
    Circuit.constraints_hold env (circuit.main (const input) |>.operations n)
    -- the output matches
    ∧ output = eval env (circuit.output (const input) n)

  soundness := fun (input, output) => circuit.assumptions input → circuit.spec input output
  completeness := fun (input, output) => circuit.assumptions input ∧ output = circuit.constantOutput input

  imply_soundness := by
    intro (input, output) ⟨n, env, h_holds, h_output⟩ h_assumptions
    simp only [h_output]
    exact circuit.original_soundness n env (const input) input ProvableType.eval_const h_assumptions h_holds

  implied_by_completeness := by
    intro (input, output) ⟨h_assumptions, h_output⟩
    use 0, circuit.proverEnvironment input
    simp only [h_output, constantOutput, and_true]
    set env := circuit.proverEnvironment input
    apply circuit.original_completeness 0 env (const input) input ProvableType.eval_const h_assumptions
    exact circuit.proverEnvironment_uses_local_witnesses h_computable input
