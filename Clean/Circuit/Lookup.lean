import Clean.Circuit.SubCircuit
import Clean.Circuit.Foundations
variable {F : Type} [Field F] {α β : TypeMap} [ProvableType α] [ProvableType β]

def FormalCircuit.toTable (circuit : FormalCircuit F α β) (name : String)
  (henv : (input: α F) → (env : Environment F) ×' env.uses_local_witnesses 0 (circuit.main (const input) |>.operations 0)) :
    TypedTable F (ProvablePair α β) where
  name := name

  valid x := circuit.assumptions x.1
  contains x := circuit.spec x.1 x.2

  map x _ :=
    let (input, _) := x
    let env := henv input
    let output_var := circuit.output (const input) 0
    let output : β F := eval env.1 output_var
    ⟨input, output⟩

  mapContains x hx := by
    let (input, _) := x
    simp only
    set env := (henv input).1 with env_def
    apply circuit.original_soundness 0 env (const input) input (ProvableType.eval_const ..) hx
    apply circuit.original_completeness 0 env (const input) input (ProvableType.eval_const ..) hx
    exact (henv input).2
