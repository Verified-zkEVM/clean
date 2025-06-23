import Clean.Circuit.SubCircuit
import Clean.Circuit.Foundations

/--
A `LookupCircuit` is a circuit that can be used to instantiate a lookup table.

It adds one additional requirement to `FormalCircuit`, which guarantees that an honest prover can actually
instantiate an environment which uses the circuit's witness generators.

Besides that, a `name` is required, to identify the table created from this circuit.
-/
structure LookupCircuit (F : Type) [Field F] (α β : TypeMap) [ProvableType α] [ProvableType β]
    extends circuit : FormalCircuit F α β where
  name : String
  computableWitnesses : circuit.computableWitnesses

namespace LookupCircuit
variable {F : Type} [Field F] {α β : TypeMap} [ProvableType α] [ProvableType β]

def proverEnvironment (circuit : LookupCircuit F α β) (input : α F) : Environment F :=
  circuit.main (const input) |>.proverEnvironment

theorem proverEnvironment_uses_local_witnesses (circuit : LookupCircuit F α β) (input : α F) :
    (circuit.proverEnvironment input).uses_local_witnesses 0 ((circuit.main (const input)).operations 0) := by
  apply Circuit.proverEnvironment_uses_local_witnesses
  apply circuit.compose_computableWitnesses
  simp [Environment.onlyAccessedBelow, ProvableType.eval_const, circuit.computableWitnesses]

def constantOutput (circuit : LookupCircuit F α β) (input : α F) : β F :=
  circuit.output (const input) 0 |> eval (circuit.proverEnvironment input)

def toTable (circuit : LookupCircuit F α β) : Table F (ProvablePair α β) where
  name := circuit.name

  -- for `(input, output)` to be contained in the lookup table defined by a circuit, means that:
  contains := fun (input, output) =>
    -- there exists an environment, such that
    ∃ n env,
    -- the circuit constraints hold
    Circuit.constraints_hold env (circuit.main (const input) |>.operations n)
    -- and the output matches
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
    simp only [h_output, LookupCircuit.constantOutput, and_true]
    set env := circuit.proverEnvironment input
    apply circuit.original_completeness 0 env (const input) input ProvableType.eval_const h_assumptions
    exact circuit.proverEnvironment_uses_local_witnesses input

-- we create another `FormalCircuit` that wraps a lookup into the table defined by the input circuit
-- this gives `circuit.lookup input` _exactly_ the same interface as `subcircuit circuit input`.

@[circuit_norm]
def lookupCircuit (circuit : LookupCircuit F α β) : FormalCircuit F α β where
  main (input : Var α F) := do
    -- we witness the output for the given input, and look up the pair in the table
    let output ← ProvableType.witness fun env => circuit.constantOutput (eval env input)

    lookup circuit.toTable (input, output)
    return output

  local_length n := size β
  output _ n := var_from_offset β n

  assumptions := circuit.assumptions
  spec := circuit.spec

  soundness := by
    intro n env input_var input h_input h_assumptions h_holds
    simp_all only [circuit_norm, toTable]

  completeness := by
    intro n env input_var h_env input h_input h_assumptions
    simp_all only [circuit_norm, toTable]
    rw [ProvableType.ext_iff]
    intro i hi
    rw [←h_env ⟨ i, hi ⟩, ProvableType.eval_var_from_offset, ProvableType.to_elements_from_elements, Vector.getElem_mapRange]

@[circuit_norm]
def lookup (circuit : LookupCircuit F α β) (input : Var α F) : Circuit F (Var β F) :=
  subcircuit (lookupCircuit circuit) input
end LookupCircuit
