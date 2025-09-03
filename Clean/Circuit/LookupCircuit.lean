import Clean.Circuit.Subcircuit
import Clean.Circuit.Foundations
import Clean.Circuit.PropertyLookup

/--
A `LookupCircuit` is a circuit that can be used to instantiate a lookup table.

It adds one additional requirement to `FormalCircuit`, which guarantees that an honest prover can actually
instantiate an environment which uses the circuit's witness generators.

Besides that, a `name` is required, to identify the table created from this circuit.
-/
structure LookupCircuit (F : Type) [Field F] {sentences : PropertySet F} (order : SentenceOrder sentences)
    (α β : TypeMap) [ProvableType α] [ProvableType β]
    extends circuit : FormalCircuit F sentences order α β where
  name : String
  computableWitnesses : circuit.ComputableWitnesses

namespace LookupCircuit
variable {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {α β : TypeMap} [ProvableType α] [ProvableType β]

def proverEnvironment (circuit : LookupCircuit F order α β) (input : α F) : Environment F :=
  circuit.main (const input) |>.proverEnvironment

theorem proverEnvironment_usesLocalWitnesses (circuit : LookupCircuit F order α β) (input : α F) (yields : YieldContext sentences) :
    (circuit.proverEnvironment input).UsesLocalWitnesses yields 0 ((circuit.main (const input)).operations 0) := by
  apply Circuit.proverEnvironment_usesLocalWitnesses
  apply circuit.compose_computableWitnesses
  simp [Environment.OnlyAccessedBelow, ProvableType.eval_const, circuit.computableWitnesses]

def constantOutput (circuit : LookupCircuit F order α β) (input : α F) : β F :=
  circuit.output (const input) 0 |> eval (circuit.proverEnvironment input)

def toTable (circuit : LookupCircuit F order α β) (yields : YieldContext sentences) : Table F (ProvablePair α β) where
  name := circuit.name

  -- for `(input, output)` to be contained in the lookup table defined by a circuit, means that:
  Contains := fun (input, output) =>
    -- there exists an environment, such that
    ∃ n env,
    -- the circuit constraints hold
    Circuit.ConstraintsHold env yields Set.univ (circuit.main (const input) |>.operations n)
    -- and the output matches
    ∧ output = eval env (circuit.output (const input) n)

  Soundness := fun (input, output) => circuit.Assumptions input → circuit.Spec Set.univ input output
  Completeness := fun (input, output) => circuit.Assumptions input ∧ output = circuit.constantOutput input

  imply_soundness := by
    intro (input, output) ⟨n, env, h_holds, h_output⟩ h_assumptions
    simp only [h_output]
    exact circuit.original_soundness n env yields Set.univ (const input) input ProvableType.eval_const h_assumptions h_holds

  implied_by_completeness := by
    intro (input, output) ⟨h_assumptions, h_output⟩
    use 0, circuit.proverEnvironment input
    simp only [h_output, LookupCircuit.constantOutput, and_true]
    set env := circuit.proverEnvironment input
    apply circuit.original_completeness 0 env yields (const input) input ProvableType.eval_const h_assumptions
    exact circuit.proverEnvironment_usesLocalWitnesses input yields

-- we create another `FormalCircuit` that wraps a lookup into the table defined by the input circuit
-- this gives `circuit.lookup input` _exactly_ the same interface as `circuit input`.

@[circuit_norm]
def lookupCircuit (circuit : LookupCircuit F order α β) (yields : YieldContext sentences) : FormalCircuit F sentences order α β where
  main (input : Var α F) := do
    -- we witness the output for the given input, and look up the pair in the table
    let output ← witness fun env => circuit.constantOutput (eval env input)

    lookup (circuit.toTable yields) (input, output)
    return output

  localLength n := size β
  output _ n := varFromOffset β n

  Assumptions := circuit.Assumptions
  Spec checked := circuit.Spec checked

  soundness := by
    intro n env yields' checked input_var input h_input h_assumptions h_holds
    simp_all only [circuit_norm, toTable]
    -- Use the monotonicity property from the underlying circuit
    apply circuit.spec_monotonic
    · exact Set.subset_univ _
    · exact h_holds

  completeness := by
    intro n env yields' input_var h_env input h_input h_assumptions
    simp_all only [circuit_norm, toTable]
    rw [ProvableType.ext_iff]
    intro i hi
    rw [←h_env ⟨ i, hi ⟩, ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  
  spec_monotonic := circuit.spec_monotonic

@[circuit_norm]
def lookup (circuit : LookupCircuit F order α β) (yields : YieldContext sentences) (input : Var α F) : Circuit sentences (Var β F) :=
  lookupCircuit circuit yields input
end LookupCircuit
