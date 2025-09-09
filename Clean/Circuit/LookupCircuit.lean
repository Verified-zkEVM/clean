import Clean.Circuit.Subcircuit
import Clean.Circuit.Foundations
import Clean.Circuit.PropertyLookup

/--
A `LookupCircuit` is a circuit that can be used to instantiate a lookup table.

It adds one additional requirement to `FormalCircuit`, which guarantees that an honest prover can actually
instantiate an environment which uses the circuit's witness generators.

Besides that, a `name` is required, to identify the table created from this circuit.

At the moment `LookupCircuit` cannot depend on `use`/`yield` mechanism.
-/
structure LookupCircuit (F : Type) [Field F]
    (α β : TypeMap) [ProvableType α] [ProvableType β]
    extends circuit : FormalCircuit (emptyOrder F) α β where
  name : String
  computableWitnesses : circuit.ComputableWitnesses

namespace LookupCircuit
variable {F : Type} [Field F] {sentences : PropertySet F}
    {α β : TypeMap} [ProvableType α] [ProvableType β]

def proverEnvironment (circuit : LookupCircuit F α β) (input : α F) : Environment F :=
  circuit.main (const input) |>.proverEnvironment

omit [Field F] in
/--
Any YieldContext for emptyPropertySet has an empty yielded set, since there are no sentences to yield.
-/
lemma yieldContext_emptyPropertySet_empty (y : YieldContext (emptyPropertySet F)) :
    y = emptyYields F := by
  ext
  -- Show y.yielded = ∅
  simp only [emptyYields]
  constructor
  · rename_i x
    simp only [Sentence, emptyPropertySet] at x
    cases x
    rename_i found _
    simp at found
  · intro
    contradiction

/--
For circuits with empty property sets, proverYields equals emptyYields.
-/
lemma proverYields_eq_emptyYields {α : Type} (circuit : Circuit (emptyPropertySet F) α) (init : List F) :
    circuit.proverYields init = emptyYields F :=
  yieldContext_emptyPropertySet_empty _

theorem proverEnvironment_usesLocalWitnessesAndYields (circuit : LookupCircuit F α β) (input : α F) :
    (circuit.proverEnvironment input).UsesLocalWitnessesAndYields (emptyYields F) 0 ((circuit.main (const input)).operations 0) := by
  rw [← proverYields_eq_emptyYields]
  apply Circuit.proverEnvironment_usesLocalWitnessesAndYields
  apply circuit.compose_computableWitnesses
  simp [Environment.OnlyAccessedBelow, ProvableType.eval_const, circuit.computableWitnesses]

def constantOutput (circuit : LookupCircuit F α β) (input : α F) : β F :=
  circuit.output (const input) 0 |> eval (circuit.proverEnvironment input)

def toTable (circuit : LookupCircuit F α β) : Table F (ProvablePair α β) where
  name := circuit.name

  -- for `(input, output)` to be contained in the lookup table defined by a circuit, means that:
  Contains := fun (input, output) =>
    -- there exists an environment, such that
    ∃ n env,
    -- the circuit constraints hold
    Circuit.ConstraintsHold env (emptyYields F) (emptyChecked F) (circuit.main (const input) |>.operations n)
    -- and the output matches
    ∧ output = eval env (circuit.output (const input) n)

  Soundness := fun (input, output) => circuit.Assumptions input → circuit.Spec (emptyChecked F) input output
  Completeness := fun (input, output) => circuit.Assumptions input ∧ output = circuit.constantOutput input

  imply_soundness := by
    intro (input, output) ⟨n, env, h_holds, h_output⟩ h_assumptions
    simp only [h_output]
    exact circuit.original_soundness n env (emptyYields F) (emptyChecked F) (const input) input ProvableType.eval_const h_assumptions h_holds

  implied_by_completeness := by
    intro (input, output) ⟨h_assumptions, h_output⟩
    use 0, circuit.proverEnvironment input
    simp only [h_output, LookupCircuit.constantOutput, and_true]
    set env := circuit.proverEnvironment input
    apply circuit.original_completeness 0 env (emptyYields F) (emptyChecked F) (const input) input ProvableType.eval_const h_assumptions
    exact circuit.proverEnvironment_usesLocalWitnessesAndYields input

-- we create another `FormalCircuit` that wraps a lookup into the table defined by the input circuit
-- this gives `circuit.lookup input` _exactly_ the same interface as `circuit input`.

@[circuit_norm]
def lookupCircuit (circuit : LookupCircuit F α β) (order : SentenceOrder sentences) : FormalCircuit order α β where
  main (input : Var α F) := do
    -- we witness the output for the given input, and look up the pair in the table
    let output ← witness fun env => circuit.constantOutput (eval env input)

    lookup circuit.toTable (input, output)
    return output

  localLength n := size β
  output _ n := varFromOffset β n

  Assumptions := circuit.Assumptions
  Spec _ := circuit.Spec (emptyChecked F)

  soundness := by
    intro n env yields' checked input_var input h_input h_assumptions h_holds
    simp_all only [circuit_norm, toTable]

  completeness := by
    intro n env yields' input_var h_env input h_input h_assumptions
    simp_all only [circuit_norm, toTable]
    rw [ProvableType.ext_iff]
    intro i hi
    rw [←h_env ⟨ i, hi ⟩, ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]

@[circuit_norm]
def lookup (circuit : LookupCircuit F α β) (order : SentenceOrder sentences) (input : Var α F) : Circuit sentences (Var β F) :=
  lookupCircuit circuit order input
end LookupCircuit
