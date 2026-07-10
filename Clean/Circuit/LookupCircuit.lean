import Clean.Circuit.Subcircuit
import Clean.Circuit.Foundations

/--
A `LookupCircuit` is a circuit that can be used to instantiate a lookup table.

It adds one additional requirement to `FormalCircuit`, which guarantees that an honest prover can actually
instantiate an environment which uses the circuit's witness generators.

Besides that, a `name` is required, to identify the table created from this circuit.
-/
-- `computableWitnesses` is now inherited from `FormalCircuitBase`, so a `LookupCircuit` adds no
-- new field beyond `FormalCircuit` — it stays a distinct type for the lookup-table API below.
structure LookupCircuit (F : Type) [FiniteField F] (α β : TypeMap) [ProvableType α] [ProvableType β]
    extends circuit : FormalCircuit F α β

namespace LookupCircuit
variable {F : Type} [FiniteField F] {α β : TypeMap} [ProvableType α] [ProvableType β]

-- the inherited `ElaboratedCircuit` instance doesn't fire through the nested `extends`, so re-expose it
instance (circuit : LookupCircuit F α β) : ElaboratedCircuit F α β circuit.main :=
  circuit.elaborated

def proverEnvironment (circuit : LookupCircuit F α β)
    (input : α F) (hint : ProverHint F) : ProverEnvironment F :=
  circuit.main (const input) |>.proverEnvironment hint

theorem proverEnvironment_usesLocalWitnesses (circuit : LookupCircuit F α β)
    (input : α F) (hint : ProverHint F) :
    (circuit.proverEnvironment input hint).UsesLocalWitnesses 0 ((circuit.main (const input)).operations 0) := by
  apply Circuit.proverEnvironment_usesLocalWitnesses
  intro env env'
  -- the input is a constant, so it agrees between any two environments
  have h_const : eval env (const input) = eval env' (const input) := by
    simp only [ProvableType.eval_const_prover]
  exact (circuit.computableWitnesses' h_const).1

def constantOutput (circuit : LookupCircuit F α β) (input : α F) (hint : ProverHint F) : β F :=
  circuit.output (const input) 0 |> eval (circuit.proverEnvironment input hint)

def toTable (circuit : LookupCircuit F α β) (hint : ProverHint F) : Table F (ProvablePair α β) where
  name := circuit.name

  -- for `(input, output)` to be contained in the lookup table defined by a circuit, means that:
  Contains := fun _ (input, output) =>
    -- there exists an environment, such that
    ∃ n env,
    -- the circuit constraints hold
    Operations.ConstraintsHold env (circuit.main (const input) |>.operations n)
    ∧ Operations.FullGuarantees env (circuit.main (const input) |>.operations n)
    -- and the output matches
    ∧ output = eval env (circuit.output (const input) n)

  Soundness := fun _ (input, output) => circuit.Assumptions input → circuit.Spec input output
  Completeness := fun _ (input, output) => circuit.Assumptions input ∧ output = circuit.constantOutput input hint

  imply_soundness := by
    intro _ (input, output) ⟨n, env, h_holds, h_guarantees, h_output⟩ h_assumptions
    simp only [h_output]
    exact (circuit.original_soundness n env (const input) input ProvableType.eval_const
      h_assumptions h_holds h_guarantees).1

  implied_by_completeness := by
    intro _ (input, output) ⟨h_assumptions, h_output⟩
    use 0, circuit.proverEnvironment input hint
    simp only [h_output, LookupCircuit.constantOutput, circuit_norm,and_true]
    set env := circuit.proverEnvironment input hint
    exact circuit.original_completeness 0 env (const input) input ProvableType.eval_const_prover
      h_assumptions (circuit.proverEnvironment_usesLocalWitnesses input hint)

-- we create another `FormalCircuit` that wraps a lookup into the table defined by the input circuit
-- this gives `circuit.lookup input` _exactly_ the same interface as `circuit input`.

@[circuit_norm]
def lookupCircuit (circuit : LookupCircuit F α β) (hint : ProverHint F) :
    FormalCircuit F α β where
  main (input : Var α F) := do
    -- we witness the output for the given input, and look up the pair in the table
    let output ← witnessNative fun env => circuit.constantOutput (eval env input) hint

    lookup (circuit.toTable hint) (input, output)
    return output

  Assumptions := circuit.Assumptions
  Spec := circuit.Spec

  soundness := by
    intro n env input_var input h_input h_assumptions h_holds
    simp_all only [circuit_norm, toTable]

  completeness := by
    intro n env input_var h_env input h_input h_assumptions
    simp only [circuit_norm, toTable] at *
    simp only [h_input] at h_env ⊢
    use h_assumptions

  computableWitnesses := by
    intro n input env env'
    refine ⟨?_, ?_⟩
    · -- forAll: the sole witness is the native output value; the lookup adds no witness/subcircuit
      simp only [circuit_norm, Witgen.WitgenIR.eval_nativeValue]
      intro h_input _
      simp only [h_input]
    · -- output: the freshly-witnessed output var only reads offsets `[n, n+size β)`,
      -- so environment agreement below `n + localLength` gives equality
      intro _ h_agrees
      simp only [circuit_norm] at h_agrees ⊢
      rw [ProvableType.eval_varFromOffset, ProvableType.eval_varFromOffset]
      congr 1
      ext i hi
      simp only [Vector.getElem_mapRange]
      exact h_agrees.1 (n + i) (by omega)

@[circuit_norm]
def lookup (circuit : LookupCircuit F α β) (hint : ProverHint F) (input : Var α F) : Circuit F (Var β F) :=
  lookupCircuit circuit hint input
end LookupCircuit
