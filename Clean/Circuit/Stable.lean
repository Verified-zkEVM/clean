import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops

namespace Circuit


/-!
# Stable Circuits

This module defines circuits with stable outputs and constraints - circuits whose behavior depends only
on the input values, not on the specific variable representation. This property is captured by four
stability fields:
1. `output_stable`: The output depends only on the input value
2. `constraints_soundness_stable`: Constraint soundness is unchanged when using const inputs
3. `constraints_completeness_stable`: Constraint completeness is unchanged when using const inputs
4. `uses_local_witnesses_stable`: UsesLocalWitnessesCompleteness is unchanged when using const inputs

This allows reasoning about `Input F` values directly rather than `Var Input F`.
-/

section
variable {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/--
`StableElaboratedCircuit` extends `ElaboratedCircuit` with stability properties ensuring
that the circuit's behavior depends only on input values, not variable representations.
-/
class StableElaboratedCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output]
    extends ElaboratedCircuit F Input Output where
  /-- The output is stable: it depends only on the input value -/
  output_stable : ∀ (env : Environment F) input offset,
    eval env (output input offset) = eval env (output (const (eval env input)) offset)

  /-- Constraint soundness is stable under const substitution -/
  constraints_soundness_stable : ∀ (env : Environment F) input_var offset,
    ConstraintsHold.Soundness env (main input_var |>.operations offset) ↔
    ConstraintsHold.Soundness env (main (const (eval env input_var)) |>.operations offset)

  /-- Constraint completeness is stable under const substitution -/
  constraints_completeness_stable : ∀ (env : Environment F) input_var offset,
    ConstraintsHold.Completeness env (main input_var |>.operations offset) ↔
    ConstraintsHold.Completeness env (main (const (eval env input_var)) |>.operations offset)

  /-- UsesLocalWitnessesCompleteness is stable under const substitution -/
  uses_local_witnesses_stable : ∀ (env : Environment F) input_var offset,
    env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) ↔
    env.UsesLocalWitnessesCompleteness offset (main (const (eval env input_var)) |>.operations offset)

/--
Soundness for stable circuits that works directly with input values rather than variables.
-/
@[circuit_norm]
def StableSoundness (F : Type) [Field F] (circuit : StableElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) (Spec : Input F → Output F → Prop) :=
  ∀ offset : ℕ, ∀ env,
  ∀ input : Input F,
  Assumptions input →
  ConstraintsHold.Soundness env (circuit.main (const input) |>.operations offset) →
  let output := eval env (circuit.output (const input) offset)
  Spec input output

/--
Completeness for stable circuits that works directly with input values rather than variables.
-/
@[circuit_norm]
def StableCompleteness (F : Type) [Field F] (circuit : StableElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) :=
  ∀ offset : ℕ, ∀ env,
  ∀ input : Input F,
  env.UsesLocalWitnessesCompleteness offset (circuit.main (const input) |>.operations offset) →
  Assumptions input →
  ConstraintsHold.Completeness env (circuit.main (const input) |>.operations offset)

section Theorems

/-- StableSoundness implies regular Soundness -/
theorem stableSoundness_implies_soundness
    (circuit : StableElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop) (Spec : Input F → Output F → Prop)
    (h : StableSoundness F circuit Assumptions Spec) :
    Soundness F circuit.toElaboratedCircuit Assumptions Spec := by
  intro offset env input_var input h_eval h_assumptions h_constraints output

  simp only [StableSoundness] at h
  specialize h offset env input h_assumptions

  simp only [output]
  rw [circuit.output_stable, h_eval]
  apply h
  rw [circuit.constraints_soundness_stable, h_eval] at h_constraints
  assumption

/-- StableCompleteness implies regular Completeness -/
theorem stableCompleteness_implies_completeness
    (circuit : StableElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop)
    (h : StableCompleteness F circuit Assumptions) :
    Completeness F circuit.toElaboratedCircuit Assumptions := by
  intro offset env input_var h_uses_local input h_eval h_assumptions

  -- Use stability to convert from const input case
  -- Note: circuit.toElaboratedCircuit.main = circuit.main by construction
  have h_main_eq : circuit.toElaboratedCircuit.main = circuit.main := rfl

  rw [circuit.constraints_completeness_stable, h_eval]

  simp only [StableCompleteness] at h
  apply h
  · rw [circuit.uses_local_witnesses_stable, h_eval] at h_uses_local
    apply h_uses_local
  · assumption

end Theorems

/--
`StableFormalCircuit` extends `StableElaboratedCircuit` with soundness and completeness proofs,
using the stable versions that work directly with input values.
-/
structure StableFormalCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output]
    extends elaborated : StableElaboratedCircuit F Input Output where
  Assumptions (_ : Input F) : Prop := True
  Spec : Input F → Output F → Prop
  soundness : StableSoundness F elaborated Assumptions Spec
  completeness : StableCompleteness F elaborated Assumptions

/--
`StableDeterministicFormalCircuit` extends `StableFormalCircuit` with uniqueness,
similar to `DeterministicFormalCircuit` but with stability.
-/
structure StableDeterministicFormalCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output]
    extends circuit : StableFormalCircuit F Input Output where
  uniqueness : ∀ (input : Input F) (out1 out2 : Output F),
    circuit.Assumptions input → circuit.Spec input out1 → circuit.Spec input out2 → out1 = out2

/--
`StableGeneralFormalCircuit` is the stable version of `GeneralFormalCircuit`,
allowing separate assumptions for soundness and completeness while maintaining stability.
-/
structure StableGeneralFormalCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output]
    extends elaborated : StableElaboratedCircuit F Input Output where
  Assumptions : Input F → Prop
  Spec : Input F → Output F → Prop
  soundness : ∀ offset : ℕ, ∀ env, ∀ input : Input F,
    ConstraintsHold.Soundness env (elaborated.main (const input) |>.operations offset) →
    let output := eval env (elaborated.output (const input) offset)
    Spec input output
  completeness : ∀ offset : ℕ, ∀ env, ∀ input : Input F,
    env.UsesLocalWitnessesCompleteness offset (elaborated.main (const input) |>.operations offset) →
    Assumptions input →
    ConstraintsHold.Completeness env (elaborated.main (const input) |>.operations offset)

/--
`StableFormalAssertion` is the stable version of `FormalAssertion` for assertion-like circuits
that maintain stability (though the output is always unit).
-/
structure StableFormalAssertion (F : Type) (Input : TypeMap) [Field F] [ProvableType Input]
    extends elaborated : StableElaboratedCircuit F Input unit where
  Assumptions : Input F → Prop
  Spec : Input F → Prop
  soundness : ∀ offset : ℕ, ∀ env, ∀ input : Input F,
    Assumptions input →
    ConstraintsHold.Soundness env (elaborated.main (const input) |>.operations offset) →
    Spec input
  completeness : ∀ offset : ℕ, ∀ env, ∀ input : Input F,
    env.UsesLocalWitnessesCompleteness offset (elaborated.main (const input) |>.operations offset) →
    Assumptions input → Spec input →
    ConstraintsHold.Completeness env (elaborated.main (const input) |>.operations offset)

  localLength _ := 0
  output _ _ := ()

section Conversions

/-- Extract the underlying `ElaboratedCircuit` from a `StableElaboratedCircuit` -/
def StableElaboratedCircuit.asElaboratedCircuit (circuit : StableElaboratedCircuit F Input Output) :
    ElaboratedCircuit F Input Output where
  main := circuit.main
  localLength := circuit.localLength
  localLength_eq := circuit.localLength_eq
  output := circuit.output
  output_eq := circuit.output_eq
  subcircuitsConsistent := circuit.subcircuitsConsistent

/-- Convert a `StableFormalCircuit` to a `FormalCircuit` -/
def StableFormalCircuit.toFormalCircuit (circuit : StableFormalCircuit F Input Output) :
    FormalCircuit F Input Output where
  elaborated := circuit.elaborated.asElaboratedCircuit
  Assumptions := circuit.Assumptions
  Spec := circuit.Spec
  soundness := stableSoundness_implies_soundness circuit.elaborated circuit.Assumptions circuit.Spec circuit.soundness
  completeness := stableCompleteness_implies_completeness circuit.elaborated circuit.Assumptions circuit.completeness

/-- Convert a `StableDeterministicFormalCircuit` to a `DeterministicFormalCircuit` -/
def StableDeterministicFormalCircuit.toDeterministicFormalCircuit
    (circuit : StableDeterministicFormalCircuit F Input Output) :
    DeterministicFormalCircuit F Input Output where
  circuit := circuit.circuit.toFormalCircuit
  uniqueness := circuit.uniqueness

/-- Convert a `StableGeneralFormalCircuit` to a `GeneralFormalCircuit` -/
def StableGeneralFormalCircuit.toGeneralFormalCircuit
    (circuit : StableGeneralFormalCircuit F Input Output) :
    GeneralFormalCircuit F Input Output where
  elaborated := circuit.elaborated.asElaboratedCircuit
  Assumptions := circuit.Assumptions
  Spec := circuit.Spec
  soundness := by
    intro offset env input_var input h_eval h_constraints output
    simp only [output]
    rw [circuit.output_stable, h_eval]
    apply circuit.soundness
    rw [circuit.constraints_soundness_stable, h_eval] at h_constraints
    apply h_constraints
  completeness := by
    intro offset env input_var h_uses_local input h_eval h_assumptions
    rw [circuit.elaborated.constraints_completeness_stable, h_eval]
    apply circuit.completeness
    · rw [circuit.elaborated.uses_local_witnesses_stable, h_eval] at h_uses_local
      exact h_uses_local
    · exact h_assumptions

/-- Convert a `StableFormalAssertion` to a `FormalAssertion` -/
def StableFormalAssertion.toFormalAssertion (circuit : StableFormalAssertion F Input) :
    FormalAssertion F Input where
  elaborated := circuit.elaborated.asElaboratedCircuit
  Assumptions := circuit.Assumptions
  Spec := circuit.Spec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_constraints
    apply circuit.soundness
    · exact h_assumptions
    · rw [circuit.elaborated.constraints_soundness_stable, h_eval] at h_constraints
      exact h_constraints
  completeness := by
    intro offset env input_var h_uses_local input h_eval h_assumptions h_spec
    rw [circuit.elaborated.constraints_completeness_stable, h_eval]
    apply circuit.completeness
    · rw [circuit.elaborated.uses_local_witnesses_stable, h_eval] at h_uses_local
      exact h_uses_local
    · exact h_assumptions
    · exact h_spec

end Conversions

section Subcircuits

/-- Convert a `StableFormalCircuit` to a `Subcircuit` -/
def StableFormalCircuit.toSubcircuit (circuit : StableFormalCircuit F Input Output)
    (n : ℕ) (input_var : Var Input F) : Subcircuit F n :=
  circuit.toFormalCircuit.toSubcircuit n input_var

/-- Convert a `StableGeneralFormalCircuit` to a `Subcircuit` -/
def StableGeneralFormalCircuit.toSubcircuit (circuit : StableGeneralFormalCircuit F Input Output)
    (n : ℕ) (input_var : Var Input F) : Subcircuit F n :=
  circuit.toGeneralFormalCircuit.toSubcircuit n input_var

/-- Convert a `StableFormalAssertion` to a `Subcircuit` -/
def StableFormalAssertion.toSubcircuit (circuit : StableFormalAssertion F Input)
    (n : ℕ) (input_var : Var Input F) : Subcircuit F n :=
  circuit.toFormalAssertion.toSubcircuit n input_var

end Subcircuits

section StabilityLemmas

/-- Key lemma: evaluating a const expression gives back the original value -/
theorem const_eval {α : TypeMap} [ProvableType α] (env : Environment F) (x : α F) :
    eval env (const x : Var α F) = x := by
  simp only [const, eval]
  conv_rhs => rw [← ProvableType.fromElements_toElements x]
  congr 1
  simp only [fromVars, Vector.map_map]
  ext i _
  simp only [Vector.getElem_map, Expression.const, Expression.eval]
  rfl

/-- Corollary: components of const also evaluate correctly -/
theorem toVars_const_eval {α : TypeMap} [ProvableType α] (env : Environment F) (x : Var α F) (i : Fin (size α)) :
    Expression.eval env ((toVars (const (eval env x)))[i]) = Expression.eval env ((toVars x)[i]) := by
  simp only [toVars, toElements]
  simp only [const, fromVars, Vector.getElem_map]
  simp only [Expression.const, Expression.eval, eval]
  rw [ProvableType.fromElements_toElements]
  simp only [Vector.getElem_map]
  rfl

/--
If all individual operations satisfy a stability property (that their constraints are equivalent
when expressions are replaced by their evaluated constants), then ConstraintsHold.Soundness is stable.
-/
theorem ConstraintsHold.Soundness_stable {ops : List (Operation F)} (env : Environment F)
    (h_stable : ∀ op ∈ ops, match op with
      | .witness _ _ => True
      | .assert e => ∃ e', Expression.eval env e' = Expression.eval env e ∧
          ConstraintsHold.Soundness env [.assert e] ↔ ConstraintsHold.Soundness env [.assert e']
      | .lookup { table, entry } => ∃ entry', entry'.map (Expression.eval env) = entry.map (Expression.eval env) ∧
          ConstraintsHold.Soundness env [.lookup { table, entry }] ↔
          ConstraintsHold.Soundness env [.lookup { table, entry := entry' }]
      | .subcircuit s => True  -- Subcircuits handle their own stability
    ) :
    ∀ ops', (∀ i, ∃ op' ∈ ops', match ops[i]?, ops'[i]? with
      | some (Operation.assert e), some (Operation.assert e') => Expression.eval env e' = Expression.eval env e
      | some (Operation.lookup l), some (Operation.lookup l') =>
          l'.entry.map (Expression.eval env) = l.entry.map (Expression.eval env) ∧ l'.table = l.table
      | some op, some op' => op = op'
      | _, _ => True
    ) → ops.length = ops'.length →
    ConstraintsHold.Soundness env ops ↔ ConstraintsHold.Soundness env ops' := by
  sorry

/-- Special case: ConstraintsHold.Soundness is stable for assert operations when expressions evaluate to the same value -/
theorem ConstraintsHold.Soundness_stable_assert (env : Environment F) (e e' : Expression F)
    (h : e.eval env = e'.eval env) :
    ConstraintsHold.Soundness env [.assert e] ↔ ConstraintsHold.Soundness env [.assert e'] := by
  simp only [ConstraintsHold.Soundness]
  simp only [h]

/-- ConstraintsHold.Completeness has the same stability property -/
theorem ConstraintsHold.Completeness_stable_assert (env : Environment F) (e e' : Expression F)
    (h : e.eval env = e'.eval env) :
    ConstraintsHold.Completeness env [.assert e] ↔ ConstraintsHold.Completeness env [.assert e'] := by
  simp only [ConstraintsHold.Completeness]
  simp only [h]

/-- Stability for forEach with a body that produces stable constraints -/
theorem ConstraintsHold.Soundness_forEach_stable {α : Type} [Inhabited α] {n : ℕ} {xs ys : Vector α n}
    {body : α → Circuit F Unit} [h_const : Circuit.ConstantLength body]
    (env : Environment F) (offset : ℕ)
    (h_body_stable : ∀ x y offset',
      ConstraintsHold.Soundness env ((body x).operations offset') ↔
      ConstraintsHold.Soundness env ((body y).operations offset')) :
    ConstraintsHold.Soundness env ((forEach xs body h_const).operations offset) ↔
    ConstraintsHold.Soundness env ((forEach ys body h_const).operations offset) := by
  sorry

/-- Special case for forEach with assertZero when expressions evaluate to the same values -/
theorem ConstraintsHold.Soundness_forEach_assertZero_stable {n : ℕ} {xs ys : Vector (Expression F) n}
    (env : Environment F) (offset : ℕ)
    (h_eval : ∀ (i : Fin n), Expression.eval env xs[i] = Expression.eval env ys[i]) :
    ConstraintsHold.Soundness env ((forEach xs assertZero).operations offset) ↔
    ConstraintsHold.Soundness env ((forEach ys assertZero).operations offset) := by
  -- We can't use Soundness_forEach_stable directly because Expression F doesn't have Inhabited
  -- Instead, we'll prove this directly
  simp only [forEach, Circuit.bind_def, Circuit.pure_def]
  simp only [Circuit.operations]
  -- The proof would show that the constraints are equivalent element by element
  sorry

end StabilityLemmas

end

end Circuit
