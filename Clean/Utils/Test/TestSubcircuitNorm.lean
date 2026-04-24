import Clean.Utils.Tactics
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Boolean

/-!
# Tests for the `subcircuit_norm` tactic

This file tests the `subcircuit_norm` tactic, which performs automatic forward
reasoning on circuit proof hypotheses.

The `subcircuit_norm` tactic looks for hypotheses that match the premise of any
lemma tagged with `@[subcircuit_norm]`, and replaces them with the conclusion.

**Background**: The current circuit proof framework uses `Subcircuit.Spec` to
replace raw constraint hypotheses with high-level spec hypotheses. The
`subcircuit_norm` tactic demonstrates an alternative approach: instead of storing
`Spec` on `Subcircuit`, we tag forward-reasoning lemmas and apply them automatically.

This is the "experiment with metaprogramming" described in the issue.
-/

namespace TestSubcircuitNorm

open Circuit

variable {p : ℕ} [Fact p.Prime]

section BasicForwardReasoning

/--
Test that `subcircuit_norm` can apply the `FormalAssertion.toSubcircuit_spec_of_constraints`
lemma to replace a raw-constraint hypothesis with its Spec.

This shows the key capability: given
  `h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat`
`subcircuit_norm` derives the spec
  `h : (assertBool.toSubcircuit n x).Spec env`
which is `True → IsBool (eval env x)`, i.e., just `IsBool (eval env x)`.
-/
example (n : ℕ) (x_var : Expression (F p)) (env : Environment (F p))
    (h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x_var).ops.toFlat) :
    (assertBool.toSubcircuit n x_var).Spec env := by
  subcircuit_norm
  -- After subcircuit_norm: h has been replaced with
  --   h : (assertBool.toSubcircuit n x_var).Spec env
  -- which is what we need to prove
  exact h

/--
Test the full forward-reasoning chain from raw constraints to `IsBool`:
1. Start with flat constraints for `assertBool`
2. `subcircuit_norm` → `(assertBool.toSubcircuit n x).Spec env`
3. `circuit_norm` → `True → IsBool (eval env x)`
4. Simplify to get `IsBool (eval env x)`

This demonstrates how `subcircuit_norm` + `circuit_norm` together replace the
hypothesis with the high-level spec, which is what `ConstraintsHold.Soundness`
currently does automatically (via `s.Spec env`).
-/
example (n : ℕ) (x_var : Expression (F p)) (env : Environment (F p))
    (h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x_var).ops.toFlat) :
    IsBool (eval env x_var) := by
  subcircuit_norm
  -- h : (assertBool.toSubcircuit n x_var).Spec env
  simp only [circuit_norm] at h
  -- h : True → IsBool (eval env x_var)
  exact h trivial

end BasicForwardReasoning

section MultipleHypotheses

/--
Test that `subcircuit_norm` works when there are multiple raw-constraint hypotheses.
It should replace ALL of them, not just the first one.
-/
example (n m : ℕ) (x_var y_var : Expression (F p)) (env : Environment (F p))
    (hx : ConstraintsHoldFlat env (assertBool.toSubcircuit n x_var).ops.toFlat)
    (hy : ConstraintsHoldFlat env (assertBool.toSubcircuit m y_var).ops.toFlat) :
    (assertBool.toSubcircuit n x_var).Spec env ∧ (assertBool.toSubcircuit m y_var).Spec env := by
  subcircuit_norm
  -- Both hx and hy have been replaced with their Spec
  exact ⟨hx, hy⟩

end MultipleHypotheses

section FormalCircuitForwardReasoning

/--
Test that `subcircuit_norm` also works for `FormalCircuit` subcircuits.
For a `FormalCircuit`, the spec has the form `Assumptions → circuit.Spec`.
-/
example {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit (F p) Input Output)
    (n : ℕ) (input_var : Var Input (F p)) (env : Environment (F p))
    (h : ConstraintsHoldFlat env (circuit.toSubcircuit n input_var).ops.toFlat) :
    (circuit.toSubcircuit n input_var).Spec env := by
  subcircuit_norm
  exact h

end FormalCircuitForwardReasoning

section DemonstrationOfEquivalence

/--
Demonstration that the `subcircuit_norm` approach is equivalent to the current
`Subcircuit.Spec` approach.

The current framework uses `ConstraintsHold.Soundness` which automatically replaces
  `ConstraintsHoldFlat env s.ops.toFlat`
with
  `s.Spec env`
in soundness proof contexts.

This theorem shows that `subcircuit_norm` achieves the same result when starting from
raw constraint hypotheses — demonstrating that `Subcircuit.Spec` could in principle
be removed if `subcircuit_norm` were used in proofs instead.
-/
theorem subcircuit_norm_derives_same_as_spec
    (n : ℕ) (x_var : Expression (F p)) (env : Environment (F p))
    -- Simulating what ConstraintsHold.SoundnessRaw would give us
    (h_raw : ConstraintsHoldFlat env (assertBool.toSubcircuit n x_var).ops.toFlat) :
    -- We can derive the same thing as ConstraintsHold.Soundness currently provides:
    (assertBool.toSubcircuit n x_var).Spec env := by
  -- The subcircuit_norm tactic automatically applies the tagged forward lemma
  -- FormalAssertion.toSubcircuit_spec_of_constraints to h_raw
  subcircuit_norm
  exact h_raw

end DemonstrationOfEquivalence

end TestSubcircuitNorm
