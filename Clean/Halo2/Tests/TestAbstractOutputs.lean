import Clean.Halo2.Tactics.AbstractOutputs
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: `abstract_outputs` — the occurrence-inventory matrix

One test per syntactic guise a subcircuit-call output takes in a proof state (the Phase-1
inventory catalogued from `Add`/`MulComplete`/`Chain`/`Mul`). Each test drives a real proof state
into the guise, runs `abstract_outputs`, and then **consumes the opaque local** — a step that only
typechecks if the output was actually abstracted to that local (guard-style: a lingering concrete
output would make the local reference or the `h_gen_out_*` equation ill-typed / absent).

Guises (see `AbstractOutputs.lean`'s module doc for the full table):
1. `(child.call …).output self` (call form, region `RegionCircuit.output` / layouter
   `Circuit.output`)
2. `child.output … self` (output form)
3. output as a field of a later call's input record
4. nested output-in-output (chained calls)
5. `eval env <output>` whole
6. projections of the output (`.x`, `.1`, …)

The engine-cooperation reuse path (re-running after `subcircuit_rw`) is exercised in
`MulComplete.lean`'s migrated completeness proof, the real-load acceptance.
-/

namespace Zcash.Circuits.Ecc.TestAbstractOutputs

open Halo2

/-! ## Guise 1 + 5: call-form output under `eval`, region level

A bare-context lemma with the child's output in call form inside `eval`. After `abstract_outputs`
the goal is `(eval env x_gen_out_0).Valid` and `h_gen_out_0 : <output> = x_gen_out_0` is in
context; `subcircuit_rw at h` + the local close it. -/
example (config : WitnessPoint.Config) (self : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Var (Unconstrained Point) Fp)
    (h : RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        ((WitnessPoint.point.call config 0 input).output self)).Valid := by
  subcircuit_rw at h
  abstract_outputs
  -- goal AND `h`'s conclusion are now `… (eval env x_gen_out_0) …` (the output opaque everywhere);
  -- `h trivial trivial` closes `(eval env x_gen_out_0).Valid`.
  exact h trivial trivial

/-! ## Guise 2 + 5: output form under `eval`, region level

Same, but the output already in output form (`WitnessPoint.point.output …`). -/
example (config : WitnessPoint.Config) (self : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Var (Unconstrained Point) Fp)
    (h : RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (WitnessPoint.point.output config 0 input self)).Valid := by
  subcircuit_rw at h
  abstract_outputs
  exact h trivial trivial

/-! ## Guise 1 vs 2 unification, layouter level (`Circuit.output`)

Call form and output form of the SAME output collapse to one local. -/
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Var (Unconstrained Point) Fp) :
    eval (⟨place, env⟩ : Placed Environment Fp)
        (((WitnessPoint.point.toFormal "wp").call config input).output i₀)
      = eval (⟨place, env⟩ : Placed Environment Fp)
        ((WitnessPoint.point.toFormal "wp").output config input i₀) := by
  abstract_outputs
  -- LHS (call form) and RHS (output form) both became `eval env x_gen_out_0`.
  rfl

/-! ## Guise 6: projection of the output

The output projected (`.x`). After abstraction the projection reads the opaque local
(`x_gen_out_0.x`); both call form and output form collapse to `x_gen_out_0.x`. -/
example (config : WitnessPoint.Config) (self : RegionIndex) (input : Var (Unconstrained Point) Fp) :
    ((WitnessPoint.point.call config 0 input).output self).x
      = (WitnessPoint.point.output config 0 input self).x := by
  abstract_outputs
  rfl

/-! ## Guise 3 + 4: chained calls (second input embeds the first output), nested output-in-output

Two chained region children (`passthrough` from `TestSubcircuitRw`): the second call's input IS the
first's output. `abstract_outputs` abstracts the inner (first) output first (innermost-first), so
the second call's chunk input becomes the opaque local; then the outer (second) output. The two
`h_gen_out_i` equations show the nested structure resolved. -/
def passthrough : FormalRegionCircuit Fp Unit Unit Point Point where
  configure := fun _ => pure ()
  synthesize _ _ input := pure input
  elaborated := {
    synthesisSummary := fun _ _ _ _ => {} }
  Spec input output _ := input.Valid → output.Valid
  ProverAssumptions input _ _ := input.Valid
  ProverSpec input output _ _ := output = input
  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA _hc
    simp only [circuit_norm] at h_output
    intro hv; rw [← h_output, h_input]; exact hv
  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output _hwit _hE _hA _hpa
    simp only [circuit_norm] at h_input h_output ⊢
    rw [← h_output, h_input]

/-- The nested output-in-output goal shape: the outer call's input embeds the inner call's output.
`abstract_outputs` yields `x_gen_out_0` (inner) and `x_gen_out_1` (outer), with
`h_gen_out_1`'s LHS input already the opaque `x_gen_out_0` — the guise-4 resolution. -/
example (config : Unit) (self : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (input : Var Point Fp) :
    eval (⟨place, env⟩ : Placed Environment Fp)
        ((passthrough.call config 0
          ((passthrough.call config 0 input).output self)).output self)
      = eval (⟨place, env⟩ : Placed Environment Fp)
        (passthrough.output config 0
          (passthrough.output config 0 input self) self) := by
  abstract_outputs
  -- LHS collapsed to `eval env x_gen_out_1`; RHS likewise. The inner output (in both the LHS input
  -- and RHS input) is `x_gen_out_0`, so `h_gen_out_1 : passthrough.output … x_gen_out_0 … = x_gen_out_1`.
  rfl

/-! ## Guise 8: raw composed output (`Bind.bind`-bodied `RegionCircuit.output`)

A parent's OWN composed do-block output — not a child bundle output, so no child `Spec` exists for
it — in the unfolded-bind spelling (the shape Mul's overflow-chunk input carries after the
completeness goal peel unfolds `mainRegion`). Abstracted WHOLE to one opaque local: the child calls
inside sit under the bind-continuation lambdas (loose bvars), unreachable-but-irrelevant inside the
local. The `show` only typechecks if the raw output was actually abstracted. A FOLDED spelling
(`(someDef cfg inp).output i₀`) is gated out — the def name is already the abstraction. -/
example (config : Unit) (self : RegionIndex) (place : RegionIndex → ℕ) (env : Environment Fp)
    (input : Var Point Fp) :
    eval (⟨place, env⟩ : Placed Environment Fp)
        ((passthrough.call config 0 input >>= fun mid =>
          passthrough.call config 0 mid).output self)
      = eval (⟨place, env⟩ : Placed Environment Fp)
        ((passthrough.call config 0 input >>= fun mid =>
          passthrough.call config 0 mid).output self) := by
  abstract_outputs
  show eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0
      = eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0
  rfl

end Zcash.Circuits.Ecc.TestAbstractOutputs
