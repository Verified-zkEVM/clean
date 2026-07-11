import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: layouter-level subcircuit composition (the C1 parity mechanism)

The layouter mirror of `TestSubcircuit`. A layouter-level parent `FormalCircuit` composes
two children and is proven sound + complete via the layouter absorption iffs:

- a **native layouter child** (`witnessPointL`), a `FormalCircuit` written directly over the
  `Circuit` monad (its body is an `assignRegion` around `WitnessPoint.point`'s region body);
- a **region child lifted via `toFormal`** (`WitnessPoint.point.toFormal`), the single
  bridge that makes every region-level gadget consumable at layouter level.

Both children are consumed, both directions, by firing the concrete-`α` layouter iffs
`FormalCircuit.subcircuit_constraints_iff_soundness'/…_completeness'` *as part of* `simp`.
`circuit_norm` decomposes the parent's layouter binds (`operations_bind` → `++` and the
layouter `constraints_region`/`extendsWitnesses_region` computation lemmas), isolates each
folded `(child.call …).operations i₀` chunk, normalizes its element type to the concrete
`Point (AssignedCell Fp)`, and the iff fires on it to expose the child's contract.

The final section checks the bare-`place`/`env` variants (`…_bare`) fire under `simp only`
in a bare-place/env lemma context — the exact scenario the `Placed`-projection-keyed iffs
miss inside loop lemmas (the `Mul.lean` headline finding).
-/

namespace Halo2.Ironwood.Ecc.TestLayouterSubcircuit

open Halo2 Halo2.Ironwood.Ecc

/-! ## The native layouter child

A `FormalCircuit` whose body creates its own region (via `assignRegion`) and runs the
witness-point region body inside it. Same config/IO/contract as `WitnessPoint.point`, lifted
to the layouter level by hand — the "native" counterpart to the `toFormal` bridge. -/
def witnessPointL :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point :=
  WitnessPoint.point.toFormal "witness_point (layouter)"

/-! ## The region child, lifted via `toFormal` (same underlying gadget, second instance) -/
def witnessPointR :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point :=
  WitnessPoint.point.toFormal "witness_point (via toFormal)"

/-! ## The layouter parent composing both children -/

/-- Layouter parent: run the native layouter child, then the `toFormal`-lifted region child,
return the second output. Both children share the config/IO; the parent's `Spec` is the
second child's (`output.Valid`). -/
def parent :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config input := do
    let _ ← witnessPointL.call config input
    witnessPointR.call config input
  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output _hE _hA hc
    -- circuit_norm peels the parent's layouter binds and isolates the two folded call chunks;
    -- the concrete-`α` layouter iffs fire on each in the same simp to expose their contracts.
    simp only [circuit_norm, FormalCircuit.subcircuit_constraints_iff_soundness'] at hc h_output
    obtain ⟨⟨_, _hspecL⟩, ⟨_, hspecR⟩⟩ := hc
    have hvalid := hspecR trivial trivial
    -- the parent output (via `circuit_norm` on `h_output`) is the second child's output
    rw [← h_output]; exact hvalid

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm, FormalCircuit.subcircuit_constraints_iff_completeness'] at hwit ⊢
    simp only [circuit_norm] at h_input
    obtain ⟨hwitL, hwitR⟩ := hwit
    refine ⟨?_, ?_⟩
    · exact Or.inr ⟨hwitL, trivial, trivial, h_input ▸ hpa⟩
    · exact Or.inr ⟨hwitR, trivial, trivial, h_input ▸ hpa⟩

/-! ## Bare-`place`/`env` variants fire under `simp only`

A lemma phrased over bare `place : RegionIndex → ℕ` / `env : Environment Fp` (no `Placed`
record in sight) — the shape a loop lemma has. The `Placed`-projection-keyed primed iffs do
NOT fire here; the `_bare` variants do. -/

-- Region bare iff: firing must expose the child's `Spec` (here `Point.Valid` of the output),
-- so the conclusion genuinely depends on the rewrite having happened.
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (FExpr Fp))
    (h : RegionOperations.Constraints place i₀ env
        ((WitnessPoint.point.call config 0 input).operations i₀)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (WitnessPoint.point.output config 0 input i₀)).Valid := by
  simp only [FormalRegionCircuit.subcircuit_constraints_iff_soundness_bare] at h
  exact h.2 trivial trivial

-- Layouter bare iff: same, at the layouter level.
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (FExpr Fp))
    (h : Halo2.Constraints place env ((witnessPointR.call config input).operations i₀) i₀) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (witnessPointR.output config input i₀)).Valid := by
  simp only [FormalCircuit.subcircuit_constraints_iff_soundness_bare] at h
  exact h.2 trivial trivial

end Halo2.Ironwood.Ecc.TestLayouterSubcircuit
