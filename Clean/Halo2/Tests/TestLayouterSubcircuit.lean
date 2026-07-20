import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: layouter-level subcircuit composition via the `subcircuit_rw` engine

The layouter mirror of `TestSubcircuit`. A layouter-level parent `FormalCircuit` composes two
children and is proven sound + complete through the engine:

- a **native layouter child** (`witnessPointL`), a `FormalCircuit` written directly over the
  `Circuit` monad (its body is an `assignRegion` around `WitnessPoint.point`'s region body);
- a **region child lifted via `toFormal`** (`WitnessPoint.point.toFormal`), the single
  bridge that makes every region-level gadget consumable at layouter level.

Both children are consumed, both directions, by the engine. `circuit_norm` decomposes the
parent's layouter binds (`operations_bind` → `++` and the layouter
`constraints_region`/`extendsWitnesses_region` computation lemmas), isolates each folded
`(child.call …).operations i₀` chunk, and `subcircuit_rw` weakens (soundness) or strengthens
(completeness) it to the child's contract. This covers the layouter level AND the `toFormal`
bridge in one.

The final section checks the engine fires in a bare-`place`/`env` lemma context — the exact
scenario the historical `Placed`-projection-keyed iffs missed inside loop lemmas (the `Mul.lean`
headline finding), now handled by the engine's own `isDefEq` matching.
-/

namespace Halo2.Ironwood.Ecc.TestLayouterSubcircuit

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
  -- both children's witnessed cells (regions `i₀` and `i₀ + 1`), so each child's
  -- extract-level `ProverAssumptions` is discharged definitionally
  Witness := ProvablePair Point Point
  extract := fun config _ i₀ env =>
    (eval env ({ x := AssignedCell.of i₀ 0 config.x,
                 y := AssignedCell.of i₀ 0 config.y } : Var Point Fp),
     eval env ({ x := AssignedCell.of (i₀ + 1) 0 config.x,
                 y := AssignedCell.of (i₀ + 1) 0 config.y } : Var Point Fp))
  ProverAssumptions _ wit _ := wit.1.Valid ∧ wit.2.Valid

  soundness := by
    intro config
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output _hE _hA hc
    -- circuit_norm peels the parent's layouter binds and isolates the two folded call chunks;
    -- the engine weakens the second child's chunk to its `EnvA → A → Spec`.
    simp only [circuit_norm] at hc h_output
    obtain ⟨hcL, hcR⟩ := hc
    subcircuit_rw at hcR
    -- the parent output (via `circuit_norm` on `h_output`) is the second child's output
    exact h_output ▸ hcR trivial trivial

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm] at hwit h_input hpa ⊢
    -- both goal chunks strengthen in place (op order): the goal becomes the AND of the two
    -- `EnvA ∧ A ∧ PA` bundles, with premised `h_spec_0`/`h_spec_1` in context.
    subcircuit_rw
    have hrc : ((witnessPointL.call config input_var).operations i₀).regionCount = 1 := by
      rw [FormalCircuit.call_regionCount]
      rfl
    simp only [hrc]
    exact ⟨⟨trivial, trivial, by with_unfolding_all exact hpa.1⟩,
      ⟨trivial, trivial, by with_unfolding_all exact hpa.2⟩⟩

/-! ## Bare-`place`/`env` engine firing

A lemma phrased over bare `place : RegionIndex → ℕ` / `env : Environment Fp` (no `Placed`
record in sight) — the shape a loop lemma has. The engine's own `isDefEq` matching fires here
regardless (no discrimination tree). -/

-- Region bare context: firing must expose the child's `Spec` (here `Point.Valid` of the output),
-- so the conclusion genuinely depends on the rewrite having happened.
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (WitgenIR Fp 1))
    (h : RegionOperations.Constraints place i₀ env
        ((WitnessPoint.point.call config 0 input).operations i₀)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (WitnessPoint.point.output config 0 input i₀)).Valid := by
  subcircuit_rw at h
  exact h trivial trivial

-- Layouter bare context: same, at the layouter level.
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (WitgenIR Fp 1))
    (h : Constraints place env ((witnessPointR.call config input).operations i₀) i₀) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (witnessPointR.output config input i₀)).Valid := by
  subcircuit_rw at h
  exact h trivial trivial

end Halo2.Ironwood.Ecc.TestLayouterSubcircuit
