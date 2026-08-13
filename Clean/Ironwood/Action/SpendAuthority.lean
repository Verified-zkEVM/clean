import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Halo2.CircuitTypeDeriving

/-!
# Orchard spend authority (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, the `Spend authority` block in `Circuit::synthesize`
(lines 629-644): `alpha_commitment = [alpha] SpendAuthG` (full-width fixed-base mul,
discarding the returned scalar decomposition), then `rk = alpha_commitment + ak_P`. The
final public-instance constraints on `rk.x`/`rk.y` belong to the enclosing action
synthesis.

## Knowledge soundness

The phase-1 donor (`Clean/Orchard/Action/SpendAuthority.lean`) could only state
`∃ alpha, rk = [alpha] SpendAuthG + ak_P` — vacuous, since `SpendAuthG` generates the
group. Here `alpha` is the `FullWidth` child's extraction data (the scalar its witnessed
window cells encode), so the `Spec` is the real knowledge-soundness statement: the
extractor reads `alpha` off any satisfying assignment and `rk = [alpha] SpendAuthG + ak_P`
holds at that `alpha`, with no existential.
-/

namespace Zcash.Circuits.Action.SpendAuthority

open Halo2
open Ecc.MulFixed (FixedBase)

/-- The input of the spend-authority block: the randomizer's nat-valued reading program
`alpha` (a prover hint — Rust `Value<pallas::Scalar>`; the `FullWidth` child derives its
85 window witnesses from it, and the scalar is the extraction data) and the
already-assigned authorizing key point `ak_P`. -/
structure Input (F : Type) where
  alpha : UnconstrainedNat F
  akP : Point F
deriving CircuitType

@[keygen_norm]
def keygenRequirements (G : FixedBase) : KeygenRequirements Fp
    (Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) (Var Input Fp) where
  configLawful cfg :=
    (Ecc.MulFixed.FullWidth.circuit G).Configured cfg.1 ×
      Ecc.Add.addFormal.Configured cfg.2
  gates _ configured :=
    configured.1.gates ++ configured.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.lookups
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.permutationColumns ++
      ([cfg.1.superConfig.addConfig.xQR,
        cfg.1.superConfig.addConfig.yQR] : List AnyColumn)
  inputCells _ _ input :=
    [input.akP.x.cell, input.akP.y.cell]

def synthesisSummary
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    FloorPlanner.SynthesisSummary :=
  (Ecc.MulFixed.FullWidth.circuitSynthesisSummary cfg.1).combine
    (FloorPlanner.SynthesisSummary.ofRegion
      (Ecc.Add.synthesisSummary cfg.2 0))

/-- Rust `Circuit::synthesize`'s spend-authority block: `[alpha] SpendAuthG` (the
`FullWidth` bundle) plus `ak_P`. `Spec` is knowledge soundness at the extracted
randomizer: `rk = [alpha] SpendAuthG + ak_P` for the `alpha` read off the witnessed
window cells — no existential. -/
def circuit (G : FixedBase) : FormalCircuit Fp
    (Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    Input Point where
  name := "spend authority"
  configure := pure

  synthesize | (fcfg, ecfg), input => do
    let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G).call fcfg input.alpha
    let rk ← Ecc.Add.addFormal.call ecfg
      { p := alphaCommitment, q := input.akP }
    pure rk

  elaborated :=
    { keygenRequirements := keygenRequirements G
      registered := by keygen_registration
      output cfg _ i :=
        { x := .of (i + 2) 1 cfg.2.xQR,
          y := .of (i + 2) 1 cfg.2.yQR }
      regionCount _ := 3
      synthesisSummary cfg _ _ := synthesisSummary cfg
      synthesisSummary_eq := by
        intro cfg input region
        simp only [synthesisSummary, circuit_norm, synthesis_summary_norm]
      output_eq := by
        intro cfg input i
        simp only [Circuit.output_bind, Circuit.output_pure,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', circuit_norm,
          Ecc.Add.addFormal_output_cells] }

  EnvAssumptions := fun (fcfg, _) env =>
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  -- `ak_P` is already assigned as a valid Pallas point before the spend-authority block
  Assumptions input := input.akP.Valid

  Witness F := Vector F 85 × Fq
  extract := fun (fcfg, _) _ i₀ env =>
    Ecc.MulFixed.FullWidth.fwExtract fcfg i₀ env

  Spec input output wit :=
    output = wit.2 • G + input.akP

  soundness := by
    circuit_proof_start2 [Ecc.MulFixed.FullWidth.circuit, Ecc.Add.addFormal]
    have hAl := alphaCommitment_spec env_assumptions
    have hAddS := rk_spec ⟨by rw [hAl]; exact G.smul_valid _, assumptions⟩
    rw [Ecc.Add.addFormal_output_cells] at rk_eq
    have hrk : ({ x := output_x, y := output_y } : Point Fp) =
        eval (⟨place, env⟩ : Placed Environment Fp) rk := by
      rw [← rk_eq]
      simp only [Point.eval_eq, circuit_norm]
      simp_all
    rw [hrk, hAddS.2, hAl]
  completeness := by
    circuit_proof_start2 [Ecc.MulFixed.FullWidth.circuit, Ecc.Add.addFormal]
    have hAl := alphaCommitment_spec env_assumptions
    exact ⟨env_assumptions, by rw [hAl]; exact G.smul_valid _, assumptions⟩

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq (G : FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    (circuit G).elaborated.synthesisSummary config input region =
      synthesisSummary config := rfl

derive_contract_bridges circuit (G : FixedBase) := circuit G

end Zcash.Circuits.Action.SpendAuthority
