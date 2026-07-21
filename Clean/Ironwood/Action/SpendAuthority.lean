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

namespace Halo2.Ironwood.Action.SpendAuthority

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point Fq)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)

/-- The input of the spend-authority block: the randomizer's nat-valued reading program
`alpha` (a prover hint — Rust `Value<pallas::Scalar>`; the `FullWidth` child derives its
85 window witnesses from it, and the scalar is the extraction data) and the
already-assigned authorizing key point `ak_P`. -/
structure Input (F : Type) where
  alpha : UnconstrainedNat F
  akP : Point F
deriving CircuitType

/-- The region count of the spend-authority block: two regions for the full-width
fixed-base mul, one for the final complete addition. -/
private theorem spendAuthority_regionCount (G : FixedBase)
    (fcfg : Ecc.MulFixed.FullWidth.Config) (ecfg : Ecc.Add.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G).call fcfg input.alpha
        let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
          { p := alphaCommitment, q := input.akP }
        pure rk : Circuit Fp (Var Point Fp)).operations i)
      = 3 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.call_regionCount]
  rfl

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

  synthesize := fun (fcfg, ecfg) input => do
    let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G).call fcfg input.alpha
    let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
      { p := alphaCommitment, q := input.akP }
    pure rk

  elaborated := fun (fcfg, ecfg) =>
    { output := fun input i =>
        ((do
          let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G).call fcfg input.alpha
          let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
            { p := alphaCommitment, q := input.akP }
          pure rk : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 3
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (spendAuthority_regionCount G fcfg ecfg input i).symm }

  EnvAssumptions := fun (fcfg, _) env =>
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  -- `ak_P` is already assigned as a valid Pallas point before the spend-authority block
  Assumptions input := input.akP.Valid

  Witness := fun F => Vector F 85 × Fq
  extract := fun (fcfg, _) _ i₀ env =>
    Ecc.MulFixed.FullWidth.fwExtract fcfg i₀ env

  Spec input output wit :=
    output = (wit.2 • G : Point Fp) + input.akP

  ProverAssumptions _ _ _ := True

  soundness := by
    circuit_proof_start2 [
      Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_assumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_spec_eq, Ecc.MulFixed.FullWidth.circuit_extract_eq,
      Ecc.Add.toFormal_assumptions_eq, Ecc.Add.toFormal_spec_eq]
    -- ═══ USER half ═══
    have hAl := h_call_alphaCommitment hE
    have hAddS := h_call_rk trivial ⟨by rw [hAl]; exact G.smul_valid _, hA⟩
    simp_all
  completeness := by
    circuit_proof_start2 [
      Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_assumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_spec_eq, Ecc.MulFixed.FullWidth.circuit_extract_eq,
      Ecc.Add.toFormal_assumptions_eq, Ecc.Add.toFormal_spec_eq]
    -- ═══ USER half ═══
    have hAl := (h_spec_0 hE).1
    exact ⟨hE, trivial, ⟨by rw [hAl]; exact G.smul_valid _, hA⟩, trivial⟩

derive_contract_bridges circuit (G : FixedBase) := circuit G

end Halo2.Ironwood.Action.SpendAuthority
