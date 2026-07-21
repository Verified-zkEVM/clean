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
    -- ═══ v2-manual FRAMEWORK prefix (atomic binds; to become one `circuit_proof_start2`) ═══
    -- (a) intro config + enter the value-landed iff form
    rintro ⟨fcfg, ecfg⟩
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output hE hA hC
    -- (b) definitional cleanup: iota-reduce the destructured-config matches everywhere,
    -- then land `h_output` on the raw do-block output via the instance's own `output_eq`
    -- law (reduce-once: the instance is the single place output spellings live)
    dsimp only [] at *
    simp only [ElaboratedCircuit.output_eq] at h_output
    -- (c) bind 1 [alphaCommitment ← (FullWidth.circuit G).call fcfg input_var.alpha]:
    --     split off the chunk, canonicalize the output spelling, then mint the atom
    --     BEFORE the continuation opens
    rw [Circuit.operations_bind, constraints_append] at hC
    rw [Circuit.output_bind] at h_output
    obtain ⟨h_call_fw, hC⟩ := hC
    simp only [FormalCircuit.output_call'] at hC h_output
    revert hC h_output
    generalize h_ac : (Ecc.MulFixed.FullWidth.circuit G).output fcfg input_var.alpha i₀
      = alphaCommitment
    intro hC h_output
    simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount] at hC h_output
    -- (d) bind 2 [rk ← (add.toFormal …).call ecfg {p := alphaCommitment, q := input_var.akP}]
    rw [Circuit.operations_bind, constraints_append] at hC
    rw [Circuit.output_bind] at h_output
    obtain ⟨h_call_add, hC⟩ := hC
    simp only [FormalCircuit.output_call'] at hC h_output
    revert hC h_output
    generalize h_rk : (Ecc.Add.add.toFormal "complete point addition").output ecfg
        { p := alphaCommitment, q := input_var.akP } (i₀ + 2) = rk
    intro hC h_output
    -- (e) terminal `pure rk`: the op list ends; `h_output` lands on the atom
    rw [Circuit.operations_pure, constraints_nil] at hC
    rw [Circuit.output_pure] at h_output
    clear hC
    -- (f) consume the child chunks: contracts over the atoms
    subcircuit_rw at h_call_fw
    subcircuit_rw at h_call_add
    -- (g) land values: destructure the input var AND value into component atoms; the
    -- literal-record simprocs then split `h_input` into per-component `eval env <var>`
    -- equations, and every eval stays WHOLE (cell spellings never materialize)
    obtain ⟨input_var_alpha, input_var_akP⟩ := input_var
    obtain ⟨input_alpha, input_akP⟩ := input
    simp only [circuit_norm] at h_input hA h_ac h_rk h_call_fw h_call_add ⊢
    obtain ⟨h_alpha, h_akP⟩ := h_input
    -- ═══ USER half ═══
    -- the full-width child: the commitment is the extracted scalar times `G`
    have hAl := h_call_fw hE trivial
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hAl
    -- the complete addition: `rk = alphaCommitment + ak_P` (both summands valid)
    have hAddS := h_call_add trivial (by
      rw [Ecc.Add.toFormal_assumptions_eq]
      exact ⟨by rw [hAl]; exact G.smul_valid _, by rw [h_akP]; exact hA⟩)
    rw [Ecc.Add.toFormal_spec_eq] at hAddS
    rw [← h_output, hAddS.2, hAl, h_akP]

  completeness := by
    -- ═══ v2-manual FRAMEWORK prefix (atomic binds; to become one `circuit_proof_start2`) ═══
    -- (a) intro config + enter the value-landed iff form
    rintro ⟨fcfg, ecfg⟩
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hW hE hA hPA
    obtain ⟨place, env⟩ := env
    -- (b) definitional cleanup + land `h_output` on the raw do-block output
    dsimp only [] at *
    simp only [ElaboratedCircuit.output_eq] at h_output
    -- (c) bind 1: split hW and the goal's constraints side, canonicalize, mint the atom
    rw [Circuit.operations_bind, extendsWitnesses_append] at hW
    rw [Circuit.operations_bind, constraints_append]
    rw [Circuit.output_bind] at h_output
    obtain ⟨hW_fw, hW⟩ := hW
    simp only [FormalCircuit.output_call'] at hW h_output ⊢
    revert hW h_output
    generalize h_ac : (Ecc.MulFixed.FullWidth.circuit G).output fcfg input_var.alpha i₀
      = alphaCommitment
    intro hW h_output
    simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount] at hW h_output ⊢
    -- (d) bind 2: same
    rw [Circuit.operations_bind, extendsWitnesses_append] at hW
    rw [Circuit.operations_bind, constraints_append]
    rw [Circuit.output_bind] at h_output
    obtain ⟨hW_add, hW⟩ := hW
    simp only [FormalCircuit.output_call'] at hW h_output ⊢
    revert hW h_output
    generalize h_rk : (Ecc.Add.add.toFormal "complete point addition").output ecfg
        { p := alphaCommitment, q := input_var.akP } (i₀ + 2) = rk
    intro hW h_output
    -- (e) terminal `pure rk`
    rw [Circuit.operations_pure, constraints_nil]
    rw [Circuit.output_pure] at h_output
    clear hW
    -- (f) strengthen the goal chunks + emit the children's completeness implications
    -- (`h_spec_k`, premised on the witness chunks in context)
    subcircuit_rw
    -- (g) land values on component atoms
    obtain ⟨input_var_alpha, input_var_akP⟩ := input_var
    obtain ⟨input_alpha, input_akP⟩ := input
    simp only [circuit_norm] at h_input hA h_ac h_rk hW_fw hW_add h_spec_0 h_spec_1 ⊢
    -- ═══ USER half ═══
    -- the full-width child's contract: the commitment is the extracted scalar times `G`
    have hAl := (h_spec_0 hE trivial trivial).1
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hAl
    refine ⟨⟨hE, trivial, trivial⟩, trivial, ?_, trivial⟩
    rw [Ecc.Add.toFormal_assumptions_eq]
    exact ⟨by rw [hAl]; exact G.smul_valid _, hA⟩

derive_contract_bridges circuit (G : FixedBase) := circuit G

end Halo2.Ironwood.Action.SpendAuthority
