import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Halo2.CircuitTypeDeriving
import Clean.Ironwood.Ecc.MulFixed.Short

/-!
# Orchard value commitment (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/gadget.rs::value_commit_orchard` (lines 115-148):
`cv = [v] ValueCommitV + [rcv] ValueCommitR` — three layouter pieces in source order:
1. `FixedPointShort::from_inner(ValueCommitV).mul(v)` (the `Ecc.MulFixed.Short`
   bundle; `v` is the signed magnitude-sign pair);
2. `FixedPoint::from_inner(ValueCommitR).mul(rcv)` (the `Ecc.MulFixed.FullWidth`
   bundle; the full-width scalar lives on the child's witness boundary — the caller's
   85 window witness programs encode it, and the scalar is the extraction data);
3. `commitment.add(blind)` (region `"complete point addition"`, `ecc/chip.rs:582-595`).

Phase-1 donor: `Clean/Orchard/Action/ValueCommit.lean`.
-/

namespace Zcash.Circuits.Action.ValueCommit

open Halo2
open Ecc.MulFixed (FixedBase)

/-- The inputs: the short child's magnitude/sign cells and the blinding scalar's
nat-valued reading program `rcv` (a prover hint — Rust `Value<pallas::Scalar>`; the
full-width child derives its window witnesses from it, the scalar is extraction data). -/
structure Inputs (F : Type) where
  rcv : UnconstrainedNat F
  magnitude : F
  sign : F
deriving CircuitType

@[keygen_norm]
def keygenRequirements
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase) :
    KeygenRequirements Fp
      (Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
        Ecc.Add.Config) (Var Inputs Fp) where
  configLawful cfg :=
    (Ecc.MulFixed.Short.circuit V).Configured cfg.1 ×
      (Ecc.MulFixed.FullWidth.circuit R).Configured cfg.2.1 ×
        Ecc.Add.addFormal.Configured cfg.2.2
  gates _ configured :=
    configured.1.gates ++ configured.2.1.gates ++
      configured.2.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.1.lookups ++
      configured.2.2.lookups
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
      configured.2.2.permutationColumns ++
        ([cfg.1.superConfig.addConfig.xQR,
          cfg.1.superConfig.addConfig.yP,
          cfg.2.1.superConfig.addConfig.xQR,
          cfg.2.1.superConfig.addConfig.yQR] : List AnyColumn)
  inputPermutationColumns _ _ input :=
    [input.magnitude.cell.column, input.sign.cell.column]

/-! ## The `value_commit_orchard` bundle -/

/-- Rust `gadget.rs::value_commit_orchard`: `[v] ValueCommitV` (short signed), `[rcv]
ValueCommitR` (full-width; the scalar is the child's extraction data), and the final
complete addition. `Spec` is the donor contract: the commitment is
`[±m] V + [rcv] R` at the sign-resolved magnitude `m < 2⁶⁴` and the extracted
full-width scalar. -/
def circuit (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase) :
    FormalCircuit Fp
    (Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    Inputs Point where
  name := "value commit"
  configure := pure

  synthesize | (scfg, fcfg, ecfg), input => do
    let commitment ← (Ecc.MulFixed.Short.circuit V).call scfg
      ⟨input.magnitude, input.sign⟩
    let blind ← (Ecc.MulFixed.FullWidth.circuit R).call fcfg input.rcv
    let cv ← Ecc.Add.addFormal.call ecfg
      { p := commitment, q := blind }
    pure cv

  elaborated :=
    { keygenRequirements := keygenRequirements V R
      registered := by keygen_registration
      output cfg _ i :=
        { x := .of (i + 4) 1 cfg.2.2.xQR,
          y := .of (i + 4) 1 cfg.2.2.yQR }
      regionCount _ := 5
      output_eq := by
        intro cfg input i
        simp only [Circuit.output_bind, Circuit.output_pure,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', circuit_norm,
          Ecc.Add.addFormal_output_cells] }

  EnvAssumptions := fun (scfg, fcfg, _) env =>
    Ecc.MulFixed.Short.EnvAssumptions scfg env ∧
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  Witness F := Vector F 85 × Fq
  extract := fun (_, fcfg, _) _ i₀ env =>
    Ecc.MulFixed.FullWidth.fwExtract fcfg (i₀ + 2) env

  Spec
  | ⟨ _, (magnitude : Fp), (sign : Fp )⟩, output, (_, s) =>
    magnitude.val < 2 ^ 64 ∧
      ((sign = 1 ∧ output = (magnitude.val : Fq) • V + s • R) ∨
        (sign = -1 ∧ output = -(magnitude.val : Fq) • V + s • R))

  ProverAssumptions := fun ⟨_, (magnitude : Fp), (sign : Fp)⟩ _ _ =>
    magnitude.val < 2 ^ 64 ∧ (sign = 1 ∨ sign = -1)

  soundness := by
    circuit_proof_start2 [Ecc.MulFixed.Short.circuit, Ecc.MulFixed.FullWidth.circuit,
      Ecc.Add.addFormal, Ecc.MulFixed.Short.Spec]
    obtain ⟨hSEnv, hFEnv⟩ := env_assumptions
    obtain ⟨hm_lt, hcases⟩ := commitment_spec hSEnv
    have hBl := blind_spec hFEnv
    have hAddS := cv_spec ⟨by
        rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _,
      by rw [hBl]; exact R.smul_valid _⟩
    refine ⟨hm_lt, ?_⟩
    rw [Ecc.Add.addFormal_output_cells] at cv_eq
    have hcv : ({ x := output_x, y := output_y } : Point Fp) =
        eval (⟨place, env⟩ : Placed Environment Fp) cv := by
      rw [← cv_eq]
      simp only [Point.eval_eq, circuit_norm]
      simp_all
    rcases hcases with ⟨hsign, hCm⟩ | ⟨hsign, hCm⟩
    · refine Or.inl ⟨hsign, ?_⟩
      rw [hcv, hAddS.2, hCm, hBl]
    · refine Or.inr ⟨hsign, ?_⟩
      rw [hcv, hAddS.2, hCm, hBl]

  completeness := by
    circuit_proof_start2 [Ecc.MulFixed.Short.circuit, Ecc.MulFixed.FullWidth.circuit,
      Ecc.Add.addFormal, Ecc.MulFixed.Short.Spec]
    obtain ⟨hSEnv, hFEnv⟩ := env_assumptions
    obtain ⟨hmag, hsign⟩ := prover_assumptions
    obtain ⟨hm_lt, hcases⟩ := commitment_spec hSEnv ⟨hmag, hsign⟩
    have hBl := blind_spec hFEnv
    refine ⟨⟨hSEnv, hmag, hsign⟩, hFEnv, ?_, by rw [hBl]; exact R.smul_valid _⟩
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _

/-- A value commitment requests only the short scalar's strict-decomposition
constant allocation. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_constantSiteCount
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config)
    (input : Var Inputs Fp) (region : RegionIndex) :
    ((circuit V R).elaborated.synthesisSummary
      config input region).constantSiteCount = 1 := by
  rw [ElaboratedCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [circuit, Circuit.operations_bind, Circuit.operations_pure,
    FloorPlanner.synthesisSummary_append, synthesis_summary_norm]

derive_contract_bridges circuit (V : Ecc.MulFixed.Short.FixedBase)
  (R : FixedBase) := circuit V R

end Zcash.Circuits.Action.ValueCommit
