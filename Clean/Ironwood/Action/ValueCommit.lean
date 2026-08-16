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
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.1.fixedColumns ++
      configured.2.2.fixedColumns
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
      configured.2.2.permutationColumns ++
        ([cfg.1.superConfig.addConfig.xQR,
          cfg.1.superConfig.addConfig.yP,
          cfg.2.1.superConfig.addConfig.xQR,
          cfg.2.1.superConfig.addConfig.yQR] : List AnyColumn)
  inputCells _ _ input :=
    [input.magnitude.cell, input.sign.cell]

def synthesisSummary
    (cfg : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) :
    FloorPlanner.SynthesisSummary :=
  (Ecc.MulFixed.Short.circuitSynthesisSummary cfg.1).combine
    ((Ecc.MulFixed.FullWidth.circuitSynthesisSummary cfg.2.1).combine
      (FloorPlanner.SynthesisSummary.ofRegion
        (Ecc.Add.synthesisSummary cfg.2.2 0)))

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq
    (cfg : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq
    (cfg : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

theorem synthesize_copyCellsAssignedFrom
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (cfg : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config)
    (input : Var Inputs Fp) (self : RegionIndex)
    (configuredShort : (Ecc.MulFixed.Short.circuit V).Configured cfg.1)
    (configuredFullWidth : (Ecc.MulFixed.FullWidth.circuit R).Configured cfg.2.1)
    (configuredAdd : Ecc.Add.addFormal.Configured cfg.2.2) :
    ((do
        let commitment ← (Ecc.MulFixed.Short.circuit V).call cfg.1
          ⟨input.magnitude, input.sign⟩
        let blind ← (Ecc.MulFixed.FullWidth.circuit R).call cfg.2.1 input.rcv
        Ecc.Add.addFormal.call cfg.2.2 { p := commitment, q := blind })
      |>.operations self).CopyCellsAssignedFrom self
        [input.magnitude.cell, input.sign.cell] := by
  let shortInput : Var Ecc.MulFixed.Short.Inputs Fp :=
    ⟨input.magnitude, input.sign⟩
  let shortOps := ((Ecc.MulFixed.Short.circuit V).call
    cfg.1 shortInput).operations self
  let shortOutput := (Ecc.MulFixed.Short.circuit V).output
    cfg.1 shortInput self
  have hshort : shortOps.CopyCellsAssignedFrom self
      [input.magnitude.cell, input.sign.cell] := by
    apply (Ecc.MulFixed.Short.circuit V).call_copyCellsAssignedFrom
      cfg.1 configuredShort shortInput self
    intro cell hcell
    rw [Ecc.MulFixed.Short.circuit_inputCells_eq] at hcell
    simpa only [shortInput] using hcell
  have hshortOutput := Ecc.MulFixed.Short.circuit_call_output_cells_assigned
    V cfg.1 shortInput self
  let fullWidthOps := ((Ecc.MulFixed.FullWidth.circuit R).call
    cfg.2.1 input.rcv).operations (self + 2)
  let fullWidthOutput := (Ecc.MulFixed.FullWidth.circuit R).output
    cfg.2.1 input.rcv (self + 2)
  have hfullWidth : fullWidthOps.CopyCellsAssignedFrom (self + 2)
      ([input.magnitude.cell, input.sign.cell] ++ shortOps.assignedCellsFrom self) := by
    apply (Ecc.MulFixed.FullWidth.circuit R).call_copyCellsAssignedFrom
      cfg.2.1 configuredFullWidth input.rcv (self + 2)
    intro cell hcell
    rw [Ecc.MulFixed.FullWidth.circuit_inputCells_eq] at hcell
    contradiction
  have hfullWidthOutput := Ecc.MulFixed.FullWidth.circuit_call_output_cells_assigned
    R cfg.2.1 input.rcv (self + 2)
  let prefixOps := shortOps ++ fullWidthOps
  have hprefix : prefixOps.CopyCellsAssignedFrom self
      [input.magnitude.cell, input.sign.cell] := by
    apply hshort.append
    simpa only [shortOps, FormalCircuit.call_regionCount', Nat.add_zero] using hfullWidth
  have hadd : ((Ecc.Add.addFormal.call cfg.2.2
      { p := shortOutput, q := fullWidthOutput }).operations (self + 4))
      |>.CopyCellsAssignedFrom (self + 4)
        ([input.magnitude.cell, input.sign.cell] ++
          prefixOps.assignedCellsFrom self) := by
    apply Ecc.Add.addFormal.call_copyCellsAssignedFrom cfg.2.2 configuredAdd
      { p := shortOutput, q := fullWidthOutput } (self + 4)
    intro cell hcell
    rw [Ecc.Add.addFormal_inputCells] at hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
    rcases hcell with rfl | rfl | rfl | rfl
    · apply List.mem_append_right
      simpa only [prefixOps, shortOps, fullWidthOps,
        Operations.assignedCellsFrom_append,
        FormalCircuit.call_regionCount', Nat.add_zero] using
        List.mem_append_left (fullWidthOps.assignedCellsFrom (self + 2))
          hshortOutput.1
    · apply List.mem_append_right
      simpa only [prefixOps, shortOps, fullWidthOps,
        Operations.assignedCellsFrom_append,
        FormalCircuit.call_regionCount', Nat.add_zero] using
        List.mem_append_left (fullWidthOps.assignedCellsFrom (self + 2))
          hshortOutput.2
    · apply List.mem_append_right
      simpa only [prefixOps, shortOps, fullWidthOps,
        Operations.assignedCellsFrom_append,
        FormalCircuit.call_regionCount', Nat.add_zero] using
        List.mem_append_right (shortOps.assignedCellsFrom self)
          hfullWidthOutput.1
    · apply List.mem_append_right
      simpa only [prefixOps, shortOps, fullWidthOps,
        Operations.assignedCellsFrom_append,
        FormalCircuit.call_regionCount', Nat.add_zero] using
        List.mem_append_right (shortOps.assignedCellsFrom self)
          hfullWidthOutput.2
  have hall := hprefix.append (by
    simpa only [prefixOps, shortOps, fullWidthOps,
      FormalCircuit.call_regionCount', Operations.regionCount_append,
      Nat.add_zero, Nat.add_assoc] using hadd)
  simpa only [Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
    FormalCircuit.call_regionCount', Ecc.MulFixed.Short.circuit_regionCount,
    Ecc.MulFixed.FullWidth.circuit_regionCount,
    List.append_assoc, Nat.add_assoc, Nat.add_zero, shortInput, shortOps,
    shortOutput, fullWidthOps, fullWidthOutput, prefixOps] using hall

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
      registered := by
        intro cfg counts hconfig input self
        simp only [Circuit.operations_bind, Circuit.operations_pure,
          Operations.KeygenRegistered.append, circuit_norm]
        exact ⟨by
          apply (Ecc.MulFixed.Short.circuit V).call_keygenRegistered
              cfg.1 hconfig.1 _ self <;> keygen_registration,
          by
            apply (Ecc.MulFixed.FullWidth.circuit R).call_keygenRegistered
                cfg.2.1 hconfig.2.1 input.rcv (self + 2) <;> keygen_registration,
          by
            apply Ecc.Add.addFormal.call_keygenRegistered cfg.2.2
                hconfig.2.2 _ (self + 4) <;> keygen_registration⟩
      copyCellsAssigned := by
        intro cfg _ hconfig input self
        simpa only [keygen_norm, keygen_spine, circuit_norm] using
          synthesize_copyCellsAssignedFrom V R cfg input self
            hconfig.1 hconfig.2.1 hconfig.2.2
      fixedWritesLawful := by
        intro cfg counts hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simpa only [Configure.output_pure, Circuit.operations_bind,
            Circuit.operations_pure, List.forall_append, circuit_norm,
            Nat.add_assoc] using
            And.intro
              ((Ecc.MulFixed.Short.circuit V).call_fixedAssignmentsAgree
                cfg.1 hconfig.1
                  { magnitude := input.magnitude, sign := input.sign } self)
              (And.intro
                ((Ecc.MulFixed.FullWidth.circuit R).call_fixedAssignmentsAgree
                  cfg.2.1 hconfig.2.1 input.rcv (self + 2))
                (Ecc.Add.addFormal.call_fixedAssignmentsAgree
                  cfg.2.2 hconfig.2.2
                    { p := (Ecc.MulFixed.Short.circuit V).output cfg.1
                        { magnitude := input.magnitude, sign := input.sign } self,
                      q := (Ecc.MulFixed.FullWidth.circuit R).output
                        cfg.2.1 input.rcv (self + 2) }
                    (self + 4)))
        · simp only [circuit_norm, synthesis_summary_norm]
      lookupActivationsWellFormed cfg input self := by
        simp only [Circuit.operations_bind, Circuit.operations_pure,
          Operations.LookupActivationsWellFormed, List.forall_append,
          circuit_norm]
        exact ⟨(Ecc.MulFixed.Short.circuit V)
            |>.call_lookupActivationsWellFormed cfg.1 _ self,
          (Ecc.MulFixed.FullWidth.circuit R)
            |>.call_lookupActivationsWellFormed cfg.2.1 input.rcv (self + 2),
          Ecc.Add.addFormal.call_lookupActivationsWellFormed cfg.2.2 _ (self + 4)⟩
      output cfg _ i :=
        { x := .of (i + 4) 1 cfg.2.2.xQR,
          y := .of (i + 4) 1 cfg.2.2.yQR }
      regionCount _ := 5
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

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) (input : Var Inputs Fp) (region : RegionIndex) :
    ((circuit V R).elaborated.synthesisSummary config input region) =
      synthesisSummary config := rfl

/-- The value-commitment circuit's two positional output cells. -/
@[keygen_output_norm]
theorem circuit_output_cells
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) (input : Var Inputs Fp) (region : RegionIndex) :
    (circuit V R).output config input region =
      { x := .of (region + 4) 1 config.2.2.xQR,
        y := .of (region + 4) 1 config.2.2.yQR } := by
  rfl

@[keygen_norm]
theorem circuit_inputCells_eq
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase) {config}
    (configured : (circuit V R).Configured config) (input : Var Inputs Fp) :
    configured.inputCells input = [input.magnitude.cell, input.sign.cell] := by
  rfl

/-- Both coordinates returned by the value-commitment call are assigned by its
final addition region. -/
theorem circuit_call_output_cells_assigned
    (V : Ecc.MulFixed.Short.FixedBase) (R : FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config ×
      Ecc.Add.Config) (input : Var Inputs Fp) (region : RegionIndex) :
    let output := (circuit V R).output config input region
    output.x.cell ∈
        (((circuit V R).call config input).operations region).assignedCellsFrom region ∧
      output.y.cell ∈
        (((circuit V R).call config input).operations region).assignedCellsFrom region := by
  rw [circuit_output_cells]
  rw [FormalCircuit.call_operations]
  let shortInput : Var Ecc.MulFixed.Short.Inputs Fp :=
    ⟨input.magnitude, input.sign⟩
  let shortOutput := (Ecc.MulFixed.Short.circuit V).output
    config.1 shortInput region
  let fullWidthOutput := (Ecc.MulFixed.FullWidth.circuit R).output
    config.2.1 input.rcv (region + 2)
  have hadd := Ecc.Add.addFormal_call_output_cells_assigned config.2.2
    { p := shortOutput, q := fullWidthOutput } (region + 4)
  simp only [Ecc.Add.addFormal_output_cells, shortInput, shortOutput,
    fullWidthOutput] at hadd
  simp only [circuit, Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
    FormalCircuit.call_regionCount', Operations.assignedCellsFrom_append,
    Ecc.MulFixed.Short.circuit_regionCount,
    Ecc.MulFixed.FullWidth.circuit_regionCount, List.mem_append,
    AssignedCell.of_cell, Nat.add_assoc, Nat.reduceAdd]
  exact ⟨Or.inr (Or.inr (Or.inl hadd.1)),
    Or.inr (Or.inr (Or.inl hadd.2))⟩

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
  rw [circuit_synthesisSummary_eq]
  simp only [synthesisSummary, synthesis_summary_norm]

derive_contract_bridges circuit (V : Ecc.MulFixed.Short.FixedBase)
  (R : FixedBase) := circuit V R

end Zcash.Circuits.Action.ValueCommit
