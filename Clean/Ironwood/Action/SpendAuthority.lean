module

public import Clean.Halo2
public import Clean.Halo2.Subcircuit
public import Clean.Utils.Tactics.ProvableStructDeriving
public import Clean.Ironwood.Ecc.Basic
public import Clean.Ironwood.Ecc.Add
public import Clean.Ironwood.Ecc.MulFixed.FullWidth
public import Clean.Halo2.CircuitTypeDeriving

@[expose] public section

/-!
# Orchard-protocol spend authority

Reference (ported from Rust):
`orchard@0.14.0/src/circuit.rs`, the `Spend authority` block in `Circuit::synthesize`
(lines 629-644): `alpha_commitment = alpha • SpendAuthG` (full-width fixed-base mul,
discarding the returned scalar decomposition), then `rk = alpha_commitment + ak_P`. The
final public-instance constraints on `rk.x`/`rk.y` belong to the enclosing action
synthesis.

## Knowledge soundness

The phase-1 donor (`Clean/Orchard/Action/SpendAuthority.lean`) could only state
`∃ alpha, rk = α • SpendAuthG + ak_P` — vacuous, since `SpendAuthG` generates the group.
Here `α` is the `FullWidth` child's extraction data (the scalar its witnessed window
cells encode), so the `Spec` is the real knowledge-soundness statement: the extractor
reads `α` off any satisfying assignment and `rk = α • SpendAuthG + ak_P` holds at that
`α`, with no existential.
-/

namespace Zcash.Circuits.Action.SpendAuthority

open Halo2
open Ecc.MulFixed (FixedBase)

/-- The input of the spend-authority block: the randomizer's limb-valued reading program
`alpha` (a prover hint — Rust `Value<pallas::Scalar>`; the `FullWidth` child derives its
85 window witnesses from it, and the scalar is the extraction data) and the
already-assigned authorizing key point `ak_P`. -/
structure Input (F : Type) where
  alpha : UnconstrainedLimbs 4 F
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
  fixedColumns _ configured :=
    configured.1.fixedColumns ++ configured.2.fixedColumns
  permutationColumns cfg configured :=
    configured.1.permutationColumns ++ configured.2.permutationColumns ++
      ([cfg.1.superConfig.addConfig.xQR,
        cfg.1.superConfig.addConfig.yQR] : List AnyColumn)
  inputCells _ _ input :=
    [input.akP.x.cell, input.akP.y.cell]
  readCells _ _ input :=
    ((Ecc.MulFixed.FullWidth.scalarWindows input.alpha).toList.flatMap
      (Witgen.valueBuilderReads (value := field))).map (·.cell)

def synthesisSummary
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    FloorPlanner.SynthesisSummary :=
  (Ecc.MulFixed.FullWidth.circuitSynthesisSummary cfg.1).combine
    (FloorPlanner.SynthesisSummary.ofRegion
      (Ecc.Add.synthesisSummary cfg.2 0))

@[synthesis_summary_norm]
theorem synthesisSummary_lookupActivationCount
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).lookupActivationCount = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

theorem synthesize_consumedCellsAssignedFrom
    (G : FixedBase)
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Input Fp) (self : RegionIndex)
    (configuredFullWidth : (Ecc.MulFixed.FullWidth.circuit G).Configured cfg.1)
    (configuredAdd : Ecc.Add.addFormal.Configured cfg.2) :
    ((do
        let alphaCommitment ←
          (Ecc.MulFixed.FullWidth.circuit G).call cfg.1 input.alpha
        Ecc.Add.addFormal.call cfg.2 { p := alphaCommitment, q := input.akP })
      |>.operations self).AssignedFrom RegionOperation.Consumes self
        ([input.akP.x.cell, input.akP.y.cell] ++
          ((Ecc.MulFixed.FullWidth.scalarWindows input.alpha).toList.flatMap
            (Witgen.valueBuilderReads (value := field))).map AssignedCell.cell) := by
  let initial := [input.akP.x.cell, input.akP.y.cell] ++
    ((Ecc.MulFixed.FullWidth.scalarWindows input.alpha).toList.flatMap
      (Witgen.valueBuilderReads (value := field))).map AssignedCell.cell
  let fullWidthOps := ((Ecc.MulFixed.FullWidth.circuit G).call
    cfg.1 input.alpha).operations self
  let fullWidthOutput := (Ecc.MulFixed.FullWidth.circuit G).output
    cfg.1 input.alpha self
  have hfullWidth : fullWidthOps.AssignedFrom RegionOperation.Consumes self initial := by
    apply (Ecc.MulFixed.FullWidth.circuit G).call_consumedCellsAssignedFrom
      cfg.1 configuredFullWidth input.alpha self
    intro cell hcell
    simp only [FormalCircuit.Configured.inputCells, FormalCircuit.Configured.readCells,
      FormalCircuit.Configured.readRelativeCellsAt, Ecc.MulFixed.FullWidth.circuit,
      FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
      KeygenRequirements.readRelativeCellsAt, List.nil_append, List.map_nil,
      List.append_nil] at hcell
    exact List.mem_append_right _ hcell
  have houtput := Ecc.MulFixed.FullWidth.circuit_call_output_cells_assigned
    G cfg.1 input.alpha self
  have hadd : ((Ecc.Add.addFormal.call cfg.2
      { p := fullWidthOutput, q := input.akP }).operations (self + 2))
      |>.AssignedFrom RegionOperation.Consumes (self + 2)
        (initial ++ fullWidthOps.assignedCellsFrom self) := by
    apply Ecc.Add.addFormal.call_consumedCellsAssignedFrom
      cfg.2 configuredAdd { p := fullWidthOutput, q := input.akP } (self + 2)
    intro cell hcell
    simp only [FormalCircuit.Configured.inputCells, FormalCircuit.Configured.readCells,
      FormalCircuit.Configured.readRelativeCellsAt, Ecc.Add.addFormal,
      FormalRegionCircuit.toFormal, Ecc.Add.add, Ecc.Add.addElaborated,
      FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements,
      KeygenRequirements.readRelativeCellsAt, List.map_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hcell
    rcases hcell with rfl | rfl | rfl | rfl
    · exact List.mem_append_right _ houtput.1
    · exact List.mem_append_right _ houtput.2
    · exact List.mem_append_left _ (List.mem_append_left _ (by simp))
    · exact List.mem_append_left _ (List.mem_append_left _ (by simp))
  have hall := hfullWidth.append (by
    simpa only [fullWidthOps, FormalCircuit.call_regionCount', Ecc.MulFixed.FullWidth.circuit_regionCount, Nat.add_zero] using hadd)
  simpa only [Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.call_regionCount', Ecc.MulFixed.FullWidth.circuit_regionCount, FormalCircuit.output_call',
    FormalCircuit.nextRegionIndex_call', Nat.add_zero, fullWidthOps,
    fullWidthOutput] using hall

/-- Rust `Circuit::synthesize`'s spend-authority block: `α • SpendAuthG` (the
`FullWidth` bundle) plus `ak_P`. `Spec` is knowledge soundness at the extracted
randomizer: `rk = α • SpendAuthG + ak_P` for the `α` read off the witnessed window
cells — no existential. -/
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
      registered := by
          intro cfg counts hconfig input self
          simp only [Circuit.operations_bind,
            Operations.KeygenRegistered.append, FormalCircuit.call_regionCount',
            Ecc.MulFixed.FullWidth.circuit_regionCount, circuit_norm]
          constructor
          · apply (Ecc.MulFixed.FullWidth.circuit G).call_keygenRegistered
                cfg.1 hconfig.1 input.alpha self
            · intro gate h
              simp only [keygenRequirements, Configure.delta_pure, List.append_nil, List.mem_append]
              exact Or.inl h
            · intro argument h
              simp only [keygenRequirements, Configure.delta_pure, List.append_nil, List.mem_append]
              exact Or.inl h
            · intro column h
              simp only [keygenRequirements, List.mem_append]
              exact Or.inl (Or.inl h)
            · keygen_registration
            · keygen_registration
          · apply Ecc.Add.addFormal.call_keygenRegistered
                cfg.2 hconfig.2 _ (self + 2)
            · intro gate h
              simp only [keygenRequirements, Configure.delta_pure, List.append_nil, List.mem_append]
              exact Or.inr h
            · intro argument h
              simp only [keygenRequirements, Configure.delta_pure, List.append_nil, List.mem_append]
              exact Or.inr h
            · intro column h
              simp only [keygenRequirements, List.mem_append]
              exact Or.inl (Or.inr h)
            · keygen_registration
            · keygen_registration
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg counts hconfig input self anchor _ hregistered
        have hlookups :
            (keygenRequirements G).lookups cfg hconfig ++
              ((pure cfg : Configure Fp _).delta counts).lookups = [] := by
          simp only [keygenRequirements, keygen_norm,
            Ecc.MulFixed.FullWidth.Configured.lookups_eq_nil G hconfig.1,
            Ecc.Add.addFormal_lookups_eq_nil hconfig.2]
        rw [hlookups] at hregistered
        exact Operations.LookupSelectorsAnchoredBy.of_registered_noLookups
          hregistered anchor
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input self program operations _hregistered
        simp only [operations, program, Configure.output_pure,
          Circuit.operations_bind,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', Ecc.MulFixed.FullWidth.circuit_regionCount,
          keygen_norm, keygen_spine]
      adviceColumnRequirements cfg :=
        (Ecc.MulFixed.FullWidth.circuit G).elaborated.adviceColumnRequirements cfg.1 ∧
        Ecc.Add.addFormal.elaborated.adviceColumnRequirements cfg.2
      consumedCellsAssigned := by
        intro cfg _ hconfig input self
        simpa only [keygen_norm, keygen_spine, circuit_norm, Operations.ConsumedCellsAssigned,
          KeygenRequirements.readRelativeCellsAt, List.map_nil, List.append_nil] using
          synthesize_consumedCellsAssignedFrom G cfg input self hconfig.1 hconfig.2
      adviceWritesConsistent := by
        intro cfg _ hconfig hadvice input self
        rcases hadvice with ⟨hfwAdv, haddAdv⟩
        simp only [Configure.output_pure, Circuit.operations_bind,
          Operations.adviceWritesConsistentFrom_append, FormalCircuit.call_regionCount',
          Ecc.MulFixed.FullWidth.circuit_regionCount, circuit_norm]
        exact ⟨(Ecc.MulFixed.FullWidth.circuit G).call_adviceWritesConsistent cfg.1
            hconfig.1 hfwAdv input.alpha self,
          Ecc.Add.addFormal.call_adviceWritesConsistent cfg.2
            hconfig.2 haddAdv _ (self + 2)⟩
      fixedWritesLawful := by
        intro cfg counts hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simpa only [Configure.output_pure, Circuit.operations_bind,
            Circuit.operations_pure, List.forall_append, circuit_norm] using
            And.intro
              ((Ecc.MulFixed.FullWidth.circuit G).call_fixedAssignmentsAgree
                cfg.1 hconfig.1 input.alpha self)
              (Ecc.Add.addFormal.call_fixedAssignmentsAgree
                cfg.2 hconfig.2
                  { p := (Ecc.MulFixed.FullWidth.circuit G).output
                      cfg.1 input.alpha self,
                    q := input.akP }
                  (self + 2))
        · simp only [circuit_norm, synthesis_summary_norm]
      lookupActivationsWellFormed cfg input self := by
        simp only [Circuit.operations_bind,
          Operations.LookupActivationsWellFormed, List.forall_append,
          circuit_norm]
        exact ⟨(Ecc.MulFixed.FullWidth.circuit G)
            |>.call_lookupActivationsWellFormed cfg.1 input.alpha self,
          Ecc.Add.addFormal.call_lookupActivationsWellFormed cfg.2 _ (self + 2)⟩
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
        simp only [Circuit.output_bind,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', Ecc.MulFixed.FullWidth.circuit_regionCount, circuit_norm,
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
    have hAddS := out_spec ⟨by rw [hAl]; exact G.smul_valid _, assumptions⟩
    have hrk : ({ x := output_x, y := output_y } : Point Fp) =
        eval (⟨place, env⟩ : Placed Environment Fp)
          (Ecc.Add.addFormal.output cfg
            { p := alphaCommitment, q := { x := input_var_akP_x, y := input_var_akP_y } }
            (i₀ + 2)) := by
      rw [Ecc.Add.addFormal_output_cells]
      simp only [Point.eval_eq, circuit_norm]
      simp_all
    rw [hrk, hAddS.2, hAl]
  completeness := by
    circuit_proof_start2 [Ecc.MulFixed.FullWidth.circuit, Ecc.Add.addFormal]
    have hAl := alphaCommitment_spec env_assumptions
    exact ⟨env_assumptions, by rw [hAl]; exact G.smul_valid _, assumptions⟩

@[keygen_norm]
theorem circuit_inputCells_eq (G : FixedBase) {config}
    (configured : (circuit G).Configured config) (input : Var Input Fp) :
    configured.inputCells input = [input.akP.x.cell, input.akP.y.cell] := by
  rfl

/-- Both coordinates returned by the spend-authority call are assigned by its
final addition region. -/
theorem circuit_call_output_cells_assigned
    (G : FixedBase) (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    let output := (circuit G).output config input region
    output.x.cell ∈
        (((circuit G).call config input).operations region).assignedCellsFrom region ∧
      output.y.cell ∈
        (((circuit G).call config input).operations region).assignedCellsFrom region := by
  have houtput : (circuit G).output config input region =
      { x := .of (region + 2) 1 config.2.xQR,
        y := .of (region + 2) 1 config.2.yQR } := rfl
  rw [houtput]
  rw [FormalCircuit.call_operations]
  let product := (Ecc.MulFixed.FullWidth.circuit G).output
    config.1 input.alpha region
  have hadd := Ecc.Add.addFormal_call_output_cells_assigned config.2
    { p := product, q := input.akP } (region + 2)
  simp only [circuit, Circuit.operations_bind,
    FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
    FormalCircuit.call_regionCount', Ecc.MulFixed.FullWidth.circuit_regionCount, Operations.assignedCellsFrom_append, Ecc.Add.addFormal_output_cells,
    List.mem_append, AssignedCell.of_cell,
    product] at hadd ⊢
  exact ⟨Or.inr hadd.1, Or.inr hadd.2⟩

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq (G : FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    (circuit G).elaborated.synthesisSummary config input region =
      synthesisSummary config := rfl

derive_contract_bridges circuit (G : FixedBase) := circuit G

end Zcash.Circuits.Action.SpendAuthority
