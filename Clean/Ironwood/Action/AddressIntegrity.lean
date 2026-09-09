import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Halo2.CircuitTypeDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Orchard diversified address integrity (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, the `Diversified address integrity` block in
`Circuit::synthesize` — the part *after* `commit_ivk` (the commitment itself is a
separate building block; its output cell feeds in here as `ivk`):
1. `ScalarVar::from_base` (`ecc/chip.rs:688-694`) — a pure wrapper, no region;
2. `g_d_old.mul(|| "[ivk] g_d_old", ivk)` — variable-base scalar mul (the `Ecc.Mul`
   bundle, four regions);
3. `NonIdentityPoint::new(|| "witness pk_d_old")` — the `"witness non-identity point"`
   region witnessing the explicit `pk_d_old`;
4. `derived_pk_d_old.constrain_equal(|| "pk_d_old equality")` — the `"constrain equal"`
   region (`ecc/chip.rs:474-488`), two copy constraints.

The block returns the witnessed `pk_d_old`. `Spec` is knowledge-sound with no
existential: `pk_d_old = ivk • g_d_old` at the input `ivk` cell (the phase-1 donor
carried the whole `CommitIvk` call inside and an `∃ ivk` — here `ivk` is an input, so
the statement is direct).

Phase-1 donor: `Clean/Orchard/Action/AddressIntegrity.lean` (post-`CommitIvk` part).
-/

namespace Zcash.Circuits.Action.AddressIntegrity

open Halo2

/-- The inputs of the address-integrity block: the committed incoming viewing key cell
`ivk` (the `commit_ivk` output, coerced by the region-free `ScalarVar::from_base`) and
the old diversified base point `g_d_old` (witnessed earlier in `synthesize`). The
explicit `pk_d_old` is witnessed *inside* the block. -/
structure Input (F : Type) where
  ivk : F
  gDOld : Point F
  -- the explicit `pk_d_old`'s reading program — a prover hint (Rust passes it as
  -- `Value<pallas::Affine>`); witnessed inside the block by the `pointNonId` region
  pkDOld : Unconstrained Point F
deriving CircuitType

def synthesisSummary
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    FloorPlanner.SynthesisSummary :=
  (Ecc.Mul.mulSynthesisSummary cfg.1).combine
    ((FloorPlanner.SynthesisSummary.ofRegion
      (Ecc.WitnessPoint.pointNonIdSynthesisSummary cfg.2 0)).combine
        (FloorPlanner.SynthesisSummary.ofRegion {}))

@[synthesis_summary_norm]
theorem synthesisSummary_lookupActivationCount
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    (synthesisSummary cfg).lookupActivationCount = 13 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    synthesis_summary_norm]

theorem synthesize_copyCellsAssignedFrom
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (self : RegionIndex)
    (configuredMul : Ecc.Mul.mul.Configured cfg.1)
    (configuredPoint : Ecc.WitnessPoint.pointNonIdFormal.Configured cfg.2) :
    ((do
        let derived ← Ecc.Mul.mul.call cfg.1
          { alpha := input.ivk, base := input.gDOld }
        let pkDOld ← Ecc.WitnessPoint.pointNonIdFormal.call cfg.2 input.pkDOld
        assignRegion "constrain equal" (do
          constrainEqual derived.x pkDOld.x
          constrainEqual derived.y pkDOld.y)
        pure pkDOld).operations self).CopyCellsAssignedFrom self
      [input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] := by
  let mulOps := (Ecc.Mul.mul.call cfg.1
    { alpha := input.ivk, base := input.gDOld }).operations self
  let mulOutput := Ecc.Mul.mul.output cfg.1
    { alpha := input.ivk, base := input.gDOld } self
  have hmul : mulOps.CopyCellsAssignedFrom self
      [input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] := by
    apply Ecc.Mul.mul.call_copyCellsAssignedFrom cfg.1 configuredMul _ self
    intro cell hcell
    rw [Ecc.Mul.mul_inputCells] at hcell
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hcell
  let pointRegion := self + Ecc.Mul.mul.regionCount
    { alpha := input.ivk, base := input.gDOld }
  let pointOps := (Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.2 input.pkDOld).operations pointRegion
  let pointOutput := Ecc.WitnessPoint.pointNonIdFormal.output
    cfg.2 input.pkDOld pointRegion
  have hpoint : pointOps.CopyCellsAssignedFrom pointRegion
      ([input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] ++
        mulOps.assignedCellsFrom self) := by
    apply Ecc.WitnessPoint.pointNonIdFormal.call_copyCellsAssignedFrom
      cfg.2 configuredPoint input.pkDOld pointRegion
    intro cell hcell
    rw [Ecc.WitnessPoint.pointNonIdFormal_inputCells] at hcell
    contradiction
  have hmulOutput := Ecc.Mul.mul_call_output_cells_assigned cfg.1
    { alpha := input.ivk, base := input.gDOld } self
  have hpointOutput :=
    Ecc.WitnessPoint.pointNonIdFormal_call_output_cells_assigned
      cfg.2 input.pkDOld pointRegion
  have hequality :
      ((assignRegion "constrain equal" (do
          constrainEqual mulOutput.x pointOutput.x
          constrainEqual mulOutput.y pointOutput.y)).operations
        (pointRegion + 1)).CopyCellsAssignedFrom (pointRegion + 1)
          (([input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] ++
              mulOps.assignedCellsFrom self) ++
            pointOps.assignedCellsFrom pointRegion) := by
    simp only [operations_assignRegion,
      Operations.copyCellsAssignedFrom_region_iff,
      Operations.copyCellsAssignedFrom_nil_iff,
      RegionCircuit.operations_bind, operations_constrainEqual,
      RegionOperations.copyCellsAssignedFrom_append_iff,
      RegionOperations.copyCellsAssignedFrom_constrainEqual_iff,
      RegionOperations.copyCellsAssignedFrom_nil_iff,
      RegionOperations.assignedCellsAfter, List.foldl_cons, List.foldl_nil,
      RegionOperation.assignedCells, List.nil_append, and_true]
    exact ⟨⟨List.mem_append_left _ (List.mem_append_right _ hmulOutput.1),
        List.mem_append_right _ hpointOutput.1⟩,
      ⟨List.mem_append_left _ (List.mem_append_right _ hmulOutput.2),
        List.mem_append_right _ hpointOutput.2⟩⟩
  have hright := hpoint.append (by
    simpa only [pointOps, FormalCircuit.call_regionCount', Nat.add_zero] using hequality)
  have hall := hmul.append (by
    simpa only [mulOps, pointRegion, FormalCircuit.call_regionCount'] using hright)
  simpa only [mulOps, mulOutput, pointRegion, pointOps, pointOutput,
    Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.nextRegionIndex_call', FormalCircuit.output_call',
    FormalCircuit.call_regionCount', Nat.add_zero] using hall

/-- Rust `Circuit::synthesize`'s diversified-address-integrity block (post-`commit_ivk`):
`ivk • g_d_old` (variable-base `Ecc.Mul`), the witnessed `pk_d_old`, and the equality
constraint between them. `Spec` is knowledge soundness at the input `ivk` cell:
`pk_d_old = ivk • g_d_old`, on-curve — no existential. -/
def circuit : FormalCircuit Fp
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    Input Point where
  name := "address integrity"
  configure := pure

  synthesize | (mcfg, wcfg), input => do
    let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
    let pkDOld ← Ecc.WitnessPoint.pointNonIdFormal.call wcfg input.pkDOld
    assignRegion "constrain equal" (do
      constrainEqual derived.x pkDOld.x
      constrainEqual derived.y pkDOld.y)
    pure pkDOld

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg :=
            Ecc.Mul.mul.Configured cfg.1 ×
              Ecc.WitnessPoint.pointNonIdFormal.Configured cfg.2
          gates _ configured := configured.1.gates ++ configured.2.gates
          lookups _ configured := configured.1.lookups ++ configured.2.lookups
          fixedColumns _ configured :=
            configured.1.fixedColumns ++ configured.2.fixedColumns
          permutationColumns cfg configured :=
            ([cfg.1.addConfig.xQR, cfg.1.addConfig.yQR,
              cfg.2.x, cfg.2.y] : List AnyColumn) ++
              configured.1.permutationColumns ++ configured.2.permutationColumns
          inputCells _ _ input :=
            [input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] }
      registered := by
        intro cfg counts hconfig input self
        simp only [Configure.output_pure, Configure.delta_pure,
          Circuit.operations_bind, operations_assignRegion,
          Circuit.operations_pure, Operations.KeygenRegistered.append,
          Operations.KeygenRegistered.region_cons,
          Operations.KeygenRegistered.nil, and_true, circuit_norm]
        exact ⟨by
          apply Ecc.Mul.mul.call_keygenRegistered
            cfg.1 hconfig.1 { alpha := input.ivk, base := input.gDOld } self <;>
              keygen_registration,
          by
            apply Ecc.WitnessPoint.pointNonIdFormal.call_keygenRegistered
              cfg.2 hconfig.2 input.pkDOld (self + 4) <;>
              keygen_registration,
          by keygen_registration⟩
      lookupSelectorAssignmentsAgree_of_registered := by
        intro cfg counts hconfig input self program operations _hregistered
        simp only [operations, program, Configure.output_pure,
          Circuit.operations_bind, operations_assignRegion,
          Circuit.operations_pure, keygen_norm, keygen_spine]
        rw [FormalCircuit.nextRegionIndex_call', Ecc.Mul.mul_call_regionCount]
        exact Ecc.WitnessPoint.pointNonIdFormal.call_lookupSelectorAssignmentsAgree
          cfg.2 hconfig.2 input.pkDOld (self + 4)
      lookupSelectorAnchorRequirements cfg _ _ :=
        LookupRangeCheck.lookupSelectorAnchorRequirements
          cfg.1.overflowConfig.lookupConfig
      lookupSelectorsAnchoredBy_of_registered := by
        intro cfg _ hconfig input self anchor hanchor _
        simp only [Configure.output_pure, Circuit.operations_bind,
          operations_assignRegion, Circuit.operations_pure, List.append_nil]
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact Ecc.Mul.mul.call_lookupSelectorsAnchoredBy
            cfg.1 hconfig.1 { alpha := input.ivk, base := input.gDOld }
              self anchor hanchor
        apply Operations.LookupSelectorsAnchoredBy.append
        · exact Ecc.WitnessPoint.pointNonIdFormal.call_lookupSelectorsAnchoredBy
            cfg.2 hconfig.2 input.pkDOld _ anchor (by trivial)
        · apply Operations.LookupSelectorsAnchoredBy.region_cons
          · apply RegionOperations.LookupSelectorsAnchoredBy.of_forall_isNotLookup
            simp only [RegionOperation.IsNotLookup, RegionCircuit.operations_bind,
              operations_constrainEqual,
              List.forall_append, List.forall_cons, List.forall_nil, and_self]
          · exact Operations.LookupSelectorsAnchoredBy.nil anchor
      copyCellsAssigned := by
        intro cfg _ hconfig input self
        simpa only [keygen_norm] using
          synthesize_copyCellsAssignedFrom cfg input self hconfig.1 hconfig.2
      fixedWritesLawful := by
        intro cfg counts hconfig input self
        apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
        · simp only [Configure.output_pure, Circuit.operations_bind,
            operations_assignRegion, Circuit.operations_pure,
            List.forall_append, circuit_norm]
          exact ⟨Ecc.Mul.mul.call_fixedAssignmentsAgree cfg.1 hconfig.1
              { alpha := input.ivk, base := input.gDOld } self,
            Ecc.WitnessPoint.pointNonIdFormal.call_fixedAssignmentsAgree
              cfg.2 hconfig.2 input.pkDOld (self + 4), by
                apply RegionOperations.HasNoFixedAssignments.fixedAssignmentsAgree
                simp [RegionOperations.HasNoFixedAssignments,
                  RegionOperation.HasNoFixedAssignment]⟩
        · simp only [circuit_norm, synthesis_summary_norm]
      lookupActivationsWellFormed cfg input self := by
        simp only [Circuit.operations_bind, operations_assignRegion,
          Circuit.operations_pure, Operations.LookupActivationsWellFormed,
          List.forall_append, circuit_norm]
        exact ⟨Ecc.Mul.mul.call_lookupActivationsWellFormed
            cfg.1 { alpha := input.ivk, base := input.gDOld } self,
          Ecc.WitnessPoint.pointNonIdFormal.call_lookupActivationsWellFormed
            cfg.2 input.pkDOld (self + 4)⟩
      output cfg _ i :=
        { x := .of (i + 4) 0 cfg.2.x,
          y := .of (i + 4) 0 cfg.2.y }
      regionCount _ := 6
      synthesisSummary cfg _ _ := synthesisSummary cfg
      synthesisSummary_eq := by
        intro cfg input region
        simp only [synthesisSummary, circuit_norm, synthesis_summary_norm]
      output_eq := by
        intro cfg input i
        simp only [Circuit.output_bind, Circuit.output_pure,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', circuit_norm,
          Ecc.WitnessPoint.pointNonIdFormal_output_cells] }

  EnvAssumptions := fun (mcfg, _) env => Ecc.Mul.EnvAssumptions mcfg env

  -- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block
  Assumptions input := input.gDOld.OnCurve

  Spec
  | ⟨(ivk : Fp), (gDOld : Point Fp), _⟩, output, _ =>
    output.OnCurve ∧ output = ivk.val • gDOld

  -- honest proving requires the explicit `pk_d_old` hint value to be the derived
  -- address — otherwise the equality constraint is unsatisfiable — and a genuine curve
  -- point (protocol-side, `ivk ≠ 0`: the derived address is never the identity; the
  -- non-identity witness gate is unsatisfiable otherwise)
  ProverAssumptions
  | ⟨(ivk : Fp), (gDOld : Point Fp), (pkDOld : Point Fp)⟩, _, _ =>
    pkDOld.OnCurve ∧ pkDOld = ivk.val • gDOld

  soundness := by
    circuit_proof_start2 [Ecc.Mul.mul, Ecc.WitnessPoint.pointNonIdFormal,
      Ecc.WitnessPoint.pointNonIdFormal_output_cells,
      Ecc.Mul.Assumptions, Ecc.Mul.Spec]
    -- because our framework did the right thing throughout, a trivially composing
    -- parent is trivially sound
    rcases pkDOld_eq with ⟨rfl, rfl⟩
    simp_all [circuit_norm]

  completeness := by
    circuit_proof_start2 [Ecc.Mul.mul, Ecc.WitnessPoint.pointNonIdFormal,
      Ecc.Mul.Assumptions, Ecc.Mul.Spec]
    -- because our framework did the right thing throughout, a trivially composing
    -- parent is trivially complete
    grind

@[keygen_norm]
theorem circuit_inputCells_eq {config}
    (configured : circuit.Configured config) (input : Var Input Fp) :
    configured.inputCells input =
      [input.ivk.cell, input.gDOld.x.cell, input.gDOld.y.cell] := by
  rfl

/-- Both coordinates returned by address integrity are the cells assigned by
the point-witness child. -/
theorem circuit_call_output_cells_assigned
    (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    let output := circuit.output config input region
    output.x.cell ∈
        ((circuit.call config input).operations region).assignedCellsFrom region ∧
      output.y.cell ∈
        ((circuit.call config input).operations region).assignedCellsFrom region := by
  have houtput : circuit.output config input region =
      { x := .of (region + 4) 0 config.2.x,
        y := .of (region + 4) 0 config.2.y } := rfl
  rw [houtput]
  rw [FormalCircuit.call_operations]
  have hpoint := Ecc.WitnessPoint.pointNonIdFormal_call_output_cells_assigned
    config.2 input.pkDOld (region + 4)
  simp only [circuit, Circuit.operations_bind, Circuit.operations_pure,
    operations_assignRegion, FormalCircuit.output_call',
    FormalCircuit.nextRegionIndex_call', FormalCircuit.call_regionCount',
    Operations.assignedCellsFrom_append, circuit_norm, List.mem_append,
    Nat.add_assoc, Nat.reduceAdd] at hpoint ⊢
  exact ⟨Or.inr (Or.inl hpoint.1), Or.inr (Or.inl hpoint.2)⟩

@[keygen_norm]
theorem circuit_lookupSelectorAnchorRequirements
    (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    circuit.elaborated.lookupSelectorAnchorRequirements config input region =
      LookupRangeCheck.lookupSelectorAnchorRequirements
        config.1.overflowConfig.lookupConfig := rfl

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq
    (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (region : RegionIndex) :
    circuit.elaborated.synthesisSummary config input region =
      synthesisSummary config := rfl

derive_contract_bridges circuit := circuit

end Zcash.Circuits.Action.AddressIntegrity
