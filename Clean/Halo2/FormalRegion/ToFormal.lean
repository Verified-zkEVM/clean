import Clean.Halo2.FormalRegion.Call

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

/-! ## The region-boundary bridge: `FormalRegionCircuit.toFormal`

Lifts a region-level gadget to a layouter-level `FormalCircuit` by wrapping its body in a
fresh `assignRegion` (halo2 helpers wrapped in their own region start at row offset 0). This
is the *single* mechanism that makes every region-level gadget consumable at layouter level;
the layouter absorption iffs then cover it with zero extra machinery.

**Contract transfer.** All contracts move over verbatim (the two levels' contract fields
mirror each other, including the config-aware `EnvAssumptions`), with one adapter forced by
the level difference: the region `extract` takes an `offset`, the layouter one does not (the
wrapping region fixes offset `0`), so the layouter `extract` is `child.extract config 0 …`. -/

namespace FormalRegionCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- Lift a region-level formal circuit to the layouter level by wrapping its body in a fresh
region. See the section docstring for the contract-transfer details. -/
@[keygen_metadata_projection]
def toFormal (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) :
    FormalCircuit F ConfigInput Config Input Output where
  name := name
  configure := child.configure
  synthesize config input := assignRegion name (child.synthesize config 0 input)
  elaborated :=
    { configureInfo := child.elaborated.configureInfo
      keygenRequirements := child.elaborated.keygenRequirements
      registered := by
        intro configInput counts hconfig input region
        have hregistered := child.elaborated.registered
          configInput counts hconfig 0 input region
        simpa only [assignRegion, Circuit.operations,
          Operations.KeygenRegistered, Operation.KeygenRegistered,
          List.Forall, and_true] using hregistered
      copyCellsAssigned := by
        intro configInput counts hconfig input region
        have hassigned := child.elaborated.copyCellsAssigned
          configInput counts hconfig 0 input region
        simp only [assignRegion, Circuit.operations,
          Operations.CopyCellsAssigned]
        rw [
          Operations.copyCellsAssignedFrom_region_iff]
        exact ⟨hassigned, .nil _ _⟩
      fixedWritesLawful := by
        intro configInput counts hconfig input region
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [assignRegion, Circuit.operations, List.forall_cons,
            List.forall_nil, and_true]
          exact child.elaborated.fixedAssignmentsAgree
            configInput counts hconfig 0 input region
        · simp [assignRegion, Circuit.operations,
            Operations.loadedTableColumns]
        · simp [assignRegion, Circuit.operations,
            Operations.loadedTableColumns]
        · simp [assignRegion, Circuit.operations,
            Operations.loadedTableColumns]
      lookupActivationsWellFormed := by
        intro config input region
        have hlawful := child.elaborated.lookupActivationsWellFormed
          config 0 input region
        simpa only [assignRegion, Circuit.operations,
          Operations.LookupActivationsWellFormed,
          Operation.LookupActivationsWellFormed, List.Forall, and_true] using hlawful
      lookupSelectorAssignmentsAgree_of_registered := by
        intro configInput counts hconfig input region
        dsimp only
        intro _hregistered
        have hagrees := child.elaborated.lookupSelectorAssignmentsAgree
          configInput counts hconfig 0 input region
        simpa only [assignRegion, Circuit.operations,
          Operations.LookupSelectorAssignmentsAgree,
          Operation.LookupSelectorAssignmentsAgree, List.Forall, and_true] using hagrees
      lookupSelectorAnchorRequirements config input region :=
        child.elaborated.lookupSelectorAnchorRequirements config 0 input region
      lookupSelectorsAnchoredBy_of_registered := by
        intro configInput counts hconfig input region anchor hanchor _
        have hchild := child.elaborated.lookupSelectorsAnchoredBy_of_registered
          configInput counts hconfig 0 input region anchor hanchor
          (child.elaborated.registered
            configInput counts hconfig 0 input region)
        simpa only [assignRegion, Circuit.operations,
          Operations.LookupSelectorsAnchoredBy, List.forall_cons,
          List.forall_nil, and_true] using hchild
      output config input i :=
        child.output config 0 input i
      regionCount _ := 1
      synthesisSummary config input region :=
        FloorPlanner.SynthesisSummary.ofRegion
          (child.elaborated.synthesisSummary config 0 input region)
      output_eq := by
        intro config input i
        rw [output_assignRegion]
        exact child.elaborated.output_eq config 0 input i
      regionCount_eq := by
        intro _ _ _
        simp only [assignRegion, Circuit.operations, Operations.regionCount]
      synthesisSummary_eq := by
        intro config input region
        simp only [assignRegion, Circuit.operations,
          FloorPlanner.synthesisSummary]
        have hsummary :
            child.elaborated.synthesisSummary config 0 input region =
              FloorPlanner.regionSynthesisSummary
                (child.synthesize config 0 input region).2 := by
          simpa only [RegionCircuit.operations] using
            child.elaborated.synthesisSummary_eq config 0 input region
        rw [← hsummary]
        exact FloorPlanner.SynthesisSummary.combine_empty _ |>.symm }
  Witness := child.Witness
  inhabitedWitness := child.inhabitedWitness
  extract config input i₀ env := child.extract config 0 input i₀ env
  EnvAssumptions := child.EnvAssumptions
  Assumptions := child.Assumptions
  Spec := child.Spec
  ProverAssumptions := child.ProverAssumptions
  ProverSpec := child.ProverSpec

  soundness := by
    intro config
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_in h_out hE hA hC
    -- the wrapping region's layouter `Constraints` peels to the child's region `Constraints`
    -- at the freshly-allocated region index `i₀` (offset 0)
    simp only [Circuit.operations, assignRegion, Halo2.Constraints] at hC
    subst h_in h_out
    -- instantiate the child's region-level soundness at `self := i₀`
    exact child.soundness config 0 i₀ env input_var hE hA hC.1

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_in h_out hW hE hA hpa
    simp only [Circuit.operations, assignRegion,
      Halo2.ExtendsWitnesses, Halo2.Constraints] at hW ⊢
    subst h_in h_out
    -- instantiate the child's region-level completeness at `self := i₀`
    have hcompl := child.completeness config 0 i₀ env input_var hW.1 hE hA hpa
    exact ⟨⟨hcompl.1, trivial⟩, hcompl.2⟩

@[simp, keygen_norm]
theorem toFormal_keygenRequirements
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) :
    (child.toFormal name).keygenRequirements =
      child.keygenRequirements :=
  rfl

/-- Lifting a region circuit does not change its configure program. This API lemma keeps
clients from relying on reduction through the full `toFormal` package. It is deliberately
not a global normalization rule: rewriting this projection inside elaborated-circuit
summaries would disrupt their dedicated reduced forms. -/
theorem toFormal_configure
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) :
    (child.toFormal name).configure = child.configure :=
  rfl

@[circuit_norm]
theorem toFormal_regionCount
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) (input : Var Input F) :
    (child.toFormal name).regionCount input = 1 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_columns
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).columns =
        (child.elaborated.synthesisSummary config 0 input region).columns := rfl

/-- Lifting a region circuit turns its reduced region footprint into the corresponding
single-region layouter footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    (child.toFormal name).elaborated.synthesisSummary config input region =
      FloorPlanner.SynthesisSummary.ofRegion
        (child.elaborated.synthesisSummary config 0 input region) := rfl

/-- A lifted region circuit has no layouter-level fixed writes whenever its reduced
region summary has no fixed columns. -/
theorem toFormal_synthesisSummary_hasNoFixedWrites
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex)
    (hsummary :
      (child.elaborated.synthesisSummary config 0 input region)
        |>.HasNoFixedColumns) :
    ((child.toFormal name).elaborated.synthesisSummary config input region)
      |>.HasNoFixedWrites := by
  rw [toFormal_synthesisSummary,
    FloorPlanner.SynthesisSummary.hasNoFixedWrites_ofRegion]
  exact hsummary

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_columnOccupancy
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) (column : FloorPlanner.RegionColumn) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).columnOccupancy column =
        if column ∈ (child.elaborated.synthesisSummary
          config 0 input region).columns then
          (child.elaborated.synthesisSummary config 0 input region).rowCount
        else 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_constantSiteCount
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).constantSiteCount =
        (child.elaborated.synthesisSummary
          config 0 input region).constantSiteCount := rfl

/-- A region circuit's configured handle remains valid after lifting it to the
layouter level. -/
def Configured.toFormal
    {child : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {name : String}
    (configured : child.Configured config) :
    (child.toFormal name).Configured config := by
  rcases configured with ⟨configInput, counts, hconfig, output_eq⟩
  exact ⟨configInput, counts, hconfig, output_eq⟩

/-- The region-to-layouter bridge preserves configure/synthesis keygen lawfulness. -/
theorem KeygenLawful.toFormal
    {child : FormalRegionCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : child.KeygenLawful requirements) (name : String := child.name) :
    (child.toFormal name).KeygenLawful requirements where
  registered := by
    intro configInput counts hconfig input region
    have hregistered :=
      FormalRegionCircuit.KeygenLawful.registered
        hlawful configInput counts hconfig 0 input region
    simpa only [toFormal, assignRegion, Circuit.operations,
      Operations.KeygenRegistered, Operation.KeygenRegistered,
      List.Forall, and_true] using hregistered

end FormalRegionCircuit

end Halo2
