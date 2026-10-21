import Clean.Halo2.Tactics.Keygen
import Clean.Halo2.ElaboratedConfigure

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

/-- The keygen arguments available at a circuit boundary. -/
structure KeygenContext (F : Type) where
  gates : List (Gate F)
  lookups : List (LookupArgument F)
  fixedColumns : List (Column .fixed)
  permutationColumns : List AnyColumn

/--
A configure result together with proof that every argument it provides or borrows is
available in an ambient keygen context.

This is the configure-side capability consumed by an opaque subcircuit call. Aggregate
configurers may package several such values; monadic composition transports them by
`mono` without reopening the configured child.
-/
structure ConfigurationCertificate
    {ConfigInput Config InputVar : Type}
    (requirements : KeygenRequirements F ConfigInput InputVar)
    (configure : ConfigInput → Configure F Config)
    (config : Config) (context : KeygenContext F) where
  configInput : ConfigInput
  counts : ConfigureCounts
  configLawful : requirements.configLawful configInput
  output_eq : (configure configInput).output counts = config
  gates : ∀ gate,
    gate ∈ requirements.gates configInput configLawful ++
      ((configure configInput).delta counts).gates →
    gate ∈ context.gates
  lookups : ∀ argument,
    argument ∈ requirements.lookups configInput configLawful ++
      ((configure configInput).delta counts).lookups →
    argument ∈ context.lookups
  fixedColumns : ∀ column,
    column ∈ requirements.fixedColumns configInput configLawful ++
      (configure configInput).fixedColumns counts →
    column ∈ context.fixedColumns
  permutationColumns : ∀ column,
    column ∈ requirements.permutationColumns configInput configLawful ++
      ((configure configInput).delta counts).permutationRequests →
    column ∈ context.permutationColumns

namespace ConfigurationCertificate

/-- The canonical certificate in the configure program's exact resulting context. -/
def ofOutput
    {ConfigInput Config InputVar : Type}
    (requirements : KeygenRequirements F ConfigInput InputVar)
    (configure : ConfigInput → Configure F Config)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (configLawful : requirements.configLawful configInput) :
    ConfigurationCertificate requirements configure
      ((configure configInput).output counts)
      { gates := requirements.gates configInput configLawful ++
          ((configure configInput).delta counts).gates
        lookups := requirements.lookups configInput configLawful ++
          ((configure configInput).delta counts).lookups
        fixedColumns := requirements.fixedColumns configInput configLawful ++
          (configure configInput).fixedColumns counts
        permutationColumns := requirements.permutationColumns configInput configLawful ++
          ((configure configInput).delta counts).permutationRequests } :=
  ⟨configInput, counts, configLawful, rfl, fun _ h => h, fun _ h => h,
    fun _ h => h, fun _ h => h⟩

/-- Transport a configured capability into a larger ambient context. -/
def mono
    {ConfigInput Config InputVar : Type}
    {requirements : KeygenRequirements F ConfigInput InputVar}
    {configure : ConfigInput → Configure F Config}
    {config : Config} {source target : KeygenContext F}
    (certificate : ConfigurationCertificate requirements configure config source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (fixedColumns : ∀ column,
      column ∈ source.fixedColumns → column ∈ target.fixedColumns)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigurationCertificate requirements configure config target where
  configInput := certificate.configInput
  counts := certificate.counts
  configLawful := certificate.configLawful
  output_eq := certificate.output_eq
  gates gate hgate := gates gate (certificate.gates gate hgate)
  lookups argument hargument :=
    lookups argument (certificate.lookups argument hargument)
  fixedColumns column hcolumn :=
    fixedColumns column (certificate.fixedColumns column hcolumn)
  permutationColumns column hcolumn :=
    permutationColumns column (certificate.permutationColumns column hcolumn)

/-- Retarget a configured capability whose circuit requests no fixed-write columns.
Unlike `mono`, this does not require the ambient source context's unrelated fixed
columns to embed into the target. -/
def retargetWithoutFixedColumns
    {ConfigInput Config InputVar : Type}
    {requirements : KeygenRequirements F ConfigInput InputVar}
    {configure : ConfigInput → Configure F Config}
    {config : Config} {source target : KeygenContext F}
    (certificate : ConfigurationCertificate requirements configure config source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (hfixed : requirements.fixedColumns certificate.configInput
        certificate.configLawful ++
      (configure certificate.configInput).fixedColumns certificate.counts = [])
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigurationCertificate requirements configure config target where
  configInput := certificate.configInput
  counts := certificate.counts
  configLawful := certificate.configLawful
  output_eq := certificate.output_eq
  gates gate hgate := gates gate (certificate.gates gate hgate)
  lookups argument hargument :=
    lookups argument (certificate.lookups argument hargument)
  fixedColumns column hcolumn := by
    rw [hfixed] at hcolumn
    exact (List.not_mem_nil hcolumn).elim
  permutationColumns column hcolumn :=
    permutationColumns column (certificate.permutationColumns column hcolumn)

end ConfigurationCertificate

/--
The complete reduced metadata of a layouter circuit's configure/synthesize pair.

Configure elaboration stays compositional through `infer_instance`; synthesis metadata
is flattened here because circuit authors frequently provide reduced output and region
count functions manually. This is the single elaboration object exposed by
`FormalCircuit` to its parents.
-/
class ElaboratedCircuit (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output]
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F)) where
  configureInfo : ∀ input, ElaboratedConfigure (configure input) := by
    intro input
    try dsimp only [configure]
    infer_instance
  /-- Keygen capabilities supplied by the caller rather than local configure. -/
  keygenRequirements : KeygenRequirements F ConfigInput (Var Input F) := {}
  /-- Configure/synthesis registration certificate. -/
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).KeygenRegistered
      (keygenRequirements.gates configInput hconfig ++ (program.delta counts).gates)
      (keygenRequirements.lookups configInput hconfig ++ (program.delta counts).lookups)
      (keygenRequirements.fixedColumns configInput hconfig ++
        program.fixedColumns counts)
      (keygenRequirements.permutationColumns configInput hconfig ++
        (program.delta counts).permutationRequests ++
        keygenRequirements.inputPermutationColumns configInput hconfig input) := by
    keygen_registration
  /-- Every copy endpoint is either a declared caller input or assigned by synthesis. -/
  copyCellsAssigned :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).CopyCellsAssigned i
      (keygenRequirements.inputCells configInput hconfig input) := by
    keygen_registration
  /-- Fixed writes have unambiguous compiler semantics. -/
  fixedWritesLawful :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).FixedWritesLawful
      (keygenRequirements.constantColumns configInput hconfig ++
        (program.delta counts).constants) := by
    intro configInput counts hconfig input i
    apply Operations.HasNoFixedWrites.fixedWritesLawful
    keygen_registration
  /-- Every lookup activation enables its master and only its declared selectors. -/
  lookupActivationsWellFormed :
    ∀ (config : Config) (input : Var Input F) (i : RegionIndex),
    ((synthesize config input).operations i).LookupActivationsWellFormed := by
    keygen_registration
  /-- Lookup-local selector valuations agree with every activation at the same row. -/
  lookupSelectorAssignmentsAgree_of_registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (_hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    let operations := (synthesize (program.output counts) input).operations i
    (hregistered : operations.KeygenRegistered
        (keygenRequirements.gates configInput _hconfig ++ (program.delta counts).gates)
        (keygenRequirements.lookups configInput _hconfig ++ (program.delta counts).lookups)
        (keygenRequirements.fixedColumns configInput _hconfig ++
          program.fixedColumns counts)
        (keygenRequirements.permutationColumns configInput _hconfig ++
          (program.delta counts).permutationRequests ++
          keygenRequirements.inputPermutationColumns configInput _hconfig input)) →
      Operations.LookupSelectorAssignmentsAgree operations := by
    intro configInput counts hconfig input i program operations hregistered
    solve
    | clear_value operations
      exact Operations.lookupSelectorAssignmentsAgree_of_keygenRegistered_noLookups
        hregistered
    | clear_value operations
      apply Operations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
        hregistered
      keygen_registration
    | keygen_registration
  /-- Reduced equations describing the physical anchors needed by lookup
  selectors which may be read while disabled. -/
  lookupSelectorAnchorRequirements :
    Config → Var Input F → RegionIndex →
      List (ℕ × FloorPlanner.RegionColumn) := fun _ _ _ => []
  /-- The reduced anchor equations suffice to anchor every auxiliary selector in
  each region that reads it. -/
  lookupSelectorsAnchoredBy_of_registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (_hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex)
      (anchor : ℕ → FloorPlanner.RegionColumn),
    SelectorAnchorRequirementsSatisfied
        (lookupSelectorAnchorRequirements
          ((configure configInput).output counts) input i) anchor →
      Operations.KeygenRegistered
        ((synthesize ((configure configInput).output counts) input).operations i)
          (keygenRequirements.gates configInput _hconfig ++
            ((configure configInput).delta counts).gates)
          (keygenRequirements.lookups configInput _hconfig ++
            ((configure configInput).delta counts).lookups)
          (keygenRequirements.fixedColumns configInput _hconfig ++
            (configure configInput).fixedColumns counts)
          (keygenRequirements.permutationColumns configInput _hconfig ++
            ((configure configInput).delta counts).permutationRequests ++
            keygenRequirements.inputPermutationColumns configInput _hconfig input) →
      Operations.LookupSelectorsAnchoredBy
        ((synthesize ((configure configInput).output counts) input).operations i)
        anchor := by
    intro configInput counts hconfig input i anchor _ hregistered
    solve
    | exact Operations.LookupSelectorsAnchoredBy.of_registered_noLookups
        hregistered anchor
    | apply Operations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
        hregistered (anchor := anchor)
      keygen_registration
    | keygen_registration
    | keygen_registration
  output : Config → Var Input F → RegionIndex → Var Output F :=
    fun config input i => (synthesize config input).output i
  regionCount : Var Input F → ℕ := fun _ => 0
  /-- Exact compositional footprint of synthesis.  Parents use this reduced value
  without unfolding the child's operation stream. -/
  synthesisSummary : Config → Var Input F → RegionIndex →
      FloorPlanner.SynthesisSummary
  output_eq : ∀ config input i,
    output config input i = (synthesize config input).output i := by
    intro _ _ _
    rfl
  regionCount_eq : ∀ config input i,
    regionCount input =
      ((synthesize config input).operations i).regionCount := by
    -- fallback: count symbolically (child call chunks via `call_regionCount` metadata —
    -- the opaque `callOps` barrier is not evaluable, by design)
    intro _ _ _
    first
    | rfl
    | simp only [circuit_norm, Circuit.operations_bind, Circuit.operations_pure,
        Operations.regionCount_append, Operations.regionCount,
        Nat.add_assoc, Nat.reduceAdd]
  synthesisSummary_eq : ∀ config input i,
    synthesisSummary config input i =
      FloorPlanner.synthesisSummary
        ((synthesize config input).operations i) := by
    intro _ _ _
    first
    | rfl
    | simp only [circuit_norm, Circuit.operations_bind,
        Circuit.operations_pure, FloorPlanner.synthesisSummary_append,
        synthesis_summary_norm]

namespace ElaboratedCircuit

/-- Package a registration proof for a circuit with no caller-supplied keygen
requirements. This keeps the empty-requirements reduction independent of a
potentially large concrete synthesis program. -/
theorem noRequirements_registered
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F))
    (hregistered : ∀ configInput counts input i,
      ((synthesize ((configure configInput).output counts) input).operations i)
        |>.KeygenRegistered ((configure configInput).delta counts).gates
          ((configure configInput).delta counts).lookups
          ((configure configInput).fixedColumns counts)
          ((configure configInput).delta counts).permutationRequests) :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : ({} : KeygenRequirements F ConfigInput (Var Input F)).configLawful
        configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).KeygenRegistered
      (({} : KeygenRequirements F ConfigInput (Var Input F)).gates
          configInput hconfig ++ (program.delta counts).gates)
      (({} : KeygenRequirements F ConfigInput (Var Input F)).lookups
          configInput hconfig ++ (program.delta counts).lookups)
      (({} : KeygenRequirements F ConfigInput (Var Input F)).fixedColumns
          configInput hconfig ++ program.fixedColumns counts)
      (({} : KeygenRequirements F ConfigInput (Var Input F)).permutationColumns
          configInput hconfig ++ (program.delta counts).permutationRequests ++
        ({} : KeygenRequirements F ConfigInput (Var Input F)).inputPermutationColumns
          configInput hconfig input) := by
  intro configInput counts hconfig input i
  cases hconfig
  simpa only [KeygenRequirements.gates, KeygenRequirements.lookups,
    KeygenRequirements.permutationColumns,
    KeygenRequirements.inputPermutationColumns, KeygenRequirements.inputCells,
    List.nil_append, List.append_nil, List.map_nil] using
      hregistered configInput counts input i

/-- Lookup-selector assignment agreement obtained from the circuit's registration
certificate and its circuit-local law. -/
theorem lookupSelectorAssignmentsAgree
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    {configure : ConfigInput → Configure F Config}
    {synthesize : Config → Var Input F → Circuit F (Var Output F)}
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex) :
    ((synthesize ((configure configInput).output counts) input).operations i)
      |>.LookupSelectorAssignmentsAgree :=
  self.lookupSelectorAssignmentsAgree_of_registered
    configInput counts hconfig input i
    (self.registered configInput counts hconfig input i)

/-- Lookup-selector anchoring obtained from the reduced anchor equations and the
circuit's registration certificate. -/
theorem lookupSelectorsAnchoredBy
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    {configure : ConfigInput → Configure F Config}
    {synthesize : Config → Var Input F → Circuit F (Var Output F)}
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.lookupSelectorAnchorRequirements
        ((configure configInput).output counts) input i) anchor) :
    ((synthesize ((configure configInput).output counts) input).operations i)
      |>.LookupSelectorsAnchoredBy anchor :=
  self.lookupSelectorsAnchoredBy_of_registered
    configInput counts hconfig input i anchor hanchor
    (self.registered configInput counts hconfig input i)

section SynthesisSummary
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}
    {configure : ConfigInput → Configure F Config}
    {synthesize : Config → Var Input F → Circuit F (Var Output F)}

/-- Project exact synthesis columns without exposing unrelated elaborated metadata. -/
@[circuit_norm ↓]
theorem synthesisSummary_columns_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).columns =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).columns :=
  congrArg FloorPlanner.SynthesisSummary.columns
    (self.synthesisSummary_eq config input i)

/-- Project one exact column occupancy without exposing unrelated metadata. -/
@[circuit_norm ↓]
theorem synthesisSummary_columnOccupancy_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex)
    (column : FloorPlanner.RegionColumn) :
    (self.synthesisSummary config input i).columnOccupancy column =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).columnOccupancy column :=
  congrArg (fun summary => summary.columnOccupancy column)
    (self.synthesisSummary_eq config input i)

/-- Project the exact deferred-constant request count without exposing unrelated metadata. -/
@[circuit_norm ↓]
theorem synthesisSummary_constantSiteCount_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).constantSiteCount =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).constantSiteCount :=
  congrArg FloorPlanner.SynthesisSummary.constantSiteCount
    (self.synthesisSummary_eq config input i)

/-- Project the ordered reduced V1 measurement input without exposing the child's
operation stream. -/
@[circuit_norm ↓]
theorem synthesisSummary_regionShapes_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).regionShapes =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).regionShapes :=
  congrArg FloorPlanner.SynthesisSummary.regionShapes
    (self.synthesisSummary_eq config input i)

end SynthesisSummary

end ElaboratedCircuit

/-- Region-level counterpart of `ElaboratedCircuit`. -/
class ElaboratedRegionCircuit (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output]
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F)) where
  configureInfo : ∀ input, ElaboratedConfigure (configure input) := by
    intro input
    try dsimp only [configure]
    infer_instance
  /-- Keygen capabilities supplied by the caller rather than local configure. -/
  keygenRequirements : KeygenRequirements F ConfigInput (Var Input F) := {}
  /-- Region-level configure/synthesis registration certificate. -/
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := configure configInput
    ((synthesize
      (program.output counts) offset input).operations region).Forall
        (RegionOperation.KeygenRegistered
          (keygenRequirements.gates configInput hconfig ++ (program.delta counts).gates)
          (keygenRequirements.lookups configInput hconfig ++ (program.delta counts).lookups)
          (keygenRequirements.fixedColumns configInput hconfig ++
            program.fixedColumns counts)
          (keygenRequirements.permutationColumns configInput hconfig ++
            (program.delta counts).permutationRequests ++
            keygenRequirements.inputPermutationColumns configInput hconfig input)) := by
    keygen_registration
  /-- Region-level copy endpoints are either declared inputs or locally assigned. -/
  copyCellsAssigned :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := configure configInput
    ((synthesize
      (program.output counts) offset input).operations region).CopyCellsAssigned region
        (keygenRequirements.inputCells configInput hconfig input) := by
    keygen_registration
  /-- Every region lookup activation enables its master and only declared selectors. -/
  lookupActivationsWellFormed :
    ∀ (config : Config) (offset : ℕ)
      (input : Var Input F) (region : RegionIndex),
    ((synthesize config offset input).operations region)
      |>.LookupActivationsWellFormed := by
    keygen_registration
  /-- Lookup-local selector valuations agree with every activation in the region. -/
  lookupSelectorAssignmentsAgree_of_registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (_hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := configure configInput
    let operations := (synthesize (program.output counts) offset input).operations region
    (hregistered : operations.Forall
        (RegionOperation.KeygenRegistered
          (keygenRequirements.gates configInput _hconfig ++ (program.delta counts).gates)
          (keygenRequirements.lookups configInput _hconfig ++ (program.delta counts).lookups)
          (keygenRequirements.fixedColumns configInput _hconfig ++
            program.fixedColumns counts)
          (keygenRequirements.permutationColumns configInput _hconfig ++
            (program.delta counts).permutationRequests ++
            keygenRequirements.inputPermutationColumns configInput _hconfig input))) →
      RegionOperations.LookupSelectorAssignmentsAgree operations := by
    intro configInput counts hconfig offset input region program operations hregistered
    solve
    | clear_value operations
      exact RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_noLookups
        hregistered
    | clear_value operations
      apply
        RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
          hregistered
      keygen_registration
    | apply RegionOperations.lookupSelectorAssignmentsAgree_of_forall_isNotLookup
      keygen_registration
    | keygen_registration
  /-- Reduced physical-anchor equations for auxiliary selectors read by this
  region circuit. -/
  lookupSelectorAnchorRequirements :
    Config → ℕ → Var Input F → RegionIndex →
      List (ℕ × FloorPlanner.RegionColumn) := fun _ _ _ _ => []
  /-- The reduced equations physically anchor every auxiliary selector read in
  this region. -/
  lookupSelectorsAnchoredBy_of_registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (_hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex)
      (anchor : ℕ → FloorPlanner.RegionColumn),
    SelectorAnchorRequirementsSatisfied
        (lookupSelectorAnchorRequirements
          ((configure configInput).output counts) offset input region) anchor →
      List.Forall
          (RegionOperation.KeygenRegistered
            (keygenRequirements.gates configInput _hconfig ++
              ((configure configInput).delta counts).gates)
            (keygenRequirements.lookups configInput _hconfig ++
              ((configure configInput).delta counts).lookups)
            (keygenRequirements.fixedColumns configInput _hconfig ++
              (configure configInput).fixedColumns counts)
            (keygenRequirements.permutationColumns configInput _hconfig ++
              ((configure configInput).delta counts).permutationRequests ++
              keygenRequirements.inputPermutationColumns configInput _hconfig input))
        ((synthesize ((configure configInput).output counts) offset input).operations region) →
      RegionOperations.LookupSelectorsAnchoredBy
        ((synthesize ((configure configInput).output counts) offset input).operations region)
        anchor := by
    intro configInput counts hconfig offset input region anchor _ hregistered
    solve
    | exact RegionOperations.LookupSelectorsAnchoredBy.of_registered_noLookups
        hregistered anchor
    | apply
        RegionOperations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
          hregistered (anchor := anchor)
      keygen_registration
    | apply RegionOperations.LookupSelectorsAnchoredBy.of_forall_isNotLookup
      keygen_registration
    | keygen_registration
  output : Config → ℕ → Var Input F → RegionIndex → Var Output F :=
    fun config offset input self =>
      (synthesize config offset input).output self
  /-- Exact footprint contributed inside the ambient region. -/
  synthesisSummary : Config → ℕ → Var Input F → RegionIndex →
      FloorPlanner.RegionSynthesisSummary
  output_eq : ∀ config offset input self,
    output config offset input self =
      (synthesize config offset input).output self := by
    intro _ _ _ _
    rfl
  synthesisSummary_eq : ∀ config offset input self,
    synthesisSummary config offset input self =
      FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations self) := by
    intro _ _ _ _
    first
    | rfl
    | simp only [circuit_norm, RegionCircuit.operations_bind,
        RegionCircuit.operations_pure,
        FloorPlanner.regionSynthesisSummary_append,
        synthesis_summary_norm]
  /-- Region-local fixed writes agree whenever they target one cell. -/
  fixedAssignmentsAgree :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (_hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    ((synthesize ((configure configInput).output counts) offset input).operations region)
      |>.FixedAssignmentsAgree := by
    intro configInput counts _hconfig offset input region
    apply RegionOperations.HasNoFixedAssignments.fixedAssignmentsAgree
    keygen_registration

namespace ElaboratedRegionCircuit

section RegionSynthesisSummary
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}
    {configure : ConfigInput → Configure F Config}
    {synthesize :
      Config → ℕ → Var Input F → RegionCircuit F (Var Output F)}

/-- Region lookup-selector assignment agreement obtained by combining registration
with the circuit-local law. -/
theorem lookupSelectorAssignmentsAgree
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((synthesize ((configure configInput).output counts) offset input).operations region)
      |>.LookupSelectorAssignmentsAgree :=
  self.lookupSelectorAssignmentsAgree_of_registered
    configInput counts hconfig offset input region
    (self.registered configInput counts hconfig offset input region)

/-- Region lookup-selector anchoring obtained from reduced anchor equations and
registration. -/
theorem lookupSelectorsAnchoredBy
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.lookupSelectorAnchorRequirements
        ((configure configInput).output counts) offset input region) anchor) :
    ((synthesize ((configure configInput).output counts) offset input).operations region)
      |>.LookupSelectorsAnchoredBy anchor :=
  self.lookupSelectorsAnchoredBy_of_registered
    configInput counts hconfig offset input region anchor hanchor
    (self.registered configInput counts hconfig offset input region)

@[circuit_norm ↓]
theorem synthesisSummary_columns_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).columns =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).columns :=
  congrArg FloorPlanner.RegionSynthesisSummary.columns
    (self.synthesisSummary_eq config offset input region)

@[circuit_norm ↓]
theorem synthesisSummary_rowCount_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).rowCount =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).rowCount :=
  congrArg FloorPlanner.RegionSynthesisSummary.rowCount
    (self.synthesisSummary_eq config offset input region)

@[circuit_norm ↓]
theorem synthesisSummary_constantSiteCount_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).constantSiteCount =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).constantSiteCount :=
  congrArg FloorPlanner.RegionSynthesisSummary.constantSiteCount
    (self.synthesisSummary_eq config offset input region)

end RegionSynthesisSummary

end ElaboratedRegionCircuit

attribute [keygen_bundle_projection, keygen_requirement_projection,
    keygen_metadata_projection]
  ElaboratedCircuit.keygenRequirements
  ElaboratedRegionCircuit.keygenRequirements

end Halo2
