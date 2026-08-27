import Clean.Halo2.FormalRegion

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

namespace FormalRegionCircuit

/-- The whole region-level `call` runtime pair, packaged with its defining equation behind
an `opaque` reduction barrier; see `FormalCircuit.callPacked` for the two-jobs design. The
implementation applies the child monad `synthesize` **exactly once** and reads both the
output and the operations off that single application (runtime: no metadata
re-materialization); the `opaque` is the kernel + elaborator reduction barrier, and the
packaged `property` re-exposes the equation (`call_eq`/`call_operations`). -/
@[keygen_call_expression]
private opaque callPacked (F : Type) [FiniteField F] (CI Cfg : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] :
    { f : FormalRegionCircuit F CI Cfg Input Output → Cfg → ℕ → Var Input F →
        RegionIndex → Var Output F × RegionOperations F //
      ∀ self config offset input region, f self config offset input region
        = (self.output config offset input region,
           (self.synthesize config offset input).operations region) } :=
  ⟨fun self config offset input region =>
      let r := self.synthesize config offset input region
      (r.1, r.2),
   fun self config offset input region => by
      have h : (self.synthesize config offset input region).1
          = self.output config offset input region :=
        (self.elaborated.output_eq config offset input region).symm
      show ((self.synthesize config offset input region).1,
          (self.synthesize config offset input region).2)
        = (self.output config offset input region,
           (self.synthesize config offset input).operations region)
      rw [h, RegionCircuit.operations]⟩

/-- Call this region circuit as a subcircuit from a parent region circuit: append the
child's operations (in the *same* ambient region), returning the child's output. The
runtime is the `callPacked` shared-application implementation (one child monad application
per call node); the child list stays a folded chunk in parent proofs (the proof boundary),
with `callPacked` the reduction barrier. Rust: calling an `assign_region` helper with the
parent's `region`/`offset`. -/
@[keygen_call_expression]
def call (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) : RegionCircuit F (Var Output F) :=
  fun region => (callPacked F ConfigInput Config Input Output).val self config offset input region

/-- The operation list a region-level `call` contributes — read off the `callPacked`
shared application behind its reduction barrier; see `FormalCircuit.callOps`. NO attribute. -/
def callOps (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) : RegionOperations F :=
  ((callPacked F ConfigInput Config Input Output).val self config offset input region).2

/-- The full region-level `call` pair, re-exposed from the packed `property`: the output
and operations of a single `call` node; see `FormalCircuit.call_eq`. -/
theorem call_eq (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    self.call config offset input region
      = (self.output config offset input region,
         (self.synthesize config offset input).operations region) :=
  (callPacked F ConfigInput Config Input Output).property self config offset input region

/-- Region-circuit analogue of `FormalCircuit.callPacked_output`. -/
@[circuit_norm]
theorem callPacked_output (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((callPacked F ConfigInput Config Input Output).val self config offset input region).1 =
      self.output config offset input region :=
  congrArg (fun t => t.1) ((callPacked F ConfigInput Config Input Output).property
    self config offset input region)

/-- Keep a packed region call opaque while exposing the operation-list projection to
keygen normalization. -/
@[keygen_norm, keygen_spine]
theorem callPacked_operations (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    RegionCircuit.operations
        (fun current => (callPacked F ConfigInput Config Input Output).val
          self config offset input current)
        region =
      ((callPacked F ConfigInput Config Input Output).val
        self config offset input region).2 := rfl

/-- The chunk-opening equation, `callOps`-spelled. NOT `@[circuit_norm]`. -/
theorem callOps_eq (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    self.callOps config offset input region
      = (self.synthesize config offset input).operations region :=
  congrArg (fun t => t.2)
    ((callPacked F ConfigInput Config Input Output).property self config offset input region)

@[circuit_norm, keygen_output_norm]
theorem call_output (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.call config offset input).output region =
      self.output config offset input region :=
  self.callPacked_output config offset input region

/-- The chunk-opening equation for region-level calls; see
`FormalCircuit.call_operations`. NOT `@[circuit_norm]`. -/
theorem call_operations (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    (self.call config offset input).operations region
      = (self.synthesize config offset input).operations region :=
  self.callOps_eq config offset input region

/-- A region call exposes the child's exact reduced synthesis footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((self.call config offset input).operations region) =
      self.elaborated.synthesisSummary config offset input region := by
  rw [self.call_operations]
  exact (self.elaborated.synthesisSummary_eq config offset input region).symm

@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary' {Output : TypeMap} [ProvableType Output]
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (@RegionCircuit.operations F _ (Output (AssignedCell F))
          (self.call config offset input) region) =
      self.elaborated.synthesisSummary config offset input region :=
  self.call_synthesisSummary config offset input region

/-- A child's reduced footprint proves that its opaque call performs no fixed writes. -/
@[keygen_norm, keygen_helper]
theorem call_hasNoFixedAssignments
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex)
    (hsummary :
      (self.elaborated.synthesisSummary config offset input region)
        |>.HasNoFixedColumns) :
    RegionOperations.HasNoFixedAssignments
      ((self.call config offset input).operations region) := by
  apply FloorPlanner.RegionSynthesisSummary.HasNoFixedColumns.hasNoFixedAssignments
  rwa [self.call_synthesisSummary]

/-- A configured region call inherits the child's fixed-assignment law. -/
theorem call_fixedAssignmentsAgree
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((self.call config offset input).operations region)
      |>.FixedAssignmentsAgree := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.fixedAssignmentsAgree
    configInput counts hconfig offset input region

/-- A fixed-stride loop of region-circuit calls reduces to the fold of the children'
already-reduced summaries. The result is the synthesis-summary normal form for
composite gadgets built from homogeneous child circuits. -/
@[synthesis_summary_norm]
theorem forRange'_call_synthesisSummary
    (circuits : ℕ → FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset stride count : ℕ)
    (inputs : ℕ → Var Input F) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((RegionCircuit.forRange' offset stride count fun i row => do
          let _ ← (circuits i).call config row (inputs i)
          pure ()).operations region) =
      (List.ofFn fun i : Fin count =>
        (circuits i.val).elaborated.synthesisSummary config
          (offset + i.val * stride) (inputs i.val) region).foldr
            FloorPlanner.RegionSynthesisSummary.combine {} := by
  rw [RegionCircuit.forRange'_regionSynthesisSummary]
  apply congrArg (List.foldr FloorPlanner.RegionSynthesisSummary.combine {})
  apply congrArg List.ofFn
  funext i
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    List.append_nil]
  exact (circuits i.val).call_synthesisSummary config
    (offset + i.val * stride) (inputs i.val) region

/-- Consume a region circuit's configure certificate without exposing routing premises. -/
@[keygen_norm]
theorem call_keygenRegistered_ofCertificate
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (hinputPermutationColumns : ∀ column,
      column ∈ certificate.configured.inputPermutationColumns input →
      column ∈ context.permutationColumns) :
    ((self.call config offset input).operations region).Forall
      (RegionOperation.KeygenRegistered context.gates context.lookups
        context.fixedColumns context.permutationColumns) := by
  rcases certificate with
    ⟨configInput, counts, hconfig, output_eq, gates, lookups, fixedColumns,
      permutationColumns⟩
  subst config
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (self.elaborated.registered
      configInput counts hconfig offset input region)
    gates lookups fixedColumns (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact permutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column (by
          simpa [Configured.inputPermutationColumns,
            ConfigurationCertificate.configured] using hcolumn))

/--
Region-level counterpart of `FormalCircuit.call_keygenRegistered`.
-/
@[keygen_norm, keygen_call]
theorem call_keygenRegistered
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ Configured.fixedColumns hconfigured →
        column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputCells : (Configured.inputCells hconfigured input).Forall fun cell =>
      cell.column ∈ targetPermutationColumns) :
    ((self.call config offset input).operations region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetFixedColumns targetPermutationColumns) := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (self.elaborated.registered
      configInput counts hconfig offset input region)
    (by simpa [Configured.gates] using hgates)
    (by simpa [Configured.lookups] using hlookups)
    (by simpa [Configured.fixedColumns] using hfixedColumns)
    (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact hpermutationColumns column (by
          simpa [Configured.permutationColumns] using hcolumn)
      · rw [KeygenRequirements.inputPermutationColumns,
          List.mem_map] at hcolumn
        obtain ⟨cell, hcell, rfl⟩ := hcolumn
        exact List.forall_iff_forall_mem.mp hinputCells cell (by
          simpa [Configured.inputCells] using hcell))

/-- Region-level registration certificate specialized to a configure output. -/
theorem call_keygenRegistered_ofOutput
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (hgates : ∀ gate,
      gate ∈ self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates →
      gate ∈ targetGates)
    (hlookups : ∀ argument,
      argument ∈ self.keygenRequirements.lookups configInput hconfig ++
        ((self.configure configInput).delta counts).lookups →
      argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ self.keygenRequirements.fixedColumns configInput hconfig ++
        (self.configure configInput).fixedColumns counts →
      column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ self.keygenRequirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputCells :
      (self.keygenRequirements.inputCells configInput hconfig input).Forall fun cell =>
        cell.column ∈ targetPermutationColumns) :
    ((self.call ((self.configure configInput).output counts) offset input).operations
      region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetFixedColumns targetPermutationColumns) := by
  apply self.call_keygenRegistered _
      (Configured.ofOutput self configInput counts hconfig)
  · simpa [Configured.gates, Configured.ofOutput] using hgates
  · simpa [Configured.lookups, Configured.ofOutput] using hlookups
  · simpa [Configured.fixedColumns, Configured.ofOutput] using hfixedColumns
  · simpa [Configured.permutationColumns, Configured.ofOutput] using
      hpermutationColumns
  · simpa [Configured.inputCells, Configured.ofOutput] using hinputCells

/-- Region-level exact-arguments counterpart of
`FormalCircuit.call_keygenRegistered_exact`. -/
theorem call_keygenRegistered_exact
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((self.call config offset input).operations region).Forall
      (RegionOperation.KeygenRegistered
        hconfigured.gates hconfigured.lookups
          hconfigured.fixedColumns
          (hconfigured.permutationColumns ++
            hconfigured.inputPermutationColumns input)) :=
  self.call_keygenRegistered config hconfigured offset input region
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => List.mem_append_left _ h)
    (List.forall_iff_forall_mem.mpr fun _ h =>
      List.mem_append_right _ <| List.mem_map_of_mem h)

/-- Every fixed write performed by a configured child uses one of the fixed
columns declared by that child. -/
theorem fixedColumn_mem_of_mem_call
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (column : Column .fixed) (row : ℕ) (value : F)
    (hassignment : .assignFixed column row value ∈
      (self.call config offset input).operations region) :
    column ∈ hconfigured.fixedColumns := by
  have hregistered := List.forall_iff_forall_mem.mp
    (self.call_keygenRegistered_exact config hconfigured offset input region)
      _ hassignment
  exact hregistered

/-- A region child call's packaged copy-provenance law remains valid in any caller
state containing its declared input cells. -/
@[keygen_norm, keygen_call]
theorem call_copyCellsAssignedFrom
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {available : List Cell}
    (hinputCells : ∀ cell,
      cell ∈ Configured.inputCells hconfigured input → cell ∈ available) :
    ((self.call config offset input).operations region)
      |>.CopyCellsAssignedFrom region available := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  apply (self.elaborated.copyCellsAssigned
    configInput counts hconfig offset input region).mono
  simpa [Configured.inputCells] using hinputCells

/-- Region copy provenance in the opaque spelling exposed after spine normalization. -/
@[keygen_call]
theorem callPacked_copyCellsAssignedFrom
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {available : List Cell}
    (hinputCells : ∀ cell,
      cell ∈ Configured.inputCells hconfigured input → cell ∈ available) :
    (((callPacked F ConfigInput Config Input Output).val self
      config offset input region).2).CopyCellsAssignedFrom region available :=
  self.call_copyCellsAssignedFrom config hconfigured offset input region hinputCells

/-- Lookup activations in a region child call obey the lookup's local selector declaration. -/
@[keygen_call]
theorem call_lookupActivationsWellFormed
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((self.call config offset input).operations region)
      |>.LookupActivationsWellFormed := by
  rw [self.call_operations]
  exact self.elaborated.lookupActivationsWellFormed
    config offset input region

/-- Region lookup-activation certificate in the opaque call spelling. -/
@[keygen_call]
theorem callPacked_lookupActivationsWellFormed
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config offset input region).2)
        |>.LookupActivationsWellFormed :=
  self.call_lookupActivationsWellFormed
    config offset input region

/-- Lookup-selector assignment agreement inherited by a region child call. -/
@[keygen_call]
theorem call_lookupSelectorAssignmentsAgree
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    ((self.call config offset input).operations region)
      |>.LookupSelectorAssignmentsAgree := by
  rcases configured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.lookupSelectorAssignmentsAgree
    configInput counts hconfig offset input region

@[keygen_call]
theorem callPacked_lookupSelectorAssignmentsAgree
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config offset input region).2).LookupSelectorAssignmentsAgree :=
  self.call_lookupSelectorAssignmentsAgree
    config configured offset input region

/-- Physical lookup-selector anchoring inherited by a region child call. -/
@[keygen_call]
theorem call_lookupSelectorsAnchoredBy
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.elaborated.lookupSelectorAnchorRequirements
        config offset input region) anchor) :
    ((self.call config offset input).operations region)
      |>.LookupSelectorsAnchoredBy anchor := by
  rcases configured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.lookupSelectorsAnchoredBy
    configInput counts hconfig offset input region anchor hanchor

@[keygen_call]
theorem callPacked_lookupSelectorsAnchoredBy
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.elaborated.lookupSelectorAnchorRequirements
        config offset input region) anchor) :
    (((callPacked F ConfigInput Config Input Output).val self
      config offset input region).2).LookupSelectorsAnchoredBy anchor :=
  self.call_lookupSelectorsAnchoredBy
    config configured offset input region anchor hanchor

/-- Region registration certificate in the opaque spelling exposed after spine
normalization. -/
@[keygen_call]
theorem callPacked_keygenRegistered
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ Configured.fixedColumns hconfigured →
        column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputCells : (Configured.inputCells hconfigured input).Forall fun cell =>
      cell.column ∈ targetPermutationColumns) :
    (((callPacked F ConfigInput Config Input Output).val
      self config offset input region).2).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetFixedColumns targetPermutationColumns) :=
  call_keygenRegistered self config hconfigured offset input region hgates hlookups
    hfixedColumns hpermutationColumns hinputCells

/--
A lawful region child remains registered when called inside a parent whose available
argument lists contain the child's requirements and configure contribution.
-/
theorem KeygenLawful.call_registered
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : self.KeygenLawful requirements)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : requirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ requirements.gates configInput hconfig ++
          ((self.configure configInput).delta counts).gates →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ requirements.lookups configInput hconfig ++
          ((self.configure configInput).delta counts).lookups →
        argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ requirements.fixedColumns configInput hconfig ++
        (self.configure configInput).fixedColumns counts →
      column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ requirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈
        requirements.inputPermutationColumns configInput hconfig input →
      column ∈ targetPermutationColumns) :
    ((self.call
      ((self.configure configInput).output counts)
      offset input).operations region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetFixedColumns targetPermutationColumns) := by
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (FormalRegionCircuit.KeygenLawful.registered
      hlawful configInput counts hconfig offset input region)
    hgates hlookups hfixedColumns (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact hpermutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column hcolumn)

end FormalRegionCircuit

end Halo2
