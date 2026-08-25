import Clean.Halo2.Formal

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

namespace FormalCircuit

variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- The whole `call` runtime triple, packaged with its defining equation behind an
`opaque` reduction barrier. One mechanism, two jobs:

* **Runtime (the perf fix).** The implementation applies the child monad `synthesize`
  **exactly once** (`let r := self.synthesize config input i`) and reads all three
  components off that single application. `opaque` initializers still *run* at runtime, so
  this sharing — not the opacity — is what stops a call node from re-materializing its
  child: no bundle's metadata shape (e.g. a spine bundle's recompute-shaped `output`
  field, which re-runs the whole child monad) can ever cause re-evaluation, because the
  runtime never reads the metadata fields at all (they are proof-side only). This kills the
  ~2^depth blow-up where each nesting level materialized its child 2–3×.
* **Proofs (the reduction barrier).** `@[irreducible]` would not suffice: the kernel
  ignores reducibility attributes, so defeq-replayed simp steps in big parent proofs would
  evaluate straight through `synthesize` into the whole child op tree (the job the retired
  `.subcircuit` constructor head used to do). `opaque` is neutral for the kernel *and* the
  elaborator across all three components; the packaged `property` re-exposes the defining
  equation as a *recorded* rewrite (`call_eq`/`call_operations` below). -/
@[keygen_call_expression]
private opaque callPacked (F : Type) [FiniteField F] (CI Cfg : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] :
    { f : FormalCircuit F CI Cfg Input Output → Cfg → Var Input F → RegionIndex →
        Var Output F × Operations F × RegionIndex //
      ∀ self config input i, f self config input i
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount input) } :=
  ⟨fun self config input i =>
      let r := self.synthesize config input i
      (r.1, r.2.1, i + self.regionCount input),
   fun self config input i => by
      -- componentwise: `output` component is exactly the elaborated `output_eq`, the
      -- other two are the `Circuit.operations`/`Circuit.nextRegionIndex` projections
      have h : (self.synthesize config input i).1 = self.output config input i :=
        (self.elaborated.output_eq config input i).symm
      show ((self.synthesize config input i).1, (self.synthesize config input i).2.1,
          i + self.regionCount input)
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount input)
      rw [h, Circuit.operations]⟩

/-- Call this circuit as a subcircuit from a parent layouter circuit: append the child's
operations, return the child's output, advance the region counter by `regionCount`. The
runtime is the `callPacked` shared-application implementation (one child monad application
per call node); the child list stays a folded chunk in parent proofs (the proof boundary,
isolated by `constraints_append`), with `callPacked` the reduction barrier for all three
components. Rust: calling a chip method. -/
@[keygen_call_expression]
def call (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) : Circuit F (Var Output F) :=
  fun i => (callPacked F ConfigInput Config Input Output).val self config input i

/-- The operation list a `call` contributes: the child's own operations, read off the
`callPacked` shared application (so no metadata re-materialization) behind its reduction
barrier. Consumers never unfold this; they rewrite with `call_operations`. NO attribute —
the opaque underneath is the barrier. -/
def callOps (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) (i : RegionIndex) : Operations F :=
  ((callPacked F ConfigInput Config Input Output).val self config input i).2.1

/-- The full `call` triple, re-exposed from the packed `property`: output, operations, and
next region index of a single `call` node. The public handle downstream proofs use to open
any component of the (otherwise opaque) `call`. -/
theorem call_eq (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    self.call config input i
      = (self.output config input i, (self.synthesize config input).operations i,
         i + self.regionCount input) :=
  (callPacked F ConfigInput Config Input Output).property self config input i

/-- The output projection of the opaque packed-call implementation is the circuit's declared
output. This is the normalization boundary used when reduction exposes the packed runtime form
before the public `call` accessor can be recognized. -/
@[circuit_norm]
theorem callPacked_output (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    ((callPacked F ConfigInput Config Input Output).val self config input i).1 =
      self.output config input i :=
  congrArg (fun t => t.1) ((callPacked F ConfigInput Config Input Output).property
    self config input i)

/-- The operation projection of a packed circuit call is the public call's operation
stream. -/
@[keygen_norm, keygen_spine]
theorem callPacked_operations (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    ((callPacked F ConfigInput Config Input Output).val self config input i).2.1 =
      (self.call config input).operations i := rfl

/-- The packed call under the `Circuit.operations` projection used by monadic
composition. -/
@[keygen_norm, keygen_spine]
theorem callPacked_circuit_operations
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    Circuit.operations
        (fun current => (callPacked F ConfigInput Config Input Output).val
          self config input current)
        i =
      ((callPacked F ConfigInput Config Input Output).val
        self config input i).2.1 := rfl

/-- The chunk-opening equation, `callOps`-spelled (for sites that unfolded
`call`/`operations` first). NOT `@[circuit_norm]`. -/
theorem callOps_eq (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    self.callOps config input i = (self.synthesize config input).operations i :=
  congrArg (fun t => t.2.1)
    ((callPacked F ConfigInput Config Input Output).property self config input i)

@[circuit_norm, keygen_output_norm]
theorem call_output (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.call config input).output i = self.output config input i :=
  self.callPacked_output config input i

/-- The chunk-opening equation: a `call`'s operations are the child's `synthesize`
operations. Deliberately NOT `@[circuit_norm]` — chunks stay folded in parent proofs;
this is the bridge the framework leaves (`Subcircuit.lean`, `subcircuit_rw`) rewrite
with. -/
theorem call_operations (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.call config input).operations i
      = (self.synthesize config input).operations i :=
  self.callOps_eq config input i

/-- A call exposes the child's exact reduced synthesis footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    FloorPlanner.synthesisSummary ((self.call config input).operations i) =
      self.elaborated.synthesisSummary config input i := by
  rw [self.call_operations]
  exact (self.elaborated.synthesisSummary_eq config input i).symm

/-- A configured layouter-level call inherits its child's fixed-write law. -/
theorem call_fixedWritesLawful
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (region : RegionIndex) :
    ((self.call config input).operations region)
      |>.FixedWritesLawful configured.constantColumns := by
  rcases configured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.fixedWritesLawful
    configInput counts hconfig input region

/-- A configured call inherits the region-agreement component independently of the
parent's constant-column capability. -/
theorem call_fixedAssignmentsAgree
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (region : RegionIndex) :
    ((self.call config input).operations region).Forall
      Operation.FixedAssignmentsAgree :=
  (self.call_fixedWritesLawful config configured input region)
    |>.regionAssignmentsAgree

/-- A fixed column appearing in a configured circuit's exact reduced synthesis
summary belongs to that circuit's declared fixed-column interface. -/
theorem Configured.mem_fixedColumns_of_mem_synthesisSummary
    (self : FormalCircuit F ConfigInput Config Input Output)
    {config : Config} (configured : self.Configured config)
    (input : Var Input F) (region : RegionIndex) (index : ℕ)
    (hcolumn : .column .fixed index ∈
      (self.elaborated.synthesisSummary config input region).columns) :
    (Column.mk index : Column .fixed) ∈ configured.fixedColumns := by
  rcases configured with ⟨configInput, counts, hconfig, houtput⟩
  subst config
  have hactual : .column .fixed index ∈
      (FloorPlanner.synthesisSummary
        ((self.synthesize ((self.configure configInput).output counts) input).operations
          region)).columns := by
    rw [← self.elaborated.synthesisSummary_columns_eq]
    exact hcolumn
  exact (self.elaborated.registered configInput counts hconfig input region)
    |>.mem_fixedColumns_of_mem_regionFixedColumns
      (Operations.mem_regionFixedColumns_of_mem_synthesisSummary_column hactual)

@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    FloorPlanner.synthesisSummary
        (@Circuit.operations F _ (Output (AssignedCell F))
          (self.call config input) i) =
      self.elaborated.synthesisSummary config input i :=
  self.call_synthesisSummary config input i

/-- A child's reduced footprint proves that its opaque layouter call performs no
fixed writes. -/
@[keygen_norm, keygen_helper]
theorem call_hasNoFixedWrites
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex)
    (hsummary :
      (self.elaborated.synthesisSummary config input i).HasNoFixedWrites) :
    Operations.HasNoFixedWrites
      ((self.call config input).operations i) := by
  apply FloorPlanner.SynthesisSummary.HasNoFixedWrites.hasNoFixedWrites
  rwa [self.call_synthesisSummary]

/--
Consume a configure certificate directly. Unlike `call_keygenRegistered`, this exposes
no gate-by-gate routing obligations to the parent.
-/
@[keygen_norm]
theorem call_keygenRegistered_ofCertificate
    (self : FormalCircuit F ConfigInput Config Input Output)
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context)
    (input : Var Input F) (i : RegionIndex)
    (hinputPermutationColumns : ∀ column,
      column ∈ certificate.configured.inputPermutationColumns input →
      column ∈ context.permutationColumns) :
    ((self.call config input).operations i).KeygenRegistered
      context.gates context.lookups context.fixedColumns
        context.permutationColumns := by
  rcases certificate with
    ⟨configInput, counts, hconfig, output_eq, gates, lookups, fixedColumns,
      permutationColumns⟩
  subst config
  rw [self.call_operations]
  exact (self.elaborated.registered
    configInput counts hconfig input i).mono gates lookups fixedColumns (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact permutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column (by
          simpa [Configured.inputPermutationColumns,
            ConfigurationCertificate.configured] using hcolumn))

/--
An embedded registration certificate closes a child call against any larger ambient
gate, lookup, and equality-column sets. This is the compositional leaf used by
`keygen_registration`.
-/
@[keygen_norm, keygen_call]
theorem call_keygenRegistered
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
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
    ((self.call config input).operations i).KeygenRegistered
      targetGates targetLookups targetFixedColumns targetPermutationColumns := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact (self.elaborated.registered
    configInput counts hconfig input i).mono
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

/-- Registration certificate specialized to a configure output. Its premises expose
the caller requirements and local configure delta directly. -/
theorem call_keygenRegistered_ofOutput
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex)
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
    ((self.call
      ((self.configure configInput).output counts) input).operations i).KeygenRegistered
        targetGates targetLookups targetFixedColumns targetPermutationColumns := by
  apply self.call_keygenRegistered _
      (Configured.ofOutput self configInput counts hconfig)
  · simpa [Configured.gates, Configured.ofOutput] using hgates
  · simpa [Configured.lookups, Configured.ofOutput] using hlookups
  · simpa [Configured.fixedColumns, Configured.ofOutput] using hfixedColumns
  · simpa [Configured.permutationColumns, Configured.ofOutput] using
      hpermutationColumns
  · simpa [Configured.inputCells, Configured.ofOutput] using hinputCells

/-- A folded call is registered in exactly the arguments carried by its configured
handle. This conclusion shape exposes every input needed by `grind`. -/
theorem call_keygenRegistered_exact
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) :
    ((self.call config input).operations i).KeygenRegistered
      hconfigured.gates hconfigured.lookups
        hconfigured.fixedColumns
        (hconfigured.permutationColumns ++
          hconfigured.inputPermutationColumns input) :=
  self.call_keygenRegistered config hconfigured input i
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => List.mem_append_left _ h)
    (List.forall_iff_forall_mem.mpr fun _ h =>
      List.mem_append_right _ <| List.mem_map_of_mem h)

/-- A child call's packaged copy-provenance law remains valid in any caller state
containing its declared input cells. -/
@[keygen_norm, keygen_call]
theorem call_copyCellsAssignedFrom
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) {available : List Cell}
    (hinputCells : ∀ cell,
      cell ∈ Configured.inputCells hconfigured input → cell ∈ available) :
    ((self.call config input).operations i).CopyCellsAssignedFrom i available := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  apply (self.elaborated.copyCellsAssigned
    configInput counts hconfig input i).mono
  simpa [Configured.inputCells] using hinputCells

/-- Copy provenance composes through a monadic bind when the first circuit's
`nextRegionIndex` agrees with the region count of its operation stream. -/
theorem bind_copyCellsAssignedFrom
    {α β : Type} (first : Circuit F α) (next : α → Circuit F β)
    (region : RegionIndex) (available : List Cell)
    (hfirst : (first.operations region).CopyCellsAssignedFrom region available)
    (hnextRegion : first.nextRegionIndex region =
      region + (first.operations region).regionCount)
    (hnext : ((next (first.output region)).operations
      (first.nextRegionIndex region)).CopyCellsAssignedFrom
        (first.nextRegionIndex region)
        (available ++ (first.operations region).assignedCellsFrom region)) :
    (((first >>= next).operations region).CopyCellsAssignedFrom region available) := by
  rw [Circuit.operations_bind]
  apply hfirst.append
  rwa [← hnextRegion]

/-- Copy provenance composes through one public-instance constraint. -/
theorem constrainInstance_bind_copyCellsAssignedFrom
    {Output : Type} (cell : AssignedCell F) (column : Column .instance)
    (row : ℕ) (next : Unit → Circuit F Output) (region : RegionIndex)
    (available : List Cell) (hcell : cell.cell ∈ available)
    (hnext : ((next ()).operations region).CopyCellsAssignedFrom
      region available) :
    (((constrainInstance cell column row >>= next).operations region)
      |>.CopyCellsAssignedFrom region available) := by
  simp only [Circuit.operations_bind, operations_constrainInstance,
    nextRegionIndex_constrainInstance, constrainInstance, Circuit.output,
    List.cons_append, List.nil_append,
    Operations.copyCellsAssignedFrom_constrainInstance_iff]
  exact ⟨hcell, hnext⟩

/-- Copy provenance composes across a formal-circuit call without opening the
child's operation stream. -/
theorem call_bind_copyCellsAssignedFrom
    {β : Type}
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (next : Var Output F → Circuit F β)
    (region : RegionIndex) (available : List Cell)
    (hinput : ∀ cell, cell ∈ configured.inputCells input → cell ∈ available)
    (hnext : ((next (self.output config input region)).operations
      (region + self.regionCount input)).CopyCellsAssignedFrom
        (region + self.regionCount input)
        (available ++ ((self.call config input).operations region).assignedCellsFrom
          region)) :
    (((self.call config input >>= next).operations region)
      |>.CopyCellsAssignedFrom region available) := by
  have hnextRegion :
      (self.call config input).nextRegionIndex region =
        region + self.regionCount input := by
    show (self.call config input region).2.2 = region + self.regionCount input
    rw [self.call_eq]
  apply bind_copyCellsAssignedFrom
  · exact self.call_copyCellsAssignedFrom config configured input region hinput
  · rw [hnextRegion, FormalCircuit.regionCount,
      self.elaborated.regionCount_eq, self.call_operations]
  · rw [hnextRegion, self.call_output]
    exact hnext

/-- Copy provenance in the opaque call spelling exposed after spine normalization. -/
@[keygen_call]
theorem callPacked_copyCellsAssignedFrom
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) {available : List Cell}
    (hinputCells : ∀ cell,
      cell ∈ Configured.inputCells hconfigured input → cell ∈ available) :
    (((callPacked F ConfigInput Config Input Output).val self
      config input i).2.1).CopyCellsAssignedFrom i available :=
  self.call_copyCellsAssignedFrom config hconfigured input i hinputCells

/-- Lookup activations in a child call obey the lookup's local selector declaration. -/
@[keygen_call]
theorem call_lookupActivationsWellFormed
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config)
    (input : Var Input F) (i : RegionIndex) :
    ((self.call config input).operations i).LookupActivationsWellFormed := by
  rw [self.call_operations]
  exact self.elaborated.lookupActivationsWellFormed config input i

/-- Lookup-activation certificate in the opaque call spelling. -/
@[keygen_call]
theorem callPacked_lookupActivationsWellFormed
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config)
    (input : Var Input F) (i : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config input i).2.1)
        |>.LookupActivationsWellFormed :=
  self.call_lookupActivationsWellFormed config input i

/-- Lookup-selector assignment agreement inherited by a layouter child call. -/
@[keygen_call]
theorem call_lookupSelectorAssignmentsAgree
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) :
    ((self.call config input).operations i).LookupSelectorAssignmentsAgree := by
  rcases configured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.lookupSelectorAssignmentsAgree
    configInput counts hconfig input i

@[keygen_call]
theorem callPacked_lookupSelectorAssignmentsAgree
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config input i).2.1).LookupSelectorAssignmentsAgree :=
  self.call_lookupSelectorAssignmentsAgree config configured input i

/-- Physical lookup-selector anchoring inherited by a layouter child call. -/
@[keygen_call]
theorem call_lookupSelectorsAnchoredBy
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.elaborated.lookupSelectorAnchorRequirements config input i)
      anchor) :
    ((self.call config input).operations i).LookupSelectorsAnchoredBy anchor := by
  rcases configured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact self.elaborated.lookupSelectorsAnchoredBy
    configInput counts hconfig input i anchor hanchor

@[keygen_call]
theorem callPacked_lookupSelectorsAnchoredBy
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (configured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied
      (self.elaborated.lookupSelectorAnchorRequirements config input i)
      anchor) :
    (((callPacked F ConfigInput Config Input Output).val self
      config input i).2.1).LookupSelectorsAnchoredBy anchor :=
  self.call_lookupSelectorsAnchoredBy
    config configured input i anchor hanchor

/-- Registration certificate in the exact opaque spelling exposed after operation-spine
normalization. -/
@[keygen_call]
theorem callPacked_keygenRegistered
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
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
      self config input i).2.1).KeygenRegistered targetGates targetLookups
        targetFixedColumns targetPermutationColumns :=
  call_keygenRegistered self config hconfigured input i hgates hlookups
    hfixedColumns hpermutationColumns hinputCells

/--
A lawful layouter child remains registered when called inside a parent whose available
argument lists contain the child's requirements and configure contribution.
-/
theorem KeygenLawful.call_registered
    {self : FormalCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : self.KeygenLawful requirements)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : requirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex)
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
      input).operations i).KeygenRegistered targetGates targetLookups
        targetFixedColumns targetPermutationColumns := by
  rw [self.call_operations]
  exact (FormalCircuit.KeygenLawful.registered
    hlawful configInput counts hconfig input i).mono hgates hlookups hfixedColumns
      (by
        intro column hcolumn
        simp only [List.mem_append] at hcolumn
        rcases hcolumn with hcolumn | hcolumn
        · exact hpermutationColumns column (by
            simpa only [List.mem_append] using hcolumn)
        · exact hinputPermutationColumns column hcolumn)

/-!
The consumption mechanism for `call` chunks lives in `Subcircuit.lean` (framework leaf
lemmas over the folded `(call …).operations` term) and `Tactics/SubcircuitRw.lean` (the
polarity-aware rewriter applying them). Extractor composition: a parent whose `Witness`
includes a child's builds `extract` by calling the child's `extract` on the child's
region range — knowledge soundness composes through the call tree by construction.
TODO: `SubcircuitsConsistent` wellformedness (child cells reference the ambient region
range `[i₀, i₀ + regionCount)`), discharged by the monad's structure.
-/


end FormalCircuit

end Halo2
