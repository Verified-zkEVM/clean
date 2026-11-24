import Midnight.SHA256.Semantics.Preimage
import Midnight.SHA256.Semantics.Structural
import Clean.Halo2.Formal

/-! The fixed Midnight SHA-256 preimage example as a Clean assertion bundle. `formal` takes the
source configuration as explicit keygen capabilities, since this absolute-column example allocates
no relative columns. `configuredFormal` is the same assertion over SHA-256's Clean configure
program, which the Midnight backend compiles to `SHA256.configured`. Synthesis uses the columns that
program allocates from empty counts, so `configure` returns its start counts; from any other start
synthesis emits blank regions and `EnvAssumptions` is false. The witness extractor and public
statement are fixed here, not chosen by a prover. Constructive witness execution
(`WitnessComplete`) is a separate contract from `FormalCircuit`'s completeness field. -/
namespace Midnight.SHA256.Semantics.Preimage
open Halo2

attribute [local irreducible] circuit WitnessCircuit.preimageCircuit extractedMessage publicDigest Spec.digest
  cleanGates cleanLookups StructuralBase.fixedColumns StructuralBase.permutationColumns
  Synthesis.operations Synthesis.toOperations Synthesis.schedule

/-- An assertion drops only the returned array; every source operation is retained. -/
def assertion : Circuit F Unit := do
  let _ ← circuit
  pure ()

theorem assertion_operations (self : RegionIndex) : assertion.operations self = circuit.operations self := by
  unfold assertion
  change _ ++ [] = _
  exact List.append_nil _

deriving instance DecidableEq for ConfigureCounts

/-- The counts a configure program starts from. -/
def startCounts : Configure F ConfigureCounts := ⟨fun counts => (counts, {}, {})⟩

/-- `startCounts` emits nothing: `pure`'s metadata. -/
instance : ElaboratedConfigure startCounts where
  constraintDegree _ := 3
  constraintDegree_eq _ := rfl
  instanceQueries_eq _ := rfl
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated counts _ :=
    (ElaboratedConfigure.pure (F := F) ()).selectorsAllocated counts trivial
  lookupSelectorsCompatible counts _ :=
    (ElaboratedConfigure.pure (F := F) ()).lookupSelectorsCompatible counts trivial
  queryRequirements _ := True
  queriesLawful counts _ := (ElaboratedConfigure.pure (F := F) ()).queriesLawful counts trivial

/-- SHA-256's Clean configure program, returning the counts it starts from. -/
def configure (_ : Unit) : Configure F ConfigureCounts := do
  let start ← startCounts
  Frontend.SHA256.configure
  return start

noncomputable instance (input : Unit) : ElaboratedConfigure (configure input) := by
  unfold configure
  elaborate_configure

theorem configure_output (input : Unit) (counts : ConfigureCounts) :
    (configure input).output counts = counts := by
  simp only [configure, Configure.output_bind, Configure.output_pure]
  rfl

/-! From empty counts, configure emits exactly the gates and lookups synthesis enables, and covers
its fixed and equality columns. The kernel evaluates the configure program. -/

theorem configure_gates : ((configure ()).delta {}).gates = cleanGates := by
  decide +kernel

theorem configure_lookups : ((configure ()).delta {}).lookups = cleanLookups := by
  decide +kernel

theorem configure_fixedColumns : (configure ()).fixedColumns {} = StructuralBase.fixedColumns := by
  decide +kernel

theorem configure_permutation : ∀ column ∈ StructuralBase.permutationColumns,
    column ∈ ((configure ()).delta {}).permutationRequests := by
  decide +kernel

theorem configure_constants : ((configure ()).delta {}).constants = [] := by
  decide +kernel

/-- 690 empty regions, as many as the assertion has. -/
def blank : Circuit F Unit := fun i => ((), List.replicate 690 (.region "" []), i + 690)

theorem blank_operations (i : RegionIndex) :
    blank.operations i = List.replicate 690 (.region "" [] : Operation F) :=
  rfl

private theorem mem_blank {i : RegionIndex} {operation : Operation F}
    (h : operation ∈ blank.operations i) : operation = .region "" [] :=
  (List.mem_replicate.mp h).2

private theorem regionCount_replicate (n : ℕ) :
    Operations.regionCount (List.replicate n (.region "" [] : Operation F)) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Operations.regionCount, ih]
    omega

/-- The assertion from empty counts, where its absolute columns are configure's. -/
def synthesizeFrom (start : ConfigureCounts) (_ : Var unit F) : Circuit F (Var unit F) :=
  if start = {} then assertion else blank

theorem synthesizeFrom_empty (input : Var unit F) : synthesizeFrom {} input = assertion := by
  simp [synthesizeFrom]

theorem synthesizeFrom_of_ne {start : ConfigureCounts} (h : start ≠ {}) (input : Var unit F) :
    synthesizeFrom start input = blank := by
  simp [synthesizeFrom, h]

/-- The synthesis footprint, by start. -/
def summary (start : ConfigureCounts) : FloorPlanner.SynthesisSummary :=
  if start = {} then FloorPlanner.synthesisSummary StructuralBase.source
  else FloorPlanner.synthesisSummary (List.replicate 690 (.region "" [] : Operation F))

theorem summary_empty :
    summary {} = FloorPlanner.synthesisSummary StructuralBase.source := by
  simp only [summary, ↓reduceIte]

theorem summary_of_ne {start : ConfigureCounts} (h : start ≠ {}) :
    summary start =
      FloorPlanner.synthesisSummary (List.replicate 690 (.region "" [] : Operation F)) := by
  simp only [summary, h, ↓reduceIte]

def synthesize (_ : Unit) (_ : Var unit F) : Circuit F (Var unit F) := assertion

def requirements : KeygenRequirements F Unit (Var unit F) where
  gates _ _ := cleanGates
  lookups _ _ := cleanLookups
  fixedColumns _ _ := StructuralBase.fixedColumns
  permutationColumns _ _ := StructuralBase.permutationColumns

/-- Private message plus the fixed native instance statement. Neither component
can be supplied independently of its actual environment coordinates. -/
abbrev WitnessData (_ : Type) := Spec.Message × Vector Nat 32

def extractWitness (self : RegionIndex) (env : Placed Environment F) : WitnessData F :=
  (extractedMessage self env, publicDigest env.env)

def assertionSpec (witness : WitnessData F) : Prop :=
  Spec.Bytes witness.1 ∧ witness.2 = Spec.digest witness.1

def proverAssumptions (witness : WitnessData F) (hint : ProverHint F) : Prop :=
  Spec.Bytes (hintMessage hint) ∧ witness.2 = Spec.digest (hintMessage hint)

def proverSpec (witness : WitnessData F) (hint : ProverHint F) : Prop :=
  witness.1 = hintMessage hint ∧ assertionSpec witness

/-- Full source structural metadata from empty counts, transported through the witness-bearing
program and arbitrary region starts; nothing is required of the caller. -/
@[implicit_reducible] noncomputable def configuredElaborated :
    ElaboratedCircuit F Unit ConfigureCounts unit unit configure synthesizeFrom where
  configureInfo _ := inferInstance
  registered := by
    rintro ⟨⟩ counts _ input self
    simp only [configure_output]
    by_cases hstart : counts = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      refine (Structural.registered privatePrograms self).mono ?_ ?_ ?_ ?_
      · intro gate hgate
        exact List.mem_append_right _ (by rw [configure_gates]; exact hgate)
      · intro argument hargument
        exact List.mem_append_right _ (by rw [configure_lookups]; exact hargument)
      · intro column hcolumn
        exact List.mem_append_right _ (by rw [configure_fixedColumns]; exact hcolumn)
      · intro column hcolumn
        exact List.mem_append_left _
          (List.mem_append_right _ (configure_permutation column hcolumn))
    · rw [synthesizeFrom_of_ne hstart, Operations.KeygenRegistered, List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      trivial
  copyCellsAssigned := by
    rintro ⟨⟩ counts _ input self
    simp only [configure_output]
    by_cases hstart : counts = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      exact Structural.copies privatePrograms self
    · rw [synthesizeFrom_of_ne hstart]
      apply Operations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
      rw [List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      rfl
  fixedWritesLawful := by
    rintro ⟨⟩ counts _ input self
    simp only [configure_output]
    change ((synthesizeFrom counts input).operations self).FixedWritesLawful
      ([] ++ ((configure ()).delta counts).constants)
    by_cases hstart : counts = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations, configure_constants]
      unfold circuit
      exact Structural.fixed privatePrograms self
    · rw [synthesizeFrom_of_ne hstart]
      apply Operations.HasNoFixedWrites.fixedWritesLawful
      rw [Operations.HasNoFixedWrites, List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      trivial
  lookupActivationsWellFormed := by
    intro start input self
    by_cases hstart : start = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      exact Structural.lookup privatePrograms self
    · rw [synthesizeFrom_of_ne hstart, Operations.LookupActivationsWellFormed,
        List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      trivial
  lookupSelectorAssignmentsAgree_of_registered := by
    rintro ⟨⟩ counts _ input self
    simp only [configure_output]
    intro _
    by_cases hstart : counts = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      exact Structural.lookupAgreement privatePrograms self
    · rw [synthesizeFrom_of_ne hstart, Operations.LookupSelectorAssignmentsAgree,
        List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      exact RegionOperations.lookupSelectorAssignmentsAgree_nil
  lookupSelectorsAnchoredBy_of_registered := by
    rintro ⟨⟩ counts _ input self anchor _ _
    rw [configure_output]
    by_cases hstart : counts = {}
    · rw [hstart, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      exact Structural.lookupAnchors privatePrograms self anchor
    · rw [synthesizeFrom_of_ne hstart, Operations.LookupSelectorsAnchoredBy,
        List.forall_iff_forall_mem]
      intro operation hoperation
      rw [mem_blank hoperation]
      exact fun argument enabled row hmember => (List.not_mem_nil hmember).elim
  output _ _ _ := ()
  output_eq := by intro _ _ _; rfl
  regionCount _ := 690
  regionCount_eq := by
    intro start input self
    show 690 = _
    by_cases hstart : start = {}
    · rw [hstart, synthesizeFrom_empty]
      change 690 = (assertion.operations self).regionCount
      rw [assertion_operations]
      unfold circuit
      exact (Structural.regions privatePrograms self).symm
    · rw [synthesizeFrom_of_ne hstart, blank_operations, regionCount_replicate]
  synthesisSummary start _ _ := summary start
  synthesisSummary_eq := by
    intro start input self
    show summary start = _
    by_cases hstart : start = {}
    · rw [hstart, summary_empty, synthesizeFrom_empty, assertion_operations]
      unfold circuit
      exact (Structural.summary privatePrograms self).symm
    · rw [summary_of_ne hstart, synthesizeFrom_of_ne hstart, blank_operations]

/-- Full source structural metadata, transported through the witness-bearing
program and arbitrary region starts. No caller-owned copy endpoint is required. -/
@[implicit_reducible] def elaborated : ElaboratedCircuit F Unit Unit unit unit pure synthesize where
  keygenRequirements := requirements
  registered := by
    intro config counts provenance input self
    change (assertion.operations self).KeygenRegistered (cleanGates ++ []) (cleanLookups ++ [])
      (StructuralBase.fixedColumns ++ []) (StructuralBase.permutationColumns ++ [] ++ [])
    rw [assertion_operations]
    simp only [List.append_nil]
    unfold circuit
    exact Structural.registered privatePrograms self
  copyCellsAssigned := by
    intro config counts provenance input self
    change (assertion.operations self).CopyCellsAssigned self []
    rw [assertion_operations]
    unfold circuit
    exact Structural.copies privatePrograms self
  fixedWritesLawful := by
    intro config counts provenance input self
    change (assertion.operations self).FixedWritesLawful ([] ++ [])
    rw [assertion_operations]
    unfold circuit
    exact Structural.fixed privatePrograms self
  lookupActivationsWellFormed := by
    intro config input self
    change (assertion.operations self).LookupActivationsWellFormed
    rw [assertion_operations]
    unfold circuit
    exact Structural.lookup privatePrograms self
  lookupSelectorAssignmentsAgree_of_registered := by
    intro config counts provenance input self program operations _
    change (assertion.operations self).LookupSelectorAssignmentsAgree
    rw [assertion_operations]
    unfold circuit
    exact Structural.lookupAgreement privatePrograms self
  lookupSelectorsAnchoredBy_of_registered := by
    intro config counts provenance input self anchor _ _
    change (assertion.operations self).LookupSelectorsAnchoredBy anchor
    rw [assertion_operations]
    unfold circuit
    exact Structural.lookupAnchors privatePrograms self anchor
  output _ _ _ := ()
  output_eq := by intro _ _ _; rfl
  regionCount _ := 690
  regionCount_eq := by
    intro config input self
    change 690 = (assertion.operations self).regionCount
    rw [assertion_operations]
    unfold circuit
    exact (Structural.regions privatePrograms self).symm
  synthesisSummary _ _ _ := FloorPlanner.synthesisSummary StructuralBase.source
  synthesisSummary_eq := by
    intro config input self
    change _ = FloorPlanner.synthesisSummary (assertion.operations self)
    rw [assertion_operations]
    unfold circuit
    exact (Structural.summary privatePrograms self).symm

/-- SHA-256 preimage assertion for the exact native 24-private-byte,
32-public-byte example. Soundness uses assigned bytes and public instances;
honesty is required only for completeness. -/
def formal : FormalCircuit F Unit Unit unit unit where
  name := "Midnight SHA-256 preimage (24 private bytes)"
  configure := pure
  synthesize := synthesize
  elaborated := elaborated
  Witness := WitnessData
  extract _ _ := extractWitness
  EnvAssumptions _ env := Capacity env.env
  Spec _ _ witness := assertionSpec witness
  ProverAssumptions _ witness hint := proverAssumptions witness hint
  ProverSpec _ _ witness hint := proverSpec witness hint
  soundness := by
    intro config self env input capacity _ satisfied
    change Constraints env.place env.env (assertion.operations self) self at satisfied
    rw [assertion_operations] at satisfied
    exact ⟨(sound self env capacity satisfied).1, (sound self env capacity satisfied).2.1⟩
  completeness := by
    intro config self env input witnesses capacity _ assumptions
    change ExtendsWitnesses env.place env.env (assertion.operations self) self at witnesses
    rw [assertion_operations] at witnesses
    obtain ⟨bytes,claim⟩ := assumptions
    have satisfied := (complete self env capacity bytes claim witnesses).1
    refine ⟨?_, extractedMessage_honest self env capacity bytes witnesses, ?_⟩
    · change Constraints env.place env.env.toEnvironment (assertion.operations self) self
      rw [assertion_operations]
      exact satisfied
    · exact ⟨(sound self env.toEnvironment capacity satisfied).1,
        (sound self env.toEnvironment capacity satisfied).2.1⟩

/-- The bundled assertion retains the complete witness-bearing native source. -/
theorem formal_operations (self : RegionIndex) :
    (formal.synthesize () ()).operations self = circuit.operations self :=
  assertion_operations self

/-- The bundled soundness field constrains the exact native instance column;
clients do not choose a separate digest extractor or assume honest witnesses. -/
theorem formal_instance_sha256 (self : RegionIndex) (env : Placed Environment F)
    (capacity : Capacity env.env)
    (satisfied : Constraints env.place env.env
      ((formal.synthesize () ()).operations self) self) (i : Fin 32) :
    env.env.inst ⟨1⟩ i.val = ((Spec.digest (extractedMessage self env))[i] : F) := by
  have publicValue := (formal.soundness () self env () capacity trivial satisfied).2
  change publicDigest env.env = Spec.digest (extractedMessage self env) at publicValue
  have value := congrArg (fun digest : Vector Nat 32 => digest[i]) publicValue
  simp only [publicDigest, Fin.getElem_fin, Vector.getElem_ofFn] at value
  simp only [Fin.getElem_fin]
  rw [← value]
  exact (ZMod.natCast_zmod_val _).symm

/-- `formal`'s assertion over SHA-256's Clean configure program, with no caller keygen
requirements. Its guarantees hold only from empty counts. -/
noncomputable def configuredFormal : FormalCircuit F Unit ConfigureCounts unit unit where
  name := "Midnight SHA-256 preimage (24 private bytes)"
  configure := configure
  synthesize := synthesizeFrom
  elaborated := configuredElaborated
  Witness := WitnessData
  extract _ _ := extractWitness
  EnvAssumptions start env := start = {} ∧ Capacity env.env
  Spec _ _ witness := assertionSpec witness
  ProverAssumptions _ witness hint := proverAssumptions witness hint
  ProverSpec _ _ witness hint := proverSpec witness hint
  soundness := by
    rintro start self env input ⟨rfl, capacity⟩ _ satisfied
    change Constraints env.place env.env ((synthesizeFrom {} input).operations self) self
      at satisfied
    rw [synthesizeFrom_empty, assertion_operations] at satisfied
    exact ⟨(sound self env capacity satisfied).1, (sound self env capacity satisfied).2.1⟩
  completeness := by
    rintro start self env input witnesses ⟨rfl, capacity⟩ _ assumptions
    change ExtendsWitnesses env.place env.env ((synthesizeFrom {} input).operations self) self
      at witnesses
    rw [synthesizeFrom_empty, assertion_operations] at witnesses
    obtain ⟨bytes,claim⟩ := assumptions
    have satisfied := (complete self env capacity bytes claim witnesses).1
    refine ⟨?_, extractedMessage_honest self env capacity bytes witnesses, ?_⟩
    · rw [synthesizeFrom_empty, assertion_operations]
      exact satisfied
    · exact ⟨(sound self env.toEnvironment capacity satisfied).1,
        (sound self env.toEnvironment capacity satisfied).2.1⟩

/-- The configuration synthesis is written for is configure's, from empty counts. -/
theorem configuredFormal_config : (configuredFormal.configure ()).output {} = {} :=
  configure_output () {}

/-- From empty counts, `configuredFormal` synthesizes `formal`'s circuit. -/
theorem configuredFormal_synthesize : configuredFormal.synthesize {} = formal.synthesize () := by
  funext input
  change synthesizeFrom {} input = assertion
  exact synthesizeFrom_empty input

end Midnight.SHA256.Semantics.Preimage
