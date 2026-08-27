import Clean.Halo2.TopLevel
import Clean.Ironwood.Action.PublicInput
import Clean.Ironwood.Action.Spec

/-!
# The deployed Orchard Action as a closed top-level circuit
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

theorem initialGeneratorTableIdx_mem
    (cfg : Config) (i : RegionIndex) :
    Operation.loadTable cfg.sinsemilla1.generatorTable.tableIdx
        ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp)) ∈
      (mainPost Specs.Sinsemilla.orchardGenerators orchardBases cfg ()).operations i := by
  simp only [mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [FormalCircuit.call_operations]
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize, synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply List.mem_append_left
  simp only [synthWitness, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [Sinsemilla.load_operations]
  simp

private theorem configuredTableSharing :
    let cfg := (configure Specs.Sinsemilla.orchardGenerators {}).1
    cfg.sinsemilla2.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle1.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle2.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.lookupConfig.tableIdx = cfg.sinsemilla1.generatorTable.tableIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem configuredLookupSelectorIndices :
    let cfg := (configure Specs.Sinsemilla.orchardGenerators {}).1
    cfg.lookupConfig.qLookup.index = 2 ∧
      cfg.lookupConfig.qRunning.index = 3 := by
  exact ⟨rfl, rfl⟩

private theorem configured_pureEnvironmentAssumptions
    (env : Placed Environment Fp) :
    let cfg := (configure Specs.Sinsemilla.orchardGenerators {}).1
    Ecc.MulFixed.FullWidth.EnvAssumptions cfg.eccConfig.mulFixedFull env ∧
    Ecc.MulFixed.Short.EnvAssumptions cfg.eccConfig.mulFixedShort env ∧
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions
      cfg.eccConfig.mulFixedBaseField env ∧
    cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index := by
  simp only [Ecc.MulFixed.FullWidth.EnvAssumptions,
    Ecc.MulFixed.Short.EnvAssumptions,
    Ecc.MulFixed.Short.InnerEnvAssumptions,
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions, circuit_norm]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨hLookup, hRunning⟩ := configuredLookupSelectorIndices
  omega

private theorem circuit_configure_eq :
    (circuit Specs.Sinsemilla.orchardGenerators orchardBases).configure =
      fun _ => configure Specs.Sinsemilla.orchardGenerators :=
  rfl

private theorem circuit_synthesize_eq (cfg : Config) :
    (circuit Specs.Sinsemilla.orchardGenerators orchardBases).synthesize cfg =
      mainPost Specs.Sinsemilla.orchardGenerators orchardBases cfg :=
  rfl

private theorem circuit_envAssumptions_eq (cfg : Config) :
    (circuit Specs.Sinsemilla.orchardGenerators orchardBases).EnvAssumptions cfg =
      EnvAssumptions cfg :=
  rfl

/--
The circuit compiler supplies the residual Action environment contract. Table
contents are deliberately absent: the circuit proofs derive those from their
respective operational hypotheses.
-/
private theorem configured_closesEnvironment
    (assignment : ProofAssignment Fp) :
    let formal := circuit Specs.Sinsemilla.orchardGenerators orchardBases
    formal.EnvAssumptions
      (TopLevelCompilation.config formal)
      (TopLevelCompilation.placedEnvironment
        formal PublicInputs.layout assignment) := by
  let formal := circuit Specs.Sinsemilla.orchardGenerators orchardBases
  let env :=
    TopLevelCompilation.placedEnvironment
      formal PublicInputs.layout assignment
  change EnvAssumptions
    (configure Specs.Sinsemilla.orchardGenerators {}).1 env
  have htable :
      2 ^ Specs.K ≤
        TopLevelCompilation.usedRows formal PublicInputs.layout := by
    have hlength := Operations.loadTable_length_le_usedRows
      (TopLevelCompilation.operations formal)
      ((configure Specs.Sinsemilla.orchardGenerators {}).1.sinsemilla1.generatorTable.tableIdx)
      ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp))
      (by
        simpa only [formal, TopLevelCompilation.operations,
          TopLevelCompilation.config, circuit_configure_eq,
          circuit_synthesize_eq] using
          initialGeneratorTableIdx_mem
            (configure Specs.Sinsemilla.orchardGenerators {}).1 0)
    have hoperations :
        2 ^ Specs.K ≤
          Halo2.usedRows (TopLevelCompilation.operations formal) := by
      simpa only [List.length_map, List.length_range] using hlength
    exact hoperations.trans (Nat.le_max_left _ _)
  have hUsable : 2 ^ Specs.K ≤ env.env.usableRows := by
    change
      2 ^ Specs.K ≤
        2 ^ TopLevelCompilation.domainExponent formal PublicInputs.layout -
          (TopLevelCompilation.constraintSystem formal).blindingFactors - 1
    exact htable.trans
      (TopLevelCompilation.usedRows_le_usableRowsAt_domainExponent
        formal PublicInputs.layout)
  obtain ⟨hs2, hm1, hm2, hlookup⟩ := configuredTableSharing
  obtain ⟨hfull, hshort, hbaseField, hdistinct⟩ :=
    configured_pureEnvironmentAssumptions env
  exact ⟨hUsable, hs2, hm1, hm2, hlookup, hfull, hshort,
    hbaseField, rfl, rfl, hdistinct⟩

/--
The deployed proof-carrying Orchard Action circuit: unit synthesis input/output,
explicit public inputs, and no unfulfilled environment contract at its boundary.
-/
private theorem actionSelectorRequirements :
    (circuit Specs.Sinsemilla.orchardGenerators orchardBases).selectorRequirements
      () {} := by
  dsimp only [FormalCircuit.selectorRequirements, Circuit.circuit,
    Circuit.elaboratedPost, Circuit.configureElaborated]
  trivial

private theorem actionQueryRequirements :
    (circuit Specs.Sinsemilla.orchardGenerators orchardBases).queryRequirements
      () {} := by
  dsimp only [FormalCircuit.queryRequirements, Circuit.circuit,
    Circuit.elaboratedPost, Circuit.configureElaborated]
  trivial

def Internal.actionCircuitImpl : TopLevelCircuit Fp Config PublicInputs where
  formalCircuit :=
    circuit Specs.Sinsemilla.orchardGenerators orchardBases
  noCallerRequirements := ⟨(), rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  selectorRequirements := actionSelectorRequirements
  queryRequirements := actionQueryRequirements
  exists_rotation_mem_fixedQueries_of_lt := by
    intro column hcolumn
    have hbound : column <
        ((Circuit.configure Specs.Sinsemilla.orchardGenerators).finalCounts {}).numFixedColumns := by
      dsimp only [TopLevelCompilation.constraintSystem, Circuit.circuit] at hcolumn
      rw [Configure.run_numFixedColumns,
        ConfigureCounts.ofConstraintSystem_empty] at hcolumn
      exact hcolumn
    obtain ⟨rotation, hquery⟩ :=
      Zcash.Circuits.Action.Circuit.configure_fixedQueries_cover
        Specs.Sinsemilla.orchardGenerators column hbound
    refine ⟨rotation, ?_⟩
    dsimp only [TopLevelCompilation.constraintSystem, Circuit.circuit]
    rw [Configure.mem_fixedQueries_run_iff]
    apply Or.inr
    rw [ConfigureCounts.ofConstraintSystem_empty]
    exact hquery
  constantSiteCount_le_constantCapacityLowerBound := by
    dsimp only
    rw [Zcash.Circuits.Action.Circuit.circuit_synthesisSummary_eq]
    set_option maxRecDepth 10000 in
      decide
  publicInputLayout := PublicInputs.layout
  PrivateWitness := PrivateWitness
  extractPrivate := fun cfg env =>
    PrivateWitness.ofActionData (extractPost cfg () 0 env)
  combine := combine
  Spec := ActionSpec
  spec_iff := by
    intros
    exact actionSpec_iff_specPost _ _
  extract_factorization := by
    dsimp
    intro env
    change combine
      (PublicInputs.layout.extract env.env)
      (PrivateWitness.ofActionData
        (extractPost
          (configure Specs.Sinsemilla.orchardGenerators {}).1 () 0 env)) =
      extractPost
        (configure Specs.Sinsemilla.orchardGenerators {}).1 () 0 env
    rw [← PublicInputs.ofActionData_extractPost
      (configure Specs.Sinsemilla.orchardGenerators {}).1 0 env (by
        simp [PublicInputs.layout, PublicInputLayout.cells,
          PublicInputLayout.cellList]
        rfl)]
    exact combine_parts
      (extractPost
        (configure Specs.Sinsemilla.orchardGenerators {}).1 () 0 env)
  assumptions_eq := rfl
  closesEnvironment := configured_closesEnvironment

/-- The concrete Action implementation and its opening equation, kept behind an
opaque reduction barrier. Runtime evaluation still computes the implementation;
proofs cross the boundary only through the API below. -/
private opaque actionCircuitPacked :
    { top : TopLevelCircuit Fp Config PublicInputs //
      top = Internal.actionCircuitImpl } :=
  ⟨Internal.actionCircuitImpl, rfl⟩

/-- The deployed Orchard Action circuit, opaque to definitional equality. -/
def actionCircuit : TopLevelCircuit Fp Config PublicInputs :=
  actionCircuitPacked.val

/-- Controlled implementation opening for the Action integration layer. This is
deliberately not a simp lemma. -/
theorem Internal.actionCircuit_eq_impl :
    actionCircuit = Internal.actionCircuitImpl :=
  actionCircuitPacked.property

/-- Action's configured primary column witnesses that its permutation family is
nonempty. -/
theorem actionCircuit_permutationColumns_nonempty :
    actionCircuit.permutationColumns ≠ [] := by
  rw [Internal.actionCircuit_eq_impl]
  simp only [TopLevelCircuit.permutationColumns,
    TopLevelCircuit.constraintSystem, Internal.actionCircuitImpl]
  let program := Circuit.configure Specs.Sinsemilla.orchardGenerators
  let primary := (program.output {}).primary.toAny
  have hprimary : primary ∈ (program.run {}).2.permutationColumns :=
    (Configure.mem_permutationColumns_run_iff program {} primary).mpr
      (Or.inr (by
        simpa only [program, primary] using
          Circuit.configure_output_primary_mem_permutationRequests
            Specs.Sinsemilla.orchardGenerators {}))
  exact List.ne_nil_of_mem hprimary

/-- Action's closed configure run allocates ten advice columns. -/
theorem actionCircuit_numAdviceColumns_eq :
    actionCircuit.constraintSystem.numAdviceColumns = 10 := by
  rw [Internal.actionCircuit_eq_impl]
  simpa only [Internal.actionCircuitImpl, TopLevelCircuit.constraintSystem,
    TopLevelCompilation.constraintSystem, Circuit.circuit] using
      Circuit.configure_finalCounts_numAdviceColumns
        Specs.Sinsemilla.orchardGenerators

/-- Action's closed configure run allocates fourteen fixed columns. -/
theorem actionCircuit_numFixedColumns_eq :
    actionCircuit.constraintSystem.numFixedColumns = 14 := by
  rw [Internal.actionCircuit_eq_impl]
  simpa only [Internal.actionCircuitImpl, TopLevelCircuit.constraintSystem,
    TopLevelCompilation.constraintSystem, Circuit.circuit] using
      Circuit.configure_finalCounts_numFixedColumns
        Specs.Sinsemilla.orchardGenerators

/-- Action's closed configure run allocates one instance column. -/
theorem actionCircuit_numInstanceColumns_eq :
    actionCircuit.constraintSystem.numInstanceColumns = 1 := by
  rw [Internal.actionCircuit_eq_impl]
  simpa only [Internal.actionCircuitImpl, TopLevelCircuit.constraintSystem,
    TopLevelCompilation.constraintSystem, Circuit.circuit] using
      Circuit.configure_finalCounts_numInstanceColumns
        Specs.Sinsemilla.orchardGenerators

/-- Action's configured gates and lookups have exact Halo 2 degree nine. -/
theorem actionCircuit_constraintDegree_eq :
    actionCircuit.constraintDegree = 9 := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

set_option maxRecDepth 10000 in
/-- Action's configured query depth requires five blinding rows. -/
theorem actionCircuit_blindingFactors_eq :
    actionCircuit.blindingFactors = 5 := by
  rw [Internal.actionCircuit_eq_impl]
  unfold TopLevelCircuit.blindingFactors TopLevelCircuit.constraintSystem
    TopLevelCompilation.constraintSystem
  simp only [Internal.actionCircuitImpl, Circuit.circuit]
  configure_norm

/-- Action's public instance layout occupies ten rows. -/
theorem actionCircuit_publicInputLayout_usedRows_eq :
    actionCircuit.publicInputLayout.usedRows = 10 := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The opaque circuit's private-witness field is the public Action witness type. -/
theorem actionCircuit_privateWitness_eq :
    actionCircuit.PrivateWitness = PrivateWitness := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- Action public inputs are serialized according to their canonical layout. -/
theorem actionCircuit_publicInputRows
    (input : PublicInputs Fp) (column : Column .instance) :
    actionCircuit.publicInputRows input column =
      PublicInputs.layout.rows input column := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The primary Action instance column is exactly the public-input element vector. -/
theorem actionCircuit_publicInputRows_zero (input : PublicInputs Fp) :
    actionCircuit.publicInputRows input ⟨0⟩ = (toElements input).toList := by
  rw [actionCircuit_publicInputRows]
  cases input
  rfl

/-- Every undeclared Action instance column serializes as zero rows. -/
theorem actionCircuit_publicInputRows_ne_zero
    (input : PublicInputs Fp) {column : ℕ} (hcolumn : column ≠ 0) :
    ∀ i, (actionCircuit.publicInputRows input ⟨column⟩).getD i 0 = 0 := by
  have hzero : ∀ x ∈ actionCircuit.publicInputRows input ⟨column⟩, x = (0 : Fp) := by
    intro x hx
    rw [actionCircuit_publicInputRows, PublicInputLayout.rows] at hx
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
    rw [List.idxOf_eq_length (by
      simp only [PublicInputs.layout, PublicInputLayout.cellList]
      simp
      intro _ hindex
      exact hcolumn hindex.symm)]
    have hlen : (toElements input).toList.length ≤ PublicInputs.layout.cellList.length := by
      simp only [PublicInputLayout.cellList_length, Vector.length_toList]
      exact le_refl _
    exact List.getD_eq_default _ _ hlen
  intro i
  rcases lt_or_ge i (actionCircuit.publicInputRows input ⟨column⟩).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hzero _ (List.getElem_mem h)
  · exact List.getD_eq_default _ _ h

private theorem actionCircuit_spec_iff_of_eq
    (top : TopLevelCircuit Fp Config PublicInputs)
    (htop : top = Internal.actionCircuitImpl)
    (input : PublicInputs Fp) (privateWitness : PrivateWitness) :
    ActionSpec input privateWitness ↔
      top.Spec input
        (cast ((congrArg (fun circuit => circuit.PrivateWitness) htop).trans
          (by simp only [Internal.actionCircuitImpl])).symm
          privateWitness) := by
  cases htop
  simp [Internal.actionCircuitImpl]

/-- The Orchard Action spec is the opaque circuit's internal spec after
transporting the public private-witness type across the circuit boundary. -/
theorem actionCircuit_spec_iff
    (input : PublicInputs Fp) (privateWitness : PrivateWitness) :
    ActionSpec input privateWitness ↔
      actionCircuit.Spec input
        (actionCircuit_privateWitness_eq.symm ▸ privateWitness) := by
  exact actionCircuit_spec_iff_of_eq actionCircuit
    Internal.actionCircuit_eq_impl input privateWitness

/-- The semantic conclusion for every Action proved in one Halo 2 bundle. -/
def BundleStatement {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Prop :=
  ∀ proofIndex, actionCircuit.Statement (inputs proofIndex)

end Zcash.Circuits.Action
