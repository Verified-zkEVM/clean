import Clean.Halo2.TopLevel
import Clean.Ironwood.Action.PublicInput
import Clean.Ironwood.Action.ConfigureCertificates
import Clean.Ironwood.Action.RealBases

/-!
# The deployed Orchard Action as a closed top-level circuit
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

private theorem initialGeneratorTableIdx_mem
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

private theorem actionDomainExponentBounds :
    DomainExponentBounds
      (TopLevelCompilation.domainRowRequirement
        (circuit Specs.Sinsemilla.orchardGenerators orchardBases)
        PublicInputs.layout)
      (TopLevelCompilation.domainExponent
        (circuit Specs.Sinsemilla.orchardGenerators orchardBases)
        PublicInputs.layout) :=
  minimalKForRows_bounds _ _

def actionCircuit : TopLevelCircuit Fp Config PublicInputs where
  formalCircuit :=
    circuit Specs.Sinsemilla.orchardGenerators orchardBases
  noCallerRequirements := ⟨(), rfl, rfl, rfl, fun _ => rfl⟩
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
  domainExponent :=
    TopLevelCompilation.domainExponent
      (circuit Specs.Sinsemilla.orchardGenerators orchardBases)
      PublicInputs.layout
  domainExponentBounds :=
    actionDomainExponentBounds
  PrivateWitness := PrivateWitness
  extractPrivate := fun cfg env =>
    PrivateWitness.ofActionData (extractPost cfg () 0 env)
  combine := combine
  Spec := fun inputs privateWitness =>
    SpecPost Specs.Sinsemilla.orchardGenerators orchardBases
      () () (combine inputs privateWitness)
  spec_iff := by
    intros
    rfl
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
    have hprimary :
        (configure Specs.Sinsemilla.orchardGenerators {}).1.primary = ⟨0⟩ := by
      rfl
    rw [← PublicInputs.ofActionData_extractPost _ _ _ hprimary]
    exact combine_parts
      (extractPost
        (configure Specs.Sinsemilla.orchardGenerators {}).1 () 0 env)
  assumptions_eq := rfl
  closesEnvironment := configured_closesEnvironment

/-- The semantic conclusion for every Action proved in one Halo 2 bundle. -/
def BundleStatement {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Prop :=
  ∀ proofIndex, actionCircuit.Statement (inputs proofIndex)

end Zcash.Circuits.Action
