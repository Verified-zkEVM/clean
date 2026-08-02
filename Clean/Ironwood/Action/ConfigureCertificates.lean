import Clean.Ironwood.Action.Circuit

/-!
# Action configure certificates

Compositional keygen capabilities exported by the direct children of
`Action.Circuit.configureChips`. Synthesis bundles consume these certificates without
opening child configure programs or their transitive operation lists.
-/

namespace Zcash.Circuits.Action.Circuit

open Halo2
open Ecc.MulFixed (FixedBase)
open Specs.Sinsemilla (Generators)

/-- The complete keygen context of one Action configure run. -/
private def actionConfigureContext (G : Generators) (counts : ConfigureCounts) :
    KeygenContext Fp :=
  { gates := ((configure G).delta counts).gates
    lookups := ((configure G).delta counts).lookups }

private theorem configure_output_lookupConfig (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).lookupConfig =
      (configureBase.output counts).lookupConfig :=
  rfl

/--
Transport the whole ECC configure certificate through Action's single direct ECC bind.
No ECC child configuration is opened above this boundary.
-/
def eccConfigureCertificate (G : Generators) (counts : ConfigureCounts) :
    Ecc.ConfigureCertificate
      (configureBase.output counts).advices
      (configureBase.output counts).lagrangeCoeffs
      (configureBase.output counts).lookupConfig
      (configureBase.finalCounts counts)
      (actionConfigureContext G counts) :=
  (Ecc.configureCertificate
    (configureBase.output counts).advices
    (configureBase.output counts).lagrangeCoeffs
    (configureBase.output counts).lookupConfig
    (configureBase.finalCounts counts)).mono
    (by
      intro gate hgate
      simp only [Ecc.configureContext] at hgate
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_gates_delta_bind_right
      unfold configureChips
      apply Configure.mem_gates_delta_bind_left
      exact hgate)
    (by
      intro argument hargument
      simp only [Ecc.configureContext, List.mem_cons] at hargument
      simp only [actionConfigureContext]
      rcases hargument with hrange | hecc
      · subst argument
        unfold configure
        apply Configure.mem_lookups_delta_bind_left
        unfold configureBase
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        simp
      · unfold configure
        apply Configure.mem_lookups_delta_bind_right
        unfold configureChips
        apply Configure.mem_lookups_delta_bind_left
        exact hecc)

/-- The fixed-base coordinate gate is one of the gates emitted by the complete Action
configure program. -/
private theorem coordsGate_mem_actionConfigure (G : Generators)
    (counts : ConfigureCounts) :
    Ecc.MulFixed.coordsGate
      ((configure G).output counts).eccConfig.mulFixedShort.superConfig ∈
      (actionConfigureContext G counts).gates := by
  rw [configure_output_eccConfig]
  simp only [actionConfigureContext]
  unfold configure
  apply Configure.mem_gates_delta_bind_right
  unfold configureChips
  apply Configure.mem_gates_delta_bind_left
  apply Ecc.mem_mulFixed_gates
  simp

private theorem fixedQuery_mem_actionConfigure_of_gate
    (G : Generators) (counts : ConfigureCounts)
    {gate : Gate Fp} (hgate : gate ∈ (actionConfigureContext G counts).gates)
    (column : Column .fixed)
    (hcolumn : (queryFixed column : Expression Fp Query) ∈ gate.queriedCells) :
    (column, 0) ∈ ((configure G).delta counts).fixedQueries := by
  have hlawful := (configureElaborated G).queriesLawful counts trivial
  exact hlawful.queriedCell_registered hgate hcolumn

private theorem coordsGate_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts)
    (column : Column .fixed)
    (hcolumn :
      (queryFixed column : Expression Fp Query) ∈
        (Ecc.MulFixed.coordsGate
          ((configure G).output counts).eccConfig.mulFixedShort.superConfig).queriedCells) :
    (column, 0) ∈ ((configure G).delta counts).fixedQueries := by
  exact fixedQuery_mem_actionConfigure_of_gate G counts
    (coordsGate_mem_actionConfigure G counts) column hcolumn

private theorem coordsGate_lagrange_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts) (index : Fin 8) :
    (((configure G).output counts).eccConfig.mulFixedShort.superConfig.lagrangeCoeffs index,
      0) ∈
      ((configure G).delta counts).fixedQueries := by
  apply coordsGate_fixedQuery_mem_actionConfigure
  fin_cases index <;>
    simp [Ecc.MulFixed.coordsGate, Gate.withSelector]

private theorem coordsGate_fixedZ_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts) :
    (((configure G).output counts).eccConfig.mulFixedShort.superConfig.fixedZ, 0) ∈
      ((configure G).delta counts).fixedQueries := by
  apply coordsGate_fixedQuery_mem_actionConfigure
  simp [Ecc.MulFixed.coordsGate, Gate.withSelector]

/-- The Poseidon hash capability transported through Action's direct Poseidon bind. -/
private def poseidonHashCertificate (G : Generators) (counts : ConfigureCounts) :
    (Poseidon.hash (Poseidon.Hash.ConstantLength.capacity 2)).ConfigurationCertificate
      ((configure G).output counts).poseidonConfig
      (actionConfigureContext G counts) := by
  let base := configureBase.output counts
  let eccCounts := (Ecc.configure base.advices base.lagrangeCoeffs
    base.lookupConfig).finalCounts (configureBase.finalCounts counts)
  apply (Poseidon.hashConfigureCertificate (Poseidon.Hash.ConstantLength.capacity 2)
    ![base.advices 6, base.advices 7, base.advices 8] (base.advices 5)
    ![base.lagrangeCoeffs 2, base.lagrangeCoeffs 3, base.lagrangeCoeffs 4]
    ![base.lagrangeCoeffs 5, base.lagrangeCoeffs 6, base.lagrangeCoeffs 7]
    eccCounts).mono
  · intro gate hgate
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_gates_delta_bind_right
    unfold configureChips
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    exact hgate
  · intro argument hargument
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_lookups_delta_bind_right
    unfold configureChips
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_left
    exact hargument

/-- The first HashPiece configure, transported through Action's direct bind. -/
private def sinsemilla1HashCertificate (G : Generators) (ns : List ℕ)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (counts : ConfigureCounts) :
    (Sinsemilla.HashToPoint.hashCircuit G ns Q hQ hns).ConfigurationCertificate
      ((configure G).output counts).sinsemilla1
      (actionConfigureContext G counts) := by
  let base := configureBase.output counts
  let chipsCounts := configureBase.finalCounts counts
  let eccCounts := (Ecc.configure base.advices base.lagrangeCoeffs
    base.lookupConfig).finalCounts chipsCounts
  let poseidonCounts := (Poseidon.configure
    ![base.advices 6, base.advices 7, base.advices 8] (base.advices 5)
    ![base.lagrangeCoeffs 2, base.lagrangeCoeffs 3, base.lagrangeCoeffs 4]
    ![base.lagrangeCoeffs 5, base.lagrangeCoeffs 6,
      base.lagrangeCoeffs 7]).finalCounts eccCounts
  apply (Sinsemilla.HashToPoint.hashConfigureCertificate G
    ns Q hQ hns (base.advices 0) (base.advices 1) (base.advices 2)
    (base.advices 3) (base.advices 4) (base.advices 6)
    (base.lagrangeCoeffs 0) base.genTable poseidonCounts).mono
  · intro gate hgate
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_gates_delta_bind_right
    unfold configureChips
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    simpa [base, chipsCounts, eccCounts, poseidonCounts] using hgate
  · intro argument hargument
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_lookups_delta_bind_right
    unfold configureChips
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_left
    simpa [base, chipsCounts, eccCounts, poseidonCounts] using hargument

private theorem sinsemilla1Gate_mem_actionConfigure (G : Generators)
    (counts : ConfigureCounts) :
    Sinsemilla.HashPiece.sinsemillaGate ((configure G).output counts).sinsemilla1 ∈
      (actionConfigureContext G counts).gates := by
  let hQ : (G.S 0).OnCurve := G.S_onCurve (by norm_num [Specs.K])
  let certificate := sinsemilla1HashCertificate G [1] (G.S 0) hQ (by simp) counts
  apply certificate.gates
  rw [List.mem_append]
  apply Or.inl
  have hconfig : certificate.configInput = ((configure G).output counts).sinsemilla1 := by
    simpa using certificate.output_eq
  rw [hconfig]
  simp [Sinsemilla.HashToPoint.hashCircuit, Sinsemilla.HashToPoint.hashRegion,
    FormalRegionCircuit.keygenRequirements,
    ElaboratedRegionCircuit.keygenRequirements]

private theorem sinsemilla1Lookup_mem_actionConfigure (G : Generators)
    (counts : ConfigureCounts) :
    Sinsemilla.HashPiece.generatorLookup G ((configure G).output counts).sinsemilla1 ∈
      (actionConfigureContext G counts).lookups := by
  let hQ : (G.S 0).OnCurve := G.S_onCurve (by norm_num [Specs.K])
  let certificate := sinsemilla1HashCertificate G [1] (G.S 0) hQ (by simp) counts
  apply certificate.lookups
  rw [List.mem_append]
  apply Or.inl
  have hconfig : certificate.configInput = ((configure G).output counts).sinsemilla1 := by
    simpa using certificate.output_eq
  rw [hconfig]
  simp [Sinsemilla.HashToPoint.hashCircuit, Sinsemilla.HashToPoint.hashRegion,
    FormalRegionCircuit.keygenRequirements,
    ElaboratedRegionCircuit.keygenRequirements]

private theorem sinsemilla1_qS2_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts) :
    (((configure G).output counts).sinsemilla1.qS2, 0) ∈
      ((configure G).delta counts).fixedQueries := by
  apply fixedQuery_mem_actionConfigure_of_gate G counts
    (sinsemilla1Gate_mem_actionConfigure G counts)
  simp [Sinsemilla.HashPiece.sinsemillaGate, Gate.withSelector]

private theorem sinsemilla1_generatorTable_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts) (column : TableColumn)
    (hcolumn : column ∈
      [((configure G).output counts).sinsemilla1.generatorTable.tableIdx,
        ((configure G).output counts).sinsemilla1.generatorTable.tableX,
        ((configure G).output counts).sinsemilla1.generatorTable.tableY]) :
    (column.inner, 0) ∈ ((configure G).delta counts).fixedQueries := by
  have hlawful := (configureElaborated G).queriesLawful counts trivial
  have hregistered := hlawful.lookupTable_registered
    (sinsemilla1Lookup_mem_actionConfigure G counts)
    (show (queryFixed column.inner : Expression Fp Query) ∈
      (Sinsemilla.HashPiece.generatorLookup G
        ((configure G).output counts).sinsemilla1).tables by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
      rcases hcolumn with rfl | rfl | rfl <;>
        simp [Sinsemilla.HashPiece.generatorLookup])
  exact hregistered

/-- Action-facing view of the two capabilities produced by a Merkle configure. -/
private structure MerkleCapabilities (config : Sinsemilla.Merkle.Config)
    (context : KeygenContext Fp) where
  condSwap : ∀ (wb : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool),
    (CondSwap.swap wb wswap).ConfigurationCertificate config.condSwap context
  gate : ∀ l : Fp,
    (Sinsemilla.Merkle.Gate.circuit l).ConfigurationCertificate config.gate context

/-- The first Merkle configure, transported through Action's direct bind. -/
private def merkle1Capabilities (G : Generators) (counts : ConfigureCounts) :
    MerkleCapabilities ((configure G).output counts).merkle1
      (actionConfigureContext G counts) := by
  let base := configureBase.output counts
  let chipsCounts := configureBase.finalCounts counts
  let eccCounts := (Ecc.configure base.advices base.lagrangeCoeffs
    base.lookupConfig).finalCounts chipsCounts
  let poseidonCounts := (Poseidon.configure
    ![base.advices 6, base.advices 7, base.advices 8] (base.advices 5)
    ![base.lagrangeCoeffs 2, base.lagrangeCoeffs 3, base.lagrangeCoeffs 4]
    ![base.lagrangeCoeffs 5, base.lagrangeCoeffs 6,
      base.lagrangeCoeffs 7]).finalCounts eccCounts
  let hashProgram := Sinsemilla.HashPiece.configure G
    (base.advices 0) (base.advices 1) (base.advices 2)
    (base.advices 3) (base.advices 4) (base.advices 6)
    (base.lagrangeCoeffs 0) base.genTable
  let hashConfig := hashProgram.output poseidonCounts
  let hashCounts := hashProgram.finalCounts poseidonCounts
  let certificate : Sinsemilla.Merkle.ConfigureCertificate hashConfig hashCounts
      (actionConfigureContext G counts) :=
    (Sinsemilla.Merkle.configureCertificate hashConfig hashCounts).mono
    (by
      intro gate hgate
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_gates_delta_bind_right
      unfold configureChips
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_left
      simpa [base, chipsCounts, eccCounts, poseidonCounts, hashProgram,
        hashConfig, hashCounts] using hgate)
    (by
      intro argument hargument
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_lookups_delta_bind_right
      unfold configureChips
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_left
      simpa [base, chipsCounts, eccCounts, poseidonCounts, hashProgram,
        hashConfig, hashCounts] using hargument)
  refine { condSwap := ?_, gate := ?_ }
  · intro wb wswap
    simpa [configure, configureChips, base, chipsCounts, eccCounts,
      poseidonCounts, hashProgram, hashConfig, hashCounts] using
      certificate.condSwap wb wswap
  · intro l
    simpa [configure, configureChips, base, chipsCounts, eccCounts,
      poseidonCounts, hashProgram, hashConfig, hashCounts] using certificate.gate l

/-- The second HashPiece configure, transported through Action's direct bind. -/
private def sinsemilla2HashCertificate (G : Generators) (ns : List ℕ)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (counts : ConfigureCounts) :
    (Sinsemilla.HashToPoint.hashCircuit G ns Q hQ hns).ConfigurationCertificate
      ((configure G).output counts).sinsemilla2
      (actionConfigureContext G counts) := by
  let base := configureBase.output counts
  let chipsCounts := configureBase.finalCounts counts
  let eccCounts := (Ecc.configure base.advices base.lagrangeCoeffs
    base.lookupConfig).finalCounts chipsCounts
  let poseidonCounts := (Poseidon.configure
    ![base.advices 6, base.advices 7, base.advices 8] (base.advices 5)
    ![base.lagrangeCoeffs 2, base.lagrangeCoeffs 3, base.lagrangeCoeffs 4]
    ![base.lagrangeCoeffs 5, base.lagrangeCoeffs 6,
      base.lagrangeCoeffs 7]).finalCounts eccCounts
  let hash1 := Sinsemilla.HashPiece.configure G
    (base.advices 0) (base.advices 1) (base.advices 2)
    (base.advices 3) (base.advices 4) (base.advices 6)
    (base.lagrangeCoeffs 0) base.genTable
  let merkle1 := Sinsemilla.Merkle.configure (hash1.output poseidonCounts)
  let hash2Counts := merkle1.finalCounts (hash1.finalCounts poseidonCounts)
  apply (Sinsemilla.HashToPoint.hashConfigureCertificate G
    ns Q hQ hns (base.advices 5) (base.advices 6) (base.advices 7)
    (base.advices 8) (base.advices 9) (base.advices 7)
    (base.lagrangeCoeffs 1) base.genTable hash2Counts).mono
  · intro gate hgate
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_gates_delta_bind_right
    unfold configureChips
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    simpa [base, chipsCounts, eccCounts, poseidonCounts, hash1, merkle1,
      hash2Counts] using hgate
  · intro argument hargument
    simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_lookups_delta_bind_right
    unfold configureChips
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_left
    simpa [base, chipsCounts, eccCounts, poseidonCounts, hash1, merkle1,
      hash2Counts] using hargument

private theorem sinsemilla2Gate_mem_actionConfigure (G : Generators)
    (counts : ConfigureCounts) :
    Sinsemilla.HashPiece.sinsemillaGate ((configure G).output counts).sinsemilla2 ∈
      (actionConfigureContext G counts).gates := by
  let hQ : (G.S 0).OnCurve := G.S_onCurve (by norm_num [Specs.K])
  let certificate := sinsemilla2HashCertificate G [1] (G.S 0) hQ (by simp) counts
  apply certificate.gates
  rw [List.mem_append]
  apply Or.inl
  have hconfig : certificate.configInput = ((configure G).output counts).sinsemilla2 := by
    simpa using certificate.output_eq
  rw [hconfig]
  simp [Sinsemilla.HashToPoint.hashCircuit, Sinsemilla.HashToPoint.hashRegion,
    FormalRegionCircuit.keygenRequirements,
    ElaboratedRegionCircuit.keygenRequirements]

private theorem sinsemilla2_qS2_fixedQuery_mem_actionConfigure
    (G : Generators) (counts : ConfigureCounts) :
    (((configure G).output counts).sinsemilla2.qS2, 0) ∈
      ((configure G).delta counts).fixedQueries := by
  apply fixedQuery_mem_actionConfigure_of_gate G counts
    (sinsemilla2Gate_mem_actionConfigure G counts)
  simp [Sinsemilla.HashPiece.sinsemillaGate, Gate.withSelector]

/-- Every fixed column allocated by the closed Action configure program is present in
its query-registration delta. The proof is assembled from the actual gates and lookup
argument that own the columns, plus the small allocation summary exported by
`configure`; it does not evaluate the full circuit. -/
theorem configure_fixedQueries_cover (G : Generators) :
    ∀ column < ((configure G).finalCounts {}).numFixedColumns,
      ∃ rotation, (⟨column⟩, rotation) ∈ ((configure G).delta {}).fixedQueries := by
  rcases configure_fixedColumn_indices G with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hcount⟩
  intro column hcolumn
  rw [hcount] at hcolumn
  interval_cases column
  · refine ⟨0, ?_⟩
    rw [← h0]
    exact sinsemilla1_generatorTable_fixedQuery_mem_actionConfigure G {}
      ((configure G).output {}).sinsemilla1.generatorTable.tableIdx (by simp)
  · refine ⟨0, ?_⟩
    rw [← h1]
    exact sinsemilla1_generatorTable_fixedQuery_mem_actionConfigure G {}
      ((configure G).output {}).sinsemilla1.generatorTable.tableX (by simp)
  · refine ⟨0, ?_⟩
    rw [← h2]
    exact sinsemilla1_generatorTable_fixedQuery_mem_actionConfigure G {}
      ((configure G).output {}).sinsemilla1.generatorTable.tableY (by simp)
  · refine ⟨0, ?_⟩
    rw [← h3]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 0
  · refine ⟨0, ?_⟩
    rw [← h4]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 1
  · refine ⟨0, ?_⟩
    rw [← h5]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 2
  · refine ⟨0, ?_⟩
    rw [← h6]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 3
  · refine ⟨0, ?_⟩
    rw [← h7]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 4
  · refine ⟨0, ?_⟩
    rw [← h8]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 5
  · refine ⟨0, ?_⟩
    rw [← h9]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 6
  · refine ⟨0, ?_⟩
    rw [← h10]
    exact coordsGate_lagrange_fixedQuery_mem_actionConfigure G {} 7
  · refine ⟨0, ?_⟩
    rw [← h11]
    exact coordsGate_fixedZ_fixedQuery_mem_actionConfigure G {}
  · refine ⟨0, ?_⟩
    rw [← h12]
    exact sinsemilla1_qS2_fixedQuery_mem_actionConfigure G {}
  · refine ⟨0, ?_⟩
    rw [← h13]
    exact sinsemilla2_qS2_fixedQuery_mem_actionConfigure G {}

/-- The second Merkle configure, transported through Action's direct bind. -/
private def merkle2Capabilities (G : Generators) (counts : ConfigureCounts) :
    MerkleCapabilities ((configure G).output counts).merkle2
      (actionConfigureContext G counts) := by
  let base := configureBase.output counts
  let chipsCounts := configureBase.finalCounts counts
  let eccCounts := (Ecc.configure base.advices base.lagrangeCoeffs
    base.lookupConfig).finalCounts chipsCounts
  let poseidonCounts := (Poseidon.configure
    ![base.advices 6, base.advices 7, base.advices 8] (base.advices 5)
    ![base.lagrangeCoeffs 2, base.lagrangeCoeffs 3, base.lagrangeCoeffs 4]
    ![base.lagrangeCoeffs 5, base.lagrangeCoeffs 6,
      base.lagrangeCoeffs 7]).finalCounts eccCounts
  let hash1 := Sinsemilla.HashPiece.configure G
    (base.advices 0) (base.advices 1) (base.advices 2)
    (base.advices 3) (base.advices 4) (base.advices 6)
    (base.lagrangeCoeffs 0) base.genTable
  let merkle1 := Sinsemilla.Merkle.configure (hash1.output poseidonCounts)
  let hash2Counts := merkle1.finalCounts (hash1.finalCounts poseidonCounts)
  let hash2 := Sinsemilla.HashPiece.configure G
    (base.advices 5) (base.advices 6) (base.advices 7)
    (base.advices 8) (base.advices 9) (base.advices 7)
    (base.lagrangeCoeffs 1) base.genTable
  let hashConfig := hash2.output hash2Counts
  let hashCounts := hash2.finalCounts hash2Counts
  let certificate : Sinsemilla.Merkle.ConfigureCertificate hashConfig hashCounts
      (actionConfigureContext G counts) :=
    (Sinsemilla.Merkle.configureCertificate hashConfig hashCounts).mono
    (by
      intro gate hgate
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_gates_delta_bind_right
      unfold configureChips
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_right
      apply Configure.mem_gates_delta_bind_left
      simpa [base, chipsCounts, eccCounts, poseidonCounts, hash1, merkle1,
        hash2Counts, hash2, hashConfig, hashCounts] using hgate)
    (by
      intro argument hargument
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_lookups_delta_bind_right
      unfold configureChips
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_right
      apply Configure.mem_lookups_delta_bind_left
      simpa [base, chipsCounts, eccCounts, poseidonCounts, hash1, merkle1,
        hash2Counts, hash2, hashConfig, hashCounts] using hargument)
  refine { condSwap := ?_, gate := ?_ }
  · intro wb wswap
    simpa [configure, configureChips, base, chipsCounts, eccCounts,
      poseidonCounts, hash1, merkle1, hash2Counts, hash2, hashConfig,
      hashCounts] using certificate.condSwap wb wswap
  · intro l
    simpa [configure, configureChips, base, chipsCounts, eccCounts,
      poseidonCounts, hash1, merkle1, hash2Counts, hash2, hashConfig,
      hashCounts] using certificate.gate l

/-- The CommitIvk gate registered by Action's direct CommitIvk configure bind. -/
private theorem commitIvkGate_mem (G : Generators) (counts : ConfigureCounts) :
    CommitIvk.gate ((configure G).output counts).commitIvkConfig ∈
      (actionConfigureContext G counts).gates := by
  simp only [actionConfigureContext]
  unfold configure
  apply Configure.mem_gates_delta_bind_right
  unfold configureChips
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_left
  unfold CommitIvk.configure
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_left
  simp

/-- Transport all capabilities from Action's shared configure prefix at once. -/
def baseConfigureCertificate (G : Generators) (counts : ConfigureCounts) :
    ConfigureBaseCertificate counts (actionConfigureContext G counts) :=
  (configureBaseCertificate counts).mono
    (by
      intro gate hgate
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_gates_delta_bind_left
      exact hgate)
    (by
      intro argument hargument
      simp only [actionConfigureContext]
      unfold configure
      apply Configure.mem_lookups_delta_bind_left
      exact hargument)

/-- The single AddChip gate configured directly in Action's shared prefix. -/
private def addChipCertificate (G : Generators) (counts : ConfigureCounts) :
    AddChip.addFormal.ConfigurationCertificate
      ((configure G).output counts).addChipConfig
      (actionConfigureContext G counts) :=
  (baseConfigureCertificate G counts).addChip

/-- The first 16-layer Merkle fold, assembled only from direct child capabilities. -/
def merkle1Certificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
      B.merkleQ_onCurve 0 16 (by norm_num) hintWitnesses.merkleSib
      hintWitnesses.merkleSwap).ConfigurationCertificate
        (((configure G).output counts).merkle1.condSwap,
          ((configure G).output counts).merkle1,
          ((configure G).output counts).lookupConfig)
        (actionConfigureContext G counts) := by
  let range := (baseConfigureCertificate G counts).shortRange 5
  let hash := sinsemilla1HashCertificate G
    Sinsemilla.Merkle.HashLayer.merkleNs B.merkleQ B.merkleQ_onCurve
    (by decide) counts
  let hashLayer := Sinsemilla.Merkle.HashLayer.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 0 (by norm_num)
    range hash ((merkle1Capabilities G counts).gate 0)
  let layer := Sinsemilla.Merkle.Layer.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 0 (by norm_num)
    (hintWitnesses.merkleSib 0) (hintWitnesses.merkleSwap 0)
    ((merkle1Capabilities G counts).condSwap _ _) hashLayer
  exact Sinsemilla.Merkle.CalculateRoot.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 0 16 (by norm_num)
    hintWitnesses.merkleSib hintWitnesses.merkleSwap layer

/-- The second 16-layer Merkle fold, assembled only from direct child capabilities. -/
def merkle2Certificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ
      B.merkleQ_onCurve 16 16 (by norm_num)
      (fun i => hintWitnesses.merkleSib (16 + i))
      (fun i => hintWitnesses.merkleSwap (16 + i))).ConfigurationCertificate
        (((configure G).output counts).merkle2.condSwap,
          ((configure G).output counts).merkle2,
          ((configure G).output counts).lookupConfig)
        (actionConfigureContext G counts) := by
  let range := (baseConfigureCertificate G counts).shortRange 5
  let hash := sinsemilla2HashCertificate G
    Sinsemilla.Merkle.HashLayer.merkleNs B.merkleQ B.merkleQ_onCurve
    (by decide) counts
  let hashLayer := Sinsemilla.Merkle.HashLayer.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 16 (by norm_num)
    range hash ((merkle2Capabilities G counts).gate 16)
  let layer := Sinsemilla.Merkle.Layer.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 16 (by norm_num)
    (hintWitnesses.merkleSib 16) (hintWitnesses.merkleSwap 16)
    ((merkle2Capabilities G counts).condSwap _ _) hashLayer
  exact Sinsemilla.Merkle.CalculateRoot.configurationCertificate
    G B.merkleQ B.merkleQ_onCurve 16 16 (by norm_num)
    (fun i => hintWitnesses.merkleSib (16 + i))
    (fun i => hintWitnesses.merkleSwap (16 + i)) layer

/-- CommitIvk, assembled from the direct Action chip capabilities. -/
def commitIvkCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (CommitIvk.Main.circuit G B.commitIvkR B.ivkQ
      B.ivkQ_onCurve).ConfigurationCertificate
      { gate := ((configure G).output counts).commitIvkConfig
        hashConfig := ((configure G).output counts).sinsemilla1
        lookupConfig := ((configure G).output counts).lookupConfig
        mulConfig := ((configure G).output counts).eccConfig.mulFixedFull
        addConfig := ((configure G).output counts).eccConfig.add }
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  let base := baseConfigureCertificate G counts
  let hash := sinsemilla1HashCertificate G CommitIvk.Main.ns B.ivkQ
    B.ivkQ_onCurve CommitIvk.Main.ns_ne_nil counts
  let commit := Sinsemilla.CommitDomain.configurationCertificate G
    CommitIvk.Main.ns B.commitIvkR B.ivkQ B.ivkQ_onCurve
    CommitIvk.Main.ns_ne_nil (ecc.mulFixedFull B.commitIvkR) hash ecc.addFormal
  have bitshift : LookupRangeCheck.bitshiftGate 10
      ((configure G).output counts).lookupConfig ∈
      (actionConfigureContext G counts).gates := by
    rw [configure_output_lookupConfig]
    exact base.bitshiftGate
  exact CommitIvk.Main.configurationCertificate G B.commitIvkR B.ivkQ
    B.ivkQ_onCurve commit bitshift (commitIvkGate_mem G counts) base.rangeLookup

private theorem noteCommitOldDirectGates (G : Generators)
    (counts : ConfigureCounts) : ∀ gate, gate ∈
      [LookupRangeCheck.bitshiftGate 10 ((configure G).output counts).lookupConfig,
        NoteCommit.YCanonicity.gate ((configure G).output counts).noteCommitOld.y,
        NoteCommit.DecomposeB.gate ((configure G).output counts).noteCommitOld.b,
        NoteCommit.DecomposeD.gate ((configure G).output counts).noteCommitOld.d,
        NoteCommit.DecomposeE.gate ((configure G).output counts).noteCommitOld.e,
        NoteCommit.DecomposeG.gate ((configure G).output counts).noteCommitOld.g,
        NoteCommit.DecomposeH.gate ((configure G).output counts).noteCommitOld.h,
        NoteCommit.GdCanonicity.gate ((configure G).output counts).noteCommitOld.gd,
        NoteCommit.PkdCanonicity.gate ((configure G).output counts).noteCommitOld.pkd,
        NoteCommit.ValueCanonicity.gate ((configure G).output counts).noteCommitOld.value,
        NoteCommit.RhoCanonicity.gate ((configure G).output counts).noteCommitOld.rho,
        NoteCommit.PsiCanonicity.gate ((configure G).output counts).noteCommitOld.psi] →
      gate ∈ (actionConfigureContext G counts).gates := by
  intro gate hgate
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | hgate
  · rw [configure_output_lookupConfig]
    exact (baseConfigureCertificate G counts).bitshiftGate
  · simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_gates_delta_bind_right
    unfold configureChips
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    rw [NoteCommit.configure_delta_gates]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate ⊢
    aesop

private theorem noteCommitNewDirectGates (G : Generators)
    (counts : ConfigureCounts) : ∀ gate, gate ∈
      [LookupRangeCheck.bitshiftGate 10 ((configure G).output counts).lookupConfig,
        NoteCommit.YCanonicity.gate ((configure G).output counts).noteCommitNew.y,
        NoteCommit.DecomposeB.gate ((configure G).output counts).noteCommitNew.b,
        NoteCommit.DecomposeD.gate ((configure G).output counts).noteCommitNew.d,
        NoteCommit.DecomposeE.gate ((configure G).output counts).noteCommitNew.e,
        NoteCommit.DecomposeG.gate ((configure G).output counts).noteCommitNew.g,
        NoteCommit.DecomposeH.gate ((configure G).output counts).noteCommitNew.h,
        NoteCommit.GdCanonicity.gate ((configure G).output counts).noteCommitNew.gd,
        NoteCommit.PkdCanonicity.gate ((configure G).output counts).noteCommitNew.pkd,
        NoteCommit.ValueCanonicity.gate ((configure G).output counts).noteCommitNew.value,
        NoteCommit.RhoCanonicity.gate ((configure G).output counts).noteCommitNew.rho,
        NoteCommit.PsiCanonicity.gate ((configure G).output counts).noteCommitNew.psi] →
      gate ∈ (actionConfigureContext G counts).gates := by
  intro gate hgate
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | hgate
  · rw [configure_output_lookupConfig]
    exact (baseConfigureCertificate G counts).bitshiftGate
  · simp only [actionConfigureContext]
    unfold configure
    apply Configure.mem_gates_delta_bind_right
    unfold configureChips
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    rw [NoteCommit.configure_delta_gates]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate ⊢
    aesop

def noteCommitOldCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
      B.noteQ_onCurve).ConfigurationCertificate
      { gates := ((configure G).output counts).noteCommitOld
        hashConfig := ((configure G).output counts).sinsemilla1
        lookupConfig := ((configure G).output counts).lookupConfig
        mulConfig := ((configure G).output counts).eccConfig.mulFixedFull
        addConfig := ((configure G).output counts).eccConfig.add }
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  let base := baseConfigureCertificate G counts
  let hash := sinsemilla1HashCertificate G NoteCommit.Main.ns B.noteQ
    B.noteQ_onCurve NoteCommit.Main.ns_ne_nil counts
  let commit := Sinsemilla.CommitDomain.configurationCertificate G
    NoteCommit.Main.ns B.noteCommitR B.noteQ B.noteQ_onCurve
    NoteCommit.Main.ns_ne_nil (ecc.mulFixedFull B.noteCommitR) hash ecc.addFormal
  exact NoteCommit.Main.configurationCertificate G B.noteCommitR B.noteQ
    B.noteQ_onCurve commit (noteCommitOldDirectGates G counts) base.rangeLookup

def noteCommitNewCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (NoteCommit.Main.circuit G B.noteCommitR B.noteQ
      B.noteQ_onCurve).ConfigurationCertificate
      { gates := ((configure G).output counts).noteCommitNew
        hashConfig := ((configure G).output counts).sinsemilla2
        lookupConfig := ((configure G).output counts).lookupConfig
        mulConfig := ((configure G).output counts).eccConfig.mulFixedFull
        addConfig := ((configure G).output counts).eccConfig.add }
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  let base := baseConfigureCertificate G counts
  let hash := sinsemilla2HashCertificate G NoteCommit.Main.ns B.noteQ
    B.noteQ_onCurve NoteCommit.Main.ns_ne_nil counts
  let commit := Sinsemilla.CommitDomain.configurationCertificate G
    NoteCommit.Main.ns B.noteCommitR B.noteQ B.noteQ_onCurve
    NoteCommit.Main.ns_ne_nil (ecc.mulFixedFull B.noteCommitR) hash ecc.addFormal
  exact NoteCommit.Main.configurationCertificate G B.noteCommitR B.noteQ
    B.noteQ_onCurve commit (noteCommitNewDirectGates G counts) base.rangeLookup

/-- ValueCommit's three borrowed ECC capabilities, composed without reopening ECC. -/
def valueCommitCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (ValueCommit.circuit B.valueCommitV B.valueCommitR).ConfigurationCertificate
      (((configure G).output counts).eccConfig.mulFixedShort,
        ((configure G).output counts).eccConfig.mulFixedFull,
        ((configure G).output counts).eccConfig.add)
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  apply ((ValueCommit.circuit B.valueCommitV B.valueCommitR).configureCertificate
    (((configure G).output counts).eccConfig.mulFixedShort,
      ((configure G).output counts).eccConfig.mulFixedFull,
      ((configure G).output counts).eccConfig.add) {}
    ⟨(ecc.mulFixedShort B.valueCommitV).configured,
      (ecc.mulFixedFull B.valueCommitR).configured,
      ecc.addFormal.configured⟩).mono
  · intro gate hgate
    simp only [ValueCommit.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, ValueCommit.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hgate
    rcases hgate with hshortOrFull | hadd
    · rcases hshortOrFull with hshort | hfull
      · exact (ecc.mulFixedShort B.valueCommitV).gates_of_configured gate hshort
      · exact (ecc.mulFixedFull B.valueCommitR).gates_of_configured gate hfull
    · exact ecc.addFormal.gates_of_configured gate hadd
  · intro argument hargument
    simp only [ValueCommit.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, ValueCommit.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hargument
    rcases hargument with hshortOrFull | hadd
    · rcases hshortOrFull with hshort | hfull
      · exact (ecc.mulFixedShort B.valueCommitV).lookups_of_configured argument hshort
      · exact (ecc.mulFixedFull B.valueCommitR).lookups_of_configured argument hfull
    · exact ecc.addFormal.lookups_of_configured argument hadd

/-- SpendAuthority's two borrowed ECC capabilities, composed without reopening ECC. -/
def spendAuthorityCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (SpendAuthority.circuit B.spendAuthG).ConfigurationCertificate
      (((configure G).output counts).eccConfig.mulFixedFull,
        ((configure G).output counts).eccConfig.add)
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  apply ((SpendAuthority.circuit B.spendAuthG).configureCertificate
    (((configure G).output counts).eccConfig.mulFixedFull,
      ((configure G).output counts).eccConfig.add) {}
    ⟨(ecc.mulFixedFull B.spendAuthG).configured,
      ecc.addFormal.configured⟩).mono
  · intro gate hgate
    simp only [SpendAuthority.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, SpendAuthority.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hgate
    rcases hgate with hfull | hadd
    · exact (ecc.mulFixedFull B.spendAuthG).gates_of_configured gate hfull
    · exact ecc.addFormal.gates_of_configured gate hadd
  · intro argument hargument
    simp only [SpendAuthority.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, SpendAuthority.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hargument
    rcases hargument with hfull | hadd
    · exact (ecc.mulFixedFull B.spendAuthG).lookups_of_configured argument hfull
    · exact ecc.addFormal.lookups_of_configured argument hadd

/-- AddressIntegrity's variable-base multiplication and point-witness capabilities. -/
def addressIntegrityCertificate (G : Generators)
    (counts : ConfigureCounts) :
    AddressIntegrity.circuit.ConfigurationCertificate
      (((configure G).output counts).eccConfig.mul,
        ((configure G).output counts).eccConfig.witnessPoint)
      (actionConfigureContext G counts) := by
  let ecc := eccConfigureCertificate G counts
  apply (AddressIntegrity.circuit.configureCertificate
    (((configure G).output counts).eccConfig.mul,
      ((configure G).output counts).eccConfig.witnessPoint) {}
    ⟨ecc.mul.configured, ecc.witnessPointNonIdFormal.configured⟩).mono
  · intro gate hgate
    have hgates : AddressIntegrity.circuit.keygenRequirements.gates
        (((configure G).output counts).eccConfig.mul,
          ((configure G).output counts).eccConfig.witnessPoint)
        ⟨ecc.mul.configured, ecc.witnessPointNonIdFormal.configured⟩ =
        ecc.mul.configured.gates ++
          ecc.witnessPointNonIdFormal.configured.gates := rfl
    rw [hgates, show ((AddressIntegrity.circuit.configure
      (((configure G).output counts).eccConfig.mul,
        ((configure G).output counts).eccConfig.witnessPoint)).delta {}).gates = []
      from rfl, List.append_nil] at hgate
    rcases List.mem_append.mp hgate with hmul | hwitness
    · exact ecc.mul.gates_of_configured gate hmul
    · exact ecc.witnessPointNonIdFormal.gates_of_configured gate hwitness
  · intro argument hargument
    have hlookups : AddressIntegrity.circuit.keygenRequirements.lookups
        (((configure G).output counts).eccConfig.mul,
          ((configure G).output counts).eccConfig.witnessPoint)
        ⟨ecc.mul.configured, ecc.witnessPointNonIdFormal.configured⟩ =
        ecc.mul.configured.lookups ++
          ecc.witnessPointNonIdFormal.configured.lookups := rfl
    rw [hlookups, show ((AddressIntegrity.circuit.configure
      (((configure G).output counts).eccConfig.mul,
        ((configure G).output counts).eccConfig.witnessPoint)).delta {}).lookups = []
      from rfl, List.append_nil] at hargument
    rcases List.mem_append.mp hargument with hmul | hwitness
    · exact ecc.mul.lookups_of_configured argument hmul
    · exact ecc.witnessPointNonIdFormal.lookups_of_configured argument hwitness

/-- DeriveNullifier composed from its two direct chip certificates and two ECC capabilities. -/
def deriveNullifierCertificate (G : Generators) (B : Bases)
    (counts : ConfigureCounts) :
    (DeriveNullifier.circuit B.nullifierK).ConfigurationCertificate
      (((configure G).output counts).poseidonConfig,
        ((configure G).output counts).addChipConfig,
        ((configure G).output counts).eccConfig.mulFixedBaseField,
        ((configure G).output counts).eccConfig.add)
      (actionConfigureContext G counts) := by
  let poseidon := poseidonHashCertificate G counts
  let addChip := addChipCertificate G counts
  let ecc := eccConfigureCertificate G counts
  apply ((DeriveNullifier.circuit B.nullifierK).configureCertificate
    (((configure G).output counts).poseidonConfig,
      ((configure G).output counts).addChipConfig,
      ((configure G).output counts).eccConfig.mulFixedBaseField,
      ((configure G).output counts).eccConfig.add) {}
    ⟨poseidon.configured, addChip.configured,
      (ecc.mulFixedBaseField B.nullifierK).configured,
      ecc.addFormal.configured⟩).mono
  · intro gate hgate
    simp only [DeriveNullifier.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, DeriveNullifier.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hgate
    rcases hgate with ((hposeidon | haddChip) | hbase) | haddGate
    · exact poseidon.gates_of_configured gate hposeidon
    · exact addChip.gates_of_configured gate haddChip
    · exact (ecc.mulFixedBaseField B.nullifierK).gates_of_configured gate hbase
    · exact ecc.addFormal.gates_of_configured gate haddGate
  · intro argument hargument
    simp only [DeriveNullifier.circuit, FormalCircuit.keygenRequirements,
      ElaboratedCircuit.keygenRequirements, DeriveNullifier.keygenRequirements,
      Configure.delta_pure, List.append_nil, List.mem_append] at hargument
    rcases hargument with ((hposeidon | haddChip) | hbase) | haddLookup
    · exact poseidon.lookups_of_configured argument hposeidon
    · exact addChip.lookups_of_configured argument haddChip
    · exact (ecc.mulFixedBaseField B.nullifierK).lookups_of_configured argument hbase
    · exact ecc.addFormal.lookups_of_configured argument haddLookup

end Zcash.Circuits.Action.Circuit
