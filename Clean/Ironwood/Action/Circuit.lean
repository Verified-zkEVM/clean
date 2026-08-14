import Clean.Halo2.CircuitTypeDeriving
import Clean.Ironwood.Ecc.Chip
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Utilities.AddChip
import Clean.Ironwood.Sinsemilla.Merkle
import Clean.Ironwood.CommitIvk.MainBundle
import Clean.Ironwood.NoteCommit.MainBundle
import Clean.Ironwood.Action.DeriveNullifier
import Clean.Ironwood.Action.ValueCommit
import Clean.Ironwood.Action.SpendAuthority
import Clean.Ironwood.Action.AddressIntegrity

/-!
# The Orchard Action circuit (Ironwood): configure

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, `impl plonk::Circuit for Circuit` —
`fn configure` (lines 271-459), VK-exact in registration order:
the ten advices, the `q_orchard` gate, the add chip, the three lookup table columns,
the `primary` instance column, equality on all advices, the eight Lagrange fixed
columns (+ constants on the first), the range check, the ECC chip, Poseidon, the two
Sinsemilla/Merkle pairs, CommitIvk, and the two NoteCommit chips.

`fn synthesize` (lines 461-828), in exact region-creation order: the generator-table
load, the eight shared witness regions, the 32-layer Merkle path (16 layers per
Sinsemilla instance), value-commit integrity, nullifier integrity, spend authority,
diversified-address integrity (CommitIvk + [ivk] g_d_old), old/new note-commitment
integrity, and the final `"Orchard circuit checks"` region (copies, the three
`assign_advice_from_instance` public inputs, `q_orchard`).
-/

namespace Zcash.Circuits.Action.Circuit

open Halo2
open Specs.Sinsemilla (Generators)

/-- Rust `Config` (`circuit.rs:120-137`): everything `synthesize` consumes. The shared
lookup config (`range_check`) is carried explicitly (Rust reaches it through the chips). -/
structure Config where
  primary : Column .instance
  qOrchard : Selector
  advices : Fin 10 → Column .advice
  addChipConfig : AddChip.Config
  eccConfig : Ecc.EccConfig
  poseidonConfig : Poseidon.Config
  sinsemilla1 : Sinsemilla.HashPiece.Config
  merkle1 : Sinsemilla.Merkle.Config
  sinsemilla2 : Sinsemilla.HashPiece.Config
  merkle2 : Sinsemilla.Merkle.Config
  commitIvkConfig : CommitIvk.Config
  noteCommitOld : NoteCommit.Config
  noteCommitNew : NoteCommit.Config
  lookupConfig : LookupRangeCheck.Config 10

/-- The `"Orchard circuit checks"` gate (`circuit.rs:290-329`): the four top-level value
checks over `advices[0..8]` at the current row, in the source's constraint order. -/
def orchardGate (qOrchard : Selector) (advices : Fin 10 → Column .advice) : Gate Fp :=
  let vOld : Expression Fp Query := queryAdvice (advices 0) 0
  let vNew : Expression Fp Query := queryAdvice (advices 1) 0
  let magnitude : Expression Fp Query := queryAdvice (advices 2) 0
  let sign : Expression Fp Query := queryAdvice (advices 3) 0
  let root : Expression Fp Query := queryAdvice (advices 4) 0
  let anchor : Expression Fp Query := queryAdvice (advices 5) 0
  let enableSpends : Expression Fp Query := queryAdvice (advices 6) 0
  let enableOutputs : Expression Fp Query := queryAdvice (advices 7) 0
  Gate.withSelector "Orchard circuit checks" qOrchard
    [vOld, vNew, magnitude, sign, root, anchor, enableSpends, enableOutputs]
    [ ("v_old - v_new = magnitude * sign", vOld - vNew - magnitude * sign),
      ("Either v_old = 0, or root = anchor", vOld * (root - anchor)),
      ("v_old = 0 or enable_spends = 1", vOld * ((1 : Fp) - enableSpends)),
      ("v_new = 0 or enable_outputs = 1", vNew * ((1 : Fp) - enableOutputs)) ]

@[circuit_norm, keygen_norm] theorem orchardGate_selector
    (qOrchard : Selector) (advices : Fin 10 → Column .advice) :
    (orchardGate qOrchard advices).selector = qOrchard := rfl

/-- Columns and shared chips allocated before the composite chip assembly. -/
structure ConfigureBase where
  primary : Column .instance
  qOrchard : Selector
  advices : Fin 10 → Column .advice
  addChipConfig : AddChip.Config
  genTable : Sinsemilla.GeneratorTableConfig
  lagrangeCoeffs : Fin 8 → Column .fixed
  lookupConfig : LookupRangeCheck.Config 10

private structure ConfigureShared where
  primary : Column .instance
  qOrchard : Selector
  advices : Fin 10 → Column .advice
  addChipConfig : AddChip.Config
  genTable : Sinsemilla.GeneratorTableConfig
  lagrangeCoeffs : Fin 8 → Column .fixed

/-- The ten advice-column allocations at the start of Action configuration. Kept as a
small configure program so its elaborated metadata composes without reducing the full
Action configure chain. -/
def configureAdvices : Configure Fp (Fin 10 → Column .advice) := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  let a9 ← adviceColumn
  return ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]

@[configure_selector_norm, keygen_norm]
private theorem configureAdvices_delta_gates (counts) :
    (configureAdvices.delta counts).gates = [] := by
  simp [configureAdvices]

@[configure_selector_norm, keygen_norm]
private theorem configureAdvices_delta_lookups (counts) :
    (configureAdvices.delta counts).lookups = [] := by
  simp [configureAdvices]

@[reducible] private def configureAdvicesInferred :
    ElaboratedConfigure configureAdvices := by
  unfold configureAdvices
  infer_instance

private theorem configureAdvices_selectorRequirements (counts) :
    configureAdvicesInferred.selectorRequirements counts := by
  dsimp only [configureAdvicesInferred, configureAdvices]
  simp [configure_selector_norm]

private instance : ElaboratedConfigure configureAdvices :=
  configureAdvicesInferred.closeSelectorRequirements
    configureAdvices_selectorRequirements

def configureAdviceEqualitiesLow (advices : Fin 10 → Column .advice) :
    Configure Fp Unit := do
  enableEquality (advices 0); enableEquality (advices 1)
  enableEquality (advices 2); enableEquality (advices 3)
  enableEquality (advices 4)

@[configure_selector_norm, keygen_norm]
private theorem configureAdviceEqualitiesLow_delta_gates
    (advices : Fin 10 → Column .advice) (counts) :
    ((configureAdviceEqualitiesLow advices).delta counts).gates = [] := by
  simp [configureAdviceEqualitiesLow]

@[configure_selector_norm, keygen_norm]
private theorem configureAdviceEqualitiesLow_delta_lookups
    (advices : Fin 10 → Column .advice) (counts) :
    ((configureAdviceEqualitiesLow advices).delta counts).lookups = [] := by
  simp [configureAdviceEqualitiesLow]

@[reducible] private def configureAdviceEqualitiesLowInferred
    (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureAdviceEqualitiesLow advices) := by
  unfold configureAdviceEqualitiesLow
  infer_instance

private theorem configureAdviceEqualitiesLow_selectorRequirements
    (advices : Fin 10 → Column .advice) (counts) :
    (configureAdviceEqualitiesLowInferred advices).selectorRequirements counts := by
  dsimp only [configureAdviceEqualitiesLowInferred,
    configureAdviceEqualitiesLow]
  simp [configure_selector_norm]

private instance (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureAdviceEqualitiesLow advices) :=
  (configureAdviceEqualitiesLowInferred advices).closeSelectorRequirements
    (configureAdviceEqualitiesLow_selectorRequirements advices)

def configureAdviceEqualitiesHigh (advices : Fin 10 → Column .advice) :
    Configure Fp Unit := do
  enableEquality (advices 5)
  enableEquality (advices 6); enableEquality (advices 7)
  enableEquality (advices 8); enableEquality (advices 9)

@[configure_selector_norm, keygen_norm]
private theorem configureAdviceEqualitiesHigh_delta_gates
    (advices : Fin 10 → Column .advice) (counts) :
    ((configureAdviceEqualitiesHigh advices).delta counts).gates = [] := by
  simp [configureAdviceEqualitiesHigh]

@[configure_selector_norm, keygen_norm]
private theorem configureAdviceEqualitiesHigh_delta_lookups
    (advices : Fin 10 → Column .advice) (counts) :
    ((configureAdviceEqualitiesHigh advices).delta counts).lookups = [] := by
  simp [configureAdviceEqualitiesHigh]

@[reducible] private def configureAdviceEqualitiesHighInferred
    (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureAdviceEqualitiesHigh advices) := by
  unfold configureAdviceEqualitiesHigh
  infer_instance

private theorem configureAdviceEqualitiesHigh_selectorRequirements
    (advices : Fin 10 → Column .advice) (counts) :
    (configureAdviceEqualitiesHighInferred advices).selectorRequirements counts := by
  dsimp only [configureAdviceEqualitiesHighInferred,
    configureAdviceEqualitiesHigh]
  simp [configure_selector_norm]

private instance (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureAdviceEqualitiesHigh advices) :=
  (configureAdviceEqualitiesHighInferred advices).closeSelectorRequirements
    (configureAdviceEqualitiesHigh_selectorRequirements advices)

/-- Equality registration for the public input and the ten Action advice columns. -/
def configureEqualities
    (primary : Column .instance) (advices : Fin 10 → Column .advice) :
    Configure Fp Unit := do
  enableEquality primary
  configureAdviceEqualitiesLow advices
  configureAdviceEqualitiesHigh advices

@[configure_selector_norm, keygen_norm]
private theorem configureEqualities_delta_gates
    (primary : Column .instance) (advices : Fin 10 → Column .advice) (counts) :
    ((configureEqualities primary advices).delta counts).gates = [] := by
  simp [configureEqualities, keygen_norm]

@[configure_selector_norm, keygen_norm]
private theorem configureEqualities_delta_lookups
    (primary : Column .instance) (advices : Fin 10 → Column .advice) (counts) :
    ((configureEqualities primary advices).delta counts).lookups = [] := by
  simp [configureEqualities, keygen_norm]

@[reducible] private def configureEqualitiesInferred
    (primary : Column .instance) (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureEqualities primary advices) := by
  unfold configureEqualities
  infer_instance

private theorem configureEqualities_selectorRequirements
    (primary : Column .instance) (advices : Fin 10 → Column .advice) (counts) :
    (configureEqualitiesInferred primary advices).selectorRequirements counts := by
  dsimp only [configureEqualitiesInferred, configureEqualities]
  simp [configure_selector_norm]

private instance (primary : Column .instance) (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configureEqualities primary advices) :=
  (configureEqualitiesInferred primary advices).closeSelectorRequirements
    (configureEqualities_selectorRequirements primary advices)

private theorem configureEqualities_advicePermutationColumn
    (primary : Column .instance) (advices : Fin 10 → Column .advice)
    (counts : ConfigureCounts) (index : Fin 10) :
    (advices index).toAny ∈
      ((configureEqualities primary advices).delta counts).permutationRequests := by
  fin_cases index <;>
    simp only [configureEqualities, configureAdviceEqualitiesLow,
      configureAdviceEqualitiesHigh, keygen_norm] <;>
    simp

private theorem configureEqualities_primaryPermutationColumn
    (primary : Column .instance) (advices : Fin 10 → Column .advice)
    (counts : ConfigureCounts) :
    primary.toAny ∈
      ((configureEqualities primary advices).delta counts).permutationRequests := by
  unfold configureEqualities
  apply Configure.mem_permutationRequests_delta_bind_left
  exact Configure.mem_permutationRequests_delta_enableEquality primary counts

/-- The eight Lagrange columns and their constant-enabled first column. -/
def configureLagrange : Configure Fp (Fin 8 → Column .fixed) := do
  let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
  let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
  let l6 ← fixedColumn; let l7 ← fixedColumn
  enableConstant l0
  return ![l0, l1, l2, l3, l4, l5, l6, l7]

@[configure_selector_norm, keygen_norm]
private theorem configureLagrange_delta_gates (counts) :
    (configureLagrange.delta counts).gates = [] := by
  simp [configureLagrange]

@[configure_selector_norm, keygen_norm]
private theorem configureLagrange_delta_lookups (counts) :
    (configureLagrange.delta counts).lookups = [] := by
  simp [configureLagrange]

@[reducible] private def configureLagrangeInferred :
    ElaboratedConfigure configureLagrange := by
  unfold configureLagrange
  infer_instance

private theorem configureLagrange_selectorRequirements (counts) :
    configureLagrangeInferred.selectorRequirements counts := by
  dsimp only [configureLagrangeInferred, configureLagrange]
  simp [configure_selector_norm]

private instance : ElaboratedConfigure configureLagrange :=
  configureLagrangeInferred.closeSelectorRequirements
    configureLagrange_selectorRequirements

/-- The shared columns and chips allocated before the range-check configuration. -/
def configureShared : Configure Fp ConfigureShared := do
  -- circuit.rs:273-284 — the ten advice columns
  let advices ← configureAdvices
  -- circuit.rs:290-329 — `q_orchard` + the top-level checks gate
  let qOrchard ← selector
  createGate (orchardGate qOrchard advices)
  -- circuit.rs:332 — the add chip (advices 7, 8 → 6)
  let addChipConfig ← AddChip.configure (advices 7) (advices 8) (advices 6)
  -- circuit.rs:335-340 — the Sinsemilla generator table columns
  let tableIdx ← lookupTableColumn
  let tableX ← lookupTableColumn
  let tableY ← lookupTableColumn
  let genTable : Sinsemilla.GeneratorTableConfig := { tableIdx, tableX, tableY }
  -- circuit.rs:343-344 — the public-input instance column
  let primary ← instanceColumn
  -- circuit.rs:347-349 — equality on all advices
  configureEqualities primary advices
  -- circuit.rs:356-365 — the eight Lagrange-coefficient fixed columns
  let lagrangeCoeffs ← configureLagrange
  return { primary, qOrchard, advices, addChipConfig, genTable,
           lagrangeCoeffs }

@[configure_selector_norm, keygen_norm]
private theorem configureShared_delta_gates (counts) :
    (configureShared.delta counts).gates =
      [orchardGate (configureShared.output counts).qOrchard
          (configureShared.output counts).advices,
        AddChip.addGate (configureShared.output counts).addChipConfig] := by
  simp [configureShared, AddChip.configure, keygen_norm]

@[configure_selector_norm, keygen_norm]
private theorem configureShared_delta_lookups (counts) :
    (configureShared.delta counts).lookups = [] := by
  simp [configureShared, AddChip.configure, keygen_norm]

@[configure_selector_norm, keygen_norm]
private theorem configureShared_qOrchard_index (counts) :
    (configureShared.output counts).qOrchard.index = counts.numSelectors := by
  simp [configureShared, configureAdvices, keygen_norm]

@[configure_selector_norm, keygen_norm]
private theorem configureShared_qAdd_index (counts) :
    (configureShared.output counts).addChipConfig.qAdd.index =
      counts.numSelectors + 1 := by
  simp [configureShared, configureAdvices, AddChip.configure, keygen_norm]

@[reducible] private def configureSharedInferred : ElaboratedConfigure configureShared := by
  unfold configureShared
  infer_instance

private theorem configureShared_selectorRequirements (counts) :
    configureSharedInferred.selectorRequirements counts := by
  dsimp only [configureSharedInferred, configure_selector_norm, configureShared]
  simp only [configure_selector_norm, and_true]
  simp [keygen_norm]

private instance : ElaboratedConfigure configureShared :=
  configureSharedInferred.closeSelectorRequirements
    configureShared_selectorRequirements

/-- Every advice column allocated by the shared Action prefix is registered for equality. -/
private theorem configureShared_advicePermutationColumn
    (counts : ConfigureCounts) (index : Fin 10) :
    ((configureShared.output counts).advices index).toAny ∈
      (configureShared.delta counts).permutationRequests := by
  unfold configureShared
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_left
  exact configureEqualities_advicePermutationColumn _ _ _ index

/-- The public-input column allocated by the shared Action prefix is registered for equality. -/
private theorem configureShared_primaryPermutationColumn
    (counts : ConfigureCounts) :
    (configureShared.output counts).primary.toAny ∈
      (configureShared.delta counts).permutationRequests := by
  unfold configureShared
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_right
  apply Configure.mem_permutationRequests_delta_bind_left
  exact configureEqualities_primaryPermutationColumn _ _ _

/-- The AddChip gate created by the shared prefix is present in that prefix's gate log. -/
private theorem configureShared_addChipGate (counts : ConfigureCounts) :
    AddChip.addGate (configureShared.output counts).addChipConfig ∈
      (configureShared.delta counts).gates := by
  unfold configureShared
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_left
  simp [AddChip.configure]

/-- The top-level Orchard gate created by the shared prefix is present in its gate log. -/
private theorem configureShared_orchardGate (counts : ConfigureCounts) :
    orchardGate (configureShared.output counts).qOrchard
      (configureShared.output counts).advices ∈
        (configureShared.delta counts).gates := by
  unfold configureShared
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_right
  apply Configure.mem_gates_delta_bind_left
  exact Configure.mem_gates_delta_createGate _ _

/-- The allocation prefix of Rust `Circuit::configure`, through the shared range check. -/
def configureBase : Configure Fp ConfigureBase := do
  let shared ← configureShared
  -- circuit.rs:375 — the shared 10-bit range check on `advices[9]`
  let lookupConfig ← LookupRangeCheck.configure 10
    (shared.advices 9) shared.genTable.tableIdx
  return { shared with lookupConfig }

@[reducible] private def configureBaseInferred : ElaboratedConfigure configureBase := by
  unfold configureBase
  infer_instance

private theorem configureBase_selectorRequirements (counts) :
    configureBaseInferred.selectorRequirements counts := by
  dsimp only [configureBaseInferred, configure_selector_norm, configureBase]
  simp [configure_selector_norm]

private instance : ElaboratedConfigure configureBase :=
  configureBaseInferred.closeSelectorRequirements
    configureBase_selectorRequirements

/-- Equality registration from the shared prefix survives the range-check suffix. -/
private theorem configureBase_advicePermutationColumn
    (counts : ConfigureCounts) (index : Fin 10) :
    ((configureBase.output counts).advices index).toAny ∈
      (configureBase.delta counts).permutationRequests := by
  unfold configureBase
  apply Configure.mem_permutationRequests_delta_bind_left
  exact configureShared_advicePermutationColumn counts index

/-- The shared public-input equality registration survives the range-check suffix. -/
private theorem configureBase_primaryPermutationColumn
    (counts : ConfigureCounts) :
    (configureBase.output counts).primary.toAny ∈
      (configureBase.delta counts).permutationRequests := by
  unfold configureBase
  apply Configure.mem_permutationRequests_delta_bind_left
  exact configureShared_primaryPermutationColumn counts

/-- The shared AddChip gate survives the range-check suffix. -/
private theorem configureBase_addChipGate (counts : ConfigureCounts) :
    AddChip.addGate (configureBase.output counts).addChipConfig ∈
      (configureBase.delta counts).gates := by
  unfold configureBase
  apply Configure.mem_gates_delta_bind_left
  exact configureShared_addChipGate counts

/-- The shared top-level Orchard gate survives the range-check suffix. -/
private theorem configureBase_orchardGate (counts : ConfigureCounts) :
    orchardGate (configureBase.output counts).qOrchard
      (configureBase.output counts).advices ∈
        (configureBase.delta counts).gates := by
  unfold configureBase
  apply Configure.mem_gates_delta_bind_left
  exact configureShared_orchardGate counts

/-- The keygen capabilities exported by Action's shared configuration prefix. -/
structure ConfigureBaseCertificate (counts : ConfigureCounts)
    (context : KeygenContext Fp) where
  orchardGate : orchardGate (configureBase.output counts).qOrchard
    (configureBase.output counts).advices ∈ context.gates
  addChip : AddChip.addFormal.ConfigurationCertificate
    (configureBase.output counts).addChipConfig context
  shortRange : ∀ numBits,
    (LookupRangeCheck.shortRangeCheck 10 numBits).ConfigurationCertificate
      (configureBase.output counts).lookupConfig context
  bitshiftGate : LookupRangeCheck.bitshiftGate 10
    (configureBase.output counts).lookupConfig ∈ context.gates
  rangeLookup : LookupRangeCheck.rangeCheckLookup 10
    (configureBase.output counts).lookupConfig ∈ context.lookups
  advicePermutationColumn : ∀ index,
    ((configureBase.output counts).advices index).toAny ∈ context.permutationColumns
  primaryPermutationColumn :
    (configureBase.output counts).primary.toAny ∈ context.permutationColumns

namespace ConfigureBaseCertificate

/-- Transport the complete shared-prefix certificate at once. -/
def mono {counts : ConfigureCounts} {source target : KeygenContext Fp}
    (certificate : ConfigureBaseCertificate counts source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigureBaseCertificate counts target where
  orchardGate := gates _ certificate.orchardGate
  addChip := certificate.addChip.mono gates lookups permutationColumns
  shortRange numBits :=
    (certificate.shortRange numBits).mono gates lookups permutationColumns
  bitshiftGate := gates _ certificate.bitshiftGate
  rangeLookup := lookups _ certificate.rangeLookup
  advicePermutationColumn index :=
    permutationColumns _ (certificate.advicePermutationColumn index)
  primaryPermutationColumn :=
    permutationColumns _ certificate.primaryPermutationColumn

end ConfigureBaseCertificate

/-- Construct the shared-prefix capabilities inside the owner of `configureBase`. -/
def configureBaseCertificate (counts : ConfigureCounts) :
    ConfigureBaseCertificate counts
      { gates := (configureBase.delta counts).gates
        lookups := (configureBase.delta counts).lookups
        permutationColumns := (configureBase.delta counts).permutationRequests } := by
  let base := configureBase.output counts
  let shared := configureShared.output counts
  let addCounts : ConfigureCounts :=
    { counts with
      numAdviceColumns := counts.numAdviceColumns + 10
      numSelectors := counts.numSelectors + 1 }
  refine
    { orchardGate := ?_
      addChip := ?_
      shortRange := ?_
      bitshiftGate := ?_
      rangeLookup := ?_
      advicePermutationColumn := ?_
      primaryPermutationColumn := ?_ }
  · exact configureBase_orchardGate counts
  · apply (AddChip.addFormalConfigureCertificate
      (base.advices 7) (base.advices 8) (base.advices 6) addCounts).mono
    · intro gate hgate
      simp [AddChip.configure] at hgate
      subst gate
      exact configureBase_addChipGate counts
    · intro argument hargument
      simp [AddChip.configure] at hargument
    · intro column hcolumn
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hcolumn
      rcases hcolumn with (hcolumn | hcolumn) | hcolumn
      · subst column
        exact configureBase_advicePermutationColumn counts 7
      · subst column
        exact configureBase_advicePermutationColumn counts 8
      · simp only [AddChip.configure, keygen_norm] at hcolumn
  · intro numBits
    apply (LookupRangeCheck.shortRangeConfigureCertificate 10 numBits
      (shared.advices 9) shared.genTable.tableIdx
      (configureShared.finalCounts counts)).mono
    · intro gate hgate
      simp only
      unfold configureBase
      apply Configure.mem_gates_delta_bind_right
      exact hgate
    · intro argument hargument
      simp only
      unfold configureBase
      apply Configure.mem_lookups_delta_bind_right
      exact hargument
    · intro column hcolumn
      simp only
      unfold configureBase
      apply Configure.mem_permutationRequests_delta_bind_right
      exact hcolumn
  · simp only
    unfold configureBase
    apply Configure.mem_gates_delta_bind_right
    apply Configure.mem_gates_delta_bind_left
    rw [LookupRangeCheck.configure_delta_gates]
    simp
  · unfold configureBase
    simp only
    apply Configure.mem_lookups_delta_bind_right
    apply Configure.mem_lookups_delta_bind_left
    rw [LookupRangeCheck.configure_delta_lookups]
    simp
  · intro index
    exact configureBase_advicePermutationColumn counts index
  · exact configureBase_primaryPermutationColumn counts

/-- The composite-chip suffix of Rust `Circuit::configure`. -/
def configureChips (G : Generators) (base : ConfigureBase) :
    Configure Fp Config := do
  let advices := base.advices
  let lagrangeCoeffs := base.lagrangeCoeffs
  let a0 := advices 0; let a1 := advices 1; let a2 := advices 2
  let a3 := advices 3; let a4 := advices 4; let a5 := advices 5
  let a6 := advices 6; let a7 := advices 7; let a8 := advices 8
  let a9 := advices 9
  let l0 := lagrangeCoeffs 0; let l1 := lagrangeCoeffs 1
  let l2 := lagrangeCoeffs 2; let l3 := lagrangeCoeffs 3
  let l4 := lagrangeCoeffs 4; let l5 := lagrangeCoeffs 5
  let l6 := lagrangeCoeffs 6; let l7 := lagrangeCoeffs 7
  -- circuit.rs:379-380 — the ECC chip
  let eccConfig ← Ecc.configure advices lagrangeCoeffs base.lookupConfig
  -- circuit.rs:383-391 — Poseidon (state `advices[6..9]`, sbox `advices[5]`,
  -- `rc_a = lagrange[2..5]`, `rc_b = lagrange[5..8]`)
  let poseidonConfig ← Poseidon.configure ![a6, a7, a8] a5 ![l2, l3, l4] ![l5, l6, l7]
  -- circuit.rs:397-410 — Sinsemilla 1 (advices[0..5], pieces `advices[6]`,
  -- `y_Q` fixed `lagrange[0]`) + Merkle 1
  let sinsemilla1 ←
    Sinsemilla.HashPiece.configure G a0 a1 a2 a3 a4 a6 l0 base.genTable
  let merkle1 ← Sinsemilla.Merkle.configure sinsemilla1
  -- circuit.rs:416-429 — Sinsemilla 2 (advices[5..], pieces `advices[7]`,
  -- `y_Q` fixed `lagrange[1]`) + Merkle 2
  let sinsemilla2 ←
    Sinsemilla.HashPiece.configure G a5 a6 a7 a8 a9 a7 l1 base.genTable
  let merkle2 ← Sinsemilla.Merkle.configure sinsemilla2
  -- circuit.rs:433 — CommitIvk
  let commitIvkConfig ← CommitIvk.configure advices
  -- circuit.rs:437-443 — the two NoteCommit chips
  let noteCommitOld ← NoteCommit.configure advices
  let noteCommitNew ← NoteCommit.configure advices
  return { primary := base.primary, qOrchard := base.qOrchard, advices,
           addChipConfig := base.addChipConfig, eccConfig, poseidonConfig,
           sinsemilla1, merkle1, sinsemilla2, merkle2, commitIvkConfig,
           noteCommitOld, noteCommitNew, lookupConfig := base.lookupConfig }

@[reducible] private def configureChipsInferred (G : Generators) (base : ConfigureBase) :
    ElaboratedConfigure (configureChips G base) := by
  unfold configureChips
  infer_instance

private theorem configureChips_selectorRequirements
    (G : Generators) (base : ConfigureBase) (counts) :
    (configureChipsInferred G base).selectorRequirements counts := by
  dsimp only [configureChipsInferred, configure_selector_norm, configureChips]
  simp only [configure_selector_norm, and_true]

private instance (G : Generators) (base : ConfigureBase) :
    ElaboratedConfigure (configureChips G base) :=
  ((configureChipsInferred G base).closeSelectorRequirements
    (configureChips_selectorRequirements G base)).withExternalSelectorSummary
      (fun _ => {}) (by
        intro counts
        rw [ElaboratedConfigure.closeSelectorRequirements_selectorSummary,
          (configureChipsInferred G base).externalSelectorSummary_eq]
        simp only [configure_selector_norm])

/-- Rust `Circuit::configure` (`circuit.rs:271-459`), VK-exact registration order. -/
def configure (G : Generators) : Configure Fp Config := do
  let base ← configureBase
  configureChips G base

@[keygen_norm] theorem configure_output_primary (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).primary =
      (configureBase.output counts).primary := by
  simp [configure, configureChips]

@[keygen_norm] theorem configure_output_qOrchard (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).qOrchard =
      (configureBase.output counts).qOrchard := by
  simp [configure, configureChips]

@[keygen_norm] theorem configure_output_advices (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).advices =
      (configureBase.output counts).advices := by
  simp [configure, configureChips]

@[keygen_norm] theorem configure_output_eccConfig (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).eccConfig =
      (Ecc.configure (configureBase.output counts).advices
        (configureBase.output counts).lagrangeCoeffs
        (configureBase.output counts).lookupConfig).output
          (configureBase.finalCounts counts) := by
  simp [configure, configureChips]

@[keygen_norm] theorem configure_output_witnessPoint_x (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).eccConfig.witnessPoint.x =
      (configureBase.output counts).advices 0 := by
  simp [configure, configureChips, Ecc.configure, Ecc.WitnessPoint.configure]

@[keygen_norm] theorem configure_output_witnessPoint_y (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).eccConfig.witnessPoint.y =
      (configureBase.output counts).advices 1 := by
  simp [configure, configureChips, Ecc.configure, Ecc.WitnessPoint.configure]

@[keygen_norm] theorem configure_output_add_xQR (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).eccConfig.add.xQR =
      (configureBase.output counts).advices 2 := by
  simp [configure, configureChips, Ecc.configure, Ecc.Add.add]

@[keygen_norm] theorem configure_output_add_yQR (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).eccConfig.add.yQR =
      (configureBase.output counts).advices 3 := by
  simp [configure, configureChips, Ecc.configure, Ecc.Add.add]

@[keygen_norm] theorem configure_output_merkle1_xA (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).merkle1.sinsemilla.xA =
      (configureBase.output counts).advices 0 := by
  simp [configure, configureChips, Sinsemilla.HashPiece.configure,
    Sinsemilla.Merkle.configure]

@[keygen_norm] theorem configure_output_merkle2_xA (G : Generators)
    (counts : ConfigureCounts) :
    ((configure G).output counts).merkle2.sinsemilla.xA =
      (configureBase.output counts).advices 5 := by
  simp [configure, configureChips, Sinsemilla.HashPiece.configure,
    Sinsemilla.Merkle.configure]

/-- The fixed-column identities exported by the closed Action configuration. Keeping
this allocation summary next to `configure` lets later lawfulness proofs reason about
the small column interface without reducing the full gate stack. -/
theorem configure_fixedColumn_indices (G : Generators) :
    let cfg := (configure G).output {}
    cfg.sinsemilla1.generatorTable.tableIdx.inner = ⟨0⟩ ∧
    cfg.sinsemilla1.generatorTable.tableX.inner = ⟨1⟩ ∧
    cfg.sinsemilla1.generatorTable.tableY.inner = ⟨2⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 0 = ⟨3⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 1 = ⟨4⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 2 = ⟨5⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 3 = ⟨6⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 4 = ⟨7⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 5 = ⟨8⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 6 = ⟨9⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 7 = ⟨10⟩ ∧
    cfg.eccConfig.mulFixedShort.superConfig.fixedZ = ⟨11⟩ ∧
    cfg.sinsemilla1.qS2 = ⟨12⟩ ∧
    cfg.sinsemilla2.qS2 = ⟨13⟩ ∧
    ((configure G).finalCounts {}).numFixedColumns = 14 := by
  simp [configure, configureBase, configureChips, configureShared,
    configureAdvices, configureAdviceEqualitiesLow,
    configureAdviceEqualitiesHigh, configureEqualities, configureLagrange,
    lookupTableColumn, AddChip.configure, LookupRangeCheck.configure,
    Poseidon.configure, Sinsemilla.HashPiece.configure,
    Sinsemilla.Merkle.configure, CommitIvk.configure, NoteCommit.configure,
    Ecc.configure, Ecc.WitnessPoint.configure, Ecc.AddIncomplete.add,
    Ecc.Add.add, Ecc.Mul.configure, Ecc.MulIncomplete.configure,
    Ecc.MulComplete.configure, Ecc.MulOverflow.configure,
    Ecc.MulFixed.configure, Ecc.MulFixed.FullWidth.configure,
    Ecc.MulFixed.Short.configure, Ecc.MulFixed.BaseFieldElem.configure,
    DecomposeRunningSum.configure, CondSwap.configure,
    Sinsemilla.Merkle.Gate.configure,
    NoteCommit.DecomposeB.configure, NoteCommit.DecomposeD.configure,
    NoteCommit.DecomposeE.configure, NoteCommit.DecomposeG.configure,
    NoteCommit.DecomposeH.configure, NoteCommit.GdCanonicity.configure,
    NoteCommit.PkdCanonicity.configure, NoteCommit.ValueCanonicity.configure,
    NoteCommit.RhoCanonicity.configure, NoteCommit.PsiCanonicity.configure,
    NoteCommit.YCanonicity.configure]

/-- The closed Action configuration allocates ten advice columns. -/
theorem configure_finalCounts_numAdviceColumns (G : Generators) :
    ((configure G).finalCounts {}).numAdviceColumns = 10 := by
  configure_norm

/-- The closed Action configuration allocates fourteen fixed columns. -/
theorem configure_finalCounts_numFixedColumns (G : Generators) :
    ((configure G).finalCounts {}).numFixedColumns = 14 := by
  configure_norm

/-- The closed Action configuration allocates one instance column. -/
theorem configure_finalCounts_numInstanceColumns (G : Generators) :
    ((configure G).finalCounts {}).numInstanceColumns = 1 := by
  configure_norm

private instance elaboratedConfigure (G : Generators) : ElaboratedConfigure (configure G) := by
  unfold configure
  infer_instance

private theorem configure_instanceQueries (G : Generators) : ∀ counts,
    ((configure G).delta counts).instanceQueries =
      [(⟨counts.numInstanceColumns⟩, 0)] := by
  configure_norm

private theorem configure_selectorRequirements (G : Generators) (counts) :
    (elaboratedConfigure G).selectorRequirements counts := by
  dsimp +instances only [configure_selector_norm, configure]
  simp only [configure_selector_norm, and_true]

private theorem configure_queryRequirements (G : Generators) (counts) :
    (elaboratedConfigure G).queryRequirements counts := by
  dsimp +instances only [configure_query_norm, configure, configureBase,
    configureChips, configureShared]
  simp +arith [configureBase, configureChips, configureShared,
    configureAdvices, configureAdviceEqualitiesLow,
    configureAdviceEqualitiesHigh, configureEqualities, configureLagrange,
    lookupTableColumn, AddChip.configure, LookupRangeCheck.configure,
    Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CommitIvk.configure, NoteCommit.configure,
    Ecc.configure, Ecc.WitnessPoint.configure, Ecc.AddIncomplete.add,
    Ecc.Add.add, Ecc.Mul.configure, Ecc.MulIncomplete.configure,
    Ecc.MulComplete.configure, Ecc.MulOverflow.configure,
    Ecc.MulFixed.configure, Ecc.MulFixed.FullWidth.configure,
    Ecc.MulFixed.Short.configure, Ecc.MulFixed.BaseFieldElem.configure,
    DecomposeRunningSum.configure,
    Configure.finalCounts_numAdviceColumns,
    Configure.finalCounts_numFixedColumns,
    Configure.finalCounts_numInstanceColumns]

/-- Reduced configure metadata shared by both Action synthesis bundles. Public
instance-query and selector requirements are stored in their compact normal forms. -/
@[reducible] def configureElaborated (G : Generators) :
    ElaboratedConfigure (configure G) :=
  let inferred : ElaboratedConfigure (configure G) := inferInstance
  { inferred with
    instanceQueries counts := [(⟨counts.numInstanceColumns⟩, 0)]
    instanceQueries_eq := configure_instanceQueries G
    selectorRequirements _ := True
    selectorsAllocated counts _ :=
      (elaboratedConfigure G).selectorsAllocated counts
        (configure_selectorRequirements G counts)
    lookupSelectorsCompatible counts _ :=
      (elaboratedConfigure G).lookupSelectorsCompatible counts
        (configure_selectorRequirements G counts)
    queryRequirements _ := True
    queriesLawful counts _ :=
      (elaboratedConfigure G).queriesLawful counts
        (configure_queryRequirements G counts) }

/-! ## Synthesize -/

open Ecc.MulFixed (FixedBase)

/-- The public-input rows of the `primary` instance column (`circuit.rs:78-86`). -/
def ANCHOR : ℕ := 0
def CV_NET_X : ℕ := 1
def CV_NET_Y : ℕ := 2
def NF_OLD : ℕ := 3
def RK_X : ℕ := 4
def RK_Y : ℕ := 5
def CMX : ℕ := 6
def ENABLE_SPEND : ℕ := 7
def ENABLE_OUTPUT : ℕ := 8
def DISABLE_CROSS_ADDRESS : ℕ := 9

/-- The fixed bases and Sinsemilla domain points the Action circuit is instantiated at
(Rust reaches them through `OrchardFixedBases` / the domain constants). -/
structure Bases where
  nullifierK : FixedBase
  valueCommitV : Ecc.MulFixed.Short.FixedBase
  valueCommitR : FixedBase
  spendAuthG : FixedBase
  commitIvkR : FixedBase
  noteCommitR : FixedBase
  merkleQ : Point Fp
  merkleQ_onCurve : merkleQ.OnCurve
  ivkQ : Point Fp
  ivkQ_onCurve : ivkQ.OnCurve
  noteQ : Point Fp
  noteQ_onCurve : noteQ.OnCurve

/-- Prover-only ℕ-indexed family of Merkle sibling witness programs (one per layer). -/
structure UnconstrainedSibs (F : Type) where
  programs : ℕ → WitgenIR F 1

@[reducible] instance : CircuitType UnconstrainedSibs where
  Var F := ℕ → WitgenIR F 1
  Value := unit
  ProverValue F := ℕ → F
  evalVerifier _ _ := ()
  evalProver pe f := fun i => ((f i).eval pe)[0]

instance : ProvableType (Value UnconstrainedSibs) :=
  (inferInstance : ProvableType unit)

/-- Prover-only ℕ-indexed family of Merkle swap flags (native closures — the cond-swap
choice is a `Bool` the prover computes from its environment). -/
structure UnconstrainedSwaps (F : Type) where
  flags : ℕ → Placed ProverEnvironment F → Bool

@[reducible] instance : CircuitType UnconstrainedSwaps where
  Var F := ℕ → Placed ProverEnvironment F → Bool
  Value := unit
  ProverValue _ := ℕ → Bool
  evalVerifier _ _ := ()
  evalProver pe f := fun i => f i pe

instance : ProvableType (Value UnconstrainedSwaps) :=
  (inferInstance : ProvableType unit)

/-- The Action circuit's private inputs as a prover-only hint block, derived per-field
(the `Unconstrained` pattern): the `Var` view is the witness programs, the verifier
value is erased, and the prover value is the evaluated data. Mirrors the Rust
`Circuit` struct's `Value<_>` fields; the fixed-base-mul scalars are nat-valued
reading programs, their 85 window witnesses derived inside the mul bundles. -/
structure PrivateInputs (F : Type) where
  psiOld : Unconstrained field F
  rhoOld : Unconstrained field F
  nk : Unconstrained field F
  vOld : Unconstrained field F
  vNew : Unconstrained field F
  psiNew : Unconstrained field F
  magnitude : Unconstrained field F
  sign : Unconstrained field F
  cmOld : Unconstrained Point F
  gdOld : Unconstrained Point F
  akP : Unconstrained Point F
  pkDOld : Unconstrained Point F
  gdNew : Unconstrained Point F
  pkdNew : Unconstrained Point F
  rcv : UnconstrainedNat F
  alpha : UnconstrainedNat F
  rivk : UnconstrainedNat F
  rcmOld : UnconstrainedNat F
  rcmNew : UnconstrainedNat F
  merkleSib : UnconstrainedSibs F
  merkleSwap : UnconstrainedSwaps F
deriving CircuitType

/-- The witness-program view of the private inputs (the Rust `Circuit` struct). -/
abbrev Witnesses (F : Type) := PrivateInputs.Var F

/-- The evaluated (prover-view) private inputs. -/
abbrev WitnessData (F : Type) := PrivateInputs.ProverValue F

/-!
## Top-level prover hints

The top-level Action circuit has no verifier-visible input.  Its prover choices enter
through one fixed witness program built from `ProverEnvironment.hint`: key generation
sees this program but does not evaluate it, while witness generation evaluates the same
program against the prover's runtime hint map.

The keys below are local data of this circuit, not a framework-wide convention.
-/

/-- One field-valued Action hint, stored as the sole column of row zero. -/
private def fieldHint (key : String) :
    Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp) :=
  pure (.hintGet key 1 (.const 0) 0)

/-- One point-valued Action hint, stored as `(x,y)` in row zero. -/
private def pointHint (key : String) :
    Witgen.MOver Fp (AssignedCell Fp) (Point (FExpr Fp)) :=
  pure {
    x := .hintGet key 2 (.const 0) 0
    y := .hintGet key 2 (.const 0) 1
  }

/-- One Nat-valued Action hint, read through the field-to-Nat bridge. -/
private def natHint (key : String) :
    Witgen.MOver Fp (AssignedCell Fp) (NExpr Fp) :=
  pure (.val (.hintGet key 1 (.const 0) 0))

/-- A Merkle sibling hint at layer `i`. -/
private def merkleSiblingHint (i : ℕ) : WitgenIR Fp 1 :=
  .ofFExpr (.hintGet "orchard.action.merkle_sibling" 1 (.const i) 0)

/--
A Merkle swap hint at layer `i`.  This remains the existing native escape hatch for
now, but reads the same `ProverHint` store as structured `hintGet`; it can later become
`UnconstrainedBool` without changing the top-level circuit interface.
-/
private def merkleSwapHint (i : ℕ) :
    Placed ProverEnvironment Fp → Bool := fun env =>
  Witgen.FExprOver.eval
      ({ env := env } : Witgen.CtxOver Fp (Placed ProverEnvironment Fp))
      ((.hintGet "orchard.action.merkle_swap" 1 (.const i) 0) : FExpr Fp) == 1

/--
The one fixed private-witness program of the top-level Action circuit.  All actual
values are chosen at proving time through `ProverHint`; callers do not parameterize
synthesis with alternative witness programs.
-/
def hintWitnesses : Witnesses Fp := {
  psiOld := fieldHint "orchard.action.psi_old"
  rhoOld := fieldHint "orchard.action.rho_old"
  nk := fieldHint "orchard.action.nk"
  vOld := fieldHint "orchard.action.v_old"
  vNew := fieldHint "orchard.action.v_new"
  psiNew := fieldHint "orchard.action.psi_new"
  magnitude := fieldHint "orchard.action.magnitude"
  sign := fieldHint "orchard.action.sign"
  cmOld := pointHint "orchard.action.cm_old"
  gdOld := pointHint "orchard.action.gd_old"
  akP := pointHint "orchard.action.ak_p"
  pkDOld := pointHint "orchard.action.pkd_old"
  gdNew := pointHint "orchard.action.gd_new"
  pkdNew := pointHint "orchard.action.pkd_new"
  rcv := natHint "orchard.action.rcv"
  alpha := natHint "orchard.action.alpha"
  rivk := natHint "orchard.action.rivk"
  rcmOld := natHint "orchard.action.rcm_old"
  rcmNew := natHint "orchard.action.rcm_new"
  merkleSib := merkleSiblingHint
  merkleSwap := merkleSwapHint
}

/-- Rust `assign_free_advice` (`circuit.rs:101-113`): the `"load private"` region, one
advice cell at row 0. -/
def loadPrivate (col : Column .advice) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion "load private" (assignAdvice col 0 w)

/-- A private-witness load copies no pre-existing cells. -/
theorem loadPrivate_copyCellsAssignedFrom
    (col : Column .advice) (w : WitgenIR Fp 1) (region : RegionIndex)
    (available : List Cell) :
    ((loadPrivate col w).operations region).CopyCellsAssignedFrom
      region available := by
  unfold loadPrivate
  keygen_registration

/-- The cell returned by a private-witness load is assigned in its region. -/
theorem loadPrivate_output_cell_assigned
    (col : Column .advice) (w : WitgenIR Fp 1) (region : RegionIndex) :
    ((loadPrivate col w).output region).cell ∈
      ((loadPrivate col w).operations region).assignedCellsFrom region := by
  simp only [loadPrivate, output_assignRegion, output_assignAdvice,
    operations_assignRegion, operations_assignAdvice,
    Operations.assignedCellsFrom,
    RegionOperations.assignedCells, RegionOperation.assignedCells,
    List.flatMap_cons, List.flatMap_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, AssignedCell.of_cell, or_false]

/-- The shared witness cells (stage A's outputs). -/
structure WitnessCells where
  psiOld : AssignedCell Fp
  rhoOld : AssignedCell Fp
  cmOld : Var Point Fp
  gdOld : Var Point Fp
  akP : Var Point Fp
  nk : AssignedCell Fp
  vOld : AssignedCell Fp
  vNew : AssignedCell Fp

def WitnessCells.copyInputCells (cells : WitnessCells) : List Cell :=
  [cells.psiOld.cell, cells.rhoOld.cell, cells.cmOld.x.cell, cells.cmOld.y.cell,
    cells.gdOld.x.cell, cells.gdOld.y.cell, cells.akP.x.cell, cells.akP.y.cell,
    cells.nk.cell, cells.vOld.cell, cells.vNew.cell]

/-- Stage A (8 regions after the table load): the shared witness regions
(`circuit.rs:467-532`). -/
def synthWitness (G : Generators) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp WitnessCells := do
  Sinsemilla.load G cfg.sinsemilla1.generatorTable
  let psiOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.psiOld)
  let rhoOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.rhoOld)
  let cmOld ← Ecc.WitnessPoint.pointFormal.call
    cfg.eccConfig.witnessPoint W.cmOld
  let gdOld ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.gdOld
  let akP ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.akP
  let nk ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.nk)
  let vOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.vOld)
  let vNew ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.vNew)
  pure { psiOld, rhoOld, cmOld, gdOld, akP, nk, vOld, vNew }

/-- Stage B's outputs. -/
structure CheckCells where
  root : AssignedCell Fp
  magnitude : AssignedCell Fp
  sign : AssignedCell Fp
  nfOld : AssignedCell Fp
  pkdOld : Var Point Fp

def CheckCells.copyInputCells (cells : CheckCells) : List Cell :=
  [cells.root.cell, cells.magnitude.cell, cells.sign.cell, cells.nfOld.cell,
    cells.pkdOld.x.cell, cells.pkdOld.y.cell]

/-- Stage B (295 regions): the Merkle path, value-commit / nullifier / spend-authority /
diversified-address integrity (`circuit.rs:535-693`). -/
def synthChecksProgram (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) : Circuit Fp CheckCells := do
  -- circuit.rs:535-548 — the Merkle path (leaf = cm_old.extract_p); 16 layers per
  -- Sinsemilla instance (`merkle.rs:122-126`, `chips[i / layers_per_chip]`)
  let half ← (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
      0 16 (by norm_num) W.merkleSib W.merkleSwap).call
    (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) { node := wc.cmOld.x }
  let root ← (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
      16 16 (by norm_num) (fun i => W.merkleSib (16 + i))
      (fun i => W.merkleSwap (16 + i))).call
    (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) { node := half }
  -- circuit.rs:551-605 — value-commit integrity
  let magnitude ← loadPrivate (cfg.advices 9) (Witgen.MOver.toIRScalar W.magnitude)
  let sign ← loadPrivate (cfg.advices 9) (Witgen.MOver.toIRScalar W.sign)
  let cvNet ← (ValueCommit.circuit B.valueCommitV B.valueCommitR).call
    (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
    { rcv := W.rcv, magnitude := magnitude, sign := sign }
  constrainInstance cvNet.x cfg.primary CV_NET_X
  constrainInstance cvNet.y cfg.primary CV_NET_Y
  -- circuit.rs:608-624 — nullifier integrity
  let nfOld ← (DeriveNullifier.circuit B.nullifierK).call
    (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
     cfg.eccConfig.add)
    { nk := wc.nk, rho := wc.rhoOld, psi := wc.psiOld, cm := wc.cmOld }
  constrainInstance nfOld cfg.primary NF_OLD
  -- circuit.rs:627-644 — spend authority
  let rk ← (SpendAuthority.circuit B.spendAuthG).call
    (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) { alpha := W.alpha, akP := wc.akP }
  constrainInstance rk.x cfg.primary RK_X
  constrainInstance rk.y cfg.primary RK_Y
  -- circuit.rs:647-693 — diversified address integrity
  -- (`ak = ak_P.extract_p()`; `ScalarVar::from_base` is region-free)
  let ivk ← (CommitIvk.Main.circuit G B.commitIvkR
      B.ivkQ B.ivkQ_onCurve).call
    { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { ak := wc.akP.x, nk := wc.nk, rivk := W.rivk }
  let pkdOld ← (AddressIntegrity.circuit).call
    (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint)
    { ivk := ivk, gDOld := wc.gdOld, pkDOld := W.pkDOld }
  pure { root, magnitude, sign, nfOld, pkdOld }

private opaque synthChecksPacked :
    { f : Generators → Bases → Witnesses Fp → Config → WitnessCells →
        Circuit Fp CheckCells //
      ∀ G B W cfg wc, f G B W cfg wc = synthChecksProgram G B W cfg wc } :=
  ⟨synthChecksProgram, by intros; rfl⟩

/-- Stage B behind a reduction barrier. Use `synthChecks_eq` when a proof intentionally
inspects the synthesis program. -/
def synthChecks (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) : Circuit Fp CheckCells :=
  synthChecksPacked.val G B W cfg wc

theorem synthChecks_eq (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) :
    synthChecks G B W cfg wc = synthChecksProgram G B W cfg wc :=
  synthChecksPacked.property G B W cfg wc

/-- Stage C's outputs: the new-note diversified-address cells (the Rust `AddressPoints`
half the cross-address stage reads; the old halves live in `WitnessCells`/`CheckCells`). -/
structure NoteCells where
  gdNew : Var Point Fp
  pkdNew : Var Point Fp

def NoteCells.copyInputCells (cells : NoteCells) : List Cell :=
  [cells.gdNew.x.cell, cells.gdNew.y.cell,
    cells.pkdNew.x.cell, cells.pkdNew.y.cell]

def synthOrchardChecks (cfg : Config) (witnessCells : WitnessCells)
    (checkCells : CheckCells) : RegionCircuit Fp Unit := do
  let _ ← copyAdvice witnessCells.vOld (cfg.advices 0) 0
  let _ ← copyAdvice witnessCells.vNew (cfg.advices 1) 0
  let _ ← copyAdvice checkCells.magnitude (cfg.advices 2) 0
  let _ ← copyAdvice checkCells.sign (cfg.advices 3) 0
  let _ ← copyAdvice checkCells.root (cfg.advices 4) 0
  let _ ← assignAdviceFromInstance cfg.primary ANCHOR (cfg.advices 5) 0
  let _ ← assignAdviceFromInstance cfg.primary ENABLE_SPEND (cfg.advices 6) 0
  let _ ← assignAdviceFromInstance cfg.primary ENABLE_OUTPUT (cfg.advices 7) 0
  (orchardGate cfg.qOrchard cfg.advices).enable 0

def orchardChecksRegionSynthesisSummary (cfg : Config) :
    FloorPlanner.RegionSynthesisSummary :=
  FloorPlanner.RegionSynthesisSummary.ofColumns
    [.column .advice (cfg.advices 0).index,
      .column .advice (cfg.advices 1).index,
      .column .advice (cfg.advices 2).index,
      .column .advice (cfg.advices 3).index,
      .column .advice (cfg.advices 4).index,
      .column .advice (cfg.advices 5).index,
      .column .advice (cfg.advices 6).index,
      .column .advice (cfg.advices 7).index,
      .selector cfg.qOrchard.index]
    1 0 (ENABLE_OUTPUT + 1)

@[synthesis_summary_norm]
theorem orchardChecksRegion_synthesisSummary_eq (cfg : Config)
    (witnessCells : WitnessCells) (checkCells : CheckCells)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((synthOrchardChecks cfg witnessCells checkCells).operations region) =
      orchardChecksRegionSynthesisSummary cfg := by
  apply FloorPlanner.RegionSynthesisSummary.ext <;>
    simp only [synthOrchardChecks, orchardChecksRegionSynthesisSummary,
      orchardGate, circuit_norm, synthesis_summary_norm]
  unfold ANCHOR ENABLE_SPEND ENABLE_OUTPUT
  omega

/-- Stage C (91 regions): old/new note-commitment integrity and the final
`"Orchard circuit checks"` region (`circuit.rs:696-826`). -/
def synthNotesProgram (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) (cc : CheckCells) : Circuit Fp NoteCells := do
  -- circuit.rs:696-729 — old note commitment integrity
  let derivedCmOld ← (NoteCommit.Main.circuit G B.noteCommitR
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := wc.gdOld.x, gdY := wc.gdOld.y, pkdX := cc.pkdOld.x, pkdY := cc.pkdOld.y,
      value := wc.vOld, rho := wc.rhoOld, psi := wc.psiOld, rcm := W.rcmOld }
  assignRegion "constrain equal" (do
    constrainEqual derivedCmOld.x wc.cmOld.x
    constrainEqual derivedCmOld.y wc.cmOld.y)
  -- circuit.rs:731-779 — new note commitment integrity (`rho_new = nf_old`)
  let gdNew ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.gdNew
  let pkdNew ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.pkdNew
  let psiNew ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.psiNew)
  let cmNew ← (NoteCommit.Main.circuit G B.noteCommitR
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := gdNew.x, gdY := gdNew.y, pkdX := pkdNew.x, pkdY := pkdNew.y,
      value := wc.vNew, rho := cc.nfOld, psi := psiNew, rcm := W.rcmNew }
  constrainInstance cmNew.x cfg.primary CMX
  -- circuit.rs:781-826 — the final `"Orchard circuit checks"` region
  assignRegion "Orchard circuit checks" (synthOrchardChecks cfg wc cc)
  pure { gdNew, pkdNew }

private opaque synthNotesPacked :
    { f : Generators → Bases → Witnesses Fp → Config → WitnessCells →
        CheckCells → Circuit Fp NoteCells //
      ∀ G B W cfg wc cc,
        f G B W cfg wc cc = synthNotesProgram G B W cfg wc cc } :=
  ⟨synthNotesProgram, by intros; rfl⟩

/-- Stage C behind a reduction barrier. Use `synthNotes_eq` when a proof intentionally
inspects the synthesis program. -/
def synthNotes (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) (cc : CheckCells) : Circuit Fp NoteCells :=
  synthNotesPacked.val G B W cfg wc cc

theorem synthNotes_eq (G : Generators) (B : Bases) (W : Witnesses Fp)
    (cfg : Config) (wc : WitnessCells) (cc : CheckCells) :
    synthNotes G B W cfg wc cc = synthNotesProgram G B W cfg wc cc :=
  synthNotesPacked.property G B W cfg wc cc

/-! ## Reduced synthesis summaries -/

/-- Exact footprint of one `load private` region. -/
def loadPrivateSynthesisSummary (column : Column .advice) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice column.index] 1 0)

@[synthesis_summary_norm]
theorem loadPrivate_synthesisSummary_eq (column : Column .advice)
    (witness : WitgenIR Fp 1) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((loadPrivate column witness).operations region) =
      loadPrivateSynthesisSummary column := by
  simp only [loadPrivate, loadPrivateSynthesisSummary, circuit_norm,
    synthesis_summary_norm]

/-- Exact reduced footprint of the Action witness-loading stage. -/
def synthWitnessSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let load := loadPrivateSynthesisSummary (cfg.advices 0)
  let point := FloorPlanner.SynthesisSummary.ofRegion
    (Ecc.WitnessPoint.pointSynthesisSummary cfg.eccConfig.witnessPoint 0)
  let nonId := FloorPlanner.SynthesisSummary.ofRegion
    (Ecc.WitnessPoint.pointNonIdSynthesisSummary cfg.eccConfig.witnessPoint 0)
  [Sinsemilla.loadSynthesisSummary,
    load, load, point, nonId, nonId, load, load, load].foldr
    FloorPlanner.SynthesisSummary.combine {}

@[synthesis_summary_norm]
theorem synthWitnessSynthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthWitnessSynthesisSummary cfg).tableRowExtent = 1025 := by
  simp only [synthWitnessSynthesisSummary, Sinsemilla.loadSynthesisSummary,
    loadPrivateSynthesisSummary, List.foldr_cons, List.foldr_nil,
    synthesis_summary_norm, Specs.K]
  norm_num

@[synthesis_summary_norm]
theorem synthWitnessSynthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthWitnessSynthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthWitnessSynthesisSummary, Sinsemilla.loadSynthesisSummary,
    loadPrivateSynthesisSummary,
    Ecc.WitnessPoint.pointSynthesisSummary,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]

theorem synthWitnessSynthesisSummary_physicalRegionShapes (cfg : Config) :
    (synthWitnessSynthesisSummary cfg).physicalRegionShapes =
      [Sinsemilla.loadSynthesisSummary,
        loadPrivateSynthesisSummary (cfg.advices 0),
        loadPrivateSynthesisSummary (cfg.advices 0),
        FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.WitnessPoint.pointSynthesisSummary
            cfg.eccConfig.witnessPoint 0),
        FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.WitnessPoint.pointNonIdSynthesisSummary
            cfg.eccConfig.witnessPoint 0),
        FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.WitnessPoint.pointNonIdSynthesisSummary
            cfg.eccConfig.witnessPoint 0),
        loadPrivateSynthesisSummary (cfg.advices 0),
        loadPrivateSynthesisSummary (cfg.advices 0),
        loadPrivateSynthesisSummary (cfg.advices 0)].flatMap
          FloorPlanner.SynthesisSummary.physicalRegionShapes := by
  unfold synthWitnessSynthesisSummary
  exact FloorPlanner.SynthesisSummary.foldr_combine_physicalRegionShapes _

@[synthesis_summary_norm]
theorem synthWitness_synthesisSummary_eq (G : Generators)
    (W : Witnesses Fp) (cfg : Config) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthWitness G W cfg).operations region) =
      synthWitnessSynthesisSummary cfg := by
  simp only [synthWitness, synthWitnessSynthesisSummary, circuit_norm,
    synthesis_summary_norm, List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

/-- Exact reduced footprint of the Action integrity-check stage. -/
def synthChecksSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let merkle1 := Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
    (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
  let merkle2 := Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
    (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
  [merkle1, merkle2,
    loadPrivateSynthesisSummary (cfg.advices 9),
    loadPrivateSynthesisSummary (cfg.advices 9),
    ValueCommit.synthesisSummary
      (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
        cfg.eccConfig.add),
    FloorPlanner.SynthesisSummary.ofInstanceRow CV_NET_X,
    FloorPlanner.SynthesisSummary.ofInstanceRow CV_NET_Y,
    DeriveNullifier.synthesisSummary
      (cfg.poseidonConfig, cfg.addChipConfig,
        cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add),
    FloorPlanner.SynthesisSummary.ofInstanceRow NF_OLD,
    SpendAuthority.synthesisSummary
      (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add),
    FloorPlanner.SynthesisSummary.ofInstanceRow RK_X,
    FloorPlanner.SynthesisSummary.ofInstanceRow RK_Y,
    CommitIvk.Main.synthesisSummary
      { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
        lookupConfig := cfg.lookupConfig,
        mulConfig := cfg.eccConfig.mulFixedFull,
        addConfig := cfg.eccConfig.add },
    AddressIntegrity.synthesisSummary
      (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint)].foldr
        FloorPlanner.SynthesisSummary.combine {}

@[synthesis_summary_norm]
theorem synthChecksSynthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthChecksSynthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthChecksSynthesisSummary,
    Sinsemilla.Merkle.CalculateRoot.synthesisSummary_tableRowExtent_eq,
    ValueCommit.synthesisSummary_tableRowExtent_eq,
    DeriveNullifier.synthesisSummary_tableRowExtent_eq,
    SpendAuthority.synthesisSummary_tableRowExtent_eq,
    CommitIvk.Main.synthesisSummary_tableRowExtent_eq,
    AddressIntegrity.synthesisSummary_tableRowExtent_eq,
    loadPrivateSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthChecksSynthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthChecksSynthesisSummary cfg).instanceRowExtent = 6 := by
  simp only [synthChecksSynthesisSummary,
    Sinsemilla.Merkle.CalculateRoot.synthesisSummary_instanceRowExtent_eq,
    ValueCommit.synthesisSummary_instanceRowExtent_eq,
    DeriveNullifier.synthesisSummary_instanceRowExtent_eq,
    SpendAuthority.synthesisSummary_instanceRowExtent_eq,
    CommitIvk.Main.synthesisSummary_instanceRowExtent_eq,
    AddressIntegrity.synthesisSummary_instanceRowExtent_eq,
    loadPrivateSynthesisSummary,
    CV_NET_X, CV_NET_Y, NF_OLD, RK_X, RK_Y,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]
  norm_num

theorem synthChecksSynthesisSummary_physicalRegionShapes (cfg : Config) :
    (synthChecksSynthesisSummary cfg).physicalRegionShapes =
      [Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
          (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig),
        Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
          (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig),
        loadPrivateSynthesisSummary (cfg.advices 9),
        loadPrivateSynthesisSummary (cfg.advices 9),
        ValueCommit.synthesisSummary
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
            cfg.eccConfig.add),
        DeriveNullifier.synthesisSummary
          (cfg.poseidonConfig, cfg.addChipConfig,
            cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add),
        SpendAuthority.synthesisSummary
          (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add),
        CommitIvk.Main.synthesisSummary
          { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add },
        AddressIntegrity.synthesisSummary
          (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint)].flatMap
            FloorPlanner.SynthesisSummary.physicalRegionShapes := by
  unfold synthChecksSynthesisSummary
  rw [FloorPlanner.SynthesisSummary.foldr_combine_physicalRegionShapes]
  simp only [List.flatMap_cons, List.flatMap_nil,
    FloorPlanner.SynthesisSummary.ofInstanceRow_physicalRegionShapes,
    List.nil_append]

@[synthesis_summary_norm]
theorem synthChecks_synthesisSummary_eq (G : Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Config) (cells : WitnessCells)
    (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthChecks G B W cfg cells).operations region) =
      synthChecksSynthesisSummary cfg := by
  simp only [synthChecks_eq, synthChecksProgram, synthChecksSynthesisSummary, circuit_norm,
    synthesis_summary_norm, List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

/-- Exact footprint of the final Orchard gate region. -/
def orchardChecksSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (orchardChecksRegionSynthesisSummary cfg)

/-- Exact reduced footprint of the Action note-commitment stage. -/
def synthNotesSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let noteOld := NoteCommit.Main.synthesisSummary
    { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig,
      mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
  let nonId := FloorPlanner.SynthesisSummary.ofRegion
    (Ecc.WitnessPoint.pointNonIdSynthesisSummary cfg.eccConfig.witnessPoint 0)
  let noteNew := NoteCommit.Main.synthesisSummary
    { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
      lookupConfig := cfg.lookupConfig,
      mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
  let copyRegion := FloorPlanner.SynthesisSummary.ofRegion {}
  [noteOld, copyRegion, nonId, nonId,
    loadPrivateSynthesisSummary (cfg.advices 0), noteNew,
    FloorPlanner.SynthesisSummary.ofInstanceRow CMX,
    orchardChecksSynthesisSummary cfg].foldr
      FloorPlanner.SynthesisSummary.combine {}

@[synthesis_summary_norm]
theorem synthNotesSynthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthNotesSynthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthNotesSynthesisSummary,
    NoteCommit.Main.synthesisSummary_tableRowExtent_eq,
    orchardChecksSynthesisSummary, loadPrivateSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthNotesSynthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthNotesSynthesisSummary cfg).instanceRowExtent = 9 := by
  simp only [synthNotesSynthesisSummary,
    NoteCommit.Main.synthesisSummary_instanceRowExtent_eq,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    orchardChecksSynthesisSummary, orchardChecksRegionSynthesisSummary,
    loadPrivateSynthesisSummary, CMX, ENABLE_OUTPUT,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]
  norm_num

theorem synthNotesSynthesisSummary_physicalRegionShapes (cfg : Config) :
    (synthNotesSynthesisSummary cfg).physicalRegionShapes =
      [NoteCommit.Main.synthesisSummary
          { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add },
        FloorPlanner.SynthesisSummary.ofRegion {},
        FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.WitnessPoint.pointNonIdSynthesisSummary
            cfg.eccConfig.witnessPoint 0),
        FloorPlanner.SynthesisSummary.ofRegion
          (Ecc.WitnessPoint.pointNonIdSynthesisSummary
            cfg.eccConfig.witnessPoint 0),
        loadPrivateSynthesisSummary (cfg.advices 0),
        NoteCommit.Main.synthesisSummary
          { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
            lookupConfig := cfg.lookupConfig,
            mulConfig := cfg.eccConfig.mulFixedFull,
            addConfig := cfg.eccConfig.add },
        orchardChecksSynthesisSummary cfg].flatMap
          FloorPlanner.SynthesisSummary.physicalRegionShapes := by
  unfold synthNotesSynthesisSummary
  rw [FloorPlanner.SynthesisSummary.foldr_combine_physicalRegionShapes]
  simp only [List.flatMap_cons, List.flatMap_nil,
    FloorPlanner.SynthesisSummary.ofInstanceRow_physicalRegionShapes,
    List.nil_append]

@[synthesis_summary_norm]
theorem synthNotes_synthesisSummary_eq (G : Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Config) (witnessCells : WitnessCells)
    (checkCells : CheckCells) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthNotes G B W cfg witnessCells checkCells).operations region) =
      synthNotesSynthesisSummary cfg := by
  simp only [synthNotes_eq, synthNotesProgram, synthNotesSynthesisSummary,
    orchardChecksSynthesisSummary, circuit_norm, synthesis_summary_norm,
    List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

/-- Rust `AddressPoints` (ironwood `circuit.rs`): the old/new-note diversified-address
points the cross-address stage compares — the base circuit's output. -/
structure AddressPoints (F : Type) where
  gdOld : Point F
  pkdOld : Point F
  gdNew : Point F
  pkdNew : Point F
deriving ProvableStruct

/-- The base-circuit output cells consumed by the cross-address copy constraints. -/
def AddressPoints.copyInputCells (points : Var AddressPoints Fp) : List Cell :=
  [points.gdOld.x.cell, points.gdOld.y.cell,
    points.pkdOld.x.cell, points.pkdOld.y.cell,
    points.gdNew.x.cell, points.gdNew.y.cell,
    points.pkdNew.x.cell, points.pkdNew.y.cell]

/-- Columns occupied by each cross-address row. -/
def crossAddressColumns (cfg : Config) :
    List FloorPlanner.RegionColumn :=
  [.column .advice (cfg.advices 0).index,
    .column .advice (cfg.advices 1).index,
    .column .advice (cfg.advices 2).index,
    .column .advice (cfg.advices 3).index,
    .column .advice (cfg.advices 4).index,
    .column .advice (cfg.advices 5).index,
    .column .advice (cfg.advices 6).index,
    .column .advice (cfg.advices 7).index,
    .column .advice (cfg.advices 8).index,
    .column .advice (cfg.advices 9).index,
    .selector cfg.qOrchard.index]

def synthCrossAddressRow (cfg : Config) (oldCell newCell : AssignedCell Fp)
    (row : ℕ) : RegionCircuit Fp Unit := do
  let dca ← assignAdviceFromInstance cfg.primary DISABLE_CROSS_ADDRESS
    (cfg.advices 0) row
  let z ← assignAdvice (cfg.advices 1) row (Poseidon.constWit 0)
  constrainConstant z 0
  let _ ← copyAdvice dca (cfg.advices 2) row
  let o3 ← assignAdvice (cfg.advices 3) row (Poseidon.constWit 1)
  constrainConstant o3 1
  let _ ← copyAdvice oldCell (cfg.advices 4) row
  let _ ← copyAdvice newCell (cfg.advices 5) row
  let o6 ← assignAdvice (cfg.advices 6) row (Poseidon.constWit 1)
  constrainConstant o6 1
  let o7 ← assignAdvice (cfg.advices 7) row (Poseidon.constWit 1)
  constrainConstant o7 1
  let _ ← copyAdvice dca (cfg.advices 8) row
  let _ ← copyAdvice dca (cfg.advices 9) row
  (orchardGate cfg.qOrchard cfg.advices).enable row

@[synthesis_summary_norm]
theorem crossAddressRow_synthesisSummary_eq (cfg : Config)
    (oldCell newCell : AssignedCell Fp) (row : ℕ) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((synthCrossAddressRow cfg oldCell newCell row).operations region) =
      FloorPlanner.RegionSynthesisSummary.ofColumns
        (crossAddressColumns cfg) (row + 1) 4 (DISABLE_CROSS_ADDRESS + 1) := by
  apply FloorPlanner.RegionSynthesisSummary.ext <;>
    simp only [synthCrossAddressRow, crossAddressColumns, orchardGate, circuit_norm,
      synthesis_summary_norm]

/-- Ironwood `Circuit::synthesize_cross_address_checks` (`circuit.rs:920-1035`): the
`"post-NU 6.3 cross-address checks"` region — one row per address coordinate. -/
def synthCrossAddressChecks (cfg : Config) (pts : Var AddressPoints Fp) :
    Circuit Fp Unit :=
  assignRegion "post-NU 6.3 cross-address checks"
    (RegionCircuit.forRange' 0 1 4 fun _ row => do
      let coords := [(pts.gdOld.x, pts.gdNew.x), (pts.gdOld.y, pts.gdNew.y),
                     (pts.pkdOld.x, pts.pkdNew.x), (pts.pkdOld.y, pts.pkdNew.y)]
      let (oldC, newC) := coords[row]!
      synthCrossAddressRow cfg oldC newC row)

def synthCrossAddressChecksSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.repeatColumns
      (crossAddressColumns cfg) 0 1 1 4 4 (DISABLE_CROSS_ADDRESS + 1))

@[synthesis_summary_norm]
theorem synthCrossAddressChecksSynthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthCrossAddressChecksSynthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthCrossAddressChecksSynthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthCrossAddressChecksSynthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthCrossAddressChecksSynthesisSummary cfg).instanceRowExtent = 10 := by
  simp only [synthCrossAddressChecksSynthesisSummary, synthesis_summary_norm,
    DISABLE_CROSS_ADDRESS]
  norm_num

@[synthesis_summary_norm]
theorem synthCrossAddressChecks_synthesisSummary_eq
    (cfg : Config) (pts : Var AddressPoints Fp) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthCrossAddressChecks cfg pts).operations region) =
      synthCrossAddressChecksSynthesisSummary cfg := by
  have hregion :
      FloorPlanner.regionSynthesisSummary
          ((RegionCircuit.forRange' 0 1 4 fun _ row =>
            let coords := [(pts.gdOld.x, pts.gdNew.x),
              (pts.gdOld.y, pts.gdNew.y),
              (pts.pkdOld.x, pts.pkdNew.x),
              (pts.pkdOld.y, pts.pkdNew.y)]
            let (oldCell, newCell) := coords[row]!
            synthCrossAddressRow cfg oldCell newCell row).operations region) =
        FloorPlanner.RegionSynthesisSummary.repeatColumns
          (crossAddressColumns cfg) 0 1 1 4 4
            (DISABLE_CROSS_ADDRESS + 1) := by
    rw [RegionCircuit.forRange'_regionSynthesisSummary]
    simp only [crossAddressRow_synthesisSummary_eq]
    simpa only [Nat.zero_add, Nat.one_mul] using
      (FloorPlanner.RegionSynthesisSummary.foldr_ofColumns_eq_repeatColumns
        (crossAddressColumns cfg) 0 1 1 4 4 (DISABLE_CROSS_ADDRESS + 1))
  rw [synthCrossAddressChecks, operations_assignRegion,
    FloorPlanner.synthesisSummary_region_cons,
    FloorPlanner.synthesisSummary_nil,
    FloorPlanner.SynthesisSummary.combine_empty,
    synthCrossAddressChecksSynthesisSummary]
  rw [hregion]

/-- The four cross-address rows request four deferred constants each. -/
@[synthesis_summary_norm]
theorem synthCrossAddressChecks_synthesisSummary_constantSiteCount
    (config : Config) (points : Var AddressPoints Fp)
    (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((synthCrossAddressChecks config points).operations
        region)).constantSiteCount = 16 := by
  rw [synthCrossAddressChecks_synthesisSummary_eq]
  simp only [synthCrossAddressChecksSynthesisSummary,
    synthesis_summary_norm]

/-- Every cross-address row occupies the first advice column. -/
@[synthesis_summary_norm]
theorem synthCrossAddressChecks_synthesisSummary_adviceZeroOccupancy
    (config : Config) (points : Var AddressPoints Fp)
    (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((synthCrossAddressChecks config points).operations region)).columnOccupancy
        (.column .advice (config.advices 0).index) = 4 := by
  rw [synthCrossAddressChecks_synthesisSummary_eq]
  simp only [synthCrossAddressChecksSynthesisSummary,
    crossAddressColumns, synthesis_summary_norm]
  simp [FloorPlanner.mem_unionColumns_iff]

/-- Cross-address checks occupy no fixed columns. -/
@[synthesis_summary_norm]
theorem synthCrossAddressChecks_synthesisSummary_fixedOccupancy
    (config : Config) (points : Var AddressPoints Fp)
    (column : Column .fixed) (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((synthCrossAddressChecks config points).operations region)).columnOccupancy
        (.column .fixed column.index) = 0 := by
  rw [synthCrossAddressChecks_synthesisSummary_eq]
  simp only [synthCrossAddressChecksSynthesisSummary,
    crossAddressColumns, synthesis_summary_norm]
  simp [FloorPlanner.mem_unionColumns_iff]

@[keygen_helper]
theorem synthCrossAddressChecks_keygenRegistered
    (cfg : Config) (pts : Var AddressPoints Fp)
    (gates : List (Gate Fp)) (lookups : List (LookupArgument Fp))
    (permutationColumns : List AnyColumn) (i : RegionIndex)
    (hadvice : ∀ index, (cfg.advices index).toAny ∈ permutationColumns)
    (hprimary : cfg.primary.toAny ∈ permutationColumns)
    (hgdOldX : pts.gdOld.x.cell.column ∈ permutationColumns)
    (hgdOldY : pts.gdOld.y.cell.column ∈ permutationColumns)
    (hpkdOldX : pts.pkdOld.x.cell.column ∈ permutationColumns)
    (hpkdOldY : pts.pkdOld.y.cell.column ∈ permutationColumns)
    (hgdNewX : pts.gdNew.x.cell.column ∈ permutationColumns)
    (hgdNewY : pts.gdNew.y.cell.column ∈ permutationColumns)
    (hpkdNewX : pts.pkdNew.x.cell.column ∈ permutationColumns)
    (hpkdNewY : pts.pkdNew.y.cell.column ∈ permutationColumns)
    (horchard : orchardGate cfg.qOrchard cfg.advices ∈ gates) :
    ((synthCrossAddressChecks cfg pts).operations i).KeygenRegistered
      gates lookups permutationColumns := by
  simp only [synthCrossAddressChecks, keygen_spine]
  keygen_registration
  all_goals
    first
    | simpa only [keygen_output_norm] using hadvice 0
    | rename_i row
      fin_cases row <;> simp_all

@[keygen_helper]
theorem synthCrossAddressChecks_copyCellsAssigned
    (cfg : Config) (points : Var AddressPoints Fp) (region : RegionIndex) :
    ((synthCrossAddressChecks cfg points).operations region)
      |>.CopyCellsAssignedFrom region points.copyInputCells := by
  unfold synthCrossAddressChecks
  simp only [operations_assignRegion, keygen_spine]
  apply RegionCircuit.forRange'_copyCellsAssignedFrom
  intro index
  fin_cases index <;>
    simp only [AddressPoints.copyInputCells, synthCrossAddressRow, keygen_spine] <;>
    keygen_registration

/-- Rust `Circuit::synthesize_base` (`circuit.rs:461-828`): the staged witness /
integrity-check / note-commitment composition, returning the `AddressPoints` the
ironwood cross-address stage reads. This alone is the pre-ironwood (fixed post-NU 6.2)
circuit — see `Action/CircuitPreIronwood.lean`. -/
def synthesizeBase (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp (Var AddressPoints Fp) := do
  let wc ← synthWitness G W cfg
  let cc ← synthChecks G B W cfg wc
  let nc ← synthNotes G B W cfg wc cc
  pure { gdOld := wc.gdOld, pkdOld := cc.pkdOld, gdNew := nc.gdNew, pkdNew := nc.pkdNew }

/-- Exact reduced footprint of the 394-region pre-Ironwood Action circuit. -/
def synthesizeBaseSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  (synthWitnessSynthesisSummary cfg).combine
    ((synthChecksSynthesisSummary cfg).combine
      (synthNotesSynthesisSummary cfg))

@[synthesis_summary_norm]
theorem synthesizeBase_synthesisSummary_eq (G : Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Config) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthesizeBase G B W cfg).operations region) =
      synthesizeBaseSynthesisSummary cfg := by
  simp only [synthesizeBase, synthesizeBaseSynthesisSummary, circuit_norm,
    synthesis_summary_norm]

/-- The ironwood (post-NU 6.3) `Circuit::synthesize` — THE top-level circuit this repo
targets: the base stages plus the cross-address checks region. -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp Unit := do
  let pts ← synthesizeBase G B W cfg
  synthCrossAddressChecks cfg pts

end Zcash.Circuits.Action.Circuit
