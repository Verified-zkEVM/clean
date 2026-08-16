import Clean.Ironwood.Ecc.WitnessPoint
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Ironwood.Ecc.MulFixed.Short
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem

/-!
# ECC chip configure (Ironwood)

The aggregate ECC configuration, in VK-exact registration order: witness point, incomplete
addition, complete addition, variable-base mul, the shared `mul_fixed` core, then the
full-width / short / base-field-element wrappers.

Reference: `halo2_gadgets/src/ecc/chip.rs`.
-/

namespace Zcash.Circuits.Ecc

open Halo2

structure EccConfig where
  -- Witness point.
  witnessPoint : WitnessPoint.Config
  -- Incomplete addition.
  addIncomplete : AddIncomplete.Config
  -- Complete addition.
  add : Add.Config
  -- Variable-base scalar multiplication.
  mul : Mul.Config
  -- Fixed-base full-width scalar multiplication.
  mulFixedFull : MulFixed.FullWidth.Config
  -- Fixed-base signed short scalar multiplication.
  mulFixedShort : MulFixed.Short.Config
  -- Fixed-base mul using a base field element as a scalar.
  mulFixedBaseField : MulFixed.BaseFieldElem.Config

/-- The aggregate ECC configuration, in VK-exact registration order. All `advices` columns are
equality-enabled. -/
def configure (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) : Configure Fp EccConfig := do
  -- witness point gate
  let witnessPoint ← WitnessPoint.configure (advices 0) (advices 1)
  -- incomplete point addition gate
  let addIncomplete ← AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  -- complete point addition gate
  let add ← Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4, advices 5,
     advices 6, advices 7, advices 8)
  -- variable-base scalar mul gates
  let mul ← Mul.configure add rangeCheck advices
  -- the shared fixed-base mul core (short, base-field, and full-width)
  let mulFixed ← MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
    add addIncomplete
  -- full-width fixed-base mul gate
  let mulFixedFull ← MulFixed.FullWidth.configure mulFixed
  -- short fixed-base mul gate
  let mulFixedShort ← MulFixed.Short.configure mulFixed
  -- base-field-element fixed-base mul gate
  let mulFixedBaseField ← MulFixed.BaseFieldElem.configure
    ![advices 6, advices 7, advices 8] rangeCheck mulFixed
  return { witnessPoint, addIncomplete, add, mul, mulFixedFull, mulFixedShort,
           mulFixedBaseField }

@[configure_selector_norm, keygen_norm] theorem configure_delta_lookups
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts) :
    ((configure advices lagrangeCoeffs rangeCheck).delta counts).lookups = [] := by
  simp [configure, WitnessPoint.configure, AddIncomplete.add, Add.add,
    Mul.configure, MulIncomplete.configure, MulComplete.configure,
    MulOverflow.configure, MulFixed.configure,
    DecomposeRunningSum.configure,
    MulFixed.FullWidth.configure,
    MulFixed.Short.configure, MulFixed.BaseFieldElem.configure]

@[keygen_norm] theorem configure_delta_constants
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts) :
    ((configure advices lagrangeCoeffs rangeCheck).delta counts).constants = [] := by
  simp [configure, WitnessPoint.configure, AddIncomplete.add, Add.add,
    Mul.configure, MulIncomplete.configure, MulComplete.configure,
    MulOverflow.configure, MulFixed.configure,
    DecomposeRunningSum.configure,
    MulFixed.FullWidth.configure,
    MulFixed.Short.configure, MulFixed.BaseFieldElem.configure]

@[keygen_norm] theorem configure_fixedColumns
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts) :
    (configure advices lagrangeCoeffs rangeCheck).fixedColumns counts =
      [((configure advices lagrangeCoeffs rangeCheck).output counts)
        |>.mulFixedShort.superConfig.fixedZ] := by
  simp [configure, WitnessPoint.configure, AddIncomplete.add, Add.add,
    Mul.configure, MulIncomplete.configure, MulComplete.configure,
    MulOverflow.configure, MulFixed.configure,
    DecomposeRunningSum.configure,
    MulFixed.FullWidth.configure,
    MulFixed.Short.configure, MulFixed.BaseFieldElem.configure]

@[reducible] private def configureInferred
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    ElaboratedConfigure (configure advices lagrangeCoeffs rangeCheck) := by
  unfold configure
  infer_instance

private theorem configure_selectorRequirements
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts) :
    (configureInferred advices lagrangeCoeffs rangeCheck).selectorRequirements
      counts := by
  dsimp only [configureInferred, configure]
  simp [keygen_norm, WitnessPoint.configure,
    AddIncomplete.add, Add.add, Mul.configure,
    MulIncomplete.configure, MulComplete.configure, MulOverflow.configure,
    MulFixed.configure,
    DecomposeRunningSum.configure,
    MulFixed.FullWidth.configure,
    MulFixed.Short.configure, MulFixed.BaseFieldElem.configure]

instance (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    ElaboratedConfigure (configure advices lagrangeCoeffs rangeCheck) :=
  ((configureInferred advices lagrangeCoeffs rangeCheck).closeSelectorRequirements
    (configure_selectorRequirements advices lagrangeCoeffs rangeCheck)).withNoExternalSelectors (by
      intro counts
      constructor
      · simp [configure_selector_norm, configure,
          WitnessPoint.configure, AddIncomplete.add, Add.add, Mul.configure,
          MulIncomplete.configure, MulComplete.configure,
          MulOverflow.configure, MulFixed.configure,
          MulFixed.FullWidth.configure, MulFixed.Short.configure,
          MulFixed.BaseFieldElem.configure,
          DecomposeRunningSum.configure]
        omega
      · rw [configure_delta_lookups]
        simp)

/-- Every advice column handed to the ECC chip is equality-enabled by its aggregate
configure program. -/
theorem advice_mem_permutationRequests (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts)
    (i : Fin 10) :
    (advices i).toAny ∈
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).permutationRequests := by
  fin_cases i
  all_goals unfold configure
  case «0» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    simp only [AddIncomplete.add]
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «1» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    simp only [AddIncomplete.add]
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «2» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    simp only [AddIncomplete.add]
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «3» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    simp only [AddIncomplete.add]
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «4» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold Mul.configure
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulIncomplete.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «5» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulFixed.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «6» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold Mul.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulOverflow.configure
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «7» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold Mul.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulOverflow.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «8» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold Mul.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulOverflow.configure
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  case «9» =>
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold Mul.configure
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold MulIncomplete.configure
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _

/-- The keygen context produced locally by one aggregate ECC configure run. -/
private def configureDeltaContext (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    KeygenContext Fp :=
  { gates := ((configure advices lagrangeCoeffs rangeCheck).delta counts).gates
    lookups := ((configure advices lagrangeCoeffs rangeCheck).delta counts).lookups
    fixedColumns := (configure advices lagrangeCoeffs rangeCheck).fixedColumns counts
    permutationColumns :=
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).permutationRequests }

/-- The capabilities exported by ECC: its local configure delta plus the range-check
lookup borrowed from its caller by variable- and base-field multiplication. -/
def configureContext (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    KeygenContext Fp :=
  { gates := ((configure advices lagrangeCoeffs rangeCheck).delta counts).gates
    lookups := LookupRangeCheck.rangeCheckLookup 10 rangeCheck ::
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).lookups
    fixedColumns := List.ofFn lagrangeCoeffs ++
      (configure advices lagrangeCoeffs rangeCheck).fixedColumns counts
    permutationColumns := rangeCheck.runningSum ::
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).permutationRequests }

/--
Opaque capabilities exported by the aggregate ECC configurer.

This first slice covers the primitive configurations at the head of the aggregate;
fixed- and variable-base multiplication capabilities will extend the same record.
-/
structure CoreConfigureCertificate (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts)
    (context : KeygenContext Fp) where
  witnessPoint : WitnessPoint.point.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).witnessPoint
    context
  witnessPointFormal : WitnessPoint.pointFormal.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).witnessPoint
    context
  witnessPointNonIdFormal : WitnessPoint.pointNonIdFormal.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).witnessPoint
    context
  addIncomplete : AddIncomplete.add.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).addIncomplete
    context
  add : Add.add.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).add
    context
  addFormal : Add.addFormal.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).add
    context

namespace CoreConfigureCertificate

/-- Transport every capability exported by an aggregate ECC configure run at once. -/
def mono
    {advices : Fin 10 → Column .advice}
    {lagrangeCoeffs : Fin 8 → Column .fixed}
    {rangeCheck : LookupRangeCheck.Config 10} {counts : ConfigureCounts}
    {source target : KeygenContext Fp}
    (certificate :
      CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (fixedColumns : ∀ column,
      column ∈ source.fixedColumns → column ∈ target.fixedColumns)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts target where
  witnessPoint := certificate.witnessPoint.mono gates lookups fixedColumns permutationColumns
  witnessPointFormal :=
    certificate.witnessPointFormal.mono gates lookups fixedColumns permutationColumns
  witnessPointNonIdFormal :=
    certificate.witnessPointNonIdFormal.mono gates lookups fixedColumns permutationColumns
  addIncomplete := certificate.addIncomplete.mono gates lookups fixedColumns permutationColumns
  add := certificate.add.mono gates lookups fixedColumns permutationColumns
  addFormal := certificate.addFormal.mono gates lookups fixedColumns permutationColumns

end CoreConfigureCertificate

/-- Construct the aggregate certificate once, inside the ECC owner module. -/
def coreConfigureCertificate (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts
      (configureDeltaContext advices lagrangeCoeffs rangeCheck counts) where
  witnessPoint :=
    (WitnessPoint.point.configureCertificate
      (advices 0, advices 1) counts ()).mono
      (by
        intro gate hgate
        simp only [WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_left
        simpa only [WitnessPoint.point] using hgate)
      (by
        intro argument hargument
        simp only [WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_left
        simpa only [WitnessPoint.point] using hargument)
      (by
        intro column hcolumn
        simp only [WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_left
        simpa only [WitnessPoint.point] using hcolumn)
      (by
        intro column hcolumn
        simp only [WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_left
        simpa only [WitnessPoint.point] using hcolumn)
  witnessPointFormal :=
    (WitnessPoint.pointFormal.configureCertificate
      (advices 0, advices 1) counts ()).mono
      (by
        intro gate hgate
        simp only [WitnessPoint.pointFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_left
        simpa only [WitnessPoint.point] using hgate)
      (by
        intro argument hargument
        simp only [WitnessPoint.pointFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_left
        simpa only [WitnessPoint.point] using hargument)
      (by
        intro column hcolumn
        simp only [WitnessPoint.pointFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_left
        simpa only [WitnessPoint.point] using hcolumn)
      (by
        intro column hcolumn
        simp only [WitnessPoint.pointFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.point, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_left
        simpa only [WitnessPoint.point] using hcolumn)
  witnessPointNonIdFormal :=
    (WitnessPoint.pointNonIdFormal.configureCertificate
      (advices 0, advices 1) counts ()).mono
      (by
        intro gate hgate
        simp only [WitnessPoint.pointNonIdFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.pointNonId, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_left
        simpa only [WitnessPoint.pointNonId] using hgate)
      (by
        intro argument hargument
        simp only [WitnessPoint.pointNonIdFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.pointNonId, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_left
        simpa only [WitnessPoint.pointNonId] using hargument)
      (by
        intro column hcolumn
        simp only [WitnessPoint.pointNonIdFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.pointNonId, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_left
        simpa only [WitnessPoint.pointNonId] using hcolumn)
      (by
        intro column hcolumn
        simp only [WitnessPoint.pointNonIdFormal,
          FormalRegionCircuit.toFormal_keygenRequirements,
          WitnessPoint.pointNonId, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_left
        simpa only [WitnessPoint.pointNonId] using hcolumn)
  addIncomplete :=
    (AddIncomplete.add.configureCertificate
      (advices 0, advices 1, advices 2, advices 3)
      ((WitnessPoint.configure (advices 0) (advices 1)).finalCounts counts) ()).mono
      (by
        intro gate hgate
        simp only [AddIncomplete.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hgate)
      (by
        intro argument hargument
        simp only [AddIncomplete.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hargument)
      (by
        intro column hcolumn
        simp only [AddIncomplete.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hcolumn)
      (by
        intro column hcolumn
        simp only [AddIncomplete.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hcolumn)
  add :=
    (Add.add.configureCertificate
      (advices 0, advices 1, advices 2, advices 3, advices 4,
        advices 5, advices 6, advices 7, advices 8)
      ((AddIncomplete.add.configure
        (advices 0, advices 1, advices 2, advices 3)).finalCounts
          ((WitnessPoint.configure
            (advices 0) (advices 1)).finalCounts counts)) ()).mono
      (by
        intro gate hgate
        simp only [Add.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hgate)
      (by
        intro argument hargument
        simp only [Add.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hargument)
      (by
        intro column hcolumn
        simp only [Add.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hcolumn)
      (by
        intro column hcolumn
        simp only [Add.add, FormalRegionCircuit.keygenRequirements,
          ElaboratedRegionCircuit.keygenRequirements, List.nil_append] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hcolumn)
  addFormal :=
    (Add.addFormal.configureCertificate
      (advices 0, advices 1, advices 2, advices 3, advices 4,
        advices 5, advices 6, advices 7, advices 8)
      ((AddIncomplete.add.configure
        (advices 0, advices 1, advices 2, advices 3)).finalCounts
          ((WitnessPoint.configure
            (advices 0) (advices 1)).finalCounts counts)) ()).mono
      (by
        intro gate hgate
        simp only [Add.addFormal, FormalCircuit.keygenRequirements] at hgate
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hgate)
      (by
        intro argument hargument
        simp only [Add.addFormal, FormalCircuit.keygenRequirements] at hargument
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hargument)
      (by
        intro column hcolumn
        simp only [Add.addFormal, FormalCircuit.keygenRequirements] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hcolumn)
      (by
        intro column hcolumn
        simp only [Add.addFormal, FormalCircuit.keygenRequirements] at hcolumn
        simp only [configureDeltaContext]
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hcolumn)

/--
The two gates borrowed through a fixed-base wrapper are registered by the shared
`MulFixed.configure` call inside the ECC chip.
-/
theorem mem_mulFixed_gates (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10)
    (counts : ConfigureCounts) (gate : Gate Fp)
    (hgate :
      let cfg :=
        ((configure advices lagrangeCoeffs rangeCheck).output counts)
          |>.mulFixedShort.superConfig
      gate ∈ [DecomposeRunningSum.rangeCheckGate 3 cfg.runningSumConfig,
        MulFixed.coordsGate cfg]) :
    gate ∈
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).gates := by
  unfold configure
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  apply List.mem_append_right
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  apply List.mem_append_right
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  apply List.mem_append_right
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  apply List.mem_append_right
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  apply List.mem_append_left
  unfold configure at hgate
  simpa [MulFixed.configure, MulFixed.Short.configure,
    DecomposeRunningSum.configure] using hgate

/-- The fixed columns exposed by the shared fixed-base configuration are either the
borrowed Lagrange columns or the locally allocated `fixedZ` column. -/
theorem mem_mulFixed_fixedColumns (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10)
    (counts : ConfigureCounts) (column : Column .fixed)
    (hcolumn :
      let cfg :=
        ((configure advices lagrangeCoeffs rangeCheck).output counts)
          |>.mulFixedShort.superConfig
      column ∈ MulFixed.fixedColumns cfg) :
    column ∈
      (configureContext advices lagrangeCoeffs rangeCheck counts).fixedColumns := by
  simp only [configureContext, List.mem_append]
  unfold MulFixed.fixedColumns at hcolumn
  rcases List.mem_append.mp hcolumn with hlagrange | hfixedZ
  · exact Or.inl hlagrange
  · simp only [List.mem_singleton] at hfixedZ
    subst column
    right
    rw [Configure.mem_fixedColumns_iff]
    simp [configure, WitnessPoint.configure, AddIncomplete.add, Add.add,
      Mul.configure, MulIncomplete.configure, MulComplete.configure,
      MulOverflow.configure, MulFixed.configure,
      DecomposeRunningSum.configure, MulFixed.FullWidth.configure,
      MulFixed.Short.configure, MulFixed.BaseFieldElem.configure]

/-- All ECC capabilities needed by the Action-level fixed-base wrappers. -/
structure ConfigureCertificate (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts)
    (context : KeygenContext Fp)
    extends CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts context where
  mul : Mul.mul.ConfigurationCertificate
    ((configure advices lagrangeCoeffs rangeCheck).output counts).mul
    context
  mulFixedShort : ∀ B : MulFixed.Short.FixedBase,
    (MulFixed.Short.circuit B).ConfigurationCertificate
      ((configure advices lagrangeCoeffs rangeCheck).output counts).mulFixedShort
      context
  mulFixedFull : ∀ B : MulFixed.FixedBase,
    (MulFixed.FullWidth.circuit B).ConfigurationCertificate
      ((configure advices lagrangeCoeffs rangeCheck).output counts).mulFixedFull
      context
  mulFixedBaseField : ∀ B : MulFixed.FixedBase,
    (MulFixed.BaseFieldElem.circuit B).ConfigurationCertificate
      ((configure advices lagrangeCoeffs rangeCheck).output counts).mulFixedBaseField
      context

namespace ConfigureCertificate

/-- Transport the complete aggregate ECC certificate as a single capability. -/
def mono
    {advices : Fin 10 → Column .advice}
    {lagrangeCoeffs : Fin 8 → Column .fixed}
    {rangeCheck : LookupRangeCheck.Config 10} {counts : ConfigureCounts}
    {source target : KeygenContext Fp}
    (certificate :
      ConfigureCertificate advices lagrangeCoeffs rangeCheck counts source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (fixedColumns : ∀ column,
      column ∈ source.fixedColumns → column ∈ target.fixedColumns)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigureCertificate advices lagrangeCoeffs rangeCheck counts target where
  toCoreConfigureCertificate :=
    certificate.toCoreConfigureCertificate.mono gates lookups fixedColumns permutationColumns
  mul := certificate.mul.mono gates lookups fixedColumns permutationColumns
  mulFixedShort B :=
    (certificate.mulFixedShort B).mono gates lookups fixedColumns permutationColumns
  mulFixedFull B :=
    (certificate.mulFixedFull B).mono gates lookups fixedColumns permutationColumns
  mulFixedBaseField B :=
    (certificate.mulFixedBaseField B).mono gates lookups fixedColumns permutationColumns

end ConfigureCertificate

/-- The fixed-column law required by the fixed-base children follows from the
borrowed Lagrange columns being distinct and allocated before the ECC configure run. -/
def configureOutputFixedColumnsLawful
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts)
    (hnodup : (List.ofFn lagrangeCoeffs).Nodup)
    (hbound : ∀ column ∈ List.ofFn lagrangeCoeffs,
      column.index < counts.numFixedColumns) :
    ((configure advices lagrangeCoeffs rangeCheck).output counts)
      |>.mulFixedShort.superConfig.FixedColumnsLawful := by
  let witnessProgram := WitnessPoint.configure (advices 0) (advices 1)
  let addIncompleteProgram := AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  let addProgram := Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4,
      advices 5, advices 6, advices 7, advices 8)
  let witnessCounts := witnessProgram.finalCounts counts
  let addIncompleteCounts := addIncompleteProgram.finalCounts witnessCounts
  let addCounts := addProgram.finalCounts addIncompleteCounts
  let addConfig := addProgram.output addIncompleteCounts
  let addIncompleteConfig := addIncompleteProgram.output witnessCounts
  let mulProgram := Mul.configure addConfig rangeCheck advices
  let mulCounts := mulProgram.finalCounts addCounts
  apply MulFixed.configureOutputFixedColumnsLawful
  · exact hnodup
  · intro column hcolumn
    apply (hbound column hcolumn).trans_le
    exact le_trans
      (Configure.counts_componentwiseLE_finalCounts
        witnessProgram counts).numFixedColumns <|
      le_trans
        (Configure.counts_componentwiseLE_finalCounts
          addIncompleteProgram witnessCounts).numFixedColumns <|
        le_trans
          (Configure.counts_componentwiseLE_finalCounts
            addProgram addIncompleteCounts).numFixedColumns
          (Configure.counts_componentwiseLE_finalCounts
            mulProgram addCounts).numFixedColumns

/-- Construct the fixed-base Action-facing ECC capabilities once in the ECC owner. -/
def configureCertificate (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts)
    (fixedColumnsLawful :
      ((configure advices lagrangeCoeffs rangeCheck).output counts)
        |>.mulFixedShort.superConfig.FixedColumnsLawful) :
    ConfigureCertificate advices lagrangeCoeffs rangeCheck counts
      (configureContext advices lagrangeCoeffs rangeCheck counts) := by
  let core : CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts
      (configureContext advices lagrangeCoeffs rangeCheck counts) :=
    (coreConfigureCertificate advices lagrangeCoeffs rangeCheck counts).mono
      (fun _ hgate => hgate)
      (fun _ hargument => List.mem_cons_of_mem _ hargument)
      (fun _ hcolumn => List.mem_append_right _ hcolumn)
      (fun _ hcolumn => List.mem_cons_of_mem _ hcolumn)
  let witnessProgram := WitnessPoint.configure (advices 0) (advices 1)
  let addIncompleteProgram := AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  let addProgram := Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4,
      advices 5, advices 6, advices 7, advices 8)
  let witnessCounts := witnessProgram.finalCounts counts
  let addIncompleteCounts := addIncompleteProgram.finalCounts witnessCounts
  let addCounts := addProgram.finalCounts addIncompleteCounts
  let addConfig := addProgram.output addIncompleteCounts
  let addIncompleteConfig := addIncompleteProgram.output witnessCounts
  let mulProgram := Mul.configure addConfig rangeCheck advices
  let mulCounts := mulProgram.finalCounts addCounts
  let mulFixedProgram := MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
    addConfig addIncompleteConfig
  let mulFixedConfig := mulFixedProgram.output mulCounts
  let mulFixedCounts := mulFixedProgram.finalCounts mulCounts
  let fullProgram := MulFixed.FullWidth.configure mulFixedConfig
  let fullCounts := fullProgram.finalCounts mulFixedCounts
  let shortProgram := MulFixed.Short.configure mulFixedConfig
  let shortCounts := shortProgram.finalCounts fullCounts
  have hrunningColumns : ∀ column,
      column ∈ MulFixed.runningSumKeygenRequirements.permutationColumns
        mulFixedConfig core.addIncomplete.configured →
      column ∈ (configureContext advices lagrangeCoeffs rangeCheck counts).permutationColumns := by
    intro column hcolumn
    rw [MulFixed.configure_output_runningSumPermutationColumns] at hcolumn
    have haddColumns : Add.permutationColumns addConfig =
        ([advices 0, advices 1, advices 2, advices 3] : List AnyColumn) :=
      Add.configure_output_permutationColumns _ _ _ _ _ _ _ _ _ _
    have hincompleteColumns : AddIncomplete.permutationColumns addIncompleteConfig =
        ([advices 0, advices 1, advices 2, advices 3] : List AnyColumn) :=
      AddIncomplete.configure_output_permutationColumns _ _ _ _ _
    rw [haddColumns, hincompleteColumns] at hcolumn
    simp only [List.mem_append] at hcolumn
    rcases hcolumn with (hprefix | hadd) | hincomplete
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
      rcases hprefix with hfour | hfour | hfive
      · rw [hfour]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 4
      · rw [hfour]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 4
      · rw [hfive]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 5
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hadd
      rcases hadd with hzero | hone | htwo | hthree
      · rw [hzero]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 0
      · rw [hone]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 1
      · rw [htwo]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 2
      · rw [hthree]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hincomplete
      rcases hincomplete with hzero | hone | htwo | hthree
      · rw [hzero]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 0
      · rw [hone]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 1
      · rw [htwo]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 2
      · rw [hthree]
        apply List.mem_cons_of_mem
        exact advice_mem_permutationRequests _ _ _ _ 3
  refine
    { toCoreConfigureCertificate := core
      mul := ?_
      mulFixedShort := ?_
      mulFixedFull := ?_
      mulFixedBaseField := ?_ }
  · apply (Mul.mul.configureCertificate
      (addConfig, rangeCheck, advices) addCounts core.add.configured).mono
    · intro gate hgate
      rcases List.mem_append.mp hgate with hrequirements | hmul
      · have hgates : Mul.mul.keygenRequirements.gates
            (addConfig, rangeCheck, advices) core.add.configured =
            core.add.configured.gates := rfl
        rw [hgates] at hrequirements
        exact core.add.gates_of_configured gate hrequirements
      · simp only [configureContext]
        rw [show Mul.mul.configure (addConfig, rangeCheck, advices) =
          Mul.configure addConfig rangeCheck advices from rfl] at hmul
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hmul
    · intro argument hargument
      rcases List.mem_append.mp hargument with hrequirements | hmul
      · have hlookups : Mul.mul.keygenRequirements.lookups
            (addConfig, rangeCheck, advices) core.add.configured =
            LookupRangeCheck.rangeCheckLookup 10 rangeCheck ::
              core.add.configured.lookups := rfl
        rw [hlookups] at hrequirements
        rcases List.mem_cons.mp hrequirements with hrange | hadd
        · simp only [configureContext, List.mem_cons]
          exact Or.inl hrange
        · exact core.add.lookups_of_configured argument hadd
      · simp only [configureContext]
        apply List.mem_cons_of_mem
        rw [show Mul.mul.configure (addConfig, rangeCheck, advices) =
          Mul.configure addConfig rangeCheck advices from rfl] at hmul
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hmul
    · intro column hcolumn
      rcases List.mem_append.mp hcolumn with hrequirements | hmul
      · have hfixedColumns : Mul.mul.keygenRequirements.fixedColumns
            (addConfig, rangeCheck, advices) core.add.configured =
            core.add.configured.fixedColumns := rfl
        rw [hfixedColumns] at hrequirements
        exact core.add.fixedColumns_of_configured column hrequirements
      · apply List.mem_append_right
        rw [show Mul.mul.configure (addConfig, rangeCheck, advices) =
          Mul.configure addConfig rangeCheck advices from rfl] at hmul
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hmul
    · intro column hcolumn
      rcases List.mem_append.mp hcolumn with hrequirements | hmul
      · rw [show Mul.mul.keygenRequirements.permutationColumns
            (addConfig, rangeCheck, advices) core.add.configured =
            ([rangeCheck.runningSum, advices 3, advices 0,
              advices 1, advices 7] : List AnyColumn) ++
                core.add.configured.permutationColumns from rfl] at hrequirements
        rcases List.mem_append.mp hrequirements with hcolumns | hadd
        · simp only [List.mem_cons] at hcolumns
          rcases hcolumns with hrange | hthree | hzero | hone | hseven
          · simp only [configureContext, List.mem_cons]
            exact Or.inl hrange
          · rw [hthree]
            apply List.mem_cons_of_mem
            exact advice_mem_permutationRequests _ _ _ _ 3
          · rw [hzero]
            apply List.mem_cons_of_mem
            exact advice_mem_permutationRequests _ _ _ _ 0
          · rw [hone]
            apply List.mem_cons_of_mem
            exact advice_mem_permutationRequests _ _ _ _ 1
          · rcases hseven with hseven | hseven
            · rw [hseven]
              apply List.mem_cons_of_mem
              exact advice_mem_permutationRequests _ _ _ _ 7
            · contradiction
        · exact core.add.permutationColumns_of_configured column hadd
      · apply List.mem_cons_of_mem
        rw [show Mul.mul.configure (addConfig, rangeCheck, advices) =
          Mul.configure addConfig rangeCheck advices from rfl] at hmul
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hmul
  · intro B
    apply ((MulFixed.Short.circuit B).configureCertificate
      mulFixedConfig fullCounts
      ⟨core.addIncomplete.configured, core.add.configured,
        fixedColumnsLawful⟩).mono
    · intro gate hgate
      simp only [MulFixed.Short.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, MulFixed.runningSumKeygenRequirements,
        List.mem_append] at hgate
      rcases hgate with hrequirements | hshort
      · rcases hrequirements with hcoreOrIncomplete | hadd
        · rcases hcoreOrIncomplete with hcore | hincomplete
          · exact mem_mulFixed_gates _ _ _ _ gate hcore
          · exact core.addIncomplete.gates_of_configured gate hincomplete
        · exact core.add.gates_of_configured gate hadd
      · simp only [configureContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hshort
    · intro argument hargument
      simp only [MulFixed.Short.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, MulFixed.runningSumKeygenRequirements,
        List.mem_append] at hargument
      rcases hargument with hrequirements | hshort
      · rcases hrequirements with hincomplete | hadd
        · exact core.addIncomplete.lookups_of_configured argument hincomplete
        · exact core.add.lookups_of_configured argument hadd
      · simp only [configureContext]
        apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hshort
    · intro column hcolumn
      simp only [MulFixed.Short.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with hrequirements | hshort
      · exact mem_mulFixed_fixedColumns _ _ _ _ column hrequirements
      · apply List.mem_append_right
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hshort
    · intro column hcolumn
      simp only [MulFixed.Short.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with (hrunning | hadd) | hshort
      · exact hrunningColumns column hrunning
      · exact core.add.permutationColumns_of_configured column hadd
      · apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hshort
  · intro B
    apply ((MulFixed.FullWidth.circuit B).configureCertificate
      mulFixedConfig mulFixedCounts
      ⟨core.addIncomplete.configured, core.add.configured,
        fixedColumnsLawful⟩).mono
    · intro gate hgate
      simp only [MulFixed.FullWidth.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, MulFixed.runningSumKeygenRequirements,
        List.mem_append] at hgate
      rcases hgate with hrequirements | hfull
      · rcases hrequirements with hcoreOrIncomplete | hadd
        · rcases hcoreOrIncomplete with hcore | hincomplete
          · exact mem_mulFixed_gates _ _ _ _ gate hcore
          · exact core.addIncomplete.gates_of_configured gate hincomplete
        · exact core.add.gates_of_configured gate hadd
      · simp only [configureContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hfull
    · intro argument hargument
      simp only [MulFixed.FullWidth.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hargument
      rcases hargument with hrequirements | hfull
      · rcases hrequirements with hincomplete | hadd
        · exact core.addIncomplete.lookups_of_configured argument hincomplete
        · exact core.add.lookups_of_configured argument hadd
      · simp only [configureContext]
        apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hfull
    · intro column hcolumn
      simp only [MulFixed.FullWidth.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with hrequirements | hfull
      · exact mem_mulFixed_fixedColumns _ _ _ _ column hrequirements
      · apply List.mem_append_right
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hfull
    · intro column hcolumn
      simp only [MulFixed.FullWidth.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with (hrunning | hadd) | hfull
      · exact hrunningColumns column hrunning
      · exact core.add.permutationColumns_of_configured column hadd
      · apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hfull
  · intro B
    apply ((MulFixed.BaseFieldElem.circuit B).configureCertificate
      (![advices 6, advices 7, advices 8], rangeCheck, mulFixedConfig)
      shortCounts
      ⟨core.addIncomplete.configured, core.add.configured,
        fixedColumnsLawful⟩).mono
    · intro gate hgate
      simp only [MulFixed.BaseFieldElem.circuit,
        FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
        MulFixed.BaseFieldElem.keygenRequirements,
        MulFixed.runningSumKeygenRequirements, List.mem_append] at hgate
      rcases hgate with hrequirements | hbase
      · rcases hrequirements with hcoreOrIncomplete | hadd
        · rcases hcoreOrIncomplete with hcore | hincomplete
          · exact mem_mulFixed_gates _ _ _ _ gate hcore
          · exact core.addIncomplete.gates_of_configured gate hincomplete
        · exact core.add.gates_of_configured gate hadd
      · simp only [configureContext]
        unfold configure
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_right
        apply Configure.mem_gates_delta_bind_left
        exact hbase
    · intro argument hargument
      simp only [MulFixed.BaseFieldElem.circuit,
        FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
        MulFixed.BaseFieldElem.keygenRequirements,
        MulFixed.runningSumKeygenRequirements, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hargument
      rcases hargument with hrequirements | hbase
      · rcases hrequirements with hadds | hrange
        · rcases hadds with hincomplete | hadd
          · exact core.addIncomplete.lookups_of_configured argument hincomplete
          · exact core.add.lookups_of_configured argument hadd
        · simp only [configureContext, List.mem_cons]
          exact Or.inl hrange
      · simp only [configureContext]
        apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_right
        apply Configure.mem_lookups_delta_bind_left
        exact hbase
    · intro column hcolumn
      simp only [MulFixed.BaseFieldElem.circuit,
        FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
        MulFixed.BaseFieldElem.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with hrequirements | hbase
      · exact mem_mulFixed_fixedColumns _ _ _ _ column hrequirements
      · apply List.mem_append_right
        unfold configure
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_right
        apply Configure.mem_fixedColumns_bind_left
        exact hbase
    · intro column hcolumn
      simp only [MulFixed.BaseFieldElem.circuit,
        FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
        MulFixed.BaseFieldElem.keygenRequirements, List.mem_append] at hcolumn
      rcases hcolumn with ((hrunning | hadd) | hrange) | hbase
      · exact hrunningColumns column hrunning
      · exact core.add.permutationColumns_of_configured column hadd
      · simp only [List.mem_singleton] at hrange
        rw [hrange]
        simp only [configureContext, List.mem_cons, true_or]
      · apply List.mem_cons_of_mem
        unfold configure
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_right
        apply Configure.mem_permutationRequests_delta_bind_left
        exact hbase

end Zcash.Circuits.Ecc
