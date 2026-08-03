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

instance (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    ElaboratedConfigure (configure advices lagrangeCoeffs rangeCheck) := by
  unfold configure
  infer_instance

/-- The keygen context produced locally by one aggregate ECC configure run. -/
private def configureDeltaContext (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    KeygenContext Fp :=
  { gates := ((configure advices lagrangeCoeffs rangeCheck).delta counts).gates
    lookups := ((configure advices lagrangeCoeffs rangeCheck).delta counts).lookups }

/-- The capabilities exported by ECC: its local configure delta plus the range-check
lookup borrowed from its caller by variable- and base-field multiplication. -/
def configureContext (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    KeygenContext Fp :=
  { gates := ((configure advices lagrangeCoeffs rangeCheck).delta counts).gates
    lookups := LookupRangeCheck.rangeCheckLookup 10 rangeCheck ::
      ((configure advices lagrangeCoeffs rangeCheck).delta counts).lookups }

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
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups) :
    CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts target where
  witnessPoint := certificate.witnessPoint.mono gates lookups
  witnessPointFormal := certificate.witnessPointFormal.mono gates lookups
  witnessPointNonIdFormal := certificate.witnessPointNonIdFormal.mono gates lookups
  addIncomplete := certificate.addIncomplete.mono gates lookups
  add := certificate.add.mono gates lookups
  addFormal := certificate.addFormal.mono gates lookups

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
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups) :
    ConfigureCertificate advices lagrangeCoeffs rangeCheck counts target where
  toCoreConfigureCertificate :=
    certificate.toCoreConfigureCertificate.mono gates lookups
  mul := certificate.mul.mono gates lookups
  mulFixedShort B := (certificate.mulFixedShort B).mono gates lookups
  mulFixedFull B := (certificate.mulFixedFull B).mono gates lookups
  mulFixedBaseField B := (certificate.mulFixedBaseField B).mono gates lookups

end ConfigureCertificate

/-- Construct the fixed-base Action-facing ECC capabilities once in the ECC owner. -/
def configureCertificate (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) (counts : ConfigureCounts) :
    ConfigureCertificate advices lagrangeCoeffs rangeCheck counts
      (configureContext advices lagrangeCoeffs rangeCheck counts) := by
  let core : CoreConfigureCertificate advices lagrangeCoeffs rangeCheck counts
      (configureContext advices lagrangeCoeffs rangeCheck counts) :=
    (coreConfigureCertificate advices lagrangeCoeffs rangeCheck counts).mono
      (fun _ hgate => hgate)
      (fun _ hargument => List.mem_cons_of_mem _ hargument)
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
  · intro B
    apply ((MulFixed.Short.circuit B).configureCertificate
      mulFixedConfig fullCounts
      ⟨core.addIncomplete.configured, core.add.configured⟩).mono
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
  · intro B
    apply ((MulFixed.FullWidth.circuit B).configureCertificate
      mulFixedConfig mulFixedCounts
      ⟨core.addIncomplete.configured, core.add.configured⟩).mono
    · intro gate hgate
      simp only [MulFixed.FullWidth.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.mem_append] at hgate
      rcases hgate with hrequirements | hfull
      · rcases hrequirements with hincomplete | hadd
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
  · intro B
    apply ((MulFixed.BaseFieldElem.circuit B).configureCertificate
      (![advices 6, advices 7, advices 8], rangeCheck, mulFixedConfig)
      shortCounts
      ⟨core.addIncomplete.configured, core.add.configured⟩).mono
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

end Zcash.Circuits.Ecc
