import Clean.Halo2.Compiler.ConstraintFamilies
import Clean.Halo2.TopLevel

/-! # Source lookup activations and configure membership -/

namespace Halo2

set_option maxHeartbeats 20000

/-- One lookup activation in the placed operation stream. -/
structure EnabledLookup (F : Type) where
  argument : LookupArgument F
  enabled : List Selector
  region : RegionIndex
  row : ℕ

namespace EnabledLookup

variable {F : Type} [FiniteField F]

/-- The selector valuation carried by this particular lookup activation. -/
def selectorValue (lookup : EnabledLookup F) (index : ℕ) : F :=
  if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0

@[simp] theorem selectorValue_mk
    (argument : LookupArgument F) (enabled : List Selector)
    (region : RegionIndex) (row index : ℕ) :
    selectorValue
        ({ argument := argument, enabled := enabled, region := region, row := row } :
          EnabledLookup F) index =
      if ∃ selector ∈ enabled, selector.index = index then 1 else 0 := rfl

/-- The lookup input tuple at the activation's placed row. -/
def inputValues (place : RegionIndex → ℕ) (env : Environment F)
    (lookup : EnabledLookup F) : List F :=
  lookup.argument.inputs.map
    (Expression.eval
      (Query.eval env
        (fun index =>
          if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0)
        (place lookup.region + lookup.row : ℕ)))

/-- The lookup table tuple at one absolute usable row. -/
def tableValues (env : Environment F) (lookup : EnabledLookup F)
    (tableRow : ℕ) : List F :=
  lookup.argument.tables.map
    (Expression.eval
      (Query.eval env
        (fun index =>
          if ∃ selector ∈ lookup.enabled, selector.index = index then 1 else 0)
        (tableRow : ℤ)))

/-- Clean's semantic lookup relation for one extracted activation. -/
def IsSatisfied (place : RegionIndex → ℕ) (env : Environment F)
    (lookup : EnabledLookup F) : Prop :=
  ∃ tableRow : ℕ, tableRow < env.usableRows ∧
    lookup.inputValues place env = lookup.tableValues env tableRow

end EnabledLookup

/-- Lookup activations in one region, retaining the region index used by placement. -/
def regionEnabledLookups {F : Type} (self : RegionIndex) :
    RegionOperations F → List (EnabledLookup F)
  | [] => []
  | .enableLookup argument enabled row :: rest =>
      ⟨argument, enabled, self, row⟩ :: regionEnabledLookups self rest
  | _ :: rest => regionEnabledLookups self rest

/-- Lookup activations in a complete layouter stream, with region indices threaded exactly as in
`Constraints`. -/
def operationEnabledLookups {F : Type} :
    Operations F → RegionIndex → List (EnabledLookup F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionEnabledLookups i body ++ operationEnabledLookups rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationEnabledLookups rest i
  | .loadTable _ _ :: rest, i => operationEnabledLookups rest i

/-- The reduced synthesis summary counts exactly the lookup activations extracted
from one region. -/
theorem regionEnabledLookups_length {F : Type}
    (self : RegionIndex) (body : RegionOperations F) :
    (regionEnabledLookups self body).length =
      (FloorPlanner.regionSynthesisSummary body).lookupActivationCount := by
  induction body with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [regionEnabledLookups, FloorPlanner.regionSynthesisSummary,
          FloorPlanner.RegionSynthesisSummary.combine_lookupActivationCount,
          FloorPlanner.RegionSynthesisSummary.ofOperation_lookupActivationCount,
          FloorPlanner.regionOperationLookupActivationCount,
          List.length_cons, inductionHypothesis] <;>
        omega

/-- The reduced synthesis summary counts exactly the lookup activations extracted
from a complete operation stream. -/
theorem operationEnabledLookups_length {F : Type}
    (operations : Operations F) (initial : RegionIndex) :
    (operationEnabledLookups operations initial).length =
      (FloorPlanner.synthesisSummary operations).lookupActivationCount := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [operationEnabledLookups, FloorPlanner.synthesisSummary,
          List.length_append, regionEnabledLookups_length,
          inductionHypothesis,
          FloorPlanner.SynthesisSummary.combine_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofRegion_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofInstanceRow_lookupActivationCount,
          FloorPlanner.SynthesisSummary.ofTableValues_lookupActivationCount,
          Nat.zero_add]

/-- Membership in a region's extracted lookup list is exactly membership of the
corresponding raw `.enableLookup` operation, with the enclosing region retained. -/
theorem mem_regionEnabledLookups_iff
    {F : Type} (lookup : EnabledLookup F)
    (self : RegionIndex) (body : RegionOperations F) :
    lookup ∈ regionEnabledLookups self body ↔
      lookup.region = self ∧
        RegionOperation.enableLookup lookup.argument lookup.enabled lookup.row ∈
          body := by
  rcases lookup with ⟨argument, enabled, region, row⟩
  induction body with
  | nil =>
      simp [regionEnabledLookups]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [regionEnabledLookups]
      all_goals aesop

/--
An extracted lookup points to the exact indexed region body containing its raw
activation operation.
-/
theorem mem_operationEnabledLookups_iff
    {F : Type} (lookup : EnabledLookup F)
    (operations : Operations F) (initial : RegionIndex) :
    lookup ∈ operationEnabledLookups operations initial ↔
      ∃ body,
        (lookup.region, body) ∈ (indexedRegions operations initial).1 ∧
          RegionOperation.enableLookup lookup.argument lookup.enabled lookup.row ∈
            body := by
  induction operations generalizing initial with
  | nil =>
      simp [operationEnabledLookups, indexedRegions]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [operationEnabledLookups, indexedRegions,
          mem_regionEnabledLookups_iff]
      all_goals aesop

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- The lookup-family projection of one region is exactly satisfaction of its extracted lookup
activations. -/
theorem region_lookup_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionConstraints .lookup place self env ops ↔
      (regionEnabledLookups self ops).Forall (EnabledLookup.IsSatisfied place env) := by
  induction ops with
  | nil => simp [RegionConstraints, regionEnabledLookups]
  | cons op rest ih =>
      cases op <;>
        simp_all [RegionConstraints, RegionConstraint, RegionOperation.Constraints,
          regionEnabledLookups, EnabledLookup.IsSatisfied, EnabledLookup.inputValues,
          EnabledLookup.tableValues]

/-- The complete lookup-family projection is exactly satisfaction of all lookup activations in the
placed operation stream. -/
theorem lookup_constraints_iff_enabledLookups
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Constraints .lookup place env ops i ↔
      (operationEnabledLookups ops i).Forall (EnabledLookup.IsSatisfied place env) := by
  induction ops generalizing i with
  | nil => simp [Constraints, operationEnabledLookups]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Constraints, ih, region_lookup_constraints_iff]
          simp [operationEnabledLookups, List.forall_append]
      | constrainInstance cell col row =>
          rw [Constraints, ih]
          simp [operationEnabledLookups]
      | loadTable table values =>
          rw [Constraints, ih]
          simp [operationEnabledLookups]

end CircuitConstraintFamily

namespace OperationsKeygenCoherent

/-- A coherent region registers every extracted enabled lookup. -/
theorem mem_lookups_of_mem_regionEnabledLookups
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ regionEnabledLookups self body) :
    enabled.argument ∈ cs.lookups := by
  induction body with
  | nil => simp [regionEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableLookup argument selectors row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledLookups, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableGate gate row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled lookup. -/
theorem mem_lookups_of_mem_operationEnabledLookups
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ operationEnabledLookups operations i) :
    enabled.argument ∈ cs.lookups := by
  induction operations generalizing i with
  | nil => simp [operationEnabledLookups] at henabled
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          rcases (region_cons
            cs name body rest).mp hcoherent with
            ⟨hoperation, hrest⟩
          simp only [operationEnabledLookups, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact mem_lookups_of_mem_regionEnabledLookups hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          have hrest := (constrainInstance_cons
            cs cell column row rest).mp hcoherent
          exact ih hrest.2.2 henabled
      | loadTable table values =>
          have hrest := (loadTable_cons
            cs table values rest).mp hcoherent
          exact ih hrest.2 henabled

end OperationsKeygenCoherent

end Halo2
