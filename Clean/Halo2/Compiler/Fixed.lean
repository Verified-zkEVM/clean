import Clean.Halo2.Compiler.ConstraintFamilies
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.TopLevel

/-!
# Fixed-data compilation and its semantics

Fixed assignments and lookup-table loads are the circuit-fixed part of Clean's
authoritative semantics.  This file extracts both forms into one list and proves that
their satisfaction is exactly the fixed constraint family.

The fixed-layout compiler uses this characterization to establish fixed constraints
from its sparse assignments, including the default-fill rows of loaded tables.
-/

variable {F : Type} [FiniteField F]

namespace Halo2

set_option maxHeartbeats 20000

/-- One fixed-data obligation declared by synthesis. -/
inductive FixedRequirement (F : Type) where
  | assignment (region : RegionIndex) (column : Column .fixed) (row : ℕ) (value : F)
  | table (column : TableColumn) (values : List F)

namespace FixedRequirement

variable {F : Type} [FiniteField F]

/-- The exact Clean semantics of one extracted fixed-data obligation. -/
def IsSatisfied (place : RegionIndex → ℕ) (env : Environment F) :
    FixedRequirement F → Prop
  | .assignment region column row value =>
      env.fixed column (place region + row : ℕ) = value
  | .table column values =>
      (∀ row : ℕ, row < values.length →
        env.fixed column.inner (row : ℤ) = values[row]!) ∧
      (values ≠ [] → ∀ row : ℕ, values.length ≤ row → row < env.usableRows →
        env.fixed column.inner (row : ℤ) = values[0]!)

end FixedRequirement

/-- Fixed assignments in one region. -/
def regionFixedRequirements {F : Type} (self : RegionIndex) :
    RegionOperations F → List (FixedRequirement F)
  | [] => []
  | .assignFixed column row value :: rest =>
      .assignment self column row value :: regionFixedRequirements self rest
  | _ :: rest => regionFixedRequirements self rest

/-- Fixed assignments and table loads in one complete operation stream. -/
def operationFixedRequirements {F : Type} :
    Operations F → RegionIndex → List (FixedRequirement F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionFixedRequirements i body ++ operationFixedRequirements rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationFixedRequirements rest i
  | .loadTable column values :: rest, i =>
      .table column values :: operationFixedRequirements rest i

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region's fixed-family projection is exactly its extracted assignments. -/
theorem region_fixed_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionConstraints .fixed place self env ops ↔
      (regionFixedRequirements self ops).Forall
        (FixedRequirement.IsSatisfied place env) := by
  induction ops with
  | nil => simp [RegionConstraints, regionFixedRequirements]
  | cons op rest ih =>
      cases op <;>
        simp_all [RegionConstraints, RegionConstraint, RegionOperation.Constraints,
          regionFixedRequirements, FixedRequirement.IsSatisfied, Environment.get_fixed]

/-- The complete fixed-family projection is satisfaction of every extracted requirement. -/
theorem fixed_constraints_iff_requirements
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Constraints .fixed place env ops i ↔
      (operationFixedRequirements ops i).Forall
        (FixedRequirement.IsSatisfied place env) := by
  induction ops generalizing i with
  | nil => simp [Constraints, operationFixedRequirements]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Constraints, ih, region_fixed_constraints_iff]
          simp [operationFixedRequirements, List.forall_append]
      | constrainInstance cell col row =>
          rw [Constraints, ih]
          simp [operationFixedRequirements]
      | loadTable column values =>
          rw [Constraints, ih]
          simp [operationFixedRequirements, FixedRequirement.IsSatisfied]

end CircuitConstraintFamily

end Halo2

/-!
## Fixed-layout compiler bridge

The keygen layout compiler emits sparse fixed-column entries from table loads and
region-local fixed assignments.  This module proves, generically, that realizing
those emitted entries supplies the `fixed` operation family used by circuit
soundness.  Selector entries and constant-copy allocation are separate compiler
products; they are not needed for the explicit fixed requirements extracted here.
-/

namespace Halo2

set_option maxHeartbeats 20000

namespace FixedLayout

/-- Every explicit row of a loaded table occurs in `Layout.tableAssignments`. -/
theorem mem_tableAssignments_of_loadTable_of_lt
    (usable : ℕ) (ops : Operations F)
    (table : TableColumn) (values : List F)
    (hload : Operation.loadTable table values ∈ ops)
    (row : ℕ) (hrow : row < values.length) :
    (table.inner.index, row, values[row]!) ∈
      Layout.tableAssignments usable ops := by
  induction ops with
  | nil => simp at hload
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          exact ih (by simpa using hload)
      | constrainInstance cell column instanceRow =>
          exact ih (by simpa using hload)
      | loadTable loadedTable loadedValues =>
          simp only [List.mem_cons] at hload
          rcases hload with hhead | htail
          · cases hhead
            unfold Layout.tableAssignments
            apply List.mem_append_left
            unfold Layout.tableColumnAssignments
            apply List.mem_append_left
            apply List.mem_map.mpr
            exact ⟨(values[row]!, row), by
              apply List.mk_mem_zipIdx_iff_getElem?.mpr
              simp [List.getElem!_eq_getElem?_getD,
                List.getElem?_eq_getElem hrow], rfl⟩
          · unfold Layout.tableAssignments
            apply List.mem_append_right
            exact ih htail

/--
Every default-fill row of a nonempty loaded table occurs in
`Layout.tableAssignments`.
-/
theorem mem_tableAssignments_of_loadTable_of_fill
    (usable : ℕ) (ops : Operations F)
    (table : TableColumn) (values : List F)
    (hload : Operation.loadTable table values ∈ ops)
    (hne : values ≠ [])
    (row : ℕ) (hlower : values.length ≤ row)
    (hupper : row < usable) :
    (table.inner.index, row, values[0]!) ∈
      Layout.tableAssignments usable ops := by
  induction ops with
  | nil => simp at hload
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          exact ih (by simpa using hload)
      | constrainInstance cell column instanceRow =>
          exact ih (by simpa using hload)
      | loadTable loadedTable loadedValues =>
          simp only [List.mem_cons] at hload
          rcases hload with hhead | htail
          · cases hhead
            unfold Layout.tableAssignments
            apply List.mem_append_left
            unfold Layout.tableColumnAssignments
            apply List.mem_append_right
            rcases values with _ | ⟨first, rest⟩
            · contradiction
            apply List.mem_map.mpr
            refine ⟨row - (first :: rest).length, ?_, ?_⟩
            · apply List.mem_range.mpr
              omega
            · simp only [List.getElem!_eq_getElem?_getD,
                List.getElem?_cons_zero, Option.getD_some]
              congr
              omega
          · unfold Layout.tableAssignments
            apply List.mem_append_right
            exact ih htail

omit [FiniteField F] in
/-- Region fixed requirements never contain a table load. -/
private theorem table_not_mem_regionFixedRequirements
    (self : RegionIndex) (body : RegionOperations F)
    (table : TableColumn) (values : List F) :
    FixedRequirement.table table values ∉
      regionFixedRequirements self body := by
  induction body with
  | nil => simp [regionFixedRequirements]
  | cons operation rest ih =>
      cases operation <;>
        simp_all [regionFixedRequirements]

omit [FiniteField F] in
/-- A table fixed requirement comes from the corresponding layouter operation. -/
theorem loadTable_mem_of_requirement
    (ops : Operations F) (i : RegionIndex)
    (table : TableColumn) (values : List F)
    (hrequirement :
      FixedRequirement.table table values ∈
        operationFixedRequirements ops i) :
    Operation.loadTable table values ∈ ops := by
  induction ops generalizing i with
  | nil => simp [operationFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationFixedRequirements, List.mem_append] at hrequirement
          rcases hrequirement with hbody | hrest
          · exact absurd hbody
              (table_not_mem_regionFixedRequirements i body table values)
          · exact List.mem_cons_of_mem _
              (ih (i := i + 1) hrest)
      | constrainInstance cell column row =>
          exact List.mem_cons_of_mem _
            (ih (i := i) (by simpa [operationFixedRequirements] using hrequirement))
      | loadTable loadedTable loadedValues =>
          simp only [operationFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih (i := i) htail)

omit [FiniteField F] in
/-- A region requirement remembers the corresponding `assignFixed` operation. -/
private theorem assignFixed_mem_of_region_requirement
    (self : RegionIndex) (body : RegionOperations F)
    (column : Column .fixed) (row : ℕ) (value : F)
    (hrequirement :
      FixedRequirement.assignment self column row value ∈
        regionFixedRequirements self body) :
    RegionOperation.assignFixed column row value ∈ body := by
  induction body with
  | nil => simp [regionFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | assignFixed assignedColumn assignedRow assignedValue =>
          simp only [regionFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih htail)
      | _ =>
          exact List.mem_cons_of_mem _
            (ih (by simpa [regionFixedRequirements] using hrequirement))

omit [FiniteField F] in
/-- A region-local assignment requirement retains its enclosing region index. -/
private theorem region_eq_of_assignment_requirement
    (self region : RegionIndex) (body : RegionOperations F)
    (column : Column .fixed) (row : ℕ) (value : F)
    (hrequirement :
      FixedRequirement.assignment region column row value ∈
        regionFixedRequirements self body) :
    region = self := by
  induction body with
  | nil => simp [regionFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | assignFixed assignedColumn assignedRow assignedValue =>
          simp only [regionFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hhead | htail
          · cases hhead
            rfl
          · exact ih htail
      | _ =>
          exact ih (by simpa [regionFixedRequirements] using hrequirement)

omit [FiniteField F] in
/--
Every extracted region fixed requirement occurs in the sparse
`Layout.regionAssignments` output at its V1 absolute row.
-/
theorem mem_regionAssignments_of_requirement
    (starts : List ℕ) (ops : Operations F) (i : RegionIndex)
    (region : RegionIndex) (column : Column .fixed)
    (row : ℕ) (value : F)
    (hrequirement :
      FixedRequirement.assignment region column row value ∈
        operationFixedRequirements ops i) :
    (column.index, Layout.place starts region + row, value) ∈
      Layout.regionAssignments starts
        (indexedRegions ops i).1 := by
  induction ops generalizing i with
  | nil => simp [operationFixedRequirements] at hrequirement
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationFixedRequirements, List.mem_append] at hrequirement
          rcases hrequirement with hbody | hrest
          · have hregion : region = i :=
              region_eq_of_assignment_requirement
                i region body column row value hbody
            subst region
            have hassign :
                RegionOperation.assignFixed column row value ∈ body := by
              apply assignFixed_mem_of_region_requirement
                i body column row value
              exact hbody
            simp only [indexedRegions]
            apply List.mem_flatMap.mpr
            refine ⟨(i, body), List.mem_cons_self, ?_⟩
            apply List.mem_filterMap.mpr
            exact ⟨.assignFixed column row value, hassign, rfl⟩
          · simp only [indexedRegions]
            apply List.mem_flatMap.mpr
            obtain ⟨indexed, hindexed, hentry⟩ :=
              List.mem_flatMap.mp
                (ih (i := i + 1) hrest)
            exact ⟨indexed, List.mem_cons_of_mem _ hindexed, hentry⟩
      | constrainInstance cell instanceColumn instanceRow =>
          exact ih (i := i)
            (by simpa [operationFixedRequirements] using hrequirement)
      | loadTable table values =>
          simp only [operationFixedRequirements, List.mem_cons] at hrequirement
          rcases hrequirement with hfalse | hrest
          · contradiction
          · exact ih (i := i) hrest

/--
Realizing the raw sparse table and region-assignment entries realizes every explicit
fixed requirement in the operation stream.
-/
theorem requirement_satisfied_of_entries
    (starts : List ℕ) (usable : ℕ)
    (ops : Operations F) (i : RegionIndex)
    (env : Environment F)
    (husable : env.usableRows = usable)
    (hentries : ∀ column row value,
      (column, row, value) ∈
        (Layout.tableAssignments usable ops ++
          Layout.regionAssignments starts
            (indexedRegions ops i).1) →
      env.fixed ⟨column⟩ (row : ℤ) = value)
    (requirement : FixedRequirement F)
    (hrequirement :
      requirement ∈ operationFixedRequirements ops i) :
    requirement.IsSatisfied (Layout.place starts) env := by
  cases requirement with
  | assignment region column row value =>
      simp only [FixedRequirement.IsSatisfied]
      have hentry := hentries column.index
        (Layout.place starts region + row) value
        (List.mem_append_right _
          (mem_regionAssignments_of_requirement
            starts ops i region column row value hrequirement))
      simpa using hentry
  | table column values =>
      simp only [FixedRequirement.IsSatisfied]
      have hload :=
        loadTable_mem_of_requirement ops i column values hrequirement
      constructor
      · intro row hrow
        have hentry := hentries column.inner.index row
          values[row]!
          (List.mem_append_left _
            (mem_tableAssignments_of_loadTable_of_lt
              usable ops column values hload row hrow))
        simpa using hentry
      · intro hne row hlower hupper
        have hrow : row < usable := by
          simpa [husable] using hupper
        have hentry := hentries column.inner.index row
          values[0]!
          (List.mem_append_left _
            (mem_tableAssignments_of_loadTable_of_fill
              usable ops column values hload hne row hlower hrow))
        simpa using hentry

/-- The entry-realization premise supplies the complete fixed constraint family. -/
theorem constraints_of_entries
    (starts : List ℕ) (usable : ℕ)
    (ops : Operations F) (i : RegionIndex)
    (env : Environment F)
    (husable : env.usableRows = usable)
    (hentries : ∀ column row value,
      (column, row, value) ∈
        (Layout.tableAssignments usable ops ++
          Layout.regionAssignments starts
            (indexedRegions ops i).1) →
      env.fixed ⟨column⟩ (row : ℤ) = value) :
    CircuitConstraintFamily.Constraints .fixed
      (Layout.place starts) env ops i := by
  rw [CircuitConstraintFamily.fixed_constraints_iff_requirements,
    List.forall_iff_forall_mem]
  intro requirement hrequirement
  exact requirement_satisfied_of_entries
    starts usable ops i env husable hentries requirement hrequirement

end FixedLayout

end Halo2

/-! ## Canonical environments realize compiler-owned fixed data -/

namespace Halo2.TopLevelCircuit

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Every emitted fixed assignment is already true in the canonical environment. -/
theorem environment_fixed_of_mem_raw (assignment : ProofAssignment F)
    {entry : Layout.FixedAssignment F}
    (hentry : entry ∈ Layout.rawAssignments (top.usableRowsAt top.domainExponent)
      top.selectorMap top.constraintSystem top.operations) :
    (top.environment assignment).fixed ⟨entry.1⟩ (entry.2.1 : ℤ) = entry.2.2 := by
  have hbounds := top.fixedAssignment_bounds_of_mem_raw entry hentry
  rw [top.environment_fixed, top.fixedValue_eq_fixedRows_getD]
  rw [Int.natMod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hbounds.2),
    Int.toNat_natCast]
  exact top.fixedRows_getD_getD_eq_of_mem_raw entry hentry

/-- A packed selector assignment is part of the compiler's fixed output. -/
theorem selectorAssignment_mem_raw {entry : Layout.FixedAssignment F}
    (hentry : entry ∈ Layout.selectorAssignments top.selectorMap top.selectorActivations) :
    entry ∈ Layout.rawAssignments (top.usableRowsAt top.domainExponent)
      top.selectorMap top.constraintSystem top.operations := by
  simpa only [Layout.rawAssignments, List.mem_append] using Or.inl (Or.inr hentry)

end Halo2.TopLevelCircuit

namespace Halo2.TopLevelCircuit

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Fixed assignments and table contents require no proof-varying hypothesis:
the compiler supplies them when constructing the environment. -/
theorem fixed_constraints (assignment : ProofAssignment F) :
    CircuitConstraintFamily.Constraints .fixed top.placement
      (top.environment assignment) top.operations 0 := by
  have hplace : Layout.place top.regionStarts = top.placement := by
    funext region
    exact (top.placement_apply region).symm
  rw [← hplace]
  apply FixedLayout.constraints_of_entries top.regionStarts
    (top.usableRowsAt top.domainExponent) top.operations 0
  · rw [top.environment_usableRows, top.usableRowsAt_domainExponent,
      top.n_eq_two_pow_domainExponent, top.domainExponent_eq_compiled]
  · intro column row value hentry
    apply top.environment_fixed_of_mem_raw assignment (entry := (column, row, value))
    simp only [Layout.rawAssignments, List.mem_append] at hentry ⊢
    rcases hentry with htable | hregion
    · exact Or.inl (Or.inl (Or.inl htable))
    · exact Or.inr hregion

end Halo2.TopLevelCircuit
