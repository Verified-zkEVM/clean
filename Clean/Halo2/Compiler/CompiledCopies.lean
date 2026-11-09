import Clean.Halo2.Compiler.ConstraintFamilies
import Clean.Halo2.Compiler.CopyLayout
import Clean.Halo2.Keygen.Domain
import Mathlib.Data.List.Forall2
import Clean.Utils.ListZip
import Clean.Halo2.Compiler.Fixed

/-!
# Copy compilation and its semantics

Clean operations declare cell, instance, and constant equalities. This module extracts
those declarations, characterizes their resolved compiler pairs, and proves that equality
on the compiled pairs establishes the source copy constraints. Registration, placement,
and constant allocation are discharged from the top-level circuit's guarantees.
-/

variable {F : Type}

namespace Halo2

/-- A semantic endpoint of a Clean copy operation, with constants represented by value. -/
inductive CopyEndpoint (F : Type) where
  | cell : Cell → CopyEndpoint F
  | instance : Column .instance → ℕ → CopyEndpoint F
  | constant : F → CopyEndpoint F
deriving Repr

namespace CopyEndpoint

variable {F : Type} [FiniteField F]

/-- Read an endpoint in Clean's placed environment. -/
def eval (place : RegionIndex → ℕ) (env : Environment F) : CopyEndpoint F → F
  | .cell c => c.eval place env
  | .instance col row => env.get col (row : ℤ)
  | .constant value => value

end CopyEndpoint

/-- A declared semantic equality. -/
abbrev DeclaredCopy (F : Type) := CopyEndpoint F × CopyEndpoint F

namespace DeclaredCopy

variable {F : Type} [FiniteField F]

/-- The equality denoted by one declared copy. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (copy : DeclaredCopy F) : Prop :=
  copy.1.eval place env = copy.2.eval place env

end DeclaredCopy

/-- The copy, if any, declared by one region operation. -/
def regionOperationDeclaredCopy? {F : Type} : RegionOperation F → Option (DeclaredCopy F)
  | .constrainEqual left right => some (.cell left, .cell right)
  | .constrainConstant cell value => some (.cell cell, .constant value)
  | .constrainInstance cell col row => some (.cell cell, .instance col row)
  | _ => none

/-- Declared copies in one region, in operation order. -/
def regionDeclaredCopies {F : Type} (ops : RegionOperations F) : List (DeclaredCopy F) :=
  ops.filterMap regionOperationDeclaredCopy?

/-- Declared copies in a complete layouter stream.  Region-local copies retain the `Cell` region
indices they were synthesized with; layouter-level instance copies are inserted in stream order. -/
def operationDeclaredCopies {F : Type} (ops : Operations F) : List (DeclaredCopy F) :=
  ops.flatMap fun
    | .region _ body => regionDeclaredCopies body
    | .constrainInstance cell col row => [(.cell cell, .instance col row)]
    | .loadTable _ _ => []

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- The copy-family projection of a region is exactly satisfaction of its extracted copies. -/
theorem region_copy_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionConstraints .copy place self env ops ↔
      (regionDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops with
  | nil => simp [RegionConstraints, regionDeclaredCopies]
  | cons op rest ih =>
      cases op <;>
        simp_all [RegionConstraints, RegionConstraint, RegionOperation.Constraints,
          regionDeclaredCopies, regionOperationDeclaredCopy?,
          DeclaredCopy.Satisfied, CopyEndpoint.eval]

/-- The complete copy-family projection is exactly satisfaction of the copies extracted from the
whole operation stream. -/
theorem copy_constraints_iff_declaredCopies
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Constraints .copy place env ops i ↔
      (operationDeclaredCopies ops).Forall (DeclaredCopy.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [Constraints, operationDeclaredCopies]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Constraints, ih, region_copy_constraints_iff]
          simp [operationDeclaredCopies, List.forall_append]
      | constrainInstance cell col row =>
          rw [Constraints, ih]
          simp [operationDeclaredCopies, DeclaredCopy.Satisfied, CopyEndpoint.eval]
      | loadTable table values =>
          rw [Constraints, ih]
          simp [operationDeclaredCopies]

end CircuitConstraintFamily

end Halo2

/-!
## Declared copies resolve into the keygen copy list

The compiler's ordinary copy stream is the resolved source-copy list; its constant
stream pairs source requests with positional allocations. These exact list
characterizations transfer source registration and row bounds to the compiled copy
list, and connect each declared copy to its compiled entry.
-/

namespace Halo2

open Layout

/-- Resolve a non-constant declared copy to the keygen copy tuple: region cells through
the placement, instance endpoints at their absolute rows. Constant endpoints resolve to
`none` — their cells are the planner's positional constants allocation. -/
def resolveDeclared (permCols : List ColRef) (starts : List ℕ) :
    CopyEndpoint F × CopyEndpoint F → Option (ℕ × ℕ × ℕ × ℕ)
  | (.cell l, .cell r) =>
      some ((resolveCell permCols starts l).1, (resolveCell permCols starts l).2,
        (resolveCell permCols starts r).1, (resolveCell permCols starts r).2)
  | (.cell c, .instance col row) =>
      some ((resolveCell permCols starts c).1, (resolveCell permCols starts c).2,
        permIndex permCols col.toAny, row)
  | _ => none

/-- A column present in the permutation layout resolves to an in-range index. -/
theorem permIndex_lt_length_of_mem
    (permCols : List ColRef) {column : AnyColumn}
    (hcolumn : column ∈ permCols.map ColRef.toAny) :
    permIndex permCols column < permCols.length := by
  have hexists : ∃ candidate ∈ permCols.map ColRef.toAny,
      decide (candidate = column) = true :=
    ⟨column, hcolumn, by simp⟩
  rw [permIndex, List.findIdx?_eq_some_of_exists hexists,
    Option.getD_some]
  simpa only [List.length_map] using
    List.findIdx_lt_length_of_exists hexists

/-- Looking up the index of a registered permutation column recovers that column. -/
theorem permCols_getD_permIndex
    (permCols : List ColRef) (column : AnyColumn) (fallback : ColRef)
    (hcolumn : column ∈ permCols.map ColRef.toAny) :
    ColRef.toAny (permCols.getD (permIndex permCols column) fallback) = column := by
  let columns := permCols.map ColRef.toAny
  have hexists : ∃ candidate ∈ columns,
      decide (candidate = column) = true :=
    ⟨column, hcolumn, by simp⟩
  have hindex : columns.findIdx (fun candidate => decide (candidate = column)) <
      columns.length :=
    List.findIdx_lt_length_of_exists hexists
  have hfound :=
    List.findIdx_getElem
      (p := fun candidate => decide (candidate = column))
      (xs := columns) (w := hindex)
  have hvalue :
      columns[columns.findIdx (fun candidate => decide (candidate = column))] =
        column := by
    exact of_decide_eq_true hfound
  have hpermIndex :
      permIndex permCols column =
        columns.findIdx (fun candidate => decide (candidate = column)) := by
    rw [permIndex, List.findIdx?_eq_some_of_exists hexists,
      Option.getD_some]
  have hpermIndexLt : permIndex permCols column < permCols.length := by
    rw [hpermIndex]
    simpa only [columns, List.length_map] using hindex
  have hvalue' :
      ColRef.toAny
          permCols[columns.findIdx (fun candidate => decide (candidate = column))] =
        column := by
    simpa only [columns, List.getElem_map] using hvalue
  rw [List.getD_eq_getElem _ _ hpermIndexLt]
  simpa only [hpermIndex] using hvalue'

namespace CopyEndpoint

/-- The column requirement carried by a declared copy endpoint. Constants acquire
their concrete column later from the floor planner's allocation. -/
def PermutationColumnRegistered
    (cs : ConstraintSystem F) : CopyEndpoint F → Prop
  | .cell c => c.column ∈ cs.permutationColumns
  | .instance column _ => column.toAny ∈ cs.permutationColumns
  | .constant _ => True

/-- The row requirement carried by a declared copy endpoint. Constants acquire
their concrete row later from the floor planner's allocation. -/
def WithinRows
    (starts : List ℕ) (bound : ℕ) : CopyEndpoint F → Prop
  | .cell c =>
      starts.getD c.regionIndex 0 + c.rowOffset < bound
  | .instance _ row => row < bound
  | .constant _ => True

end CopyEndpoint

/-- Both endpoints of a coherent region copy use registered permutation columns. -/
theorem regionDeclaredCopies_permutationColumns
    (cs : ConstraintSystem F) (body : RegionOperations F)
    (hcoherent : body.Forall (RegionOperation.KeygenCoherent cs))
    (copy : DeclaredCopy F) (hcopy : copy ∈ regionDeclaredCopies body) :
    copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs := by
  rw [regionDeclaredCopies, List.mem_filterMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  have hRegistered := List.forall_iff_forall_mem.mp hcoherent op hOp
  cases op <;> simp only [regionOperationDeclaredCopy?, reduceCtorEq] at hCopy
  all_goals obtain rfl := Option.some.inj hCopy
  all_goals simpa [CopyEndpoint.PermutationColumnRegistered,
    RegionOperation.KeygenCoherent] using hRegistered

/-- Both endpoints of every coherent layouter copy use registered permutation
columns. -/
theorem operationDeclaredCopies_permutationColumns
    (cs : ConstraintSystem F) (operations : Operations F)
    (hcoherent : OperationsKeygenCoherent cs operations)
    (copy : DeclaredCopy F) (hcopy : copy ∈ operationDeclaredCopies operations) :
    copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs := by
  rw [operationDeclaredCopies, List.mem_flatMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  have hRegistered := List.forall_iff_forall_mem.mp hcoherent op hOp
  cases op with
  | region name body => exact regionDeclaredCopies_permutationColumns cs body hRegistered copy hCopy
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      exact hRegistered
  | loadTable table values => simp at hCopy

/-- Both endpoints of a region copy lie inside the complete operation footprint. -/
theorem regionDeclaredCopies_rows
    (root : Operations F) (name : String) (body : RegionOperations F)
    (hregion : Operation.region name body ∈ root)
    (copy : DeclaredCopy F) (hcopy : copy ∈ regionDeclaredCopies body) :
    copy.1.WithinRows (FloorPlanner.V1.starts root) (usedRows root) ∧
      copy.2.WithinRows (FloorPlanner.V1.starts root) (usedRows root) := by
  rw [regionDeclaredCopies, List.mem_filterMap] at hcopy
  obtain ⟨operation, hoperation, hcopy⟩ := hcopy
  cases operation with
  | constrainEqual left right =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact cells_row_lt_usedRows_of_constrainEqual_mem
        root name body hregion left right hoperation
  | constrainConstant cell value =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact ⟨cell_row_lt_usedRows_of_constrainConstant_mem
        root name body hregion cell value hoperation, trivial⟩
  | constrainInstance cell column row =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      exact rows_lt_usedRows_of_region_constrainInstance_mem
        root name body hregion cell column row hoperation
  | assignAdvice column row witness => simp [regionOperationDeclaredCopy?] at hcopy
  | assignFixed column row value => simp [regionOperationDeclaredCopy?] at hcopy
  | enableGate gate row => simp [regionOperationDeclaredCopy?] at hcopy
  | enableLookup argument selectors row => simp [regionOperationDeclaredCopy?] at hcopy

/-- Both endpoints of every layouter copy lie inside the complete operation
footprint. -/
theorem operationDeclaredCopies_rows
    (operations : Operations F) (copy : DeclaredCopy F)
    (hcopy : copy ∈ operationDeclaredCopies operations) :
    copy.1.WithinRows (FloorPlanner.V1.starts operations) (usedRows operations) ∧
      copy.2.WithinRows (FloorPlanner.V1.starts operations) (usedRows operations) := by
  rw [operationDeclaredCopies, List.mem_flatMap] at hcopy
  obtain ⟨op, hOp, hCopy⟩ := hcopy
  cases op with
  | region name body => exact regionDeclaredCopies_rows operations name body hOp copy hCopy
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      exact rows_lt_usedRows_of_constrainInstance_mem operations cell column row hOp
  | loadTable table values => simp at hCopy

/-- Copy compilation resolves precisely the non-constant source copies. -/
theorem regionCopiesSplit_fst_eq (columns : List ColRef) (starts : List ℕ)
    (body : RegionOperations F) (constants : List (ℕ × ℕ × ℕ)) :
    (regionCopiesSplit columns starts body constants).1 =
      (regionDeclaredCopies body).filterMap (resolveDeclared columns starts) := by
  simp only [regionCopiesSplit, regionDeclaredCopies, List.filterMap_filterMap]
  congr 1
  funext op
  cases op <;> rfl

/-- The complete equality stream is a pointwise resolution of the source copies;
the positional constants walk does not affect it. -/
theorem V1_go_fst_eq (columns : List ColRef) (starts : List ℕ)
    (ops : Operations F) (constants : List (ℕ × ℕ × ℕ)) :
    (V1.go columns starts ops constants).1.1 =
      (operationDeclaredCopies ops).filterMap (resolveDeclared columns starts) := by
  induction ops generalizing constants with
  | nil => simp [V1.go, operationDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp [V1.go, operationDeclaredCopies, List.filterMap_append,
        regionCopiesSplit_fst_eq, resolveDeclared, ih]

/-- Resolving registered endpoints produces in-range permutation columns. -/
theorem resolveDeclared_columns_lt (cs : ConstraintSystem F) (starts : List ℕ)
    (copy : DeclaredCopy F) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared (permColsOf cs) starts copy = some tuple)
    (hColumns : copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs) :
    tuple.1 < (permColsOf cs).length ∧ tuple.2.2.1 < (permColsOf cs).length := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  all_goals constructor <;> apply permIndex_lt_length_of_mem <;> rw [permColsOf_map_toAny]
  all_goals first | exact hColumns.1 | exact hColumns.2

/-- Address resolution preserves the row bounds of source endpoints. -/
theorem resolveDeclared_rows_lt (columns : List ColRef) (starts : List ℕ)
    (bound : ℕ) (copy : DeclaredCopy F) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared columns starts copy = some tuple)
    (hRows : copy.1.WithinRows starts bound ∧ copy.2.WithinRows starts bound) :
    tuple.2.1 < bound ∧ tuple.2.2.2 < bound := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  all_goals simpa only [CopyEndpoint.WithinRows, resolveCell, place] using hRows

/-- **Every resolvable declared copy is in the V1 copy list**: region-local copies land
in their region's extracted stream, layouter-level instance copies inline, and the
whole equality/instance stream prefixes the copy list. -/
theorem mem_V1_copyList_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations F) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint F × CopyEndpoint F) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ operationDeclaredCopies ops) :
    tuple ∈ V1.copyList permCols starts ops consts := by
  rw [V1.copyList, List.mem_append]
  exact Or.inl (by
    rw [V1_go_fst_eq, List.mem_filterMap]
    exact ⟨copy, hmem, hres⟩)

/-- Decode raw copy tuples into typed cells under a bounds certificate. -/
def decodeCopies (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    List (FlatCell numCols n × FlatCell numCols n) :=
  raw.attach.map fun t =>
    ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
      (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))

/-- Decoding then re-encoding is the identity: the bounds certificate is the whole
content of the `hcopies` hypothesis. -/
theorem decodeCopies_map (numCols n : ℕ) (raw : List (ℕ × ℕ × ℕ × ℕ))
    (h : ∀ t ∈ raw, t.1 < numCols ∧ t.2.1 < n ∧ t.2.2.1 < numCols ∧ t.2.2.2 < n) :
    (decodeCopies numCols n raw h).map
        (fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) = raw := by
  rw [decodeCopies, List.map_map]
  have : (fun (t : { x // x ∈ raw }) => t.1) =
      ((fun p : (FlatCell numCols n × FlatCell numCols n) =>
          (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) ∘
        fun t : { x // x ∈ raw } =>
          ((⟨t.1.1, (h t.1 t.2).1⟩, ⟨t.1.2.1, (h t.1 t.2).2.1⟩),
            (⟨t.1.2.2.1, (h t.1 t.2).2.2.1⟩, ⟨t.1.2.2.2, (h t.1 t.2).2.2.2⟩))) := by
    funext t
    rfl
  rw [← this]
  exact List.attach_map_subtype_val raw

/-- The constant-declaration sites of a region body, in body order. -/
def constSites : RegionOperations F → List (Cell × F)
  | [] => []
  | .constrainConstant cell value :: rest => (cell, value) :: constSites rest
  | _ :: rest => constSites rest

/-- The constants half of a region's copy extraction, in closed zipped form: each
constant site pairs with the next allocation-map entry — the constants cell on the
left, the site's resolved cell on the right — and the tail of the map is returned. -/
theorem regionCopiesSplit_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations F) (consts : List (ℕ × ℕ × ℕ)) :
    (regionCopiesSplit permCols starts body consts).2.1 =
      ((constSites body).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (regionCopiesSplit permCols starts body consts).2.2 =
        consts.drop (constSites body).length := by
  induction body generalizing consts with
  | nil => simp [regionCopiesSplit, regionCopiesSplit.go, constSites]
  | cons op rest ih =>
      cases op with
      | constrainConstant cell value =>
          cases consts with
          | nil =>
              simpa [regionCopiesSplit, regionCopiesSplit.go, constSites] using ih []
          | cons entry cs =>
              simpa [regionCopiesSplit, regionCopiesSplit.go, constSites] using ih cs
      | constrainEqual | constrainInstance | assignAdvice | assignFixed | enableGate | enableLookup =>
          exact ih consts

/-- The constant-declaration sites of a whole operation stream: region sites in region
order (V1 defers them all to the end of synthesis, in this order). -/
def operationConstSites : Operations F → List (Cell × F)
  | [] => []
  | .region _ body :: rest => constSites body ++ operationConstSites rest
  | .constrainInstance _ _ _ :: rest => operationConstSites rest
  | .loadTable _ _ :: rest => operationConstSites rest

/-- A region's constant sites are exactly its declared constant copies. -/
theorem mem_constSites_iff_declaredCopy (body : RegionOperations F) (cell : Cell) (value : F) :
    (cell, value) ∈ constSites body ↔
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈ regionDeclaredCopies body := by
  induction body with
  | nil => simp [constSites, regionDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp_all [constSites, regionDeclaredCopies, regionOperationDeclaredCopy?]

/-- The positional constant-site stream retains precisely the source constant copies. -/
theorem mem_operationConstSites_iff_declaredCopy (ops : Operations F) (cell : Cell) (value : F) :
    (cell, value) ∈ operationConstSites ops ↔
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈ operationDeclaredCopies ops := by
  induction ops with
  | nil => simp [operationConstSites, operationDeclaredCopies]
  | cons op rest ih =>
      cases op <;> simp_all [operationConstSites, operationDeclaredCopies,
        mem_constSites_iff_declaredCopy]

/-- Every constant site in a keygen-lawful operation stream lies on an
equality-enabled column. -/
theorem operationConstSite_column_mem_permutationColumns
    (cs : ConstraintSystem F) (operations : Operations F)
    (hregistered : OperationsKeygenCoherent cs operations)
    {cell : Cell} {value : F}
    (hsite : (cell, value) ∈ operationConstSites operations) :
    cell.column ∈ cs.permutationColumns := by
  exact (operationDeclaredCopies_permutationColumns cs operations hregistered _
    ((mem_operationConstSites_iff_declaredCopy operations cell value).mp hsite)).1

/-- A whole-stream constant site lies below the compiler-derived operation
footprint. -/
theorem constantSite_row_lt_usedRows
    (operations : Operations F) (cell : Cell) (value : F)
    (hsite : (cell, value) ∈ operationConstSites operations) :
    (FloorPlanner.V1.starts operations).getD cell.regionIndex 0 +
        cell.rowOffset <
      usedRows operations := by
  exact (operationDeclaredCopies_rows operations _
    ((mem_operationConstSites_iff_declaredCopy operations cell value).mp hsite)).1

/-- The values retained by `constSites` are exactly the region operations'
`constrainConstant` values, in the same order. -/
theorem constSites_map_snd (body : RegionOperations F) :
    (constSites body).map Prod.snd =
      FloorPlanner.V1.regionConstantValues body := by
  induction body with
  | nil => rfl
  | cons operation rest ih =>
      cases operation <;>
        simp [constSites, FloorPlanner.V1.regionConstantValues, ih]

/-- Walking indexed regions and walking the operation stream directly collect the
same constant values in the same order. Region indices do not affect this stream. -/
theorem indexedRegions_constantValues
    (ops : Operations F) (nextRegion : ℕ) :
    ((indexedRegions ops nextRegion).1.flatMap fun (_, body) =>
      FloorPlanner.V1.regionConstantValues body) =
      (operationConstSites ops).map Prod.snd := by
  induction ops generalizing nextRegion with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, operationConstSites, List.map_append,
            List.flatMap_cons]
          rw [ih, constSites_map_snd]
      | constrainInstance cell column row =>
          simpa only [indexedRegions, operationConstSites] using ih nextRegion
      | loadTable table values =>
          simpa only [indexedRegions, operationConstSites] using ih nextRegion

/-- V1's planner value stream is the value projection of the semantic bridge's
constant-site stream. This is an algorithmic identity, independent of any circuit. -/
theorem operationConstSites_map_snd (ops : Operations F) :
    (operationConstSites ops).map Prod.snd =
      FloorPlanner.V1.constantValues ops := by
  unfold FloorPlanner.V1.constantValues
  symm
  exact indexedRegions_constantValues ops 0

theorem operationConstSites_length (ops : Operations F) :
    (operationConstSites ops).length =
      (FloorPlanner.V1.constantValues ops).length := by
  rw [← operationConstSites_map_snd, List.length_map]

/-- Positional V1 allocation preserves each constant site's value. The only premise
is allocation completeness; no concrete circuit computation is involved. -/
theorem constantAllocation_value [FiniteField F]
    (ops : Operations F) (constantColumns : List ℕ)
    {site : Cell × F} {entry : ℕ × ℕ × ℕ}
    (hfit :
      (operationConstSites ops).length ≤
        (FloorPlanner.V1.constantAssignments ops constantColumns).length)
    (hallocation :
      (site, entry) ∈
        (operationConstSites ops).zip
          ((FloorPlanner.V1.constantAssignments ops constantColumns).map
            fun (value, column, row) => (FiniteField.val value, column, row))) :
    entry.1 = FiniteField.val site.2 := by
  have hFull := hfit
  rw [operationConstSites_length] at hFull
  have hValues := congrArg (List.map FiniteField.val)
    (FloorPlanner.V1.constantAssignments_map_fst ops constantColumns hFull)
  have hPairs : List.Forall₂ (fun site entry => FiniteField.val site.2 = entry.1)
      (operationConstSites ops)
      ((FloorPlanner.V1.constantAssignments ops constantColumns).map
        fun (value, column, row) => (FiniteField.val value, column, row)) := by
    rw [← List.forall₂_map_left_iff
        (R := fun value (entry : ℕ × ℕ × ℕ) => value = entry.1)
        (f := fun site : Cell × F => FiniteField.val site.2),
      ← List.forall₂_map_right_iff (R := Eq) (f := Prod.fst), List.forall₂_eq_eq_eq]
    simpa only [List.map_map, Function.comp_def, ← operationConstSites_map_snd] using
      hValues.symm
  exact (List.forall₂_zip hPairs hallocation).symm

/-- The V1 constants stream in closed zipped form: every constant site across the
stream pairs with its allocation-map entry, in region-then-body order. -/
theorem V1_go_snd_eq (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations F) (consts : List (ℕ × ℕ × ℕ)) :
    (V1.go permCols starts ops consts).1.2 =
      ((operationConstSites ops).zip consts).map (fun se =>
        (permIndex permCols (ColRef.toAny (.fixed se.2.2.1)), se.2.2.2,
          (resolveCell permCols starts se.1.1).1,
          (resolveCell permCols starts se.1.1).2)) ∧
      (V1.go permCols starts ops consts).2 =
        consts.drop (operationConstSites ops).length := by
  induction ops generalizing consts with
  | nil => simp [V1.go, operationConstSites]
  | cons op rest ih =>
      cases op with
      | region name body =>
          obtain ⟨hCopies, hRemaining⟩ := regionCopiesSplit_snd_eq permCols starts body consts
          obtain ⟨hTail, hFinal⟩ := ih (consts.drop (constSites body).length)
          simp only [V1.go, hRemaining, hCopies, hTail, hFinal, operationConstSites,
            List.zip_append_drop, List.map_append, List.length_append, List.drop_drop, and_self]
      | constrainInstance cell col row =>
          simpa only [V1.go, operationConstSites] using ih consts
      | loadTable table values =>
          simpa only [V1.go, operationConstSites] using ih consts

/-- Every tuple in the V1 copy list lies below the compiler-derived operation
footprint. Constant allocations need only be present positionally and carry their
generic planner row bound; no concrete circuit computation is involved. -/
theorem V1_copyList_rows_lt_usedRows
    (operations : Operations F) (permCols : List ColRef)
    (constants : List (ℕ × ℕ × ℕ))
    (hconstantRows :
      ∀ entry ∈ constants, entry.2.2 < usedRows operations)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈
      V1.copyList permCols (FloorPlanner.V1.starts operations)
        operations constants) :
    tuple.2.1 < usedRows operations ∧
      tuple.2.2.2 < usedRows operations := by
  rw [V1.copyList, List.mem_append] at htuple
  rcases htuple with hequality | hconstant
  · rw [V1_go_fst_eq, List.mem_filterMap] at hequality
    obtain ⟨copy, hCopy, hResolve⟩ := hequality
    exact resolveDeclared_rows_lt _ _ _ copy tuple hResolve
      (operationDeclaredCopies_rows operations copy hCopy)
  · have hconstants :=
      (V1_go_snd_eq permCols (FloorPlanner.V1.starts operations)
        operations constants).1
    rw [hconstants, List.mem_map] at hconstant
    obtain ⟨⟨⟨cell, value⟩, entry⟩, hallocation, htuple⟩ := hconstant
    have hsite : (cell, value) ∈ operationConstSites operations :=
      (List.of_mem_zip hallocation).1
    have hentry : entry ∈ constants :=
      (List.of_mem_zip hallocation).2
    obtain rfl := htuple
    exact ⟨hconstantRows entry hentry,
      constantSite_row_lt_usedRows operations cell value hsite⟩

/-- Every tuple in V1's copy list uses in-range permutation columns whenever synthesis
is keygen-lawful and the planner's constants allocation uses configured constant
columns. -/
theorem V1_copyList_columns_lt
    (cs : ConstraintSystem F) (operations : Operations F)
    (hregistered : OperationsKeygenCoherent cs operations)
    (starts : List ℕ) (constants : List (ℕ × ℕ × ℕ))
    (hconstantColumns : ∀ entry ∈ constants,
      (AnyColumn.mk .fixed entry.2.1) ∈ cs.permutationColumns)
    (tuple : ℕ × ℕ × ℕ × ℕ)
    (htuple : tuple ∈ V1.copyList
      (Layout.permColsOf cs) starts operations constants) :
    tuple.1 < (Layout.permColsOf cs).length ∧
      tuple.2.2.1 < (Layout.permColsOf cs).length := by
  rw [V1.copyList, List.mem_append] at htuple
  rcases htuple with hequality | hconstant
  · rw [V1_go_fst_eq, List.mem_filterMap] at hequality
    obtain ⟨copy, hCopy, hResolve⟩ := hequality
    exact resolveDeclared_columns_lt cs starts copy tuple hResolve
      (operationDeclaredCopies_permutationColumns cs operations hregistered copy hCopy)
  · have hconstants :=
      (V1_go_snd_eq (Layout.permColsOf cs) starts
        operations constants).1
    rw [hconstants, List.mem_map] at hconstant
    obtain ⟨⟨⟨cell, value⟩, entry⟩, hallocation, htuple⟩ := hconstant
    have hsite : (cell, value) ∈ operationConstSites operations :=
      (List.of_mem_zip hallocation).1
    have hentry : entry ∈ constants :=
      (List.of_mem_zip hallocation).2
    obtain rfl := htuple
    constructor <;>
      apply permIndex_lt_length_of_mem <;>
      rw [Layout.permColsOf_map_toAny]
    · exact hconstantColumns entry hentry
    · exact operationConstSite_column_mem_permutationColumns
        cs operations hregistered hsite

/-- Every declared copy has a `Cell` left endpoint, and its right endpoint is a cell,
an instance read, or a constant — so every declared copy either resolves or is a
constant declaration. -/
theorem exists_resolveDeclared_or_constant_of_mem_operationDeclaredCopies
    (ops : Operations F) (permCols : List ColRef)
    (starts : List ℕ) :
    ∀ copy ∈ operationDeclaredCopies ops,
      (∃ tuple, resolveDeclared permCols starts copy = some tuple) ∨
        ∃ c v, copy = (.cell c, .constant v) := by
  intro copy hCopy
  rw [operationDeclaredCopies, List.mem_flatMap] at hCopy
  obtain ⟨op, _, hCopy⟩ := hCopy
  cases op with
  | region name body =>
      simp only [regionDeclaredCopies, List.mem_filterMap] at hCopy
      obtain ⟨op, _, hCopy⟩ := hCopy
      cases op <;> simp only [regionOperationDeclaredCopy?, reduceCtorEq] at hCopy
      all_goals obtain rfl := Option.some.inj hCopy
      all_goals simp [resolveDeclared]
  | constrainInstance cell column row =>
      obtain rfl := List.mem_singleton.mp hCopy
      simp [resolveDeclared]
  | loadTable table values => simp at hCopy

end Halo2

/-! ## Soundness of the compiler copy list

Allocated constants and resolved cell equalities recover the source copy constraints.
-/

namespace Halo2

open Layout

/-- Read a raw keygen coordinate through its permutation-column layout. -/
def rawCopyValue (columns : List ColRef) (env : Environment F) (cell : ℕ × ℕ) : F :=
  env.get (ColRef.toAny (columns.getD cell.1 (.advice 0))) (cell.2 : ℤ)

theorem rawCopyValue_permIndex
    (columns : List ColRef) (env : Environment F) (column : AnyColumn) (row : ℕ)
    (hcolumn : column ∈ columns.map ColRef.toAny) :
    rawCopyValue columns env (permIndex columns column, row) = env.get column (row : ℤ) := by
  simp only [rawCopyValue, permCols_getD_permIndex columns column (.advice 0) hcolumn]

/-- Resolving a registered cell preserves its environment read. -/
theorem rawCopyValue_resolveCell
    (cs : ConstraintSystem F) (starts : List ℕ) (env : Environment F) (cell : Cell)
    (hColumn : cell.column ∈ cs.permutationColumns) :
    rawCopyValue (permColsOf cs) env (resolveCell (permColsOf cs) starts cell) =
      cell.eval (fun region => starts.getD region 0) env := by
  simpa only [resolveCell, place, Cell.eval] using
    rawCopyValue_permIndex (permColsOf cs) env cell.column
      (starts.getD cell.regionIndex 0 + cell.rowOffset)
      (by simpa only [permColsOf_map_toAny] using hColumn)

/-- Resolution changes only coordinates, not the equality denoted by a copy. -/
theorem resolveDeclared_satisfied_iff
    (cs : ConstraintSystem F) (starts : List ℕ) (env : Environment F)
    (copy : DeclaredCopy F) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hResolve : resolveDeclared (permColsOf cs) starts copy = some tuple)
    (hColumns : copy.1.PermutationColumnRegistered cs ∧
      copy.2.PermutationColumnRegistered cs) :
    DeclaredCopy.Satisfied (fun region => starts.getD region 0) env copy ↔
      rawCopyValue (permColsOf cs) env (tuple.1, tuple.2.1) =
        rawCopyValue (permColsOf cs) env (tuple.2.2.1, tuple.2.2.2) := by
  rcases copy with ⟨left, right⟩
  cases left <;> cases right <;> simp only [resolveDeclared, reduceCtorEq] at hResolve
  all_goals obtain rfl := Option.some.inj hResolve
  · simp only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env _ hColumns.1,
      rawCopyValue_resolveCell cs starts env _ hColumns.2]
  · rename_i cell column row
    simp only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env _ hColumns.1,
      rawCopyValue_permIndex (permColsOf cs) env column.toAny row
        (by simpa only [permColsOf_map_toAny, CopyEndpoint.PermutationColumnRegistered]
          using hColumns.2)]

/-- A declared constant copy occurs in the positional allocation part of the
compiler's copy list, with the requested literal retained by its allocated cell. -/
theorem constantPair_mem_copyList [FiniteField F]
    (columns : List ColRef) (starts : List ℕ) (ops : Operations F)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites ops).length ≤ constants.length)
    (hvalues : ∀ site entry, (site, entry) ∈ (operationConstSites ops).zip constants →
      entry.1 = FiniteField.val site.2)
    {cell : Cell} {value : F}
    (hcopy : (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
      operationDeclaredCopies ops) :
    ∃ entry ∈ constants, entry.1 = FiniteField.val value ∧
      (permIndex columns (ColRef.toAny (.fixed entry.2.1)), entry.2.2,
        (resolveCell columns starts cell).1, (resolveCell columns starts cell).2) ∈
        V1.copyList columns starts ops constants := by
  have hsite := (mem_operationConstSites_iff_declaredCopy ops cell value).mpr hcopy
  rw [← List.map_fst_zip hfit, List.mem_map] at hsite
  obtain ⟨⟨_, entry⟩, hallocation, rfl⟩ := hsite
  refine ⟨entry, (List.of_mem_zip hallocation).2, hvalues _ _ hallocation, ?_⟩
  have hgo := (V1_go_snd_eq columns starts ops constants).1
  rw [V1.copyList, List.mem_append]
  right
  rw [hgo]
  exact List.mem_map.mpr ⟨((cell, value), entry), hallocation, rfl⟩

/-- Raw pair equality and reads of allocated constants suffice for all declared
copies. Registration is the only address requirement; this also covers an empty
permutation-column layout. -/
theorem copy_constraints_of_rawPairValues [FiniteField F]
    (cs : ConstraintSystem F) (ops : Operations F)
    (hregistered : OperationsKeygenCoherent cs ops)
    (starts : List ℕ) (env : Environment F)
    (constants : List (ℕ × ℕ × ℕ))
    (hfit : (operationConstSites ops).length ≤ constants.length)
    (hvalues : ∀ site entry, (site, entry) ∈ (operationConstSites ops).zip constants →
      entry.1 = FiniteField.val site.2)
    (hcolumns : ∀ entry ∈ constants,
      AnyColumn.mk .fixed entry.2.1 ∈ cs.permutationColumns)
    (pairValues : ∀ pair ∈ V1.copyList (Layout.permColsOf cs) starts ops constants,
      rawCopyValue (Layout.permColsOf cs) env (pair.1, pair.2.1) =
        rawCopyValue (Layout.permColsOf cs) env (pair.2.2.1, pair.2.2.2))
    (constantValues : ∀ entry ∈ constants,
      env.get (AnyColumn.mk .fixed entry.2.1) (entry.2.2 : ℤ) = FiniteField.fromNat entry.1)
    (i : RegionIndex) :
    CircuitConstraintFamily.Constraints .copy
      (fun region => starts.getD region 0) env ops i := by
  apply (CircuitConstraintFamily.copy_constraints_iff_declaredCopies _ env ops i).mpr
  apply List.forall_iff_forall_mem.mpr
  intro copy hcopy
  have hregisteredCopy := operationDeclaredCopies_permutationColumns cs ops hregistered copy hcopy
  rcases exists_resolveDeclared_or_constant_of_mem_operationDeclaredCopies
    ops (permColsOf cs) starts copy hcopy with
    ⟨tuple, hResolve⟩ | ⟨cell, value, rfl⟩
  · exact (resolveDeclared_satisfied_iff cs starts env copy tuple hResolve hregisteredCopy).mpr
      (pairValues tuple (mem_V1_copyList_of_declared (permColsOf cs) starts ops constants
        copy tuple hResolve hcopy))
  · obtain ⟨entry, hEntry, hValue, hMem⟩ :=
      constantPair_mem_copyList (permColsOf cs) starts ops constants hfit hvalues hcopy
    have hColumn : AnyColumn.mk .fixed entry.2.1 ∈ (permColsOf cs).map ColRef.toAny := by
      rw [permColsOf_map_toAny]
      exact hcolumns entry hEntry
    have hRead := rawCopyValue_permIndex (permColsOf cs) env
      (AnyColumn.mk .fixed entry.2.1) entry.2.2 hColumn
    have hEqual := (pairValues _ hMem).symm.trans (hRead.trans (constantValues entry hEntry))
    simpa only [DeclaredCopy.Satisfied, CopyEndpoint.eval,
      rawCopyValue_resolveCell cs starts env cell hregisteredCopy.1, hValue,
      FiniteField.fromNat_val] using hEqual

end Halo2

/-! ## Soundness of compiled copy semantics

Copy compilation resolves region-local cells to absolute coordinates and allocates
fixed cells for constants. Its semantic output is equality on these resolved pairs.
The permutation argument may enforce these equalities without exposing source operations.
-/

namespace Halo2.TopLevelCircuit

variable [FiniteField F]

open Layout

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Resolved copy pairs, including the fixed cells allocated for constant copies. -/
def copyPairs : List (ℕ × ℕ × ℕ × ℕ) :=
  Layout.V1.copyList (Layout.permColsOf top.constraintSystem) top.regionStarts
    top.operations (Layout.constantCopyEntries top.constraintSystem top.operations)

/-- Both endpoints of every compiled copy have equal values in the assignment. -/
def CopiesCompiled (assignment : ProofAssignment F) : Prop :=
  ∀ pair ∈ top.copyPairs,
    rawCopyValue (Layout.permColsOf top.constraintSystem) (top.environment assignment)
        (pair.1, pair.2.1) =
      rawCopyValue (Layout.permColsOf top.constraintSystem) (top.environment assignment)
        (pair.2.2.1, pair.2.2.2)

/-- Registration, placement, and constant allocation turn resolved copy equality
into all source copy constraints. Fixed values come from the circuit, not a hypothesis. -/
theorem copy_constraints_of_compiled (assignment : ProofAssignment F)
    (hcopies : top.CopiesCompiled assignment) :
    CircuitConstraintFamily.Constraints .copy top.placement
      (top.environment assignment) top.operations 0 := by
  have hfit := top.constantValues_length_le_constantAssignments_length
  have hsiteFit : (operationConstSites top.operations).length ≤
      (Layout.constantCopyEntries top.constraintSystem top.operations).length := by
    simpa only [Layout.constantCopyEntries, List.length_map, operationConstSites_length] using hfit
  have hplace : (fun region => top.regionStarts.getD region 0) = top.placement := by
    funext region
    exact (top.placement_apply region).symm
  rw [← hplace]
  apply copy_constraints_of_rawPairValues top.constraintSystem top.operations
    top.keygenCoherent top.regionStarts (top.environment assignment)
    (Layout.constantCopyEntries top.constraintSystem top.operations) hsiteFit
    ?_ ?_ hcopies ?_ 0
  · intro site entry h
    apply constantAllocation_value top.operations
      (top.constraintSystem.constants.map (·.index))
      (by simpa only [operationConstSites_length] using hfit)
    simpa only [Layout.constantCopyEntries] using h
  · intro entry hentry
    rw [Layout.constantCopyEntries, List.mem_map] at hentry
    obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
    exact top.constantAssignmentColumn_mem_permutationColumns hentry
  · intro entry hentry
    rw [Layout.constantCopyEntries, List.mem_map] at hentry
    obtain ⟨⟨value, column, row⟩, hentry, rfl⟩ := hentry
    have hraw : (column, row, value) ∈ Layout.rawAssignments
        (top.usableRowsAt top.domainExponent) top.selectorMap
        top.constraintSystem top.operations := by
      simp only [Layout.rawAssignments, List.mem_append]
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact List.mem_map.mpr ⟨(value, column, row), hentry, rfl⟩
    simpa only [FiniteField.fromNat_val] using top.environment_fixed_of_mem_raw assignment hraw

end Halo2.TopLevelCircuit
