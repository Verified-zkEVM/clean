import Clean.Halo2.Keygen.PinnedCs
import Clean.Halo2.Keygen.Semantics
import Clean.Halo2.Keygen.Layout

/-!
# Closed top-level formal circuits

`FormalCircuit` is the compositional interface: a child may require environment facts
from its parent.  A deployed circuit needs one additional boundary.  Its configuration,
operation stream, placement, and domain must describe a successful synthesis, and its
own setup operations must discharge every environment fact required by its children.

`TopLevelCircuit` records that boundary without adding those facts to the circuit's
public input or verifier assumptions.
-/

namespace Halo2

variable {F : Type}

private theorem accumulator_le_foldl_max (values : List ℕ) (accumulator : ℕ) :
    accumulator ≤ values.foldl max accumulator := by
  induction values generalizing accumulator with
  | nil => exact Nat.le_refl accumulator
  | cons value values inductionHypothesis =>
      exact le_trans (Nat.le_max_left accumulator value)
        (inductionHypothesis (max accumulator value))

private theorem member_le_foldl_max
    (values : List ℕ) (value accumulator : ℕ)
    (hmember : value ∈ values) :
    value ≤ values.foldl max accumulator := by
  induction values generalizing accumulator with
  | nil => simp only [List.not_mem_nil] at hmember
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · subst head
        exact le_trans (Nat.le_max_right accumulator value)
          (accumulator_le_foldl_max tail (max accumulator value))
      · exact inductionHypothesis (max accumulator head) htail

/-- Every loaded table contributes its explicit block length to the operation
footprint used by top-level domain selection. -/
theorem Operations.loadTable_length_le_usedRows
    (operations : Operations F) (table : TableColumn) (values : List F)
    (hload : Operation.loadTable table values ∈ operations) :
    values.length ≤ Halo2.usedRows operations := by
  let tableExtents := operations.map Operation.tableRowExtent
  have hextent :
      Operation.tableRowExtent (.loadTable table values) ∈ tableExtents :=
    List.mem_map.mpr ⟨.loadTable table values, hload, rfl⟩
  have htable :
      Operation.tableRowExtent (.loadTable table values) ≤
        tableExtents.foldl max 0 :=
    member_le_foldl_max tableExtents
      (Operation.tableRowExtent (.loadTable table values)) 0 hextent
  have hlength :
      values.length ≤
        Operation.tableRowExtent (.loadTable table values) := by
    cases values <;> simp [Operation.tableRowExtent]
  unfold Halo2.usedRows
  exact hlength.trans (htable.trans
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)))

/-!
## Top-level public inputs

A top-level circuit declares the instance cells containing its public input once.
Both extraction from a verifier environment and serialization for a verifier are
derived from that declaration.
-/

structure PublicInputLayout
    (PublicInput : TypeMap) [ProvableType PublicInput]
    (columns : List (Column .instance)) where
  /-- Length of the dense public prefix supplied for each queried instance column. -/
  columnSizes : Vector ℕ columns.length
  /-- The structured public input serializes to exactly those column prefixes. -/
  size_eq : columnSizes.toList.sum = size PublicInput

namespace PublicInputLayout

variable {F : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    {columns : List (Column .instance)}

/-- The public-input cells in column-prefix order. -/
def cellList
    (self : PublicInputLayout PublicInput columns) :
    List (Column .instance × ℕ) :=
  (columns.zip self.columnSizes.toList).flatMap fun (column, columnSize) =>
    (List.range columnSize).map fun row => (column, row)

@[simp] theorem cellList_length
    (self : PublicInputLayout PublicInput columns) :
    self.cellList.length = size PublicInput := by
  rw [cellList, List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [List.map_snd_zip]
  · exact self.size_eq
  · simp

/-- The cell containing one serialized public-input element. -/
def cells
    (self : PublicInputLayout PublicInput columns) :
    Fin (size PublicInput) → Column .instance × ℕ :=
  fun i =>
    self.cellList.get
      ⟨i, by rw [self.cellList_length]; exact i.isLt⟩

/-- A derived public-input cell belongs to one of the layout's columns. -/
theorem cellList_fst_mem
    (self : PublicInputLayout PublicInput columns)
    (cell : Column .instance × ℕ)
    (hcell : cell ∈ self.cellList) :
    cell.1 ∈ columns := by
  rw [cellList, List.mem_flatMap] at hcell
  obtain ⟨⟨column, columnSize⟩, hcolumn, hcell⟩ := hcell
  have hcolumn' :
      column ∈
        (columns.zip self.columnSizes.toList).map Prod.fst :=
    List.mem_map.mpr ⟨(column, columnSize), hcolumn, rfl⟩
  rw [List.map_fst_zip] at hcolumn'
  · obtain ⟨row, _, rfl⟩ := List.mem_map.mp hcell
    exact hcolumn'
  · simp

theorem cells_fst_mem_columns
    (self : PublicInputLayout PublicInput columns)
    (i : Fin (size PublicInput)) :
    (self.cells i).1 ∈ columns := by
  apply self.cellList_fst_mem
  unfold cells
  exact List.get_mem self.cellList
    ⟨i, by rw [self.cellList_length]; exact i.isLt⟩

/-- Prefix cells are distinct whenever their column list is distinct. -/
theorem cellList_nodup
    (self : PublicInputLayout PublicInput columns)
    (hcolumns : columns.Nodup) :
    self.cellList.Nodup := by
  rw [cellList, List.nodup_flatMap]
  constructor
  · rintro ⟨column, columnSize⟩ hpair
    apply List.nodup_range.map
    intro left right heq
    exact Prod.mk.inj heq |>.2
  · let pairs := columns.zip self.columnSizes.toList
    have hfst : (pairs.map Prod.fst).Nodup := by
      dsimp only [pairs]
      rw [List.map_fst_zip]
      · exact hcolumns
      · simp
    have hpairs : pairs.Nodup := hfst.of_map Prod.fst
    apply hpairs.pairwise_of_forall_ne
    intro left hleft right hright hne
    have hfst_ne : left.1 ≠ right.1 := by
      intro heq
      exact hne (List.inj_on_of_nodup_map hfst hleft hright heq)
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro cell hcellLeft hcellRight
    obtain ⟨leftRow, _, hleftCell⟩ := List.mem_map.mp hcellLeft
    obtain ⟨rightRow, _, hrightCell⟩ := List.mem_map.mp hcellRight
    rw [← hleftCell] at hrightCell
    exact hfst_ne (Prod.mk.inj hrightCell |>.1.symm)

/-- The derived prefix-cell map is injective. -/
theorem cells_injective
    (self : PublicInputLayout PublicInput columns)
    (hcolumns : columns.Nodup) :
    Function.Injective self.cells := by
  intro left right heq
  unfold cells at heq
  apply Fin.ext
  exact congrArg (fun index : Fin self.cellList.length => index.val)
    ((self.cellList_nodup hcolumns).get_inj_iff.mp heq)

/-- The largest public prefix length required by this layout. -/
def usedRows
    (self : PublicInputLayout PublicInput columns) : ℕ :=
  self.columnSizes.toList.foldl max 0

/-- Every derived prefix cell lies below the layout's row requirement. -/
theorem cellList_snd_lt_usedRows
    (self : PublicInputLayout PublicInput columns)
    (cell : Column .instance × ℕ)
    (hcell : cell ∈ self.cellList) :
    cell.2 < self.usedRows := by
  rw [cellList, List.mem_flatMap] at hcell
  obtain ⟨⟨column, columnSize⟩, hcolumn, hcell⟩ := hcell
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hcell
  have hsize :
      columnSize ∈ self.columnSizes.toList := by
    have :
        columnSize ∈
          (columns.zip self.columnSizes.toList).map Prod.snd :=
      List.mem_map.mpr ⟨(column, columnSize), hcolumn, rfl⟩
    rw [List.map_snd_zip] at this
    · exact this
    · simp
  exact (List.mem_range.mp hrow).trans_le
    (member_le_foldl_max self.columnSizes.toList columnSize 0 hsize)

theorem cells_snd_lt_usedRows
    (self : PublicInputLayout PublicInput columns)
    (i : Fin (size PublicInput)) :
    (self.cells i).2 < self.usedRows := by
  apply self.cellList_snd_lt_usedRows
  unfold cells
  exact List.get_mem self.cellList
    ⟨i, by rw [self.cellList_length]; exact i.isLt⟩

/-- Read the public input from its declared instance cells. -/
def extract (self : PublicInputLayout PublicInput columns)
    (env : Environment F) : PublicInput F :=
  fromElements (Vector.ofFn fun i =>
    env.inst (self.cells i).1 (self.cells i).2)

/-- Associate each public-input element with its declared instance cell. -/
def assignments (self : PublicInputLayout PublicInput columns)
    (input : PublicInput F) :
    Vector ((Column .instance × ℕ) × F) (size PublicInput) :=
  Vector.ofFn fun i => (self.cells i, (toElements input)[i])

/--
Serialize one instance column as a dense row prefix.

Cells absent from the public-input layout are zero. For a top-level circuit the
layout columns are distinct, so every declared cell selects exactly one serialized
public-input element.
-/
def rows [Zero F] (self : PublicInputLayout PublicInput columns)
    (input : PublicInput F) (column : Column .instance) : List F :=
  (List.range self.usedRows).map fun row =>
    (toElements input).toList.getD
      (self.cellList.idxOf (column, row)) 0

/-- The row serialization reads back every declared public-input element. -/
theorem rows_getD_cells
    [Zero F]
    (self : PublicInputLayout PublicInput columns)
    (hcolumns : columns.Nodup)
    (input : PublicInput F) (i : Fin (size PublicInput)) :
    (self.rows input (self.cells i).1).getD
        (self.cells i).2 0 =
      (toElements input)[i] := by
  have hrow := self.cells_snd_lt_usedRows i
  rw [List.getD_eq_getElem _ _ (by simpa [rows] using hrow)]
  simp only [rows, List.getElem_map, List.getElem_range]
  have hindex :
      self.cellList.idxOf (self.cells i) = i.val := by
    unfold cells
    apply List.Nodup.idxOf_getElem
    exact self.cellList_nodup hcolumns
  rw [hindex]
  rw [List.getD_eq_getElem _ _ (by
    simpa only [Vector.length_toList] using i.isLt)]
  rw [Vector.getElem_toList]
  rfl

theorem extract_eq
    (self : PublicInputLayout PublicInput columns)
    (env : Environment F) (input : PublicInput F)
    (hvalues : ∀ i,
      env.inst (self.cells i).1 (self.cells i).2 =
        (toElements input)[i]) :
    self.extract env = input := by
  unfold extract
  rw [← ProvableType.fromElements_toElements input]
  congr 1
  rw [Vector.ext_iff]
  intro i hi
  simpa using hvalues ⟨i, hi⟩

end PublicInputLayout

/-- The proof-varying advice and instance portions of a Halo2 assignment. -/
structure ProofAssignment (F : Type) where
  /-- Values of the proof's advice columns. -/
  advice : Column .advice → ℤ → F
  /-- Values of the proof's public instance columns. -/
  inst : Column .instance → ℤ → F

/-!
The canonical compiler below is defined before `TopLevelCircuit` so the structure's
law fields can be stated directly against circuit-derived environments.
-/

namespace TopLevelCompilation

variable
    {F : Type} [FiniteField F]
    {Config : Type}
    {PublicInput : TypeMap} [ProvableType PublicInput]

def config
    (circuit : FormalCircuit F Unit Config unit unit) : Config :=
  (circuit.configure () {}).1

def constraintSystem
    (circuit : FormalCircuit F Unit Config unit unit) :
    ConstraintSystem F :=
  (circuit.configure () {}).2

/-- Instance-query requests emitted by this circuit's configure program. -/
def configureInstanceQueries
    (circuit : FormalCircuit F Unit Config unit unit) :
    List (Column .instance × Rotation) :=
  (circuit.elaborated.configureInfo ()).instanceQueries {}

/-- Queried instance columns, in their first-query order. -/
def publicInputColumns
    (circuit : FormalCircuit F Unit Config unit unit) :
    List (Column .instance) :=
  (configureInstanceQueries circuit).map Prod.fst |>.dedup

@[simp] theorem publicInputColumns_nodup
    (circuit : FormalCircuit F Unit Config unit unit) :
    (publicInputColumns circuit).Nodup :=
  List.nodup_dedup _

/-- Every summarized configure query occurs in the interpreted configure result. -/
theorem exists_rotation_mem_configuredInstanceQueries_of_mem_publicInputColumns
    (circuit : FormalCircuit F Unit Config unit unit)
    (column : Column .instance)
    (hcolumn : column ∈ publicInputColumns circuit) :
    ∃ rotation,
      (column, rotation) ∈ (circuit.configure () {}).2.instanceQueries := by
  rw [publicInputColumns, List.mem_dedup, List.mem_map] at hcolumn
  obtain ⟨⟨foundColumn, rotation⟩, hquery, hcolumn⟩ := hcolumn
  simp only at hcolumn
  subst foundColumn
  refine ⟨rotation, ?_⟩
  rw [configureInstanceQueries] at hquery
  rw [← (circuit.elaborated.configureInfo ()).instanceQueries_eq] at hquery
  change
    (column, rotation) ∈
      ((circuit.configure ()).run {}).2.instanceQueries
  rw [Configure.mem_instanceQueries_run_iff]
  exact Or.inr hquery

def operations
    (circuit : FormalCircuit F Unit Config unit unit) : Operations F :=
  (circuit.synthesize (config circuit) ()).operations 0

def regionStarts
    (circuit : FormalCircuit F Unit Config unit unit) : List ℕ :=
  FloorPlanner.V1.starts (operations circuit)

def selectorActivations
    (circuit : FormalCircuit F Unit Config unit unit) : List (ℕ × ℕ) :=
  activations (regionStarts circuit) (indexedRegions (operations circuit) 0).1

def placement
    (circuit : FormalCircuit F Unit Config unit unit) :
    RegionIndex → ℕ :=
  fun region => (regionStarts circuit).getD region 0

def usedRows
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) : ℕ :=
  max (Halo2.usedRows (operations circuit)) layout.usedRows

def domainExponent
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) : ℕ :=
  Halo2.minimalKForRows (constraintSystem circuit) (usedRows circuit layout)

def selectorMap
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) :
    SelCompressMap :=
  deriveSelCompressMap (constraintSystem circuit)
    (2 ^ domainExponent circuit layout) (selectorActivations circuit)

/-- The canonical domain leaves room for the circuit's complete operation footprint. -/
theorem usedRows_le_usableRowsAt_domainExponent
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) :
    usedRows circuit layout ≤
      2 ^ domainExponent circuit layout -
        (constraintSystem circuit).blindingFactors - 1 := by
  have hfit :
      usedRows circuit layout +
          (constraintSystem circuit).blindingFactors + 1 ≤
        2 ^ domainExponent circuit layout := by
    exact (Nat.le_max_left _ _).trans
      (Halo2.minimalKForRows_fits
        (constraintSystem circuit) (usedRows circuit layout))
  omega

def fixedAssignments
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) :
    List (Layout.FixedAssignment F) :=
  Layout.compileFixed
    (2 ^ domainExponent circuit layout -
      (constraintSystem circuit).blindingFactors - 1)
    (selectorMap circuit layout) (constraintSystem circuit) (operations circuit)

def fixedRows
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit)) :
    List (List F) :=
  Layout.denseFixedColumns
    (2 ^ domainExponent circuit layout)
    (PinnedConstraintSystem.derive
      (constraintSystem circuit) (selectorMap circuit layout)).numFixedColumns
    (fixedAssignments circuit layout)

def fixedValue
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (column : Column .fixed) (row : ℤ) : F :=
  (fixedRows circuit layout).getD column.index [] |>.getD
    (row.natMod (2 ^ domainExponent circuit layout)) 0

def environment
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F) : Environment F where
  get column row :=
    match column.kind with
    | .advice => assignment.advice ⟨column.index⟩ row
    | .fixed => fixedValue circuit layout ⟨column.index⟩ row
    | .instance => assignment.inst ⟨column.index⟩ row
  usableRows :=
    2 ^ domainExponent circuit layout -
      (constraintSystem circuit).blindingFactors - 1

@[simp] theorem environment_advice
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F)
    (column : Column .advice) (row : ℤ) :
    (environment circuit layout assignment).advice column row =
      assignment.advice column row :=
  rfl

@[simp] theorem environment_fixed
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F)
    (column : Column .fixed) (row : ℤ) :
    (environment circuit layout assignment).fixed column row =
      fixedValue circuit layout column row := by
  simp only [Environment.fixed, environment, Column.toAny]

@[simp] theorem environment_inst
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F)
    (column : Column .instance) (row : ℤ) :
    (environment circuit layout assignment).inst column row =
      assignment.inst column row :=
  rfl

@[simp] theorem environment_usableRows
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F) :
    (environment circuit layout assignment).usableRows =
      2 ^ domainExponent circuit layout -
        (constraintSystem circuit).blindingFactors - 1 :=
  rfl

def placedEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F) : Placed Environment F :=
  ⟨placement circuit, environment circuit layout assignment⟩

def proverEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    ProverEnvironment F where
  toEnvironment := environment circuit layout assignment
  hint := hint

def placedProverEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (layout : PublicInputLayout PublicInput (publicInputColumns circuit))
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    Placed ProverEnvironment F :=
  ⟨placement circuit, proverEnvironment circuit layout assignment hint⟩

end TopLevelCompilation

/-- A closed formal circuit together with its public/private witness boundary. -/
structure TopLevelCircuit
    (F : Type) [FiniteField F]
    (Config : Type) (PublicInput : TypeMap)
    [ProvableType PublicInput] where
  /-- The underlying unit-config-input, unit-input, unit-output formal circuit. -/
  formalCircuit : FormalCircuit F Unit Config unit unit
  /-- A closed circuit borrows no gate or lookup arguments from an enclosing circuit. -/
  noCallerRequirements : formalCircuit.keygenRequirements.EmptyAt ()
  /-- A closed circuit borrows no selector allocation from an incoming configure state. -/
  selectorRequirements : formalCircuit.selectorRequirements () {}
  /-- A closed circuit borrows no queryable columns from an incoming configure state. -/
  queryRequirements : formalCircuit.queryRequirements () {}
  /-- Every fixed column allocated by the closed configure program is queried. Child
  circuits may leave this obligation to a parent that queries their column later, so the
  law belongs specifically at the top-level boundary. -/
  exists_rotation_mem_fixedQueries_of_lt :
    ∀ column <
        (TopLevelCompilation.constraintSystem formalCircuit).numFixedColumns,
      ∃ rotation,
        (⟨column⟩, rotation) ∈
          (TopLevelCompilation.constraintSystem formalCircuit).fixedQueries := by
    configure_norm
  /-- The exact number of deferred constant requests fits the capacity guaranteed by
  exact compositional column occupancies. -/
  constantSiteCount_le_constantCapacityLowerBound :
    let config := TopLevelCompilation.config formalCircuit
    let summary := formalCircuit.elaborated.synthesisSummary config () 0
    summary.constantSiteCount ≤
      summary.constantCapacityLowerBound
        (TopLevelCompilation.constraintSystem formalCircuit).constants
  /--
  Dense public prefixes for the instance columns derived from this circuit's own
  configure-time query list.
  -/
  publicInputLayout :
    PublicInputLayout PublicInput
      (TopLevelCompilation.publicInputColumns formalCircuit)
  /-- The part of the extracted witness not contained in the public input. -/
  PrivateWitness : Type
  /-- Extract the private witness from a top-level execution, which starts at region zero. -/
  extractPrivate :
    Config → Placed Environment F → PrivateWitness
  /-- Reassemble the formal circuit's witness from its public and private parts. -/
  combine :
    PublicInput F → PrivateWitness → formalCircuit.Witness F
  /-- The top-level specification, stated explicitly at both witness parts. -/
  Spec : PublicInput F → PrivateWitness → Prop
  /-- The split top-level specification is exactly the formal circuit's specification. -/
  spec_iff :
    ∀ publicInput privateWitness,
      Spec publicInput privateWitness ↔
        formalCircuit.Spec () () (combine publicInput privateWitness)
  /-- Recombining both extracted parts recovers the formal circuit's extracted witness. -/
  extract_factorization :
    let config := (formalCircuit.configure () {}).1
    ∀ (env : Placed Environment F),
      combine
        (publicInputLayout.extract env.env)
        (extractPrivate config env) =
      formalCircuit.extract config () 0 env
  /-- A top-level circuit has no assumptions supplied by an enclosing circuit. -/
  assumptions_eq : formalCircuit.Assumptions = fun _ => True
  /--
  The canonical compiled environment supplies the residual facts that the circuit
  cannot establish from either constraints or witness extension.
  -/
  closesEnvironment :
    ∀ (assignment : ProofAssignment F),
      formalCircuit.EnvAssumptions
        (TopLevelCompilation.config formalCircuit)
        (TopLevelCompilation.placedEnvironment
          formalCircuit publicInputLayout assignment)

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- The configuration produced by the top-level circuit's own configure run. -/
def config (self : TopLevelCircuit F Config PublicInput) : Config :=
  TopLevelCompilation.config self.formalCircuit

/-- The circuit-derived constraint system used by key generation. -/
def constraintSystem (self : TopLevelCircuit F Config PublicInput) :
    ConstraintSystem F :=
  TopLevelCompilation.constraintSystem self.formalCircuit

/-- The permutation chunk width derived from the circuit's constraint system. -/
def chunkLen (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.chunkLen

/-- The number of advice columns configured by the circuit. -/
def adviceColumnCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.numAdviceColumns

/-- The number of selectors configured by the circuit. -/
def selectorCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.numSelectors

/-- The number of lookup arguments configured by the circuit. -/
def lookupCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.lookups.length

/-- The columns participating in the circuit's permutation argument. -/
def permutationColumns
    (self : TopLevelCircuit F Config PublicInput) : List AnyColumn :=
  self.constraintSystem.permutationColumns

/-- The number of columns participating in the circuit's permutation argument. -/
def permutationColumnCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.permutationColumns.length

/-- The configure interpreter retains each equality-enabled column only at its first
request. -/
theorem permutationColumns_nodup
    (self : TopLevelCircuit F Config PublicInput) :
    self.permutationColumns.Nodup := by
  apply Configure.permutationColumns_run_nodup
  simp

private def flattenColumn
    (counts : ConfigureCounts) : AnyColumn → ℕ
  | ⟨.advice, index⟩ => index
  | ⟨.fixed, index⟩ => counts.numAdviceColumns + index
  | ⟨.instance, index⟩ =>
      counts.numAdviceColumns + counts.numFixedColumns + index

private theorem flattenColumn_lt
    (counts : ConfigureCounts) (column : AnyColumn)
    (hcolumn : column.Allocated counts) :
    flattenColumn counts column <
      counts.numAdviceColumns + counts.numFixedColumns +
        counts.numInstanceColumns := by
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simp only [AnyColumn.Allocated, flattenColumn] at hcolumn ⊢ <;>
    omega

private theorem flattenColumn_injective_of_allocated
    (counts : ConfigureCounts) {left right : AnyColumn}
    (hleft : left.Allocated counts) (hright : right.Allocated counts)
    (heq : flattenColumn counts left = flattenColumn counts right) :
    left = right := by
  rcases left with ⟨leftKind, leftIndex⟩
  rcases right with ⟨rightKind, rightIndex⟩
  cases leftKind <;> cases rightKind <;>
    simp only [AnyColumn.Allocated, flattenColumn] at hleft hright heq ⊢ <;>
    try omega
  all_goals congr 1 <;> omega

/-- The number of chunks in the circuit's permutation argument. -/
def permutationSetCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  (self.permutationColumnCount + self.chunkLen - 1) / self.chunkLen

/-- The number of quotient-polynomial pieces required by the circuit. -/
def quotientPieceCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  csDegree self.constraintSystem - 1

/-- Public-input cells are distinct by construction from queried columns and prefixes. -/
theorem publicInputLayout_cells_injective
    (self : TopLevelCircuit F Config PublicInput) :
    Function.Injective self.publicInputLayout.cells := by
  apply self.publicInputLayout.cells_injective
  exact TopLevelCompilation.publicInputColumns_nodup self.formalCircuit

/-- Serialize one circuit-derived public instance column as a dense row prefix. -/
def publicInputRows
    (self : TopLevelCircuit F Config PublicInput)
    (input : PublicInput F) (column : Column .instance) : List F :=
  self.publicInputLayout.rows input column

/-- Circuit-derived public row serialization reads back every declared cell. -/
theorem publicInputRows_getD_cell
    (self : TopLevelCircuit F Config PublicInput)
    (input : PublicInput F) (i : Fin (size PublicInput)) :
    (self.publicInputRows input (self.publicInputLayout.cells i).1).getD
        (self.publicInputLayout.cells i).2 0 =
      (toElements input)[i] := by
  exact self.publicInputLayout.rows_getD_cells
    (TopLevelCompilation.publicInputColumns_nodup self.formalCircuit)
    input i

/-- Each public-input cell's column has a verifier query at some rotation. -/
theorem exists_rotation_mem_instanceQueries_of_publicInputLayout_cell
    (self : TopLevelCircuit F Config PublicInput)
    (i : Fin (size PublicInput)) :
    ∃ rotation,
      ((self.publicInputLayout.cells i).1, rotation) ∈
        self.constraintSystem.instanceQueries := by
  obtain ⟨rotation, hquery⟩ :=
    TopLevelCompilation.exists_rotation_mem_configuredInstanceQueries_of_mem_publicInputColumns
      self.formalCircuit
      (self.publicInputLayout.cells i).1
      (self.publicInputLayout.cells_fst_mem_columns i)
  refine ⟨rotation, ?_⟩
  exact hquery

/-- The closed top-level operation stream. -/
def operations (self : TopLevelCircuit F Config PublicInput) : Operations F :=
  TopLevelCompilation.operations self.formalCircuit

/-- Every copied cell in a closed top-level circuit is assigned before use. -/
theorem operationsCopyCellsAssigned
    (self : TopLevelCircuit F Config PublicInput) :
    self.operations.CopyCellsAssigned 0 [] := by
  exact self.formalCircuit.operationsCopyCellsAssigned
    () () self.noCallerRequirements

/-- Exact compositional footprint published by the formal circuit. -/
def synthesisSummary (self : TopLevelCircuit F Config PublicInput) :
    FloorPlanner.SynthesisSummary :=
  self.formalCircuit.elaborated.synthesisSummary self.config () 0

theorem synthesisSummary_eq_operations
    (self : TopLevelCircuit F Config PublicInput) :
    self.synthesisSummary = FloorPlanner.synthesisSummary self.operations := by
  exact self.formalCircuit.elaborated.synthesisSummary_eq self.config () 0

/-- The compactly elaborated, ordered region shapes consumed by V1 measurement. -/
def plannerShapes (self : TopLevelCircuit F Config PublicInput) :
    List FloorPlanner.RegionShape :=
  FloorPlanner.indexRegionSummaries 0 self.synthesisSummary.regionShapes

/-- Elaborated planner shapes are exactly V1's measurement of the full operation
stream. -/
theorem plannerShapes_eq_measureRegions
    (self : TopLevelCircuit F Config PublicInput) :
    self.plannerShapes = FloorPlanner.measureRegions self.operations := by
  unfold plannerShapes
  rw [self.synthesisSummary_eq_operations]
  exact (FloorPlanner.measureRegions_eq_synthesisSummary_regionShapes _).symm

def constantSiteCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.synthesisSummary.constantSiteCount

def constantCapacityLowerBound
    (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.synthesisSummary.constantCapacityLowerBound
    self.constraintSystem.constants

/-- Every configured constants column is equality-enabled by `enableConstant`. -/
theorem constantColumn_mem_permutationColumns
    (self : TopLevelCircuit F Config PublicInput)
    {column : Column .fixed}
    (hcolumn : column ∈ self.constraintSystem.constants) :
    column.toAny ∈ self.permutationColumns := by
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  have hlawful : delta.QueriesLawful (program.finalCounts {}) :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  have hdelta : column ∈ delta.constants := by
    simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
      program, Configure.run, Configure.delta, ConfigureDelta.apply,
      List.nil_append] using hcolumn
  have hrequest : column.toAny ∈ delta.permutationRequests :=
    List.forall_iff_forall_mem.mp
      hlawful.constants_permutationRequests column hdelta
  exact (Configure.mem_permutationColumns_run_iff program {} column.toAny).mpr
    (Or.inr hrequest)

/-- Every V1 constant allocation uses an equality-enabled constants column. -/
theorem constantAssignmentColumn_mem_permutationColumns
    (self : TopLevelCircuit F Config PublicInput)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈
        FloorPlanner.V1.constantAssignments self.operations
          (self.constraintSystem.constants.map (·.index))) :
    (AnyColumn.mk .fixed column) ∈ self.permutationColumns := by
  have hcolumn := FloorPlanner.V1.constantAssignments_column_mem
    self.operations (self.constraintSystem.constants.map (·.index))
    hassignment
  obtain ⟨configuredColumn, hconfigured, hindex⟩ :=
    List.mem_map.mp hcolumn
  have hpermutation :=
    self.constantColumn_mem_permutationColumns hconfigured
  cases configuredColumn
  simpa only [Column.toAny, AnyColumn.mk.injEq] using
    hindex ▸ hpermutation

/-- V1 allocates one constants-column cell for every deferred constant request. -/
theorem constantValues_length_le_constantAssignments_length
    (self : TopLevelCircuit F Config PublicInput) :
    (FloorPlanner.V1.constantValues self.operations).length ≤
      (FloorPlanner.V1.constantAssignments self.operations
        (self.constraintSystem.constants.map (·.index))).length := by
  apply FloorPlanner.V1.constantValues_length_le_constantAssignments_length
  rw [FloorPlanner.V1.constantValues_length]
  have hcapacity :
      self.synthesisSummary.constantSiteCount ≤
        self.synthesisSummary.constantCapacityLowerBound
          self.constraintSystem.constants := by
    simpa only [synthesisSummary, constraintSystem, config] using
      self.constantSiteCount_le_constantCapacityLowerBound
  rw [self.synthesisSummary_eq_operations] at hcapacity
  exact hcapacity.trans
    (FloorPlanner.V1.synthesisSummary_constantCapacityLowerBound_le
      self.operations self.constraintSystem.constants)

/-- V1 region starts derived from the circuit's operation stream. -/
def regionStarts (self : TopLevelCircuit F Config PublicInput) : List ℕ :=
  TopLevelCompilation.regionStarts self.formalCircuit

/-- Selector activations produced by synthesis and V1 placement. -/
def selectorActivations
    (self : TopLevelCircuit F Config PublicInput) : List (ℕ × ℕ) :=
  TopLevelCompilation.selectorActivations self.formalCircuit

/-- The circuit-owned V1 placement function. -/
def placement (self : TopLevelCircuit F Config PublicInput) :
    RegionIndex → ℕ :=
  TopLevelCompilation.placement self.formalCircuit

@[simp] theorem placement_apply
    (self : TopLevelCircuit F Config PublicInput) (region : RegionIndex) :
    self.placement region = self.regionStarts.getD region 0 :=
  rfl

/-- The operation footprint that key generation requires to fit in usable rows. -/
def usedRows (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  TopLevelCompilation.usedRows self.formalCircuit self.publicInputLayout

/-- The complete synthesis operation footprint is included in top-level row usage. -/
theorem operations_usedRows_le_usedRows
    (self : TopLevelCircuit F Config PublicInput) :
    Halo2.usedRows self.operations ≤ self.usedRows := by
  exact Nat.le_max_left _ _

/-- Every public-input cell is below the compiler-derived usable-row requirement. -/
theorem publicInputLayout_cells_snd_lt_usedRows
    (self : TopLevelCircuit F Config PublicInput)
    (i : Fin (size PublicInput)) :
    (self.publicInputLayout.cells i).2 < self.usedRows := by
  exact (self.publicInputLayout.cells_snd_lt_usedRows i).trans_le
    (Nat.le_max_right _ _)

/-- The smallest keygen domain exponent derived from this circuit. -/
def domainExponent (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  TopLevelCompilation.domainExponent self.formalCircuit self.publicInputLayout

/-- The size of the circuit's smallest fitting evaluation domain. -/
def n (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  2 ^ self.domainExponent

/-- The circuit-owned domain size is the power of two selected by compilation. -/
@[simp] theorem n_eq_two_pow_domainExponent
    (self : TopLevelCircuit F Config PublicInput) :
    self.n = 2 ^ self.domainExponent := by
  rfl

/-- The circuit's evaluation domain is nonempty. -/
theorem n_pos (self : TopLevelCircuit F Config PublicInput) :
    0 < self.n := by
  rw [n_eq_two_pow_domainExponent]
  exact pow_pos (by decide) self.domainExponent

/-- The circuit's evaluation-domain size is nonzero. -/
theorem n_ne_zero (self : TopLevelCircuit F Config PublicInput) :
    self.n ≠ 0 :=
  Nat.ne_of_gt self.n_pos

/-- The selector-compression map derived from this circuit and its fitting domain. -/
def selectorMap
    (self : TopLevelCircuit F Config PublicInput) : SelCompressMap :=
  TopLevelCompilation.selectorMap self.formalCircuit self.publicInputLayout

/-- The blinding-row count derived from the circuit's constraint system. -/
def blindingFactors (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.constraintSystem.blindingFactors

/-- Halo2's usable-row count at an evaluation-domain exponent. -/
def usableRowsAt
    (self : TopLevelCircuit F Config PublicInput) (k : ℕ) : ℕ :=
  2 ^ k - self.blindingFactors - 1

/-- The usable-row prefix never extends beyond its evaluation domain. -/
theorem usableRowsAt_le_domainSize
    (self : TopLevelCircuit F Config PublicInput) (k : ℕ) :
    self.usableRowsAt k ≤ 2 ^ k := by
  simp only [usableRowsAt]
  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

/-- At the circuit-selected exponent, every usable row lies in the circuit's
domain. -/
theorem usableRowsAt_domainExponent_le_n
    (self : TopLevelCircuit F Config PublicInput) :
    self.usableRowsAt self.domainExponent ≤ self.n := by
  rw [self.n_eq_two_pow_domainExponent]
  exact self.usableRowsAt_le_domainSize self.domainExponent

/-- The circuit's fitting domain leaves exactly the non-blinding prefix usable. -/
@[simp] theorem usableRowsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput) :
    self.usableRowsAt self.domainExponent =
      self.n - self.blindingFactors - 1 := by
  rfl

/-- The total domain compiler leaves room for the full circuit footprint. -/
theorem usedRows_le_usableRowsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput) :
    self.usedRows ≤ self.usableRowsAt self.domainExponent := by
  simpa only [usedRows, usableRowsAt, domainExponent, blindingFactors,
    constraintSystem] using
    TopLevelCompilation.usedRows_le_usableRowsAt_domainExponent
      self.formalCircuit self.publicInputLayout

/-- The compiler-derived domain includes Halo 2's three mandatory terminal rows. -/
theorem blindingFactors_add_three_le_domainSize
    (self : TopLevelCircuit F Config PublicInput) :
    self.blindingFactors + 3 ≤ self.n := by
  have hfit := Halo2.minimalKForRows_fits
    self.constraintSystem self.usedRows
  have hminimum :
      self.constraintSystem.minimumRows ≤ 2 ^ self.domainExponent :=
    (Nat.le_max_right _ _).trans hfit
  simpa only [ConstraintSystem.minimumRows, blindingFactors,
    n_eq_two_pow_domainExponent] using hminimum

/-- Every public-input cell lies in the compiler-derived usable-row range. -/
theorem publicInputLayout_cells_snd_lt_usableRowsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput)
    (i : Fin (size PublicInput)) :
    (self.publicInputLayout.cells i).2 <
      self.usableRowsAt self.domainExponent :=
  (self.publicInputLayout_cells_snd_lt_usedRows i).trans_le
    self.usedRows_le_usableRowsAt_domainExponent

/-- The canonical domain leaves a usable row beyond the blinding suffix. -/
theorem blindingFactors_succ_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput) :
    self.blindingFactors + 1 < self.n := by
  have hfit := (Nat.le_max_right _ _).trans
    (Halo2.minimalKForRows_fits
      (TopLevelCompilation.constraintSystem self.formalCircuit)
      (TopLevelCompilation.usedRows self.formalCircuit self.publicInputLayout))
  simp only [ConstraintSystem.minimumRows] at hfit
  simp only [blindingFactors, n_eq_two_pow_domainExponent, domainExponent,
    TopLevelCompilation.domainExponent, constraintSystem] at *
  omega

/-- The canonical domain has strictly more rows than the blinding count. -/
theorem blindingFactors_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput) :
    self.blindingFactors < self.n :=
  Nat.lt_of_succ_lt self.blindingFactors_succ_lt_domainSize

/-- The pinned constraint system derived solely from the closed circuit. -/
def pinnedCS (self : TopLevelCircuit F Config PublicInput) :
    PinnedConstraintSystem F :=
  PinnedConstraintSystem.derive self.constraintSystem self.selectorMap

/-- The authoritative query layout used to compile this circuit's expressions. -/
def gateQueryState (self : TopLevelCircuit F Config PublicInput) : QueryState :=
  queryWalkInit self.selectorMap self.constraintSystem

/-- A selector compression emitted by this circuit's compiler resolves in its
authoritative query state. -/
theorem gateQueryState_resolves_selectorMap_lookup
    (self : TopLevelCircuit F Config PublicInput)
    {selector : ℕ} {compressed : SelCompress}
    (hlookup : self.selectorMap.lookup selector = some compressed) :
    self.gateQueryState.ResolvesQuery
      (.fixed ⟨compressed.packedCol⟩ 0) := by
  unfold gateQueryState
  unfold selectorMap TopLevelCompilation.selectorMap at hlookup ⊢
  unfold constraintSystem
  exact queryWalkInit_resolves_deriveSelCompressMap_lookup
    (TopLevelCompilation.constraintSystem self.formalCircuit)
    (2 ^ TopLevelCompilation.domainExponent
      self.formalCircuit self.publicInputLayout)
    (TopLevelCompilation.selectorActivations self.formalCircuit) hlookup

/--
The circuit-owned pinned constraint system is exactly the projection using its
circuit-owned selector map.
-/
theorem pinnedCS_eq_derive
    (self : TopLevelCircuit F Config PublicInput) :
    self.pinnedCS =
      PinnedConstraintSystem.derive self.constraintSystem self.selectorMap :=
  rfl

/-- The instance-query layout of the circuit-owned pinned constraint system. -/
def instanceQueryLayout
    (self : TopLevelCircuit F Config PublicInput) : List (ℕ × ℤ) :=
  self.pinnedCS.instanceQueryLayout

/-- The advice-query layout of the circuit-owned pinned constraint system. -/
def adviceQueryLayout
    (self : TopLevelCircuit F Config PublicInput) : List (ℕ × ℤ) :=
  self.pinnedCS.adviceQueryLayout

/-- The fixed-query layout of the circuit-owned pinned constraint system. -/
def fixedQueryLayout
    (self : TopLevelCircuit F Config PublicInput) : List (ℕ × ℤ) :=
  self.pinnedCS.fixedQueryLayout

/-- The number of instance queries in the circuit-owned pinned constraint system. -/
def instanceQueryCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.instanceQueryLayout.length

/-- The number of advice queries in the circuit-owned pinned constraint system. -/
def adviceQueryCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.adviceQueryLayout.length

/-- The number of fixed queries in the circuit-owned pinned constraint system. -/
def fixedQueryCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.fixedQueryLayout.length

@[simp] theorem adviceQueryLayout_eq_constraintSystem
    (self : TopLevelCircuit F Config PublicInput) :
    self.adviceQueryLayout =
      self.constraintSystem.adviceQueries.map fun query =>
        (query.1.index, query.2) := by
  simp [adviceQueryLayout, pinnedCS, PinnedConstraintSystem.derive,
    projectCS]

@[simp] theorem instanceQueryLayout_eq_constraintSystem
    (self : TopLevelCircuit F Config PublicInput) :
    self.instanceQueryLayout =
      self.constraintSystem.instanceQueries.map fun query =>
        (query.1.index, query.2) := by
  simp [instanceQueryLayout, pinnedCS, PinnedConstraintSystem.derive,
    projectCS]

@[simp] theorem fixedQueryLayout_eq_gateQueryState
    (self : TopLevelCircuit F Config PublicInput) :
    self.fixedQueryLayout = self.gateQueryState.fixed.toList := by
  simp [fixedQueryLayout, gateQueryState, pinnedCS,
    PinnedConstraintSystem.derive, projectCS]

/-- Equality-enabled columns have the rotation-zero query slot used by the
permutation compiler. This follows for every top-level circuit from the configure
program's query lawfulness. -/
theorem permutationColumn_mem_queryLayout
    (self : TopLevelCircuit F Config PublicInput)
    {column : AnyColumn} (hcolumn : column ∈ self.permutationColumns) :
    match column with
    | ⟨.advice, index⟩ => (index, 0) ∈ self.adviceQueryLayout
    | ⟨.fixed, index⟩ => (index, 0) ∈ self.fixedQueryLayout
    | ⟨.instance, index⟩ => (index, 0) ∈ self.instanceQueryLayout := by
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  have hdelta : column ∈ delta.permutationRequests := by
    have hrun :=
      (Configure.mem_permutationColumns_run_iff program {} column).mp
        (by simpa [permutationColumns, constraintSystem,
          TopLevelCompilation.constraintSystem, program] using hcolumn)
    exact hrun.resolve_left (by simp)
  have hregistered := List.forall_iff_forall_mem.mp
    hlawful.permutationRequests_registered column hdelta
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      have hdeltaQuery : (⟨index⟩, 0) ∈ delta.adviceQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hquery : (⟨index⟩, 0) ∈ self.constraintSystem.adviceQueries := by
        have hrun :=
          (Configure.mem_adviceQueries_run_iff
            program {} (⟨index⟩, 0)).mpr
              (Or.inr (by simpa only [delta] using hdeltaQuery))
        simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
          program] using hrun
      rw [adviceQueryLayout_eq_constraintSystem]
      exact List.mem_map.mpr ⟨(⟨index⟩, 0), hquery, rfl⟩
  | fixed =>
      have hdeltaQuery : (⟨index⟩, 0) ∈ delta.fixedQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hquery : (⟨index⟩, 0) ∈ self.constraintSystem.fixedQueries := by
        have hrun :=
          (Configure.mem_fixedQueries_run_iff
            program {} (⟨index⟩, 0)).mpr
              (Or.inr (by simpa only [delta] using hdeltaQuery))
        simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
          program] using hrun
      rw [fixedQueryLayout_eq_gateQueryState]
      simpa [QueryState.ResolvesQuery, gateQueryState] using
        queryWalkInit_resolves_fixed_of_mem self.selectorMap hquery
  | «instance» =>
      have hdeltaQuery : (⟨index⟩, 0) ∈ delta.instanceQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hquery : (⟨index⟩, 0) ∈ self.constraintSystem.instanceQueries := by
        have hrun :=
          (Configure.mem_instanceQueries_run_iff
            program {} (⟨index⟩, 0)).mpr
              (Or.inr (by simpa only [delta] using hdeltaQuery))
        simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
          program] using hrun
      rw [instanceQueryLayout_eq_constraintSystem]
      exact List.mem_map.mpr ⟨(⟨index⟩, 0), hquery, rfl⟩

/-- Every equality-enabled column was allocated by the same closed configure run. -/
theorem permutationColumn_allocated
    (self : TopLevelCircuit F Config PublicInput)
    {column : AnyColumn} (hcolumn : column ∈ self.permutationColumns) :
    column.Allocated
      (ConfigureCounts.ofConstraintSystem self.constraintSystem) := by
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  have hdelta : column ∈ delta.permutationRequests := by
    have hrun :=
      (Configure.mem_permutationColumns_run_iff program {} column).mp
        (by simpa [permutationColumns, constraintSystem,
          TopLevelCompilation.constraintSystem, program] using hcolumn)
    exact hrun.resolve_left (by simp)
  have hregistered := List.forall_iff_forall_mem.mp
    hlawful.permutationRequests_registered column hdelta
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      have hquery : (⟨index⟩, 0) ∈ delta.adviceQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hindex := List.forall_iff_forall_mem.mp
        hlawful.adviceQueries_fst_lt_numAdviceColumns
        (⟨index⟩, 0) hquery
      simpa only [AnyColumn.Allocated, constraintSystem,
        TopLevelCompilation.constraintSystem, ConfigureCounts.ofConstraintSystem,
        program, counts, Configure.run_numAdviceColumns] using hindex
  | fixed =>
      have hquery : (⟨index⟩, 0) ∈ delta.fixedQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hindex := List.forall_iff_forall_mem.mp
        hlawful.fixedQueries_fst_lt_numFixedColumns
        (⟨index⟩, 0) hquery
      simpa only [AnyColumn.Allocated, constraintSystem,
        TopLevelCompilation.constraintSystem, ConfigureCounts.ofConstraintSystem,
        program, counts, Configure.run_numFixedColumns] using hindex
  | «instance» =>
      have hquery : (⟨index⟩, 0) ∈ delta.instanceQueries := by
        simpa [ConfigureDelta.RegistersPermutationColumn] using hregistered
      have hindex := List.forall_iff_forall_mem.mp
        hlawful.instanceQueries_fst_lt_numInstanceColumns
        (⟨index⟩, 0) hquery
      simpa only [AnyColumn.Allocated, constraintSystem,
        TopLevelCompilation.constraintSystem, ConfigureCounts.ofConstraintSystem,
        program, counts, Configure.run_numInstanceColumns] using hindex

/-- The duplicate-free permutation family fits inside the disjoint configured advice,
fixed, and instance column spaces. -/
theorem permutationColumnCount_le_configuredColumnCount
    (self : TopLevelCircuit F Config PublicInput) :
    self.permutationColumnCount ≤
      self.constraintSystem.numAdviceColumns +
        self.constraintSystem.numFixedColumns +
          self.constraintSystem.numInstanceColumns := by
  classical
  let counts := ConfigureCounts.ofConstraintSystem self.constraintSystem
  let columns := self.permutationColumns.toFinset
  let indices := columns.image (flattenColumn counts)
  have hinjective : Set.InjOn (flattenColumn counts) columns := by
    intro left hleft right hright heq
    apply flattenColumn_injective_of_allocated counts
    · apply self.permutationColumn_allocated
      exact List.mem_toFinset.mp (show left ∈ columns from hleft)
    · apply self.permutationColumn_allocated
      exact List.mem_toFinset.mp (show right ∈ columns from hright)
    · exact heq
  have hindicesCard : indices.card = columns.card := by
    exact Finset.card_image_iff.mpr hinjective
  have hsubset : indices ⊆ Finset.range
      (counts.numAdviceColumns + counts.numFixedColumns +
        counts.numInstanceColumns) := by
    intro index hindex
    rw [Finset.mem_image] at hindex
    obtain ⟨column, hcolumn, rfl⟩ := hindex
    rw [Finset.mem_range]
    apply flattenColumn_lt
    apply self.permutationColumn_allocated
    exact List.mem_toFinset.mp (show column ∈ columns from hcolumn)
  calc
    self.permutationColumnCount = columns.card := by
      exact (List.toFinset_card_of_nodup
        self.permutationColumns_nodup).symm
    _ = indices.card := hindicesCard.symm
    _ ≤ (Finset.range
        (counts.numAdviceColumns + counts.numFixedColumns +
          counts.numInstanceColumns)).card :=
      Finset.card_le_card hsubset
    _ = self.constraintSystem.numAdviceColumns +
        self.constraintSystem.numFixedColumns +
          self.constraintSystem.numInstanceColumns := by
      simp only [Finset.card_range, counts,
        ConfigureCounts.ofConstraintSystem]

/-- The number of fixed columns in the circuit-owned pinned constraint system. -/
def fixedColumnCount (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  self.pinnedCS.numFixedColumns

@[simp] theorem fixedColumnCount_eq
    (self : TopLevelCircuit F Config PublicInput) :
    self.fixedColumnCount =
      self.constraintSystem.numFixedColumns + self.selectorMap.newFixedCols := by
  simp [fixedColumnCount, pinnedCS, PinnedConstraintSystem.derive, projectCS]

/-- Every fixed column in the post-compression verifier constraint system has a query
slot. Original columns are covered by the closed circuit's configure law; selector
compression covers its appended suffix by construction. -/
theorem exists_rotation_mem_fixedQueryLayout_of_lt
    (self : TopLevelCircuit F Config PublicInput) :
    ∀ column < self.fixedColumnCount,
      ∃ rotation, (column, rotation) ∈ self.fixedQueryLayout := by
  intro column hcolumn
  rw [fixedColumnCount_eq] at hcolumn
  by_cases horiginal : column < self.constraintSystem.numFixedColumns
  · obtain ⟨rotation, hquery⟩ :=
      self.exists_rotation_mem_fixedQueries_of_lt column horiginal
    refine ⟨rotation, ?_⟩
    rw [fixedQueryLayout_eq_gateQueryState]
    simpa [QueryState.ResolvesQuery, gateQueryState] using
      queryWalkInit_resolves_fixed_of_mem self.selectorMap hquery
  · let index := column - self.constraintSystem.numFixedColumns
    have hindex : index < self.selectorMap.newFixedCols := by
      omega
    have hcolumnEq :
        self.constraintSystem.numFixedColumns + index = column := by
      omega
    refine ⟨0, ?_⟩
    rw [fixedQueryLayout_eq_gateQueryState]
    rw [← hcolumnEq]
    simpa [QueryState.ResolvesQuery, gateQueryState] using
      queryWalkInit_resolves_packedColumn
        self.constraintSystem self.selectorMap hindex

/-- Every fixed-query slot names a column in the post-compression verifier constraint
system. -/
theorem fixedQueryLayout_columns_lt
    (self : TopLevelCircuit F Config PublicInput) :
    self.fixedQueryLayout.Forall fun query =>
      query.1 < self.fixedColumnCount := by
  rw [fixedQueryLayout_eq_gateQueryState, fixedColumnCount_eq]
  apply queryWalkInit_fixedQueries_bounded
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  rw [List.forall_iff_forall_mem]
  intro query hquery
  have hdelta : query ∈ delta.fixedQueries := by
    have hrun := (Configure.mem_fixedQueries_run_iff program {} query).mp hquery
    exact hrun.resolve_left (by simp)
  have hlt := List.forall_iff_forall_mem.mp
    hlawful.fixedQueries_fst_lt_numFixedColumns query hdelta
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    program, counts, Configure.run_numFixedColumns,
    ConfigureCounts.ofConstraintSystem_empty] using hlt

/-- Every advice-query slot names a column allocated by the closed configure
program. -/
theorem adviceQueryLayout_columns_lt
    (self : TopLevelCircuit F Config PublicInput) :
    self.adviceQueryLayout.Forall fun query =>
      query.1 < self.constraintSystem.numAdviceColumns := by
  rw [adviceQueryLayout_eq_constraintSystem,
    List.forall_map_iff]
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  rw [List.forall_iff_forall_mem]
  intro query hquery
  have hdelta : query ∈ delta.adviceQueries := by
    have hrun := (Configure.mem_adviceQueries_run_iff program {} query).mp hquery
    exact hrun.resolve_left (by simp)
  have hlt := List.forall_iff_forall_mem.mp
    hlawful.adviceQueries_fst_lt_numAdviceColumns query hdelta
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    program, counts, Configure.run_numAdviceColumns,
    ConfigureCounts.ofConstraintSystem_empty] using hlt

/-- Every instance-query slot names a column allocated by the closed configure
program. -/
theorem instanceQueryLayout_columns_lt
    (self : TopLevelCircuit F Config PublicInput) :
    self.instanceQueryLayout.Forall fun query =>
      query.1 < self.constraintSystem.numInstanceColumns := by
  rw [instanceQueryLayout_eq_constraintSystem,
    List.forall_map_iff]
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.formalCircuit.queriesLawful () {} self.queryRequirements
  rw [List.forall_iff_forall_mem]
  intro query hquery
  have hdelta : query ∈ delta.instanceQueries := by
    have hrun := (Configure.mem_instanceQueries_run_iff program {} query).mp hquery
    exact hrun.resolve_left (by simp)
  have hlt := List.forall_iff_forall_mem.mp
    hlawful.instanceQueries_fst_lt_numInstanceColumns query hdelta
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    program, counts, Configure.run_numInstanceColumns,
    ConfigureCounts.ofConstraintSystem_empty] using hlt

/-- All circuit-derived fixed-cell assignments, before dense row expansion. -/
def fixedAssignments
    (self : TopLevelCircuit F Config PublicInput) :
    List (Layout.FixedAssignment F) :=
  TopLevelCompilation.fixedAssignments
    self.formalCircuit self.publicInputLayout

/-- The dense fixed columns compiled canonically from the top-level circuit. -/
def fixedRows
    (self : TopLevelCircuit F Config PublicInput) : List (List F) :=
  TopLevelCompilation.fixedRows self.formalCircuit self.publicInputLayout

@[simp] theorem fixedRows_length
    (self : TopLevelCircuit F Config PublicInput) :
    self.fixedRows.length = self.fixedColumnCount := by
  apply Layout.denseFixedColumns_length

/-- Every compiled fixed column spans the full evaluation domain. -/
theorem fixedRows_getD_length
    (self : TopLevelCircuit F Config PublicInput)
    (column : ℕ)
    (hcolumn : column < self.fixedColumnCount) :
    (self.fixedRows.getD column []).length = self.n := by
  apply Layout.denseFixedColumns_getD_length
  exact hcolumn

/--
Read a compiled fixed column with Halo2's cyclic domain-row semantics.

Rotations may produce negative or out-of-domain integer rows, so the row is reduced
modulo the nonempty evaluation domain before reading the dense column.
-/
def fixedValue
    (self : TopLevelCircuit F Config PublicInput)
    (column : Column .fixed) (row : ℤ) : F :=
  TopLevelCompilation.fixedValue
    self.formalCircuit self.publicInputLayout column row

/--
Construct the complete semantic environment from exactly the proof-varying assignment.
Fixed values and usable rows are circuit-derived and cannot be supplied independently.
-/
def environment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) : Environment F :=
  TopLevelCompilation.environment
    self.formalCircuit self.publicInputLayout assignment

/-- The canonical environment paired with the circuit-owned V1 placement. -/
def placedEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) : Placed Environment F :=
  TopLevelCompilation.placedEnvironment
    self.formalCircuit self.publicInputLayout assignment

/-- Add prover-only hints to the canonical proof assignment. -/
def proverEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    ProverEnvironment F :=
  TopLevelCompilation.proverEnvironment
    self.formalCircuit self.publicInputLayout assignment hint

/-- The canonical prover environment paired with circuit-owned placement. -/
def placedProverEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    Placed ProverEnvironment F :=
  TopLevelCompilation.placedProverEnvironment
    self.formalCircuit self.publicInputLayout assignment hint

@[simp, circuit_norm] theorem environment_advice
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F)
    (column : Column .advice) (row : ℤ) :
    (self.environment assignment).advice column row =
      assignment.advice column row := by
  rfl

@[simp, circuit_norm] theorem environment_fixed
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F)
    (column : Column .fixed) (row : ℤ) :
    (self.environment assignment).fixed column row =
      self.fixedValue column row := by
  simpa only [environment, fixedValue] using
    TopLevelCompilation.environment_fixed
      self.formalCircuit self.publicInputLayout assignment column row

@[simp, circuit_norm] theorem environment_inst
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F)
    (column : Column .instance) (row : ℤ) :
    (self.environment assignment).inst column row =
      assignment.inst column row := by
  rfl

@[simp, circuit_norm] theorem environment_usableRows
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) :
    (self.environment assignment).usableRows =
      self.usableRowsAt self.domainExponent := by
  rfl

@[simp] theorem placedEnvironment_place
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) :
    (self.placedEnvironment assignment).place = self.placement := by
  rfl

@[simp] theorem placedEnvironment_env
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) :
    (self.placedEnvironment assignment).env = self.environment assignment := by
  rfl

/--
The circuit-side static premise needed to connect synthesized gate and lookup
activations to the pinned constraint system derived from `configure`.
-/
def KeygenCoherent
    (self : TopLevelCircuit F Config PublicInput) : Prop :=
  OperationsKeygenCoherent self.constraintSystem self.operations

/-- Configure/synthesis registration coherence follows from the circuit-derived
constraint system; it is not a separate top-level circuit obligation. -/
theorem keygenCoherent
    (self : TopLevelCircuit F Config PublicInput) :
    self.KeygenCoherent := by
  exact self.formalCircuit.operationsKeygenCoherent
    () () self.noCallerRequirements

/-- Every synthesized lookup activation enables its master and only selectors declared
by that lookup. -/
theorem lookupActivationsWellFormed
    (self : TopLevelCircuit F Config PublicInput) :
    self.operations.LookupActivationsWellFormed := by
  exact self.formalCircuit.elaborated.lookupActivationsWellFormed
    self.config () 0

/-- Configure composition keeps every gate and lookup selector compatible with every
configured lookup's master-selector discipline. -/
theorem lookupSelectorsCompatible
    (self : TopLevelCircuit F Config PublicInput) :
    Halo2.LookupSelectorsCompatible
      self.constraintSystem.gates self.constraintSystem.lookups := by
  let program := self.formalCircuit.configure ()
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hcompatible := self.formalCircuit.lookupSelectorsCompatible
    () counts self.selectorRequirements
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    program, counts, Configure.run, ConfigureCounts.ofConstraintSystem,
    ConfigureDelta.apply, List.nil_append] using hcompatible

/-- The global lookup-selector law follows generically from configure registration,
lookup-local activation, and configure-time selector compatibility. -/
theorem lookupSelectorsLawful
    (self : TopLevelCircuit F Config PublicInput) :
    self.operations.LookupSelectorsLawful self.constraintSystem.lookups :=
  Operations.lookupSelectorsLawful_of_registered self.keygenCoherent
    self.lookupActivationsWellFormed self.lookupSelectorsCompatible

/-- Every configured gate's activation selector is allocated. -/
theorem gateSelectorsAllocated
    (self : TopLevelCircuit F Config PublicInput) :
    self.constraintSystem.gates.Forall fun gate =>
      gate.selector.index < self.constraintSystem.numSelectors := by
  let program := self.formalCircuit.configure ()
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hallocated :=
    (self.formalCircuit.selectorsAllocated
      () counts self.selectorRequirements).gates
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    program, counts, Configure.run, ConfigureCounts.ofConstraintSystem,
    ConfigureDelta.apply, List.nil_append] using hallocated

/-- Every selector atom in a top-level circuit's lookup inputs is allocated. -/
theorem lookupInputsAllocated
    (self : TopLevelCircuit F Config PublicInput) :
    ∀ argument ∈ self.constraintSystem.lookups,
      ∀ expression ∈ argument.inputs,
        expression.selectorBound ≤ self.constraintSystem.numSelectors := by
  exact (self.formalCircuit.lookupSelectorsAllocated
    () self.selectorRequirements).lookupInputsAllocated

/-- Every selector used by a lookup has compression degree zero. Static configure
compatibility excludes it from all gate selector sets, and gate well-formedness owns
every selector atom in each gate polynomial. -/
theorem lookupInputSelectorDegree_eq_zero
    (self : TopLevelCircuit F Config PublicInput)
    (argument : LookupArgument F)
    (hargument : argument ∈ self.constraintSystem.lookups)
    (expression : Expression F Query) (hexpression : expression ∈ argument.inputs)
    {selector : ℕ} (hselector : selector ∈ expression.selectorIndices) :
    (selectorMaxDegrees self.constraintSystem)[selector]! = 0 := by
  have hbound := self.lookupInputsAllocated argument hargument
    expression hexpression
  have hallocated :=
    (Expression.lt_selectorBound_of_mem_selectorIndices
      expression hselector).trans_le hbound
  apply selectorMaxDegrees_eq_zero_of_complexGateSelectors
    self.constraintSystem hallocated
  rw [List.forall_iff_forall_mem]
  intro gate hgate
  have hcompatible := List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp self.lookupSelectorsCompatible.1
      gate hgate) argument hargument
  have hcompatible' :
      (argument.auxiliarySelectorIndices.Forall fun candidate =>
        candidate ≠ gate.selector.index) ∧
      (argument.masterSelector.index = gate.selector.index →
        gate.selector.simple = false) := by
    simpa [Gate.LookupSelectorsCompatible,
      Selector.LookupSelectorsCompatible,
      LookupArgument.selectorUsage] using hcompatible
  intro hgateSelector
  by_cases hmaster : selector = argument.masterSelector.index
  · exact hcompatible'.2 (by omega)
  · have hauxiliary : selector ∈ argument.auxiliarySelectorIndices :=
      List.mem_filter.mpr ⟨List.mem_flatMap.mpr
        ⟨expression, hexpression, hselector⟩, by simpa⟩
    have hdisjoint := List.forall_iff_forall_mem.mp hcompatible'.1
      selector hauxiliary
    omega

/-- Every query declaration emitted by the closed configure program is valid and
names a column allocated by that program. -/
theorem configureQueriesLawful
    (self : TopLevelCircuit F Config PublicInput) :
    ((self.formalCircuit.configure ()).delta {}).QueriesLawful
      ((self.formalCircuit.configure ()).finalCounts {}) :=
  self.formalCircuit.queriesLawful () {} self.queryRequirements

/-- Every selector-compressed gate expression resolves read-only against the circuit's
compiler-derived query layout. -/
theorem gateQueriesResolved
    (self : TopLevelCircuit F Config PublicInput) :
    ∀ expression ∈ flatGates self.constraintSystem,
      (substSelectorMap self.selectorMap.lookup expression).QueriesResolved
        self.gateQueryState := by
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.configureQueriesLawful
  intro expression hexpression
  rw [flatGates, List.mem_flatMap] at hexpression
  obtain ⟨gate, hgate, hexpression⟩ := hexpression
  obtain ⟨constraint, hconstraint, rfl⟩ :=
    List.mem_map.mp hexpression
  have hgateDelta : gate ∈ delta.gates := by
    simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
      program, delta, Configure.run, ConfigureCounts.ofConstraintSystem,
      ConfigureDelta.apply, List.nil_append] using hgate
  have hgateRegistered : gate.QueriesRegistered delta :=
    List.forall_iff_forall_mem.mp hlawful.gates_queriesRegistered
      gate hgateDelta
  have hregistered : constraint.poly.QueriesRegistered delta :=
    List.forall_iff_forall_mem.mp hgateRegistered
      constraint hconstraint
  have hsource : constraint.poly.QueriesResolved self.gateQueryState := by
    simpa only [gateQueryState, constraintSystem,
      TopLevelCompilation.constraintSystem, program, delta, counts,
      Configure.run, ConfigureCounts.ofConstraintSystem,
      ConfigureDelta.apply, List.nil_append] using
      hregistered.queriesResolved_queryWalkInit_apply
        (initial := {}) (counts := counts) self.selectorMap
  apply substSelectorMap_queriesResolved self.selectorMap.lookup
    self.gateQueryState constraint.poly hsource
  intro selector compressed hlookup
  exact self.gateQueryState_resolves_selectorMap_lookup hlookup

/-- Every selector-compressed lookup expression resolves against the same authoritative
query layout. -/
theorem lookupQueriesResolved
    (self : TopLevelCircuit F Config PublicInput) :
    ∀ argument ∈ self.constraintSystem.lookups,
      (argument.inputs.map
        (substSelectorMap self.selectorMap.lookup)).Forall
          (·.QueriesResolved self.gateQueryState) ∧
      (argument.tables.map
        (substSelectorMap self.selectorMap.lookup)).Forall
          (·.QueriesResolved self.gateQueryState) := by
  let program := self.formalCircuit.configure ()
  let delta := program.delta {}
  let counts := program.finalCounts {}
  have hlawful : delta.QueriesLawful counts :=
    self.configureQueriesLawful
  intro argument hargument
  have hargumentDelta : argument ∈ delta.lookups := by
    simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
      program, delta, Configure.run, ConfigureCounts.ofConstraintSystem,
      ConfigureDelta.apply, List.nil_append] using hargument
  have hregistered : argument.QueriesRegistered delta :=
    List.forall_iff_forall_mem.mp hlawful.lookups_queriesRegistered
      argument hargumentDelta
  have resolve (expression : Expression F Query)
      (hexpression : expression.QueriesRegistered delta) :
      (substSelectorMap self.selectorMap.lookup expression).QueriesResolved
        self.gateQueryState := by
    have hsource : expression.QueriesResolved self.gateQueryState := by
      simpa only [gateQueryState, constraintSystem,
        TopLevelCompilation.constraintSystem, program, delta, counts,
        Configure.run, ConfigureCounts.ofConstraintSystem,
        ConfigureDelta.apply, List.nil_append] using
        hexpression.queriesResolved_queryWalkInit_apply
          (initial := {}) (counts := counts) self.selectorMap
    apply substSelectorMap_queriesResolved self.selectorMap.lookup
      self.gateQueryState expression hsource
    intro selector compressed hlookup
    exact self.gateQueryState_resolves_selectorMap_lookup hlookup
  constructor
  · rw [List.forall_iff_forall_mem]
    intro expression hexpression
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
    exact resolve source
      (List.forall_iff_forall_mem.mp hregistered.1 source hsource)
  · rw [List.forall_iff_forall_mem]
    intro expression hexpression
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
    exact resolve source
      (List.forall_iff_forall_mem.mp hregistered.2 source hsource)

/-- A closed circuit's configure program contains no malformed query declarations. -/
theorem invalidQueriedCells_eq_nil
    (self : TopLevelCircuit F Config PublicInput) :
    self.constraintSystem.invalidQueriedCells = [] := by
  have h := self.configureQueriesLawful.invalidQueriedCells_eq_nil
  simpa only [constraintSystem, TopLevelCompilation.constraintSystem,
    Configure.run, ConfigureCounts.ofConstraintSystem,
    ConfigureDelta.apply, List.nil_append] using h

/-- Read this circuit's public input from its declared instance cells. -/
def extractPublicInput (self : TopLevelCircuit F Config PublicInput)
    (env : Environment F) : PublicInput F :=
  self.publicInputLayout.extract env

/-- Read this circuit's private witness from a placed environment. -/
def extractPrivateWitness (self : TopLevelCircuit F Config PublicInput)
    (env : Placed Environment F) : self.PrivateWitness :=
  self.extractPrivate self.config env

/-- The externally visible statement: some private witness satisfies the circuit spec. -/
def Statement (self : TopLevelCircuit F Config PublicInput)
    (publicInput : PublicInput F) : Prop :=
  ∃ privateWitness, self.Spec publicInput privateWitness

/--
Top-level soundness for the canonical environment compiled from a proof assignment.

The caller supplies only proof-varying advice/instance values and satisfaction of the
resulting constraints. Placement, fixed values, usable rows, and synthesis
well-formedness are derived internally.
-/
theorem soundness
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F)
    (hconstraints :
      Constraints self.placement (self.environment assignment)
        self.operations 0) :
    self.Spec
      (self.extractPublicInput (self.environment assignment))
      (self.extractPrivateWitness (self.placedEnvironment assignment)) := by
  let env := self.placedEnvironment assignment
  apply (self.spec_iff _ _).mpr
  unfold extractPublicInput extractPrivateWitness config
  change self.formalCircuit.Spec () ()
    (self.combine
      (self.publicInputLayout.extract env.env)
      (self.extractPrivate (self.formalCircuit.configure () {}).1 env))
  rw [self.extract_factorization]
  apply self.formalCircuit.soundness self.config 0 env ()
  · exact self.closesEnvironment assignment
  · rw [self.assumptions_eq]
    trivial
  · simpa [env] using hconstraints

/-- A satisfying assignment establishes the external statement for its public input. -/
theorem statement_soundness
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F)
    (hconstraints :
      Constraints self.placement (self.environment assignment)
        self.operations 0) :
    self.Statement
      (self.extractPublicInput (self.environment assignment)) :=
  ⟨self.extractPrivateWitness (self.placedEnvironment assignment),
    self.soundness assignment hconstraints⟩

/--
Honest-prover top-level completeness for the canonical proof assignment.

The prover hint remains a separate runtime-only value; it is not proof assignment data
and is erased from the verifier environment.
-/
theorem completeness
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) (hint : ProverHint F)
    (hwitnesses :
      ExtendsWitnesses self.placement
        (self.proverEnvironment assignment hint) self.operations 0)
    (hprover : self.formalCircuit.ProverAssumptions
      (eval (self.placedProverEnvironment assignment hint)
        (show Var unit F from ()))
      (self.formalCircuit.extract self.config () 0
        (self.placedEnvironment assignment))
      hint) :
    Constraints self.placement (self.environment assignment)
        self.operations 0 ∧
      self.formalCircuit.ProverSpec
        (eval (self.placedProverEnvironment assignment hint)
          (show Var unit F from ()))
        (eval (self.placedProverEnvironment assignment hint)
          (self.formalCircuit.output self.config () 0))
        (self.formalCircuit.extract self.config () 0
          (self.placedEnvironment assignment))
        hint := by
  let env := self.placedProverEnvironment assignment hint
  apply self.formalCircuit.completeness self.config 0 env ()
  · simpa [env, placedProverEnvironment] using hwitnesses
  · exact self.closesEnvironment assignment
  · rw [self.assumptions_eq]
    trivial
  · simpa [env, placedProverEnvironment, proverEnvironment] using hprover

end TopLevelCircuit

end Halo2
