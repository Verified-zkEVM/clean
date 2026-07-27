import Clean.Halo2.Keygen.PinnedCs
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

/--
Static configure/synthesis coherence for one region operation.

Assignments and copies need no configure-phase registration. Gate and lookup
activations do: their semantic expressions must be among the arguments from which
key generation constructs the pinned constraint system.
-/
@[circuit_norm]
def RegionOperation.KeygenCoherent
    (cs : ConstraintSystem F) : RegionOperation F → Prop
  | .enableGate gate _ => gate ∈ cs.gates
  | .enableLookup argument _ _ => argument ∈ cs.lookups
  | _ => True

/-- Static configure/synthesis coherence for one layouter operation. -/
@[circuit_norm]
def Operation.KeygenCoherent
    (cs : ConstraintSystem F) : Operation F → Prop
  | .region _ body => body.Forall (RegionOperation.KeygenCoherent cs)
  | _ => True

/--
Every gate and lookup emitted by synthesis was registered by the same circuit's
configure phase.

`FormalCircuit` intentionally keeps `configure` and `synthesize` independent, so
this property cannot be derived for an arbitrary value of that type. A deployed
top-level circuit certifies it once; the verifier-to-circuit bridge then uses it
generically.
-/
def OperationsKeygenCoherent
    (cs : ConstraintSystem F) (operations : Operations F) : Prop :=
  operations.Forall (Operation.KeygenCoherent cs)

@[circuit_norm]
theorem OperationsKeygenCoherent.nil
    (cs : ConstraintSystem F) :
    OperationsKeygenCoherent cs [] := by
  simp [OperationsKeygenCoherent]

/-- Configure/synthesis coherence composes across operation-stream append. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.append
    (cs : ConstraintSystem F) (left right : Operations F) :
    OperationsKeygenCoherent cs (left ++ right) ↔
      OperationsKeygenCoherent cs left ∧
        OperationsKeygenCoherent cs right := by
  simp [OperationsKeygenCoherent]

/-- A region is coherent exactly when each operation in its body is coherent. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.region_cons
    (cs : ConstraintSystem F) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.region name body :: rest) ↔
      body.Forall (RegionOperation.KeygenCoherent cs) ∧
        OperationsKeygenCoherent cs rest := by
  simp [OperationsKeygenCoherent, Operation.KeygenCoherent]

@[circuit_norm]
theorem OperationsKeygenCoherent.constrainInstance_cons
    (cs : ConstraintSystem F) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    OperationsKeygenCoherent cs
        (.constrainInstance cell column row :: rest) ↔
      OperationsKeygenCoherent cs rest := by
  simp [OperationsKeygenCoherent, Operation.KeygenCoherent]

@[circuit_norm]
theorem OperationsKeygenCoherent.loadTable_cons
    (cs : ConstraintSystem F) (table : TableColumn)
    (values : List F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.loadTable table values :: rest) ↔
      OperationsKeygenCoherent cs rest := by
  simp [OperationsKeygenCoherent, Operation.KeygenCoherent]

/--
Closing a constraint system under an operation stream makes configure/synthesis
registration coherence true by construction.
-/
theorem OperationsKeygenCoherent.closeWithOperations
    [DecidableEq F] (cs : ConstraintSystem F) (operations : Operations F) :
    OperationsKeygenCoherent (cs.closeWithOperations operations) operations := by
  rw [OperationsKeygenCoherent, List.forall_iff_forall_mem]
  intro operation hoperation
  cases operation with
  | region name body =>
      rw [Operation.KeygenCoherent, List.forall_iff_forall_mem]
      intro regionOperation hregionOperation
      cases regionOperation with
      | enableGate gate row =>
          apply ConstraintSystem.mem_gates_closeWithOperations_of_enabled
          simp only [Operations.enabledGates, List.mem_flatMap]
          refine ⟨.region name body, hoperation, ?_⟩
          simp only [RegionOperations.enabledGates]
          exact List.mem_filterMap.mpr
            ⟨.enableGate gate row, hregionOperation, rfl⟩
      | enableLookup argument selectors row =>
          apply ConstraintSystem.mem_lookups_closeWithOperations_of_enabled
          simp only [Operations.enabledLookups, List.mem_flatMap]
          refine ⟨.region name body, hoperation, ?_⟩
          simp only [RegionOperations.enabledLookups]
          exact List.mem_filterMap.mpr
            ⟨.enableLookup argument selectors row, hregionOperation, rfl⟩
      | assignAdvice
      | assignFixed
      | constrainEqual
      | constrainConstant
      | constrainInstance =>
          trivial
  | constrainInstance
  | loadTable =>
      trivial

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

private theorem exists_region_operation_of_mem_indexedRegions
    {operations : Operations F} {start region : ℕ}
    {body : RegionOperations F}
    (hregion : (region, body) ∈ (indexedRegions operations start).1) :
    ∃ name, Operation.region name body ∈ operations := by
  induction operations generalizing start with
  | nil =>
      simp [indexedRegions] at hregion
  | cons operation rest ih =>
      cases operation with
      | region name headBody =>
          simp only [indexedRegions, List.mem_cons] at hregion
          rcases hregion with hhead | hrest
          · have : body = headBody := congrArg Prod.snd hhead
            subst body
            exact ⟨name, List.mem_cons_self⟩
          · obtain ⟨foundName, hfound⟩ := ih hrest
            exact ⟨foundName, List.mem_cons_of_mem _ hfound⟩
      | constrainInstance cell column row =>
          exact
            let ⟨foundName, hfound⟩ := ih hregion
            ⟨foundName, List.mem_cons_of_mem _ hfound⟩
      | loadTable table values =>
          exact
            let ⟨foundName, hfound⟩ := ih hregion
            ⟨foundName, List.mem_cons_of_mem _ hfound⟩

/-- Select the region-local law for one indexed region body. -/
theorem Operations.LookupRelevantSelectorActivationsExact.of_region
    {operations : Operations F}
    (hlaw : operations.LookupRelevantSelectorActivationsExact)
    {region : RegionIndex} {body : RegionOperations F}
    (hregion : (region, body) ∈ (indexedRegions operations 0).1) :
    body.LookupRelevantSelectorActivationsExact := by
  obtain ⟨name, hoperation⟩ :=
    exists_region_operation_of_mem_indexedRegions hregion
  exact List.forall_iff_forall_mem.mp hlaw
    (.region name body) hoperation

/-- Select the exact activation equivalence for one lookup selector leaf. -/
theorem RegionOperations.LookupRelevantSelectorActivationsExact.of_lookup
    {body : RegionOperations F}
    (hlaw : body.LookupRelevantSelectorActivationsExact)
    {argument : LookupArgument F} {enabled : List Selector} {row : ℕ}
    (hlookup :
      RegionOperation.enableLookup argument enabled row ∈ body)
    {expression : Expression F Query}
    (hexpression : expression ∈ argument.inputs)
    {selector : ℕ}
    (hselector : selector ∈ expression.selectorIndices) :
    SelectorEnabledAtIndex enabled selector ↔
      body.SelectorActivatedAt selector row := by
  have hoperation :=
    List.forall_iff_forall_mem.mp hlaw
      (.enableLookup argument enabled row) hlookup
  have hinput :=
    List.forall_iff_forall_mem.mp hoperation expression hexpression
  exact List.forall_iff_forall_mem.mp hinput selector hselector

/--
The region-local synthesis law, combined with V1's guarded placement, supplies the
exact global selector activation rows consumed by lookup projection.
-/
theorem Operations.LookupRelevantSelectorActivationsExact.placed
    {operations : Operations F}
    (hlaw : operations.LookupRelevantSelectorActivationsExact) :
    FloorPlanner.PlacedLookupSelectorRowsExact operations
      (FloorPlanner.V1.starts operations) := by
  apply FloorPlanner.V1.starts_placedLookupSelectorRowsExact_of_regionLaw
  intro region body hregion
  exact hlaw.of_region hregion

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
  circuit.toConstraintSystem () ()

/-- Queried instance columns, in their first-query order. -/
def publicInputColumns
    (circuit : FormalCircuit F Unit Config unit unit) :
    List (Column .instance) :=
  (constraintSystem circuit).queriedInstanceColumns

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
  /-- Synthesized lookup selector activations are represented exactly. -/
  lookupRelevantSelectorActivationsExact :
    let config := (formalCircuit.configure () {}).1
    Operations.LookupRelevantSelectorActivationsExact
      ((formalCircuit.synthesize config ()).operations 0)
  /-- Lookup inputs do not contain simple selectors. -/
  lookupInputsNoSimpleSelectors :
    let config := (formalCircuit.configure () {}).1
    Operations.LookupInputsNoSimpleSelectors
      ((formalCircuit.synthesize config ()).operations 0)
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

/-- The circuit-derived constraint system used by key generation: the configure result
closed under every gate and lookup enabled by this circuit's synthesis. -/
def constraintSystem (self : TopLevelCircuit F Config PublicInput) :
    ConstraintSystem F :=
  TopLevelCompilation.constraintSystem self.formalCircuit

/-- Public-input cells are distinct by construction from queried columns and prefixes. -/
theorem publicInputLayout_cells_injective
    (self : TopLevelCircuit F Config PublicInput) :
    Function.Injective self.publicInputLayout.cells := by
  apply self.publicInputLayout.cells_injective
  exact self.constraintSystem.queriedInstanceColumns_nodup

/-- Each public-input cell's column has a verifier query at some rotation. -/
theorem exists_rotation_mem_instanceQueries_of_publicInputLayout_cell
    (self : TopLevelCircuit F Config PublicInput)
    (i : Fin (size PublicInput)) :
    ∃ rotation,
      ((self.publicInputLayout.cells i).1, rotation) ∈
        self.constraintSystem.instanceQueries := by
  apply
    self.constraintSystem
      |>.exists_rotation_mem_instanceQueries_of_mem_queriedInstanceColumns
  exact self.publicInputLayout.cells_fst_mem_columns i

/-- The closed top-level operation stream. -/
def operations (self : TopLevelCircuit F Config PublicInput) : Operations F :=
  TopLevelCompilation.operations self.formalCircuit

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

/-- The total domain compiler leaves room for the full circuit footprint. -/
theorem usedRows_le_usableRowsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput) :
    self.usedRows ≤ self.usableRowsAt self.domainExponent := by
  simpa only [usedRows, usableRowsAt, domainExponent, blindingFactors,
    constraintSystem] using
    TopLevelCompilation.usedRows_le_usableRowsAt_domainExponent
      self.formalCircuit self.publicInputLayout

/-- Every public-input cell lies in the compiler-derived usable-row range. -/
theorem publicInputLayout_cells_snd_lt_usableRowsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput)
    (i : Fin (size PublicInput)) :
    (self.publicInputLayout.cells i).2 <
      self.usableRowsAt self.domainExponent :=
  (self.publicInputLayout_cells_snd_lt_usedRows i).trans_le
    self.usedRows_le_usableRowsAt_domainExponent

/-- The pinned constraint system derived solely from the closed circuit: the
projection of its synthesis-closed constraint system through its circuit-owned
selector map. -/
def pinnedCS (self : TopLevelCircuit F Config PublicInput) :
    PinnedConstraintSystem F :=
  PinnedConstraintSystem.derive self.constraintSystem self.selectorMap

/--
The circuit-owned pinned constraint system is exactly the projection using its
circuit-owned selector map.
-/
theorem pinnedCS_eq_derive
    (self : TopLevelCircuit F Config PublicInput) :
    self.pinnedCS =
      PinnedConstraintSystem.derive self.constraintSystem self.selectorMap :=
  rfl

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
    self.fixedRows.length =
      (PinnedConstraintSystem.derive
        self.constraintSystem self.selectorMap).numFixedColumns := by
  apply Layout.denseFixedColumns_length

/-- Every compiled fixed column spans the full evaluation domain. -/
theorem fixedRows_getD_length
    (self : TopLevelCircuit F Config PublicInput)
    (column : ℕ)
    (hcolumn :
      column <
        (PinnedConstraintSystem.derive
          self.constraintSystem self.selectorMap).numFixedColumns) :
    (self.fixedRows.getD column []).length =
      2 ^ self.domainExponent := by
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
  apply OperationsKeygenCoherent.closeWithOperations

/--
Every selector atom in a top-level circuit's lookup inputs is allocated by its
synthesis-closed constraint system.
-/
theorem lookupInputsAllocated
    (self : TopLevelCircuit F Config PublicInput) :
    ∀ argument ∈ self.constraintSystem.lookups,
      ∀ expression ∈ argument.inputs,
        expression.selectorBound ≤ self.constraintSystem.numSelectors := by
  exact ConstraintSystem.lookupInputsAllocated_closeWithOperations
    (self.formalCircuit.configure () {}).2
    (self.formalCircuit.toOperations () ())

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
