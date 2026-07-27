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
  let tableLengths := operations.filterMap fun operation =>
    match operation with
    | .loadTable _ loaded => some loaded.length
    | _ => none
  have hlength : values.length ∈ tableLengths := by
    apply List.mem_filterMap.mpr
    exact ⟨.loadTable table values, hload, rfl⟩
  have htable : values.length ≤ tableLengths.foldl max 0 :=
    member_le_foldl_max tableLengths values.length 0 hlength
  unfold Halo2.usedRows
  exact le_trans htable (Nat.le_max_right _ _)

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
    (Config : Type) (PublicInput : TypeMap) [ProvableType PublicInput] where
  cells : Config → Fin (size PublicInput) → Column .instance × ℕ

namespace PublicInputLayout

variable {F Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Read the public input from its declared instance cells. -/
def extract (self : PublicInputLayout Config PublicInput)
    (config : Config) (env : Environment F) : PublicInput F :=
  fromElements (Vector.ofFn fun i =>
    env.inst (self.cells config i).1 (self.cells config i).2)

/-- Associate each public-input element with its declared instance cell. -/
def assignments (self : PublicInputLayout Config PublicInput)
    (config : Config) (input : PublicInput F) :
    Vector ((Column .instance × ℕ) × F) (size PublicInput) :=
  Vector.ofFn fun i => (self.cells config i, (toElements input)[i])

theorem extract_eq
    (self : PublicInputLayout Config PublicInput)
    (config : Config) (env : Environment F) (input : PublicInput F)
    (hvalues : ∀ i,
      env.inst (self.cells config i).1 (self.cells config i).2 =
        (toElements input)[i]) :
    self.extract config env = input := by
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

def config
    (circuit : FormalCircuit F Unit Config unit unit) : Config :=
  (circuit.configure () {}).1

def constraintSystem
    (circuit : FormalCircuit F Unit Config unit unit) :
    ConstraintSystem F :=
  circuit.toConstraintSystem () ()

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
    (circuit : FormalCircuit F Unit Config unit unit) : ℕ :=
  Halo2.usedRows (operations circuit)

def domainExponent
    (circuit : FormalCircuit F Unit Config unit unit) : ℕ :=
  Halo2.minimalK (constraintSystem circuit) (operations circuit)

def selectorMap
    (circuit : FormalCircuit F Unit Config unit unit) : SelCompressMap :=
  deriveSelCompressMap (constraintSystem circuit)
    (2 ^ domainExponent circuit) (selectorActivations circuit)

/-- The canonical domain leaves room for the circuit's complete operation footprint. -/
theorem usedRows_le_usableRowsAt_domainExponent
    (circuit : FormalCircuit F Unit Config unit unit) :
    usedRows circuit ≤
      2 ^ domainExponent circuit -
        (constraintSystem circuit).blindingFactors - 1 := by
  have hfit :
      usedRows circuit + (constraintSystem circuit).blindingFactors + 1 ≤
        2 ^ domainExponent circuit := by
    exact (Nat.le_max_left _ _).trans
      (Halo2.minimalK_fits
        (constraintSystem circuit) (operations circuit))
  omega

def fixedAssignments
    (circuit : FormalCircuit F Unit Config unit unit) :
    List (Layout.FixedAssignment F) :=
  Layout.compileFixed
    (2 ^ domainExponent circuit -
      (constraintSystem circuit).blindingFactors - 1)
    (selectorMap circuit) (constraintSystem circuit) (operations circuit)

def fixedRows
    (circuit : FormalCircuit F Unit Config unit unit) : List (List F) :=
  Layout.denseFixedColumns
    (2 ^ domainExponent circuit)
    (PinnedConstraintSystem.derive
      (constraintSystem circuit) (selectorMap circuit)).numFixedColumns
    (fixedAssignments circuit)

def fixedValue
    (circuit : FormalCircuit F Unit Config unit unit)
    (column : Column .fixed) (row : ℤ) : F :=
  (fixedRows circuit).getD column.index [] |>.getD
    (row.natMod (2 ^ domainExponent circuit)) 0

def environment
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F) : Environment F where
  get column row :=
    match column.kind with
    | .advice => assignment.advice ⟨column.index⟩ row
    | .fixed => fixedValue circuit ⟨column.index⟩ row
    | .instance => assignment.inst ⟨column.index⟩ row
  usableRows :=
    2 ^ domainExponent circuit -
      (constraintSystem circuit).blindingFactors - 1

@[simp] theorem environment_advice
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F)
    (column : Column .advice) (row : ℤ) :
    (environment circuit assignment).advice column row =
      assignment.advice column row :=
  rfl

@[simp] theorem environment_fixed
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F)
    (column : Column .fixed) (row : ℤ) :
    (environment circuit assignment).fixed column row =
      fixedValue circuit column row := by
  simp only [Environment.fixed, environment, Column.toAny]

@[simp] theorem environment_inst
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F)
    (column : Column .instance) (row : ℤ) :
    (environment circuit assignment).inst column row =
      assignment.inst column row :=
  rfl

@[simp] theorem environment_usableRows
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F) :
    (environment circuit assignment).usableRows =
      2 ^ domainExponent circuit -
        (constraintSystem circuit).blindingFactors - 1 :=
  rfl

def placedEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F) : Placed Environment F :=
  ⟨placement circuit, environment circuit assignment⟩

def proverEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    ProverEnvironment F where
  toEnvironment := environment circuit assignment
  hint := hint

def placedProverEnvironment
    (circuit : FormalCircuit F Unit Config unit unit)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    Placed ProverEnvironment F :=
  ⟨placement circuit, proverEnvironment circuit assignment hint⟩

end TopLevelCompilation

/-- A closed formal circuit together with its public/private witness boundary. -/
structure TopLevelCircuit
    (F : Type) [FiniteField F]
    (Config : Type) (PublicInput : TypeMap)
    [ProvableType PublicInput] where
  /-- The underlying unit-config-input, unit-input, unit-output formal circuit. -/
  formalCircuit : FormalCircuit F Unit Config unit unit
  /-- The instance cells containing the public input. -/
  publicInputLayout : PublicInputLayout Config PublicInput
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
        (publicInputLayout.extract config env.env)
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
        (TopLevelCompilation.placedEnvironment formalCircuit assignment)

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
  TopLevelCompilation.usedRows self.formalCircuit

/-- The smallest keygen domain exponent derived from this circuit. -/
def domainExponent (self : TopLevelCircuit F Config PublicInput) : ℕ :=
  TopLevelCompilation.domainExponent self.formalCircuit

/-- The selector-compression map derived from this circuit and its fitting domain. -/
def selectorMap
    (self : TopLevelCircuit F Config PublicInput) : SelCompressMap :=
  TopLevelCompilation.selectorMap self.formalCircuit

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
      self.formalCircuit

/-- All circuit-derived fixed-cell assignments, before dense row expansion. -/
def fixedAssignments
    (self : TopLevelCircuit F Config PublicInput) :
    List (Layout.FixedAssignment F) :=
  TopLevelCompilation.fixedAssignments self.formalCircuit

/-- The dense fixed columns compiled canonically from the top-level circuit. -/
def fixedRows
    (self : TopLevelCircuit F Config PublicInput) : List (List F) :=
  TopLevelCompilation.fixedRows self.formalCircuit

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
  TopLevelCompilation.fixedValue self.formalCircuit column row

/--
Construct the complete semantic environment from exactly the proof-varying assignment.
Fixed values and usable rows are circuit-derived and cannot be supplied independently.
-/
def environment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) : Environment F :=
  TopLevelCompilation.environment self.formalCircuit assignment

/-- The canonical environment paired with the circuit-owned V1 placement. -/
def placedEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) : Placed Environment F :=
  TopLevelCompilation.placedEnvironment self.formalCircuit assignment

/-- Add prover-only hints to the canonical proof assignment. -/
def proverEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    ProverEnvironment F :=
  TopLevelCompilation.proverEnvironment self.formalCircuit assignment hint

/-- The canonical prover environment paired with circuit-owned placement. -/
def placedProverEnvironment
    (self : TopLevelCircuit F Config PublicInput)
    (assignment : ProofAssignment F) (hint : ProverHint F) :
    Placed ProverEnvironment F :=
  TopLevelCompilation.placedProverEnvironment
    self.formalCircuit assignment hint

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
      self.formalCircuit assignment column row

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
  self.publicInputLayout.extract self.config env

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
      (self.publicInputLayout.extract
        (self.formalCircuit.configure () {}).1 env.env)
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
