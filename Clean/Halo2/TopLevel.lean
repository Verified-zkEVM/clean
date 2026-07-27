import Clean.Halo2.Keygen.PinnedCs

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

/--
Generic well-formedness facts supplied by successful synthesis/layout rather than by
the proof's constraint polynomials.

The first required fact is table fit: every declared table's explicit block lies in
the usable rows.  Further compiler invariants (for example region bounds) belong in
this same structure when the operation semantics begins consuming them.
-/
structure SynthesisWellFormed
    {F : Type} [FiniteField F]
    (env : Environment F) (operations : Operations F) : Prop where
  tablesFit :
    ∀ (table : TableColumn) (values : List F),
      .loadTable table values ∈ operations →
      values.length ≤ env.usableRows

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
  cells_injective : ∀ config, Function.Injective (cells config)

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

/--
A closed formal circuit together with its public/private witness boundary.

Configuration and synthesis inputs and the circuit output are all unit.  The public
input occupies declared instance cells; the remaining witness is extracted
separately.  `extract_factorization` connects this boundary to the formal circuit's
native witness extraction, while `spec_iff` connects the top-level specification to
the formal circuit's specification.

The two closure fields correspond to the verifier and honest-prover views.  They are
separate because `Constraints` and `ExtendsWitnesses` expose the fixed/table data
through different predicates.
-/
structure TopLevelCircuit
    (F : Type) [FiniteField F]
    (Config : Type) (PublicInput : TypeMap)
    [ProvableType PublicInput] where
  formalCircuit : FormalCircuit F Unit Config unit unit
  publicInputLayout : PublicInputLayout Config PublicInput
  PrivateWitness : Type
  extractPrivate :
    Config → RegionIndex → Placed Environment F → PrivateWitness
  combine :
    PublicInput F → PrivateWitness → formalCircuit.Witness F
  Spec : PublicInput F → PrivateWitness → Prop
  spec_iff :
    ∀ publicInput privateWitness,
      Spec publicInput privateWitness ↔
        formalCircuit.Spec () () (combine publicInput privateWitness)
  extract_factorization :
    let config := (formalCircuit.configure () {}).1
    ∀ (i : RegionIndex) (env : Placed Environment F),
      combine
        (publicInputLayout.extract config env.env)
        (extractPrivate config i env) =
      formalCircuit.extract config () i env
  assumptions_eq : formalCircuit.Assumptions = fun _ => True
  lookupRelevantSelectorActivationsExact :
    let config := (formalCircuit.configure () {}).1
    Operations.LookupRelevantSelectorActivationsExact
      ((formalCircuit.synthesize config ()).operations 0)
  lookupInputsNoSimpleSelectors :
    let config := (formalCircuit.configure () {}).1
    Operations.LookupInputsNoSimpleSelectors
      ((formalCircuit.synthesize config ()).operations 0)
  closesEnvironmentSoundness :
    let config := (formalCircuit.configure () {}).1
    ∀ (i : RegionIndex) (env : Placed Environment F),
      SynthesisWellFormed env.env
        ((formalCircuit.synthesize config ()).operations i) →
      Constraints env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env
  closesEnvironmentCompleteness :
    let config := (formalCircuit.configure () {}).1
    ∀ (i : RegionIndex) (env : Placed ProverEnvironment F),
      SynthesisWellFormed env.toEnvironment.env
        ((formalCircuit.synthesize config ()).operations i) →
      ExtendsWitnesses env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env.toEnvironment

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- The configuration produced by the top-level circuit's own configure run. -/
def config (self : TopLevelCircuit F Config PublicInput) : Config :=
  (self.formalCircuit.configure () {}).1

/-- The circuit-derived constraint system used by key generation: the configure result
closed under every gate and lookup enabled by this circuit's synthesis. -/
def constraintSystem (self : TopLevelCircuit F Config PublicInput) :
    ConstraintSystem F :=
  self.formalCircuit.toConstraintSystem () ()

/-- The closed top-level operation stream. -/
def operations (self : TopLevelCircuit F Config PublicInput)
    (i : RegionIndex := 0) : Operations F :=
  (self.formalCircuit.synthesize self.config ()).operations i

/--
The circuit-side static premise needed to connect synthesized gate and lookup
activations to the pinned constraint system derived from `configure`.
-/
def KeygenCoherent
    (self : TopLevelCircuit F Config PublicInput) : Prop :=
  OperationsKeygenCoherent self.constraintSystem (self.operations 0)

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
    (i : RegionIndex) (env : Placed Environment F) : self.PrivateWitness :=
  self.extractPrivate self.config i env

/-- The externally visible statement: some private witness satisfies the circuit spec. -/
def Statement (self : TopLevelCircuit F Config PublicInput)
    (publicInput : PublicInput F) : Prop :=
  ∃ privateWitness, self.Spec publicInput privateWitness

/--
Generic verifier-side top-level soundness.  The public theorem consumes successful
synthesis/layout and the circuit constraints, but no circuit-specific environment or
input assumption.
-/
theorem soundness
    (self : TopLevelCircuit F Config PublicInput)
    (i : RegionIndex) (env : Placed Environment F)
    (hwellFormed : SynthesisWellFormed env.env (self.operations i))
    (hconstraints : Constraints env.place env.env (self.operations i) i) :
    self.Spec
      (self.extractPublicInput env.env)
      (self.extractPrivateWitness i env) := by
  apply (self.spec_iff _ _).mpr
  unfold extractPublicInput extractPrivateWitness config
  rw [self.extract_factorization]
  apply self.formalCircuit.soundness self.config i env ()
  · exact self.closesEnvironmentSoundness i env hwellFormed hconstraints
  · rw [self.assumptions_eq]
    trivial
  · exact hconstraints

/-- A satisfying assignment establishes the external statement for its public input. -/
theorem statement_soundness
    (self : TopLevelCircuit F Config PublicInput)
    (i : RegionIndex) (env : Placed Environment F)
    (hwellFormed : SynthesisWellFormed env.env (self.operations i))
    (hconstraints : Constraints env.place env.env (self.operations i) i) :
    self.Statement (self.extractPublicInput env.env) :=
  ⟨self.extractPrivateWitness i env,
    self.soundness i env hwellFormed hconstraints⟩

/--
Generic honest-prover top-level completeness.  As on the verifier side, successful
synthesis/layout closes the environment contract internally.
-/
theorem completeness
    (self : TopLevelCircuit F Config PublicInput)
    (i : RegionIndex) (env : Placed ProverEnvironment F)
    (hwitnesses : ExtendsWitnesses env.place env.env (self.operations i) i)
    (hwellFormed : SynthesisWellFormed env.toEnvironment.env (self.operations i))
    (hprover : self.formalCircuit.ProverAssumptions
      (eval env (show Var unit F from ()))
      (self.formalCircuit.extract self.config () i env.toEnvironment)
      env.env.hint) :
    Constraints env.place env.toEnvironment.env (self.operations i) i ∧
      self.formalCircuit.ProverSpec
        (eval env (show Var unit F from ()))
        (eval env (self.formalCircuit.output self.config () i))
        (self.formalCircuit.extract self.config () i env.toEnvironment)
        env.env.hint := by
  apply self.formalCircuit.completeness self.config i env ()
  · exact hwitnesses
  · exact self.closesEnvironmentCompleteness i env hwellFormed hwitnesses
  · rw [self.assumptions_eq]
    trivial
  · exact hprover

end TopLevelCircuit

end Halo2
