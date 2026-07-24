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

/--
A configured, unit-input formal circuit whose verifier assumptions are exactly
`True`, and whose own successful synthesis discharges its compositional environment
requirements.

The two closure fields correspond to the verifier and honest-prover views.  They are
separate because `Constraints` and `ExtendsWitnesses` expose the fixed/table data
through different predicates.
-/
structure TopLevelCircuit
    (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Output : TypeMap)
    [CircuitType Output] where
  formalCircuit : FormalCircuit F ConfigInput Config unit Output
  configInput : ConfigInput
  assumptions_eq : formalCircuit.Assumptions = fun _ => True
  closesEnvironmentSoundness :
    let config := (formalCircuit.configure configInput {}).1
    ∀ (i : RegionIndex) (env : Placed Environment F),
      SynthesisWellFormed env.env
        ((formalCircuit.synthesize config ()).operations i) →
      Constraints env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env
  closesEnvironmentCompleteness :
    let config := (formalCircuit.configure configInput {}).1
    ∀ (i : RegionIndex) (env : Placed ProverEnvironment F),
      SynthesisWellFormed env.toEnvironment.env
        ((formalCircuit.synthesize config ()).operations i) →
      ExtendsWitnesses env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env.toEnvironment

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- The configuration produced by the top-level circuit's own configure run. -/
def config (self : TopLevelCircuit F ConfigInput Config Output) : Config :=
  (self.formalCircuit.configure self.configInput {}).1

/-- The circuit-derived constraint system used by key generation: the configure result
closed under every gate and lookup enabled by this circuit's synthesis. -/
def constraintSystem (self : TopLevelCircuit F ConfigInput Config Output) :
    ConstraintSystem F :=
  self.formalCircuit.toConstraintSystem self.configInput ()

/-- The closed top-level operation stream. -/
def operations (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex := 0) : Operations F :=
  (self.formalCircuit.synthesize self.config ()).operations i

/--
The circuit-side static premise needed to connect synthesized gate and lookup
activations to the pinned constraint system derived from `configure`.
-/
def KeygenCoherent
    (self : TopLevelCircuit F ConfigInput Config Output) : Prop :=
  OperationsKeygenCoherent self.constraintSystem (self.operations 0)

/-- Configure/synthesis registration coherence follows from the circuit-derived
constraint system; it is not a separate top-level circuit obligation. -/
theorem keygenCoherent
    (self : TopLevelCircuit F ConfigInput Config Output) :
    self.KeygenCoherent := by
  apply OperationsKeygenCoherent.closeWithOperations

/--
Every selector atom in a top-level circuit's lookup inputs is allocated by its
synthesis-closed constraint system.
-/
theorem lookupInputsAllocated
    (self : TopLevelCircuit F ConfigInput Config Output) :
    ∀ argument ∈ self.constraintSystem.lookups,
      ∀ expression ∈ argument.inputs,
        expression.selectorBound ≤ self.constraintSystem.numSelectors := by
  exact ConstraintSystem.lookupInputsAllocated_closeWithOperations
    (self.formalCircuit.configure self.configInput {}).2
    (self.formalCircuit.toOperations self.configInput ())

/-- The semantic statement extracted from a placed satisfying assignment. -/
def Statement (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex) (env : Placed Environment F) : Prop :=
  self.formalCircuit.Spec
    (eval env (show Var unit F from ()))
    (eval env (self.formalCircuit.output self.config () i))
    (self.formalCircuit.extract self.config () i env)

/--
Generic verifier-side top-level soundness.  The public theorem consumes successful
synthesis/layout and the circuit constraints, but no circuit-specific environment or
input assumption.
-/
theorem soundness
    (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex) (env : Placed Environment F)
    (hwellFormed : SynthesisWellFormed env.env (self.operations i))
    (hconstraints : Constraints env.place env.env (self.operations i) i) :
    self.Statement i env := by
  apply self.formalCircuit.soundness self.config i env ()
  · exact self.closesEnvironmentSoundness i env hwellFormed hconstraints
  · rw [self.assumptions_eq]
    trivial
  · exact hconstraints

/--
Generic honest-prover top-level completeness.  As on the verifier side, successful
synthesis/layout closes the environment contract internally.
-/
theorem completeness
    (self : TopLevelCircuit F ConfigInput Config Output)
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
