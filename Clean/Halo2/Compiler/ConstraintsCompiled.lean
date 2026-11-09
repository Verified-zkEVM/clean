import Clean.Halo2.TopLevel
import Clean.Halo2.Compiler.CompiledGates
import Clean.Halo2.Compiler.CompiledCopies
import Clean.Halo2.Compiler.CompiledLookups

/-! # Semantic soundness of the Halo2 compiler

Compiled gate vanishing, copy equality, and lookup membership establish the source
constraints and hence the specification for the extracted witness.
-/

variable {F : Type} [FiniteField F]

namespace Halo2.TopLevelCircuit

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)

/-- Extract the witness used by the circuit specification. No secrecy is assumed. -/
def extractWitness (assignment : ProofAssignment F) : top.PrivateWitness :=
  top.extractPrivate top.config (top.placedEnvironment assignment)

end Halo2.TopLevelCircuit

/-! ## Compiled constraints

The public boundary consists of compiled gate evaluations, resolved copy equality,
and tuple membership at compiled lookup activations. Selector compression, query
indexing, placement, and constant allocation are discharged internally. Fixed
assignments are already true in the circuit-owned environment.
-/

namespace Halo2.TopLevelCircuit

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Row-level satisfaction of the circuit's compiled constraints. -/
structure ConstraintsCompiled (assignment : ProofAssignment F) : Prop where
  gates : top.GatesCompiled assignment
  copies : top.CopiesCompiled assignment
  lookups : top.LookupsCompiled assignment

/-- Compiler semantics imply source constraints, including circuit-owned fixed data. -/
theorem constraints_of_compiled [FieldDomainParams F] [CircuitFieldSupport top]
    (assignment : ProofAssignment F) (h : top.ConstraintsCompiled assignment) :
    Constraints top.placement (top.environment assignment) top.operations 0 := by
  rw [CircuitConstraintFamily.constraints_iff_families]
  exact ⟨top.gate_constraints_of_compiled assignment h.gates,
    top.copy_constraints_of_compiled assignment h.copies,
    top.lookup_constraints_of_compiled assignment h.lookups,
    top.fixed_constraints assignment⟩

/-- Compiled satisfaction proves the circuit specification for its extracted witness
and public input, without exposing source operations or compiler transformations. -/
theorem soundness_compiled [FieldDomainParams F] [CircuitFieldSupport top]
    (assignment : ProofAssignment F) (h : top.ConstraintsCompiled assignment) :
    top.Spec (top.extractPublicInput (top.environment assignment))
      (top.extractWitness assignment) :=
  top.soundness assignment (top.constraints_of_compiled assignment h)

end Halo2.TopLevelCircuit
