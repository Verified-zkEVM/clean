import Midnight.SHA256.Admission.SourceCopies
import Midnight.SHA256.Admission.Physical
import Midnight.SHA256.Admission.Erasure
import Midnight.SHA256.Semantics.Formal

/-! Closed `CertifiedCircuit.Certificate` for the SHA-256 preimage assertion: configuration,
fixed layout, copy provenance and bounds, and every operation/activation obligation. No runtime
check or captured layout is assumed. -/
namespace Midnight.SHA256.Admission
open Halo2 Midnight.Chips
attribute [local irreducible] configured cleanGates cleanLookups Synthesis.operations
  Semantics.Preimage.assertion Semantics.Preimage.circuit WitnessCircuit.preimageCircuit

def source_certificate : CertifiedCircuit.Certificate configured
    (Synthesis.operations activation) 13 .simple where
  configuration := configuration
  rows := minimumRows
  layout := Physical.certificate
  copies := by
    change CopyLawful.Lawful _ checked.toCleanDelta.gates checked.toCleanDelta.lookups _ _ _ _ _
    rw [gates, lookups, usableRows, constantColumn]
    exact source_copies
  operations := by
    change OperationsLawful.Lawful _ checked.toCleanDelta.gates checked.toCleanDelta.lookups _ _ _
    rw [gates, lookups, usableRows, constantColumn]
    exact source_operations

theorem assertion_erased :
    WitnessErasure.operations (Semantics.Preimage.assertion.operations 0) =
      Synthesis.operations activation := by
  rw [Semantics.Preimage.assertion_operations]
  unfold Semantics.Preimage.circuit
  exact WitnessErasure.preimage_operations_eq_source Semantics.Preimage.privatePrograms

/-- Admission of the actual private-hint assertion, retaining its witness IR. -/
def native_certificate : CertifiedCircuit.Certificate configured
    (Semantics.Preimage.assertion.operations 0) 13 .simple :=
  Erasure.certificate configured (Semantics.Preimage.assertion.operations 0) 13
    (assertion_erased.symm ▸ source_certificate)

theorem native_admission : Nonempty (CertifiedCircuit.Certificate configured
    (Semantics.Preimage.assertion.operations 0) 13 .simple) := ⟨native_certificate⟩

/-- Every SHA lookup is owned and reads table columns that `loadTable` fills. -/
theorem lookupsStated {ops : Operations F}
    (tables : OperationsLawful.tableColumns ops = [11, 12, 13, 14, 15]) :
    configured.lookups.toList.all (·.stated ops) = true := by
  simp only [Keygen.BatchedLookup.stated, tables]
  decide +kernel

/-- The SHA source has no `rows` gate and only stated lookups, so on a stream loading its tables
`Constraints` is the whole of Rust's vanishing argument. -/
theorem satisfied {ops : Operations F} {k : Nat} {place : RegionIndex → Nat} {env : Environment F}
    (tables : OperationsLawful.tableColumns ops = [11, 12, 13, 14, 15])
    (constraints : Constraints place env ops 0) : CertifiedCircuit.Satisfied configured ops k place env :=
  ⟨constraints, CertifiedCircuit.RowGatesHold.of_owned gatesOwned ops k env,
    CertifiedCircuit.RowLookupsHold.of_stated (lookupsStated tables) k env⟩

end Midnight.SHA256.Admission
