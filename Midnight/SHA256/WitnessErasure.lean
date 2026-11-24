import Midnight.SHA256.WitnessErasureCore
import Midnight.SHA256.WitnessErasureCode
import Midnight.SHA256.Semantics.StructuralComposition

/-! Closed source identities for the real witness circuit, using the generic
advice-only erasure and the exact lossless reference comparison. -/
namespace Midnight.SHA256.WitnessErasure
open Halo2

theorem reference_operations :
    operations ((WitnessCircuit.preimageCircuit referenceInput).operations) =
      Synthesis.operations SHA256.activation := by
  have h := congrArg (List.map Code.decode) reference_code
  rw [Code.decode_encode_operations, Code.decode_encode_operations,
    source_operations_fixedpoint] at h
  exact h

/-- Exact universal keygen identity: for every collection of 24 input programs,
erasing only advice computations yields `Synthesis.operations`, the keygen
schedule ported from Rust. This equality includes full gate/lookup expressions, every fixed/table
value, all named regions and the ordered copy stream. -/
theorem preimage_operations_eq_source (input : Vector (WitgenIR F 1) 24) :
    operations ((WitnessCircuit.preimageCircuit input).operations) =
      Synthesis.operations SHA256.activation :=
  (preimage_operations_independent input referenceInput 0).trans reference_operations

open Semantics
attribute [local irreducible] Synthesis.schedule Synthesis.synthesize
  WitnessCircuit.synthesize WitnessCheckpoints.bodyOperations
  WitnessCheckpoints.publicOperations WitnessCheckpoints.preimageOperations
  WitnessErasureCheckpoints.observe WitnessErasureCheckpoints.fullChunk
  StructuralComposition.fullChunk

end Midnight.SHA256.WitnessErasure
