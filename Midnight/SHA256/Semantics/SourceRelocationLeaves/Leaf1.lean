import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem initialRelocates (offset : Nat) :
    WitnessErasure.operations (initialOperations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (initialOperations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
