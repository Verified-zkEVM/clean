import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem inputRelocates (offset : Nat) :
    WitnessErasure.operations (inputOperations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (inputOperations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
