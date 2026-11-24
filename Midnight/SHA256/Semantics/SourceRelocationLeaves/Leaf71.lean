import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem round3Relocates (offset : Nat) :
    WitnessErasure.operations (round3Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round3Operations 0)) := by
  sha256_witness_unfold round3
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
