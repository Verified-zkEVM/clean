import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem round27Relocates (offset : Nat) :
    WitnessErasure.operations (round27Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round27Operations 0)) := by
  sha256_witness_unfold round27
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
