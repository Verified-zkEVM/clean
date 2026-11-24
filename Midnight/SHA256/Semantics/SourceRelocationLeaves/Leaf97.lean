import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem round29Relocates (offset : Nat) :
    WitnessErasure.operations (round29Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round29Operations 0)) := by
  sha256_witness_unfold round29
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
