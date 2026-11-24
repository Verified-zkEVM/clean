import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand16Relocates (offset : Nat) :
    WitnessErasure.operations (expand16Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand16Operations 0)) := by
  sha256_witness_unfold expand16
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
