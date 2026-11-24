import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand20Relocates (offset : Nat) :
    WitnessErasure.operations (expand20Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand20Operations 0)) := by
  sha256_witness_unfold expand20
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
