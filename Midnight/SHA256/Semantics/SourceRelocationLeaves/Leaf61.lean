import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand57Relocates (offset : Nat) :
    WitnessErasure.operations (expand57Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand57Operations 0)) := by
  sha256_witness_unfold expand57
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
