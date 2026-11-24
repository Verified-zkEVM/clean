import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

set_option cbv.maxSteps 200000
sha256_relocation_reduction in

theorem round57Relocates (offset : Nat) :
    WitnessErasure.operations (round57Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round57Operations 0)) := by
  sha256_witness_unfold round57
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
