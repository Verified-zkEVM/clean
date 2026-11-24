import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

set_option cbv.maxSteps 200000
sha256_relocation_reduction in

theorem round48Relocates (offset : Nat) :
    WitnessErasure.operations (round48Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round48Operations 0)) := by
  sha256_witness_unfold round48
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
