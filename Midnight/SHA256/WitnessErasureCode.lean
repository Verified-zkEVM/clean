import Midnight.SHA256.Semantics.WitnessErasureComposition

/-! Closed lossless comparison, kept above the reusable structural encoding. -/
namespace Midnight.SHA256.WitnessErasure
open Halo2

/-- Closed structural equality checked by the Lean kernel. The code retains
actual configured gate/lookup objects, all fixed/table values and ordered copies;
it discards precisely the advice program. There is no native-decision axiom. -/
theorem reference_code :
    ((WitnessCircuit.preimageCircuit referenceInput).operations).map Code.encode =
      (Synthesis.operations SHA256.activation).map Code.encode :=
  Semantics.WitnessErasureCheckpoints.reference_code

end Midnight.SHA256.WitnessErasure
