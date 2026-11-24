import LoweringFixtures.Common

/-! The SHA-256 baseline. `MidnightVK`'s `nb_public_inputs` is what the native chip counted
(interface.rs:434, native_chip.rs:524), one per layouter instance copy on column 1, so Lean derives
it from the stream (32) and Rust's half counts the same copies: `ShaPreImageCircuitVk`. -/
namespace LoweringFixtures.PublicInputs
open Halo2 Midnight.Keygen

def fixture : Midnight.Export.Replay.Fixture := sha

/-- The rows of the stream's layouter instance copies on instance column 1. -/
def publicRows : List Nat := sha.ops.filterMap fun
  | .constrainInstance _ column row => if column.index == 1 then some row else none
  | _ => none

#guard publicRows == List.range 32
#guard publicInputCount sha.ops == 32

end LoweringFixtures.PublicInputs
