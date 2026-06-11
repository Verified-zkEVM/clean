import Clean.Orchard.Poseidon.Pow5

/-!
# Orchard Poseidon sponge APIs

This module mirrors `halo2_gadgets/src/poseidon.rs` around `Sponge`,
`poseidon_sponge`, and `PoseidonSpongeInstructions`.

The source-level implementation is intentionally not added yet.  The next step is to
port the width-3/rate-2 `initial_state` and `add_input` APIs without exposing internal
permutation rows or hash boundary values as caller inputs.
-/

namespace Orchard
namespace Poseidon
namespace Sponge

/-- Placeholder namespace for the source-level Poseidon sponge state machine. -/
def sourceFile : String := "halo2_gadgets/src/poseidon.rs"

end Sponge
end Poseidon
end Orchard
