import Clean.Orchard.Poseidon.Sponge

/-!
# Orchard Poseidon hash APIs

This module mirrors `halo2_gadgets/src/poseidon.rs::Hash`.

The source-level `Hash::init` and `Hash::hash` circuits should eventually compose the
sponge APIs from `Clean.Orchard.Poseidon.Sponge`, including the constant-length padding
schedule used by Orchard's `P128Pow5T3` nullifier hash.
-/

namespace Orchard
namespace Poseidon
namespace Hash

/-- Placeholder namespace for the source-level Poseidon hash API. -/
def sourceFile : String := "halo2_gadgets/src/poseidon.rs"

end Hash
end Poseidon
end Orchard
