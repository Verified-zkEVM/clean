import Clean.Orchard.Poseidon.Pow5.Constants
import Clean.Orchard.Poseidon.Pow5
import Clean.Orchard.Poseidon.Sponge
import Clean.Orchard.Poseidon.Hash

/-!
# Orchard Poseidon

Source-shaped Orchard Poseidon module tree.

The file structure mirrors `halo2_gadgets/src/poseidon.rs` and
`halo2_gadgets/src/poseidon/pow5.rs`:

- `Clean.Orchard.Poseidon.Pow5.Constants` contains the concrete Pallas constants from
  `halo2_poseidon/src/fp.rs`.
- `Clean.Orchard.Poseidon.Pow5` contains the `Pow5Chip` gate-level and entry-level
  circuits from `poseidon/pow5.rs`.
- `Clean.Orchard.Poseidon.Sponge` is reserved for `poseidon.rs` sponge helpers and
  `PoseidonSpongeInstructions`-level APIs.
- `Clean.Orchard.Poseidon.Hash` is reserved for the source-level `Hash::init` and
  `Hash::hash` APIs.

Gate assertions live under `.Gate`, e.g. `Orchard.Poseidon.FullRound.Gate.circuit`,
while source-shaped row entry points live under the permutation namespace as
`Permute.FullRound.circuit` and `Permute.PartialRounds.circuitP128`.
-/
