import Clean.Orchard.Poseidon.Pow5
import Clean.Orchard.Poseidon.Sponge
import Clean.Orchard.Poseidon.Hash

/-!
# Orchard Poseidon

Source-shaped Orchard Poseidon module tree.

The file structure mirrors `halo2_gadgets/src/poseidon.rs` and
`halo2_gadgets/src/poseidon/pow5.rs`:

- `Clean.Orchard.Poseidon.Pow5` contains the `Pow5Chip` gate-level and entry-level
  circuits from `poseidon/pow5.rs`.
- `Clean.Orchard.Poseidon.Sponge` is reserved for `poseidon.rs` sponge helpers and
  `PoseidonSpongeInstructions`-level APIs.
- `Clean.Orchard.Poseidon.Hash` is reserved for the source-level `Hash::init` and
  `Hash::hash` APIs.

The existing gate modules remain available at their old names, e.g.
`Orchard.Poseidon.FullRound.circuit`, through the `Pow5` import.
-/
