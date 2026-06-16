import Clean.Orchard.Action.CommitIvkGate

/-!
# Orchard incoming viewing key commitment

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `gadgets::commit_ivk`

The custom arithmetic gate lives in `Orchard.Action.CommitIvk.Gate`.
-/

namespace Orchard.Action.CommitIvk

/-!
TODO(source-conformance): `gadgets::commit_ivk` is not implemented.

The replacement should construct the `CommitIvk` message/canonicity gate, call
`CommitDomain::short_commit`, wire returned running sums into the canonicity gate,
witness `[rivk] CommitIvkR` internally, and return the extracted x-coordinate as `ivk`.
-/

end Orchard.Action.CommitIvk
