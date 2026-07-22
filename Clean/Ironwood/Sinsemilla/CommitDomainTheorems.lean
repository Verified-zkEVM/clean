import Clean.Ironwood.Sinsemilla.ChainTheorems
import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.AddTheorems

/-!
# Sinsemilla commit domain

Reference: `halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`.

- `CommitDomain::commit`: `M.hash_to_point(msg) + [r] R`, with the blinding term a
  full-width fixed-base multiplication and the sum a complete addition. The output keeps
  the per-piece running sums `zs` (halo2's `commit` returns `(Point, Vec<RunningSum>)`),
  read by `NoteCommit`/`CommitIvk` for their canonicity gates.
- `CommitDomain::blinding_factor` is the bare `[r] R`, i.e. exactly
  `MulFixed.FullWidth.circuit R`.

`HashDomain::hash` and `CommitDomain::short_commit` (both `hash_to_point`/`commit`
followed by `x`-extraction) are realized inline where Orchard needs them — `MerkleCRH`
extracts `x` in `Merkle.HashLayer`, and `commit_ivk` extracts `x` after `commit` — so
they have no standalone gadget here.

The domain constants (`Q`, the generator table, the blinding base `R`) are abstract
parameters with the properties the proofs need (`Q.OnCurve`, `Generators.S_ne_zero`,
`FixedBase`).
-/

namespace Zcash.Circuits.Sinsemilla

open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Specs.Sinsemilla (Generators)
open Ecc

/-! ### `CommitDomain::commit` -/

namespace CommitDomain

end CommitDomain

end Zcash.Circuits.Sinsemilla
