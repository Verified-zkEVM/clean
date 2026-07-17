import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.MulFixed.Short
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain

/-!
# Sinsemilla commit domain (Ironwood)

Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`
- `CommitDomain::commit` (`sinsemilla.rs:488-509`):
  ```
  let (blind, _) = self.R.mul(layouter.namespace(|| "[r] R"), r)?;   // 501
  let (p, zs)    = self.M.hash_to_point(layouter.namespace(|| "M"), message)?;  // 502
  let commitment = p.add(layouter.namespace(|| "M + [r] R"), &blind)?;          // 503
  Ok((commitment, zs))
  ```
  i.e. `commit(msg, r) = hash_to_point(Q, msg) + [r]·R`, keeping the per-piece running
  sums `zs` (`NoteCommit`/`CommitIvk` read individual `zs[i][j]` cells).
- `CommitDomain::blinding_factor` (`sinsemilla.rs:471-486`) is the bare `[r]·R`.

## The `[r]R` leg — Rust→Lean resolution (the stated boundary)

`R : ecc::FixedPoint<C, EccChip>` (`sinsemilla.rs:417`), and `self.R.mul(..)` (`sinsemilla.rs:501`)
resolves to `FixedPoint::mul` — **full-width fixed-base scalar multiplication**. In the phase-one
donor (`Clean/Orchard/Sinsemilla/CommitDomain.lean`) this is `MulFixed.FullWidth.circuit R`.

**`MulFixed` is NOT ported to the Ironwood (region-level) tree** (only the phase-one
`GeneralFormalCircuit` form exists). Per the slice's hard rule, the `[r]R` leg is therefore a
**stated boundary**: the composition structure is real, but the fixed-base child is carried as an
*abstract* `FormalRegionCircuit` parameter `blind` with its interface pinned (via the
`blind_*_eq` projection hypotheses) to the exact contract a ported `MulFixed.FullWidth` would
expose (output on-curve/valid, `output = r • R`). When `MulFixed.FullWidth` lands in Ironwood,
these hypotheses are discharged by that gadget's bundle; the CommitDomain composition above it
needs no change.

## Donor lifting

Value algebra (`Chain.PieceChunks`, `Chain.ZsFacts`, `Chain.honestChunks`, `Chain.PieceBounds`)
is reused from `Clean/Ironwood/Sinsemilla/Chain.lean` (itself donor-lifted). The `Spec` /
`ProverAssumptions` mirror the donor `CommitDomain.*`, re-expressed over the region-level
`Chain.circuit` output (which exposes the full `zs` HVec + the message's first double-and-add row).

## The `Q`-seed wrapper

The Ironwood `Chain.circuit` enters at an accumulator `(xA, yA)` seeded from the domain point `Q`
(its `Spec` quantifies `∀ A, A.OnCurve → A.x = input.xA → 2·A.y = enterYA → …`). The wrapper
assigns `Q`'s coordinates into the entering cells (constrained-constant, so soundness pins `A = Q`)
before the `Chain.circuit` call.
-/

namespace Halo2.Ironwood.Sinsemilla.CommitDomain

open Orchard (Point Fq)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Specs.Sinsemilla (Generators hashToPoint)
open Orchard.Specs (K)
open Orchard.Sinsemilla (HVec)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Halo2.Ironwood.Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded)
open Halo2.Ironwood.Sinsemilla.Chain
  (zLengths PieceChunks ZsFacts honestChunks PieceBounds ZsHonest pieceChunks_bound
   pieceChunks_honestChunks)

/-! ## Config

The parent config bundles the shared `Chain`/`HashPiece.Config` (the hash leg), the `Ecc.Add`
child config (the final sum), the blinding child's config `BCfg`, and the constant-seed columns
for `Q`. -/

/-- The `commit` config, parameterized by the blinding child's config type `BCfg`: the hash leg's
`HashPiece.Config`, the complete-addition child's `Add.Config`, the blinding child's config, and
the constant-seed columns for `Q`. -/
structure Config (BCfg : Type) where
  hashConfig : HashPiece.Config
  addConfig : Ecc.Add.Config
  blindConfig : BCfg
  /-- The advice columns the `Q`-seed cells are assigned + constrained-constant into. -/
  seedX : Column .advice
  seedY : Column .advice

/-! ## Inputs / Output (donor-mirrored) -/

/-- Inputs of `commit`: the message pieces (whole message, `k` pieces). The full-width blinding
scalar `r` (canonical `Fq` representative) lives on the abstract blinding child's boundary — it is
threaded as a separate `Var BInput Fp` (the child's own input type) so the CommitDomain `Input`
record stays a plain `ProvableStruct` (no old-Clean `UnconstrainedNat` provable in the region
tree). -/
structure Input (k : ℕ) (F : Type) where
  pieces : Vector F k
deriving ProvableStruct

/-- Outputs of `commit`: the commitment point and the hash running sums, mirroring halo2's
`commit` returning `(CommitmentPoint, Vec<RunningSum>)`. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-! ## The commit body — PENDING REWORK (`sinsemilla-loop-design.md`)

The previous `commitBody` seeded `Q` through two constrained-constant advice cells
(`seedX`/`seedY`) — NOT Rust-faithful (`hash_to_point.rs::public_q_initialization` uses
`q_sinsemilla4` + the `fixed_y_q` column + `assign_advice_from_constant(x_a, Q.x)`), and
consumed the old cell-input `Chain` API. The rework lands together with the faithful
`hash_message` Q-init port: `commit = hash_message(Q, msg) + [r]R` with the chain called
via `Chain.circuit G ns (fun _ => Q.y)` and `A = Q` pinned by the constant copy (x) and
the init gate (y). The `[r]R` leg stays the abstract `MulFixed.FullWidth` boundary
(`BlindSpecPinned`/`BlindEnvPinned`). -/

variable {BCI BCfg : Type}

/-- The blinding child's `Spec` is the `scalarOf input • R` contract. -/
def BlindSpecPinned {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point)
    (R : FixedBase) (scalarOf : Value (Input k) Fp → Fq) : Prop :=
  blind.Spec = fun input (output : Point Fp) _ => output.Valid ∧ output = scalarOf input • R

/-- The blinding child has no environment assumptions and trivial `Assumptions`. -/
def BlindEnvPinned {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point) : Prop :=
  blind.EnvAssumptions = (fun _ _ => True) ∧ blind.Assumptions = fun _ => True

/-- `CommitDomain::blinding_factor` is the bare `[r]R` — the abstract blinding child itself. -/
def blindingFactor {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point) :
    FormalRegionCircuit Fp BCI BCfg (Input k) Point :=
  blind

end Halo2.Ironwood.Sinsemilla.CommitDomain
