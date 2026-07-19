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

namespace Halo2.Ironwood.Sinsemilla

open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)
open Specs.Sinsemilla (Generators)
open Ecc

/-! ### `CommitDomain::commit` -/

namespace CommitDomain

/-- Inputs of `commit`: the message pieces and the prover-side full-width blinding
scalar behind the `ScalarFixed` value `r` (the canonical natural representative of the
`Fq` scalar). -/
structure Input (k : ℕ) (F : Type) where
  pieces : Vector F k
  r : UnconstrainedNat F
deriving CircuitType

instance (k : ℕ) : Inhabited (Var (Input k) Fp) :=
  ⟨{ pieces := default, r := default }⟩

/-- Outputs of `commit`: the commitment point and the hash running sums, mirroring
halo2's `commit` returning `(CommitmentPoint, Vec<RunningSum>)`. `NoteCommit`/`CommitIvk`
read individual `zs[i][j]` cells for their canonicity gates. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  zs : HVec (Chain.zLengths ns) F
deriving ProvableStruct

theorem eval_zs {F : Type} [FiniteField F] (env : Environment F) (ns : List ℕ) (out : Var (Output ns) F) :
    (eval env out).zs = eval env out.zs := by
  simp only [circuit_norm]

def Spec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : Value (Input (ns.length + 1)) Fp)
    (output : Value (Output (n₀ :: ns)) Fp) (_ : ProverData Fp) : Prop :=
  ∃ (chunks : List ℕ) (r : Fq),
    Chain.PieceChunks (n₀ :: ns) input.pieces chunks ∧
    Chain.ZsFacts (n₀ :: ns) chunks output.zs ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point = B + r • R

def ProverAssumptions (G : Generators) (Q : Point Fp) (n₀ : ℕ)
    (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) input.pieces ∧
  (∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) input.pieces) = some B) ∧
  (show ℕ from input.r) < PALLAS_SCALAR_CARD

def ProverSpec (G : Generators) (Q : Point Fp) (R : MulFixed.FixedBase)
    (n₀ : ℕ) (ns : List ℕ) (input : ProverValue (Input (ns.length + 1)) Fp)
    (output : ProverValue (Output (n₀ :: ns)) Fp) (_ : ProverHint Fp) : Prop :=
  Chain.ZsHonest (n₀ :: ns) input.pieces output.zs ∧
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) input.pieces) = some B →
    output.point = B + ((show ℕ from input.r : ℕ) : Fq) • R

end CommitDomain

end Halo2.Ironwood.Sinsemilla
