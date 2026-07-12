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

/-! ## The commit body (region-level composition)

`commit` in one ambient region: seed `Q`, run the hash chain, run the blinding mul, sum. The
blinding child is the abstract `FormalRegionCircuit` `blind` (the `[r]R` STATED BOUNDARY). Offsets
are threaded so the children do not collide. -/

/-- The number of rows the hash leg occupies for a whole message `n₀ :: ns` (from
`Chain.pieceRows`). -/
def hashRows (n₀ : ℕ) (ns : List ℕ) : ℕ := Chain.pieceRows (n₀ :: ns)

variable {BCI BCfg : Type}

/-- The commit body. `Q` is the domain point (on-curve), `blind` the abstract `[r]R` child
(`MulFixed.FullWidth` interface — the stated boundary). The blinding child shares CommitDomain's
`Input` record (in a real `MulFixed.FullWidth` port the scalar `r` is a field of that record; here
`Input` carries only the verifier-visible pieces, and the child reads `r` from its own hint) — so
`blind.call` is fed the same `input`.
- seed `Q.x`/`Q.y` into `seedX`/`seedY` at `offset` as constrained constants (pins the chain's
  entering accumulator to `A = Q`);
- run `Chain.circuit G (n₀ :: ns)` on the pieces entering at the seeded `(x_a, y_a) = Q`;
- run the blinding child `blind` (the `[r]R` leg — the stated boundary);
- add the hash point and the blinding point via `Ecc.Add.add`;
- return `⟨commitment, hashOut.zs⟩`. -/
def commitBody (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (blind : FormalRegionCircuit Fp BCI BCfg (Input (ns.length + 1)) Point)
    (cfg : Config BCfg) (offset : ℕ)
    (input : Var (Input (ns.length + 1)) Fp) :
    RegionCircuit Fp (Var (Output (n₀ :: ns)) Fp) := do
  -- seed Q into the entering accumulator cells (constrained constants)
  let xACell ← assignAdvice cfg.seedX offset (.native fun _ => #v[Q.x])
  constrainConstant xACell Q.x
  let yACell ← assignAdvice cfg.seedY offset (.native fun _ => #v[Q.y])
  constrainConstant yACell Q.y
  -- hash leg: hash_to_point(Q, msg), entering at (Q.x, Q.y)
  let hashOut ← (Chain.circuit G (n₀ :: ns)).call cfg.hashConfig (offset + 1)
    { pieces := Vector.cast (by simp) input.pieces, xA := xACell, yA := yACell }
  -- blinding leg: [r]R (STATED BOUNDARY — abstract MulFixed.FullWidth child)
  let blindPt ← blind.call cfg.blindConfig (offset + 1 + hashRows n₀ ns) input
  -- commitment = hashPoint + [r]R
  let commitment ← Ecc.Add.add.call cfg.addConfig
    (offset + 1 + hashRows n₀ ns + 1)
    { p := hashOut.point, q := blindPt }
  return { point := commitment, zs := hashOut.zs }

/-! ## Contract (donor `CommitDomain.Spec`, region-level)

`EnvAssumptions` is the loaded generator table (the hash child's env-assumption; the blinding
child has none, `blind_envAssumptions_eq`). `Spec`: the message decomposes into a flat chunk
list, the running sums are its per-piece suffix recombinations, and for the domain point `Q` the
commitment is `hashToPoint(Q, chunks) + r • R`. -/

/-- The `commit` spec (donor `CommitDomain.Spec`), verifier view, seeded at `Q`. `R` is the
blinding base, `scalarOf` the abstract blinding scalar. Existentially matches the donor's `∃ r`;
here the witness is pinned to `scalarOf input`. -/
def Spec (G : Generators) (Q : Point Fp) (R : FixedBase) (n₀ : ℕ) (ns : List ℕ)
    (scalarOf : Value (Input (ns.length + 1)) Fp → Fq)
    (input : Value (Input (ns.length + 1)) Fp)
    (output : Value (Output (n₀ :: ns)) Fp) (_ : Unit) : Prop :=
  ∃ chunks : List ℕ,
    PieceChunks (n₀ :: ns) input.pieces chunks ∧
    ZsFacts (n₀ :: ns) chunks output.zs ∧
    ∀ B, hashToPoint G.S Q chunks = some B →
      output.point = B + scalarOf input • R

/-- The honest-prover precondition (donor `CommitDomain.ProverAssumptions`): the pieces are in
range and the honest chain over `Q` is defined. (The scalar-range fact is on the abstract
blinding child's boundary, discharged there.) -/
def ProverAssumptions (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (input : Value (Input (ns.length + 1)) Fp) : Prop :=
  PieceBounds (n₀ :: ns) input.pieces ∧
  (∃ B, hashToPoint G.S Q (honestChunks (n₀ :: ns) input.pieces) = some B)

/-! ## Contract-projection bridges (the ported children stay folded)

`rfl`-bridges exposing exactly the `Chain`/`Add` children's contract fields without unfolding the
bundle literals — the MulComplete/Chain pattern. FRAMEWORK CANDIDATE: a deriving-style mechanism
exposing a `FormalRegionCircuit` literal's contract projections without unfolding. -/

private theorem chain_spec_eq (G : Generators) (n₀ : ℕ) (ns : List ℕ) :
    (Chain.circuit G (n₀ :: ns)).Spec = Chain.Spec G (n₀ :: ns) := rfl

private theorem chain_envAssumptions_eq (G : Generators) (n₀ : ℕ) (ns : List ℕ)
    (cfg : HashPiece.Config) (env : Placed Environment Fp) :
    (Chain.circuit G (n₀ :: ns)).EnvAssumptions cfg env
      = GeneratorTableLoaded G cfg.generatorTable env.env := rfl

private theorem add_spec_eq :
    Ecc.Add.add.Spec = fun (input : Value Ecc.Add.Inputs Fp) output _ =>
      output.Valid ∧ output = input.p + input.q := rfl

private theorem add_assumptions_eq :
    Ecc.Add.add.Assumptions = fun (input : Value Ecc.Add.Inputs Fp) =>
      input.p.Valid ∧ input.q.Valid := rfl

/-! ## The blinding-child interface hypotheses (the `[r]R` STATED BOUNDARY)

The abstract child's pinned contract — exactly what a ported `MulFixed.FullWidth` bundle exposes.
`scalarOf` is the (abstract) canonical `Fq` scalar the child multiplies `R` by, read from the
child's input value; a real `MulFixed.FullWidth` port instantiates it as `input.r`'s canonical
representative. The hypotheses are passed to soundness/completeness; discharged by that gadget's
`rfl`-projections when it lands. -/

/-- The blinding child's `Spec` is the `scalarOf input • R` contract. -/
def BlindSpecPinned {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point)
    (R : FixedBase) (scalarOf : Value (Input k) Fp → Fq) : Prop :=
  blind.Spec = fun input (output : Point Fp) _ => output.Valid ∧ output = scalarOf input • R

/-- The blinding child has no environment assumptions and trivial `Assumptions`. -/
def BlindEnvPinned {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point) : Prop :=
  blind.EnvAssumptions = (fun _ _ => True) ∧ blind.Assumptions = fun _ => True

/-! ## Soundness

Composition of three folded child calls: the hash chain (`Chain.circuit`, ported), the blinding
mul (`blind`, stated boundary), and the complete addition (`Ecc.Add.add`, ported). The `Q`-seed
constrained-constants pin the chain's entering accumulator to `A = Q`; the chain contract then
delivers `hashToPoint(Q, chunks)`; the addition contract delivers the sum.

STRUCTURE-COMPLETE-WITH-STATED-SORRIES (per the sanctioned fallback). The statement is final; the
donor glue (`pieceChunks_bound`, `hashToPoint_valid`, the seed-pinning, the three child
consumptions via the `subcircuit_rw` engine) is identified inline. The one genuine cut is the
`[r]R` boundary, discharged by `hBlindSpec` (`BlindSpecPinned`). -/
theorem commitBody_sound (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (n₀ : ℕ) (ns : List ℕ)
    (blind : FormalRegionCircuit Fp BCI BCfg (Input (ns.length + 1)) Point) (R : FixedBase)
    (scalarOf : Value (Input (ns.length + 1)) Fp → Fq)
    (hBlindSpec : BlindSpecPinned blind R scalarOf) (hBlindEnv : BlindEnvPinned blind)
    (cfg : Config BCfg)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (hTable : GeneratorTableLoaded G cfg.hashConfig.generatorTable env)
    (offset : ℕ)
    (input : Var (Input (ns.length + 1)) Fp)
    (hc : RegionOperations.Constraints place self env
      ((commitBody G Q n₀ ns blind cfg offset input).operations self)) :
    Spec G Q R n₀ ns scalarOf
      (eval (⟨place, env⟩ : Placed Environment Fp) input)
      (eval (⟨place, env⟩ : Placed Environment Fp)
        ((commitBody G Q n₀ ns blind cfg offset input).output self)) () := by
  -- Cut lines (all final in statement):
  --  1. peel `commitBody.operations` into: seed asserts ++ chain.call ++ blind.call ++ add.call
  --     (`RegionCircuit.operations_bind` + `constraints_append`, as in `chainBody_sound`).
  --  2. seed: `constrainConstant` pins `eval xACell = Q.x`, `eval yACell = Q.y`, so the chain's
  --     entering `A` (any on-curve `A` with `A.x = Q.x`, `2·A.y = enterYA`) is `A = Q`.
  --  3. chain: `subcircuit_rw at hChain` weakens the chunk to `EnvA → A → Chain.Spec`; feed the
  --     table `hTable` and apply, then `chain_spec_eq` exposes `Chain.Spec`, giving `chunks`,
  --     `PieceChunks`, `ZsFacts`, and the chain contract `∀ A …, output.point =
  --     hashToPoint(Q,chunks)` (instantiated at `A = Q`).
  --  4. blind: `subcircuit_rw at hBlind`, `hBlindSpec` gives `blindPt.Valid ∧ blindPt = r • R`
  --     (the [r]R BOUNDARY — pinned interface).
  --  5. add: `subcircuit_rw at hAdd`, `add_spec_eq` gives `commitment = hashPoint + blindPt`,
  --     discharging `Add`'s `Assumptions` from the chain point's validity
  --     (`hashToPoint_valid (Or.inl hQ) (pieceChunks_bound hPC)`) and `R.smul_valid`.
  --  6. assemble: `output.point = B + r • R`; `output.zs = hashOut.zs`; `PieceChunks`/`ZsFacts`.
  sorry

/-! ## Completeness

Honest-prover mirror: the three child chunks consumed via the `subcircuit_rw` engine in `legacy`
mode (peel the goal's `Constraints` into the seed ++ chain ++ blind ++ add shape, then
`subcircuit_rw legacy` strengthens each chunk to its precondition bundle and introduces the
premised `h_spec_0`/`h_spec_1`/`h_spec_2 : EnvA → A → PA → Spec ∧ ProverSpec`). The chain's
`ProverSpec` (off `h_spec_0`) gives the honest commitment; the blinding child's `ProverSpec` gives
`blindPt = r • R`; the addition's `Spec` closes on the two valid summands. -/
theorem commitBody_complete (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (n₀ : ℕ) (ns : List ℕ)
    (blind : FormalRegionCircuit Fp BCI BCfg (Input (ns.length + 1)) Point) (R : FixedBase)
    (hBlindEnv : BlindEnvPinned blind)
    (cfg : Config BCfg)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (hTable : GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env.toEnvironment)
    (offset : ℕ) (input : Var (Input (ns.length + 1)) Fp)
    (hpa : ProverAssumptions G Q n₀ ns (eval env.toEnvironment input))
    (hwit : RegionOperations.ExtendsWitnesses env.place self env.env
      ((commitBody G Q n₀ ns blind cfg offset input).operations self)) :
    RegionOperations.Constraints env.place self env.env
      ((commitBody G Q n₀ ns blind cfg offset input).operations self) := by
  -- Cut lines (all final in statement):
  --  1. peel `commitBody.operations` (as soundness), `extendsWitnesses_append`.
  --  2. seed cells honest-fill to `Q.x`/`Q.y` (their `constrainConstant` is idempotent).
  --  3. chain: `h_spec_0` (from `subcircuit_rw legacy`) applied to the chain's `ProverAssumptions`
  --     — discharged from `hpa` (`PieceBounds` + defined honest chain at `A = Q`) — yields
  --     `Chain.Spec ∧ Chain.ProverSpec` (the honest hash point `B`); its precondition bundle
  --     discharges the chain chunk in the strengthened goal.
  --  4. blind: `h_spec_1` (the [r]R BOUNDARY — the child discharges its own `ProverAssumptions`;
  --     `blind`'s honest `ProverSpec` gives `blindPt = r • R`).
  --  5. add: `Ecc.Add.add` completeness on the two valid summands (`hashToPoint_valid`,
  --     `R.smul_valid`).  6. reassemble via `constraints_append`.
  sorry

/-! ## The gadget bundle -/

instance elaborated (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (blind : FormalRegionCircuit Fp BCI BCfg (Input (ns.length + 1)) Point)
    (cfg : Config BCfg) (offset : ℕ) :
    ElaboratedRegionCircuit Fp (Input (ns.length + 1)) (Output (n₀ :: ns))
      (fun input : Var (Input (ns.length + 1)) Fp =>
        commitBody G Q n₀ ns blind cfg offset input) := {}

/-- `CommitDomain::commit`. `EnvAssumptions` is the loaded generator table (the hash child's
env-assumption; the blinding child has none). Soundness/completeness compose the ported hash
(`Chain.circuit`) and addition (`Ecc.Add.add`) children with the STATED-BOUNDARY blinding child
`blind` (an abstract `MulFixed.FullWidth` interface — `MulFixed` is unported to Ironwood), pinned
by the `BlindSpecPinned`/`BlindEnvPinned` hypotheses and the abstract scalar `scalarOf`. -/
def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (n₀ : ℕ) (ns : List ℕ)
    (blind : FormalRegionCircuit Fp BCI BCfg (Input (ns.length + 1)) Point) (R : FixedBase)
    (scalarOf : Value (Input (ns.length + 1)) Fp → Fq)
    (hBlindSpec : BlindSpecPinned blind R scalarOf) (hBlindEnv : BlindEnvPinned blind) :
    FormalRegionCircuit Fp (Config BCfg) (Config BCfg)
      (Input (ns.length + 1)) (Output (n₀ :: ns)) where
  name := "sinsemilla CommitDomain::commit"
  configure := fun cfg => pure cfg
  synthesize cfg offset input := commitBody G Q n₀ ns blind cfg offset input
  elaborated cfg offset := elaborated G Q n₀ ns blind cfg offset
  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env
  Assumptions _ := True
  Spec := Spec G Q R n₀ ns scalarOf
  ProverAssumptions input _ := ProverAssumptions G Q n₀ ns input
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    -- the body soundness does the work; land the abstract input/output on the body's eval forms
    -- (`ElaboratedRegionCircuit.output_eq` + `ProvableStruct.eval_cells_eq_eval`, as in
    -- `Chain.circuit.soundness`).
    sorry
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    -- the body completeness does the work; land `hpa` on the body's `ProverAssumptions`.
    sorry

/-! ## `CommitDomain::blinding_factor`

The bare `[r]R` (`sinsemilla.rs:471-486`). Region-level, this is exactly the stated-boundary
blinding child. -/

/-- `CommitDomain::blinding_factor` is the bare `[r]R` — the abstract blinding child itself. -/
def blindingFactor {k : ℕ} (blind : FormalRegionCircuit Fp BCI BCfg (Input k) Point) :
    FormalRegionCircuit Fp BCI BCfg (Input k) Point :=
  blind

end Halo2.Ironwood.Sinsemilla.CommitDomain
