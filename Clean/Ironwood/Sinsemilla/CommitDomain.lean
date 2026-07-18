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
import Clean.Ironwood.Sinsemilla.HashToPoint

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

/-! ## The commit body

`commit = hash_to_point(Q, msg) + [r]R` (`sinsemilla.rs:488-509`), on the faithful
`hash_message` bundle (`HashToPoint.hashCircuit` — the Q-init is inside its region). The
`[r]R` leg is the abstract `MulFixed.FullWidth` boundary
(`BlindSpecPinned`/`BlindEnvPinned`). -/

variable {BCI BCfg : Type}

/-- The blinding child's `Spec` is the `scalarOf input • R` contract (with validity). The
child is LAYOUTER-level (Rust `FixedPoint::mul` spans several regions; the ported
`mul_fixed` synthesize is a `Circuit`). -/
def BlindSpecPinned {k : ℕ} (blind : FormalCircuit Fp BCI BCfg (Input k) Point)
    (R : FixedBase) (scalarOf : Value (Input k) Fp → Fq) : Prop :=
  blind.Spec = fun input (output : Point Fp) _ => output.Valid ∧ output = scalarOf input • R

/-- The blinding child carries no ambient/verifier/honest preconditions. -/
def BlindEnvPinned {k : ℕ} (blind : FormalCircuit Fp BCI BCfg (Input k) Point) : Prop :=
  blind.EnvAssumptions = (fun _ _ => True) ∧ blind.Assumptions = (fun _ => True) ∧
  blind.ProverAssumptions = fun _ _ _ => True

/-- `CommitDomain::blinding_factor` is the bare `[r]R` — the abstract blinding child itself. -/
def blindingFactor {k : ℕ} (blind : FormalCircuit Fp BCI BCfg (Input k) Point) :
    FormalCircuit Fp BCI BCfg (Input k) Point :=
  blind

/-! ## The `commit` bundle -/

open Orchard.Specs.Sinsemilla (hashToPoint)

-- local contract bridges for the hash child (proof-typed binders)
private theorem hashC_spec_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x) :
    (HashToPoint.hashCircuit G ns Q hQ hns hpos).Spec
      = fun input output wit => HashToPoint.Spec G ns Q input output wit := rfl

private theorem hashC_envAssumptions_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x)
    (cfg : HashPiece.Config) (env : Placed Environment Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns hpos).EnvAssumptions cfg env
      = Sinsemilla.GeneratorTableLoaded G cfg.generatorTable env.env := rfl

private theorem hashC_proverAssumptions_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit ns Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns hpos).ProverAssumptions input wit hint
      = HashToPoint.ProverAssumptions G ns Q input := rfl

private theorem hashC_proverSpec_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x)
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (output : Value (HashToPoint.Output ns.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit ns Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns hpos).ProverSpec input output wit hint
      = HashToPoint.ProverSpec G ns Q input output := rfl

/-- A layouter child's call chunk counts its own regions. -/
private theorem blind_call_regionCount {k : ℕ}
    (blind : FormalCircuit Fp BCI BCfg (Input k) Point) (bcfg : BCfg)
    (input : Var (Input k) Fp) (j : RegionIndex) :
    Operations.regionCount ((blind.call bcfg input).operations j)
      = blind.regionCount bcfg input := by
  simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
  rw [show blind.regionCount bcfg input
      = Operations.regionCount ((blind.synthesize bcfg input).operations j) from
    ((blind.elaborated bcfg).regionCount_eq input j)]
  rfl

/-- The region count of `commit`: the blinding child's regions, the hash region, the
final complete addition. -/
private theorem commit_regionCount
    (G : Generators) (ns : List ℕ)
    (blind : FormalCircuit Fp BCI BCfg (Input ns.length) Point)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x)
    (bcfg : BCfg) (hcfg : HashPiece.Config) (acfg : Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let blindOut ← blind.call bcfg input
        let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns hpos).call hcfg
          { pieces := input.pieces }
        let result ← (Ecc.Add.add.toFormal "M + [r] R").call acfg
          { p := hashOut.point, q := blindOut }
        pure result).operations i)
      = blind.regionCount bcfg input + 2 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (inp : Var (Sinsemilla.Chain.Inputs ns.length) Fp),
      Operations.regionCount
        (((HashToPoint.hashCircuit G ns Q hQ hns hpos).call hcfg inp).operations j) = 1
    from fun j inp => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      rw [show ((HashToPoint.hashCircuit G ns Q hQ hns hpos).synthesize hcfg inp j).2.1
          = ((assignRegion (HashToPoint.hashRegion G ns Q hQ hns hpos).name
              ((HashToPoint.hashRegion G ns Q hQ hns hpos).synthesize hcfg 0
                inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [show ∀ (j : RegionIndex) (inp : Var Ecc.Add.Inputs Fp),
      Operations.regionCount
        (((Ecc.Add.add.toFormal "M + [r] R").call acfg inp).operations j) = 1
    from fun j inp => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      rw [show ((Ecc.Add.add.toFormal "M + [r] R").synthesize acfg inp j).2.1
          = ((assignRegion "M + [r] R"
              (Ecc.Add.add.synthesize acfg 0 inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [blind_call_regionCount blind bcfg input i]

/-- Rust `CommitDomain::commit` (`sinsemilla.rs:488-509`): `[r]R` (the abstract blinding
child), `hash_to_point(Q, msg)` (the proven hash bundle), and the final complete addition
`M + [r]R`. `Spec`: the commitment is `SinsemillaHashToPoint(Q, chunks) + scalarOf·R`
whenever the hash is defined, with the message chunking and running-sum facts exposed. -/
def commit (G : Generators) (ns : List ℕ)
    (blind : FormalCircuit Fp BCI BCfg (Input ns.length) Point)
    (R : FixedBase) (scalarOf : Value (Input ns.length) Fp → Fq)
    (hBS : BlindSpecPinned blind R scalarOf) (hBE : BlindEnvPinned blind)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) (hpos : ∀ x ∈ ns, 0 < x) :
    FormalCircuit Fp (BCI × BCfg × HashPiece.Config × Ecc.Add.Config)
      (BCfg × HashPiece.Config × Ecc.Add.Config) (Input ns.length) Point where
  name := "sinsemilla commit"
  configure := fun (_, cfg) => pure cfg

  synthesize := fun (bcfg, hcfg, acfg) input => do
    let blindOut ← blind.call bcfg input
    let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns hpos).call hcfg
      { pieces := input.pieces }
    let result ← (Ecc.Add.add.toFormal "M + [r] R").call acfg
      { p := hashOut.point, q := blindOut }
    pure result

  elaborated := fun (bcfg, hcfg, acfg) =>
    { output := fun input i =>
        ((do
          let blindOut ← blind.call bcfg input
          let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns hpos).call hcfg
            { pieces := input.pieces }
          let result ← (Ecc.Add.add.toFormal "M + [r] R").call acfg
            { p := hashOut.point, q := blindOut }
          pure result : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun input => blind.regionCount bcfg input + 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (commit_regionCount G ns blind Q hQ hns hpos bcfg hcfg acfg input i).symm }

  EnvAssumptions := fun (_, hcfg, _) env =>
    Sinsemilla.GeneratorTableLoaded G hcfg.generatorTable env.env

  Assumptions _ := True

  Witness := Sinsemilla.Chain.ChainWit ns
  extract := fun (bcfg, hcfg, _) input i₀ env =>
    (HashToPoint.hashCircuit G ns Q hQ hns hpos).extract hcfg
      { pieces := input.pieces } (i₀ + blind.regionCount bcfg input) env

  Spec input output wit :=
    ∃ chunks : List ℕ,
      Sinsemilla.Chain.PieceChunks ns (input.pieces) chunks ∧
      Sinsemilla.Chain.ZsFacts ns chunks wit.zs ∧
      ∀ B, hashToPoint G.S Q chunks = some B →
        output.Valid ∧ output = B + (scalarOf input • R : Point Fp)

  ProverAssumptions input _ _ :=
    Sinsemilla.Chain.PieceBounds ns (input.pieces) ∧
    ∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns (input.pieces)) = some B

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨hBlind, hHash, hAdd⟩ := hc
    -- the blind child's pinned contract
    have hBl := hBlind (by rw [hBE.1]; trivial) (by rw [hBE.2.1]; trivial)
    rw [hBS] at hBl
    -- the hash child's contract
    have hHashS := hHash (by rw [hashC_envAssumptions_eq']; exact _hE) trivial
    rw [hashC_spec_eq', blind_call_regionCount blind cfg.1 input_var i₀] at hHashS
    obtain ⟨chunks, hPC, hZs, -, hContract⟩ := hHashS
    -- input eval landing
    have hin : (eval (⟨env.place, env.env⟩ : Placed Environment Fp)
        ({ pieces := input_var.pieces }
          : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
        : Value (Sinsemilla.Chain.Inputs ns.length) Fp).pieces
        = input.pieces := by
      rw [← h_input, ProvableStruct.eval_cells_eq_eval,
        Sinsemilla.Chain.inputs_eval_literal]
      with_unfolding_all rfl
    rw [show (eval (⟨env.place, env.env⟩ : Placed Environment Fp)
        ({ pieces := input_var.pieces }
          : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
        : Value (Sinsemilla.Chain.Inputs ns.length) Fp).pieces
      = input.pieces from hin] at hPC
    refine ⟨chunks, hPC, hZs, ?_⟩
    intro B hB
    have hcoords := hContract B hB
    -- the hash output point value IS the eval'd point (projection commute; go through
    -- the componentwise `ProvableStruct.eval` — the flat eval of the whole symbolic-size
    -- Output struct is a whnf wall)
    have hpoint : (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0
        : Value (HashToPoint.Output ns.length) Fp).point
        = (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval]
      with_unfolding_all rfl
    have hpx := congrArg Orchard.Point.x hpoint
    have hpy := congrArg Orchard.Point.y hpoint
    -- the hash point equals B
    have hPB : (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0.point
        : Value Point Fp) = B := by
      obtain ⟨bx, byv⟩ := B
      have hx : (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp).x = bx := by rw [← hpx]; exact hcoords.1
      have hy : (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp).y = byv := by rw [← hpy]; exact hcoords.2
      rw [← hx, ← hy]
    -- B is a valid point (the chunks are generator indices)
    have hBvalid : B.Valid :=
      Orchard.Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound hPC) hB
    -- Add-input projection commutes (componentwise eval route — the flat eval is a
    -- whnf wall)
    have heP : ((eval (⟨env.place, env.env⟩ : Placed Environment Fp)
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).p : Point Fp)
        = (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval]
      with_unfolding_all rfl
    have heQ : ((eval (⟨env.place, env.env⟩ : Placed Environment Fp)
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).q : Point Fp)
        = (eval (⟨env.place, env.env⟩ : Placed Environment Fp) x_gen_out_1
          : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval]
      with_unfolding_all rfl
    -- the complete addition's contract
    have hAddS := hAdd trivial (by
      show ((eval (⟨env.place, env.env⟩ : Placed Environment Fp)
          ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
          : Value Ecc.Add.Inputs Fp).p : Point Fp).Valid ∧
        ((eval (⟨env.place, env.env⟩ : Placed Environment Fp)
          ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
          : Value Ecc.Add.Inputs Fp).q : Point Fp).Valid
      constructor
      · rw [heP, hPB]; exact hBvalid
      · rw [heQ]; exact hBl.1)
    obtain ⟨hVout, hSum⟩ := hAddS
    refine ⟨hVout, ?_⟩
    rw [hSum, heP, hPB, heQ, hBl.2, ← h_input, ProvableStruct.eval_cells_eq_eval]

  completeness := by
    circuit_proof_start
    obtain ⟨hPBounds, B0, hB0⟩ := hPA
    obtain ⟨bx, byv⟩ := B0
    -- the blind child's contract (its obligations are pinned trivial)
    have hBl := (h_spec_0 (by rw [hBE.1]; trivial) (by rw [hBE.2.1]; trivial)
      (by rw [hBE.2.2]; trivial)).1
    rw [hBS] at hBl
    -- prover input landing
    have hinP : (eval env ({ pieces := input_var.pieces }
        : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
        : Value (Sinsemilla.Chain.Inputs ns.length) Fp).pieces = input.pieces := by
      rw [← h_input, ProvableStruct.eval_cells_eq_eval_prover,
        Sinsemilla.Chain.inputs_eval_literal]
      with_unfolding_all rfl
    -- the hash child's honest-prover precondition
    have hPAhash : (HashToPoint.hashCircuit G ns Q hQ hns hpos).ProverAssumptions
        (eval env ({ pieces := input_var.pieces }
          : Var (Sinsemilla.Chain.Inputs ns.length) Fp))
        ((HashToPoint.hashCircuit G ns Q hQ hns hpos).extract cfg.2.1
          { pieces := input_var.pieces }
          (i₀ + ((blind.call cfg.1 input_var).operations i₀).regionCount)
          env.toEnvironment)
        env.env.hint := by
      rw [hashC_proverAssumptions_eq']
      refine ⟨hns, ?_, ⟨bx, byv⟩, ?_⟩
      · rw [hinP]; exact hPBounds
      · rw [hinP]; exact hB0
    -- the hash child's honest contract (prover side: the output point IS the honest hash)
    have hPSHash := (h_spec_1 (by rw [hashC_envAssumptions_eq']; exact _hE) trivial hPAhash).2
    rw [hashC_proverSpec_eq'] at hPSHash
    have hres := hPSHash ⟨bx, byv⟩ (by rw [hinP]; exact hB0)
    -- prover-eval output point = verifier-eval point (projection commute + hint erasure)
    have hpointP : (eval env x_gen_out_0
        : Value (HashToPoint.Output ns.length) Fp).point
        = (eval env.toEnvironment x_gen_out_0.point : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval_prover]
      with_unfolding_all rfl
    -- the hash point equals the honest B0
    have hPB0 : (eval env.toEnvironment x_gen_out_0.point : Value Point Fp)
        = (⟨bx, byv⟩ : Point Fp) := by
      have hx : (eval env.toEnvironment x_gen_out_0.point : Value Point Fp).x = bx := by
        rw [← congrArg Orchard.Point.x hpointP]; exact hres.1
      have hy : (eval env.toEnvironment x_gen_out_0.point : Value Point Fp).y = byv := by
        rw [← congrArg Orchard.Point.y hpointP]; exact hres.2
      rw [← hx, ← hy]
    have hB0valid : (⟨bx, byv⟩ : Point Fp).Valid :=
      Orchard.Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound
          (Sinsemilla.Chain.pieceChunks_honestChunks ns input.pieces hPBounds)) hB0
    -- Add-input projections (verifier eval over the hint-erased env)
    have hePv : ((eval env.toEnvironment
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).p : Point Fp)
        = (eval env.toEnvironment x_gen_out_0.point : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval]
      with_unfolding_all rfl
    have heQv : ((eval env.toEnvironment
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).q : Point Fp)
        = (eval env.toEnvironment x_gen_out_1 : Value Point Fp) := by
      rw [ProvableStruct.eval_cells_eq_eval]
      with_unfolding_all rfl
    refine ⟨⟨by rw [hBE.1]; trivial, by rw [hBE.2.1]; trivial, by rw [hBE.2.2]; trivial⟩,
      ⟨by rw [hashC_envAssumptions_eq']; exact _hE, trivial, hPAhash⟩,
      trivial, ?_, trivial⟩
    show ((eval env.toEnvironment
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).p : Point Fp).Valid ∧
      ((eval env.toEnvironment
        ({ p := x_gen_out_0.point, q := x_gen_out_1 } : Var Ecc.Add.Inputs Fp)
        : Value Ecc.Add.Inputs Fp).q : Point Fp).Valid
    constructor
    · rw [hePv, hPB0]; exact hB0valid
    · rw [heQv]; exact hBl.1

end Halo2.Ironwood.Sinsemilla.CommitDomain
