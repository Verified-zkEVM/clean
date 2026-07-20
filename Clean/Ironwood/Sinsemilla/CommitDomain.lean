import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Ecc.MulFixed.ShortTheorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth
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
  let commitment = p.add(layouter.namespace(|| "complete point addition"), &blind)?;          // 503
  Ok((commitment, zs))
  ```
  i.e. `commit(msg, r) = hash_to_point(Q, msg) + [r]·R`, keeping the per-piece running
  sums `zs` (`NoteCommit`/`CommitIvk` read individual `zs[i][j]` cells).
- `CommitDomain::blinding_factor` (`sinsemilla.rs:471-486`) is the bare `[r]·R`.

## The `[r]R` leg

`R : ecc::FixedPoint<C, EccChip>` (`sinsemilla.rs:417`), and `self.R.mul(..)` (`sinsemilla.rs:501`)
resolves to `FixedPoint::mul` — full-width fixed-base scalar multiplication, the Ironwood
`Ecc.MulFixed.FullWidth.circuit R windows` bundle (parameterized by the caller's 85 window
witness programs; the scalar the windows encode is the child's extraction data, so the
commitment `Spec` is stated at the extracted scalar).

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

open Halo2.Ironwood (Point Fq)
open Halo2.Ironwood.Ecc (DoubleAndAddRow)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Specs.Sinsemilla (Generators hashToPoint)
open Halo2.Ironwood.Specs (K)
open Halo2.Ironwood.Sinsemilla (HVec)
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
`[r]R` leg is the `Ecc.MulFixed.FullWidth` bundle. -/

/-- `CommitDomain::blinding_factor` (`sinsemilla.rs:471-486`) is the bare `[r]R`. -/
def blindingFactor (R : FixedBase) (windows : Vector (FExpr Fp) 85) :
    FormalCircuit Fp Ecc.MulFixed.Config Ecc.MulFixed.FullWidth.Config unit Point :=
  Ecc.MulFixed.FullWidth.circuit R windows

/-! ### Blinding-child contract bridges (`rfl`, child stays folded) -/

section BlindBridges

variable (R : FixedBase) (windows : Vector (FExpr Fp) 85)

private theorem blind_spec_eq :
    (Ecc.MulFixed.FullWidth.circuit R windows).Spec
      = fun _ (output : Point Fp) (s : Vector Fp 85 × Fq) =>
          output = (s.2 • R : Point Fp) := rfl

private theorem blind_assumptions_eq :
    (Ecc.MulFixed.FullWidth.circuit R windows).Assumptions = fun _ => True := rfl

private theorem blind_envAssumptions_eq :
    (Ecc.MulFixed.FullWidth.circuit R windows).EnvAssumptions
      = Ecc.MulFixed.FullWidth.EnvAssumptions := rfl

private theorem blind_proverAssumptions_eq :
    (Ecc.MulFixed.FullWidth.circuit R windows).ProverAssumptions
      = fun _ (s : Vector Fp 85 × Fq) _ => ∀ w : Fin 85, (s.1[w.val]).val < 8 := rfl

private theorem blind_proverSpec_eq :
    (Ecc.MulFixed.FullWidth.circuit R windows).ProverSpec
      = fun _ _ _ _ => True := rfl

private theorem blind_extract_eq (cfg : Ecc.MulFixed.FullWidth.Config) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (Ecc.MulFixed.FullWidth.circuit R windows).extract cfg () i env
      = Ecc.MulFixed.FullWidth.fwExtract cfg i env := rfl

end BlindBridges

/-! ## The `commit` bundle -/

open Halo2.Ironwood.Specs.Sinsemilla (hashToPoint)

-- local contract bridges for the hash child (proof-typed binders)
private theorem hashC_spec_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ []) :
    (HashToPoint.hashCircuit G ns Q hQ hns).Spec
      = fun input output wit => HashToPoint.Spec G ns Q input output wit := rfl

private theorem hashC_envAssumptions_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : HashPiece.Config) (env : Placed Environment Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns).EnvAssumptions cfg env
      = Sinsemilla.GeneratorTableLoaded G cfg.generatorTable env.env := rfl

private theorem hashC_proverAssumptions_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit ns Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns).ProverAssumptions input wit hint
      = HashToPoint.ProverAssumptions G ns Q input := rfl

private theorem hashC_proverSpec_eq' (G : Generators) (ns : List ℕ) (Q : Point Fp)
    (hQ : Q.OnCurve) (hns : ns ≠ [])
    (input : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
    (output : Value (HashToPoint.Output ns.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit ns Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G ns Q hQ hns).ProverSpec input output wit hint
      = HashToPoint.ProverSpec G ns Q input output := rfl

/-- The blinding child's call chunk spans its two regions. -/
private theorem blind_call_regionCount (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (bcfg : Ecc.MulFixed.FullWidth.Config) (j : RegionIndex) :
    Operations.regionCount
      (((Ecc.MulFixed.FullWidth.circuit R windows).call bcfg ()).operations j) = 2 := by
  rw [FormalCircuit.call_regionCount]
  rfl

/-- The region count of `commit`: the blinding child's two regions, the hash region, the
final complete addition. -/
private theorem commit_regionCount
    (G : Generators) (ns : List ℕ)
    (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ [])
    (bcfg : Ecc.MulFixed.FullWidth.Config) (hcfg : HashPiece.Config)
    (acfg : Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let blindOut ← (Ecc.MulFixed.FullWidth.circuit R windows).call bcfg ()
        let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
          { pieces := input.pieces }
        let result ← (Ecc.Add.add.toFormal "complete point addition").call acfg
          { p := hashOut.point, q := blindOut }
        pure result).operations i)
      = 4 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (inp : Var (Sinsemilla.Chain.Inputs ns.length) Fp),
      Operations.regionCount
        (((HashToPoint.hashCircuit G ns Q hQ hns).call hcfg inp).operations j) = 1
    from fun j inp => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      rw [show ((HashToPoint.hashCircuit G ns Q hQ hns).synthesize hcfg inp j).2.1
          = ((assignRegion (HashToPoint.hashRegion G ns Q hQ hns).name
              ((HashToPoint.hashRegion G ns Q hQ hns).synthesize hcfg 0
                inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [show ∀ (j : RegionIndex) (inp : Var Ecc.Add.Inputs Fp),
      Operations.regionCount
        (((Ecc.Add.add.toFormal "complete point addition").call acfg inp).operations j) = 1
    from fun j inp => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      rw [show ((Ecc.Add.add.toFormal "complete point addition").synthesize acfg inp j).2.1
          = ((assignRegion "complete point addition"
              (Ecc.Add.add.synthesize acfg 0 inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [blind_call_regionCount R windows bcfg i]

/-- Rust `CommitDomain::commit` (`sinsemilla.rs:488-509`): `[r]R` (the
`Ecc.MulFixed.FullWidth` bundle), `hash_to_point(Q, msg)` (the proven hash bundle), and
the final complete addition `M + [r]R`. `Spec`: the commitment is
`SinsemillaHashToPoint(Q, chunks) + s·R` at the extracted window scalar `s`, whenever the
hash is defined, with the message chunking and running-sum facts exposed. -/
def commit (G : Generators) (ns : List ℕ)
    (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalCircuit Fp
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Input ns.length) Point where
  name := "sinsemilla commit"
  configure := pure

  synthesize := fun (bcfg, hcfg, acfg) input => do
    let blindOut ← (Ecc.MulFixed.FullWidth.circuit R windows).call bcfg ()
    let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
      { pieces := input.pieces }
    let result ← (Ecc.Add.add.toFormal "complete point addition").call acfg
      { p := hashOut.point, q := blindOut }
    pure result

  elaborated := fun (bcfg, hcfg, acfg) =>
    { output := fun input i =>
        ((do
          let blindOut ← (Ecc.MulFixed.FullWidth.circuit R windows).call bcfg ()
          let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
            { pieces := input.pieces }
          let result ← (Ecc.Add.add.toFormal "complete point addition").call acfg
            { p := hashOut.point, q := blindOut }
          pure result : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 4
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (commit_regionCount G ns R windows Q hQ hns bcfg hcfg acfg input i).symm }

  EnvAssumptions := fun (bcfg, hcfg, _) env =>
    Sinsemilla.GeneratorTableLoaded G hcfg.generatorTable env.env ∧
    Ecc.MulFixed.FullWidth.EnvAssumptions bcfg env

  Assumptions _ := True

  Witness := fun F => Sinsemilla.Chain.ChainWit ns F × (Vector F 85 × Fq)
  extract := fun (bcfg, hcfg, _) input i₀ env =>
    ((HashToPoint.hashCircuit G ns Q hQ hns).extract hcfg
      { pieces := input.pieces } (i₀ + 2) env,
     Ecc.MulFixed.FullWidth.fwExtract bcfg i₀ env)

  Spec input output wit :=
    ∃ chunks : List ℕ,
      Sinsemilla.Chain.PieceChunks ns (input.pieces) chunks ∧
      Sinsemilla.Chain.ZsFacts ns chunks wit.1.zs ∧
      ∀ B, hashToPoint G.S Q chunks = some B →
        output.Valid ∧ output = B + (wit.2.2 • R : Point Fp)

  ProverAssumptions input wit _ :=
    Sinsemilla.Chain.PieceBounds ns (input.pieces) ∧
    (∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns (input.pieces)) = some B) ∧
    ∀ w : Fin 85, (wit.2.1[w.val]).val < 8

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨hTableE, hMulE⟩ := _hE
    obtain ⟨hBlind, hHash, hAdd⟩ := hc
    -- the blind child's contract: the output is the extracted window scalar times `R`
    have hBl := hBlind (by rw [blind_envAssumptions_eq]; exact hMulE)
      (by rw [blind_assumptions_eq]; trivial)
    rw [blind_spec_eq, blind_extract_eq] at hBl
    -- the hash child's contract
    have hHashS := hHash (by rw [hashC_envAssumptions_eq']; exact hTableE) trivial
    rw [hashC_spec_eq', blind_call_regionCount R windows cfg.1 i₀] at hHashS
    obtain ⟨chunks, hPC, hZs, -, hContract⟩ := hHashS
    -- input eval landing: hPC is in the componentwise normal form; bridge to the
    -- whole-struct `h_input` by unfolding defeq
    have hPC' : PieceChunks ns input.pieces chunks := by
      rw [← h_input]
      with_unfolding_all exact hPC
    refine ⟨chunks, hPC', hZs, ?_⟩
    intro B hB
    have hcoords := hContract B hB
    -- the hash output point value IS the eval'd point (projection commute; go through
    -- the componentwise `ProvableStruct.eval` — the flat eval of the whole symbolic-size
    -- Output struct is a whnf wall)
    have hpoint : (ProvableStruct.eval place env x_gen_out_0).point
        = (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp) := by
      with_unfolding_all rfl
    -- the hash point equals B
    have hPB : (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0.point
        : Value Point Fp) = B := by
      obtain ⟨bx, byv⟩ := B
      have hx : (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp).x = bx := by
        rw [← hpoint]; exact hcoords.1
      have hy : (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp).y = byv := by
        rw [← hpoint]; exact hcoords.2
      rw [← hx, ← hy]
    -- B is a valid point (the chunks are generator indices)
    have hBvalid : B.Valid :=
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound hPC) hB
    -- the complete addition's contract (input literal already eval'd componentwise)
    have hAddS := hAdd trivial (by
      show (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp).Valid ∧
        (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_1
          : Value Point Fp).Valid
      constructor
      · rw [hPB]; exact hBvalid
      · rw [hBl]; exact R.smul_valid _)
    obtain ⟨hVout, hSum⟩ := hAddS
    refine ⟨hVout, ?_⟩
    rw [hSum, hPB, hBl]

  completeness := by
    circuit_proof_start
    obtain ⟨hTableE, hMulE⟩ := _hE
    obtain ⟨hPBounds, ⟨B0, hB0⟩, hWin⟩ := hPA
    obtain ⟨bx, byv⟩ := B0
    -- the blind child's contract
    have hBl := (h_spec_0 (by rw [blind_envAssumptions_eq]; exact hMulE)
      (by rw [blind_assumptions_eq]; trivial)
      (by rw [blind_proverAssumptions_eq, blind_extract_eq]; exact hWin)).1
    rw [blind_spec_eq, blind_extract_eq] at hBl
    -- the hash child's honest-prover precondition, stated over the whole-struct eval
    -- (which elaborates); bridged to the componentwise normal form by unfolding defeq
    -- at the use sites
    have hPAhash : (HashToPoint.hashCircuit G ns Q hQ hns).ProverAssumptions
        ({ pieces := (ProvableStruct.eval place env input_var).pieces }
          : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
        ((HashToPoint.hashCircuit G ns Q hQ hns).extract cfg.2.1
          { pieces := input_var.pieces }
          (i₀ + (((Ecc.MulFixed.FullWidth.circuit R windows).call cfg.1 ()).operations
            i₀).regionCount)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
        env.hint := by
      rw [hashC_proverAssumptions_eq', h_input]
      exact ⟨hns, hPBounds, ⟨bx, byv⟩, hB0⟩
    -- the hash child's honest contract (prover side: the output point IS the honest hash)
    have hPSHash := (h_spec_1 (by rw [hashC_envAssumptions_eq']; exact hTableE)
      trivial (by with_unfolding_all exact hPAhash)).2
    rw [hashC_proverSpec_eq'] at hPSHash
    have hres := hPSHash ⟨bx, byv⟩ (by
      rw [← h_input] at hB0
      with_unfolding_all exact hB0)
    -- the prover contract's output is the verifier eval over the hint-erased env;
    -- projection commute through the componentwise `ProvableStruct.eval` (the flat
    -- eval of the whole symbolic-size Output struct is a whnf wall)
    have hpointP : (ProvableStruct.eval place env.toEnvironment x_gen_out_0).point
        = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point
          : Value Point Fp) := by
      with_unfolding_all rfl
    -- the hash point equals the honest B0
    have hPB0 : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point : Value Point Fp)
        = (⟨bx, byv⟩ : Point Fp) := by
      have hx : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point : Value Point Fp).x = bx := by
        rw [← hpointP]; exact hres.1
      have hy : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point : Value Point Fp).y = byv := by
        rw [← hpointP]; exact hres.2
      rw [← hx, ← hy]
    have hB0valid : (⟨bx, byv⟩ : Point Fp).Valid :=
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_valid (Or.inl hQ)
        (Sinsemilla.Chain.pieceChunks_bound
          (Sinsemilla.Chain.pieceChunks_honestChunks ns input.pieces hPBounds)) hB0
    refine ⟨⟨by rw [blind_envAssumptions_eq]; exact hMulE,
      by rw [blind_assumptions_eq]; trivial,
      by rw [blind_proverAssumptions_eq, blind_extract_eq]; exact hWin⟩,
      ⟨by rw [hashC_envAssumptions_eq']; exact hTableE, trivial,
        by with_unfolding_all exact hPAhash⟩,
      trivial, ?_, trivial⟩
    show (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point
        : Value Point Fp).Valid ∧
      (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_1
        : Value Point Fp).Valid
    constructor
    · rw [hPB0]; exact hB0valid
    · rw [hBl]; exact R.smul_valid _

end Halo2.Ironwood.Sinsemilla.CommitDomain
