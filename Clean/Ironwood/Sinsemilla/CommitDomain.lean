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
import Clean.Halo2.CircuitTypeDeriving

/-!
# Sinsemilla commit domain

`commit(msg, r) = hash_to_point(Q, msg) + [r]·R`, keeping the per-piece running sums `zs`
(`NoteCommit`/`CommitIvk` read individual `zs[i][j]` cells). The `[r]·R` leg is full-width
fixed-base scalar mul (`Ecc.MulFixed.FullWidth.circuit R`): the blinding scalar enters as the
input's nat-valued reading program `r`, the child derives its 85 window witnesses from it, and the
scalar it encodes is extraction data, so the commitment `Spec` is stated at the extracted scalar.

The `Chain.circuit` enters at an accumulator seeded from the domain point `Q`: the wrapper assigns
`Q`'s coordinates into the entering cells as constrained constants, so soundness pins `A = Q`.

Reference: `halo2_gadgets/src/sinsemilla.rs`.
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

/-- The `commit` config, parameterized by the blinding child's config type `BCfg`. -/
structure Config (BCfg : Type) where
  -- The hash leg's config.
  hashConfig : HashPiece.Config
  -- The final complete-addition child's config.
  addConfig : Ecc.Add.Config
  -- The blinding child's config.
  blindConfig : BCfg

/-! ## Inputs / Output -/

/-- The message pieces and the blinding scalar's nat-valued reading program `r` (a prover hint —
Rust `Value<pallas::Scalar>`; the full-width child derives its 85 window witnesses from it and the
scalar it encodes is the child's extraction data). -/
structure Input (k : ℕ) (F : Type) where
  -- The message pieces (the whole `k`-piece message).
  pieces : Vector F k
  -- The blinding scalar's nat-valued reading program (prover hint).
  r : UnconstrainedNat F
deriving CircuitType

structure Output (ns : List ℕ) (F : Type) where
  -- The commitment point.
  point : Point F
  -- The hash running sums.
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-! ## The commit body

`commit = hash_to_point(Q, msg) + [r]R` on the `hash_message` bundle (Q-init inside its region);
the `[r]R` leg is the `Ecc.MulFixed.FullWidth` bundle. -/

/-- `CommitDomain::blinding_factor` is the bare `[r]R` — exactly the full-width fixed-base
mul bundle, whose input is the blinding scalar's nat-valued reading program. -/
def blindingFactor (R : FixedBase) :
    FormalCircuit Fp Ecc.MulFixed.Config Ecc.MulFixed.FullWidth.Config UnconstrainedNat Point :=
  Ecc.MulFixed.FullWidth.circuit R

/-! ## The `commit` bundle -/

open Halo2.Ironwood.Specs.Sinsemilla (hashToPoint)

-- contract bridges for the hash child come from the generated
-- `HashToPoint.hashCircuit_*` home stack
/-- The region count of `commit`: the blinding child's two regions, the hash region, the
final complete addition. -/
private theorem commit_regionCount
    (G : Generators) (ns : List ℕ)
    (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ [])
    (bcfg : Ecc.MulFixed.FullWidth.Config) (hcfg : HashPiece.Config)
    (acfg : Ecc.Add.Config)
    (input : Var (Input ns.length) Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let blindOut ← (Ecc.MulFixed.FullWidth.circuit R).call bcfg input.r
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
      rw [FormalCircuit.call_operations]
      simp only [Circuit.operations]
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
      rw [FormalCircuit.call_operations]
      simp only [Circuit.operations]
      rw [show ((Ecc.Add.add.toFormal "complete point addition").synthesize acfg inp j).2.1
          = ((assignRegion "complete point addition"
              (Ecc.Add.add.synthesize acfg 0 inp)).operations j) from rfl,
        operations_assignRegion]
      simp only [Operations.regionCount]]
  rw [Ecc.MulFixed.FullWidth.circuit_call_regionCount R bcfg input.r i]

/-- `CommitDomain::commit`: `[r]R` (the `Ecc.MulFixed.FullWidth` bundle), `hash_to_point(Q, msg)`
(the hash bundle), and the final complete addition `M + [r]R`. `Spec`: the commitment is
`SinsemillaHashToPoint(Q, chunks) + s·R` at the extracted window scalar `s`, whenever the
hash is defined, with the message chunking and running-sum facts exposed. -/
def commit (G : Generators) (ns : List ℕ)
    (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ []) :
    FormalCircuit Fp
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Ecc.MulFixed.FullWidth.Config × HashPiece.Config × Ecc.Add.Config)
      (Input ns.length) Point where
  name := "sinsemilla commit"
  configure := pure

  synthesize := fun (bcfg, hcfg, acfg) input => do
    let blindOut ← (Ecc.MulFixed.FullWidth.circuit R).call bcfg input.r
    let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
      { pieces := input.pieces }
    let result ← (Ecc.Add.add.toFormal "complete point addition").call acfg
      { p := hashOut.point, q := blindOut }
    pure result

  elaborated := fun (bcfg, hcfg, acfg) =>
    { output := fun input i =>
        ((do
          let blindOut ← (Ecc.MulFixed.FullWidth.circuit R).call bcfg input.r
          let hashOut ← (HashToPoint.hashCircuit G ns Q hQ hns).call hcfg
            { pieces := input.pieces }
          let result ← (Ecc.Add.add.toFormal "complete point addition").call acfg
            { p := hashOut.point, q := blindOut }
          pure result : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 4
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (commit_regionCount G ns R Q hQ hns bcfg hcfg acfg input i).symm }

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

  ProverAssumptions input _ _ :=
    Sinsemilla.Chain.PieceBounds ns (input.pieces) ∧
    (∃ B, hashToPoint G.S Q
      (Sinsemilla.Chain.honestChunks ns (input.pieces)) = some B)

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨hTableE, hMulE⟩ := _hE
    obtain ⟨hBlind, hHash, hAdd⟩ := hc
    -- the blind child's contract: the output is the extracted window scalar times `R`
    have hBl := hBlind (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hBl
    -- the hash child's contract
    have hHashS := hHash (by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE) trivial
    rw [HashToPoint.hashCircuit_spec_eq] at hHashS
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
    obtain ⟨hPBounds, B0, hB0⟩ := hPA
    obtain ⟨bx, byv⟩ := B0
    -- the blind child's contract
    have hBl := (h_spec_0 (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
      (by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial)).1
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hBl
    -- the pieces value bridge: the hint-erased eval of the message-piece cells equals the
    -- prover-view piece value `input_pieces` (`h_input` lands componentwise; the hint-erased
    -- and prover-view evals of a pure-provable var agree up to defeq)
    have hpe : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) input_var.pieces
        : Value (fields ns.length) Fp) = input_pieces := by
      rw [← h_input.1]; with_unfolding_all rfl
    -- the hash child's honest-prover precondition, stated over the hint-erased eval
    have hPAhash : (HashToPoint.hashCircuit G ns Q hQ hns).ProverAssumptions
        ({ pieces := eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) input_var.pieces }
          : Value (Sinsemilla.Chain.Inputs ns.length) Fp)
        ((HashToPoint.hashCircuit G ns Q hQ hns).extract cfg.2.1
          { pieces := input_var.pieces }
          (i₀ + (((Ecc.MulFixed.FullWidth.circuit R).call cfg.1 input_var.r).operations
            i₀).regionCount)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
        env.hint := by
      rw [HashToPoint.hashCircuit_proverAssumptions_eq]
      simp only [hpe]
      exact ⟨hns, hPBounds, ⟨bx, byv⟩, hB0⟩
    -- the hash child's honest contract (prover side: the output point IS the honest hash)
    have hPSHash := (h_spec_1 (by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE)
      trivial (by with_unfolding_all exact hPAhash)).2
    rw [HashToPoint.hashCircuit_proverSpec_eq] at hPSHash
    have hres := hPSHash ⟨bx, byv⟩ (by
      simp only [hpe]; exact hB0)
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
          (Sinsemilla.Chain.pieceChunks_honestChunks ns input_pieces hPBounds)) hB0
    refine ⟨⟨by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hMulE,
      by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial,
      by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial⟩,
      ⟨by rw [HashToPoint.hashCircuit_envAssumptions_eq]; exact hTableE, trivial,
        by with_unfolding_all exact hPAhash⟩,
      trivial, ?_, trivial⟩
    show (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0.point
        : Value Point Fp).Valid ∧
      (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_1
        : Value Point Fp).Valid
    constructor
    · rw [hPB0]; exact hB0valid
    · rw [hBl]; exact R.smul_valid _

/-! ## Bundle contract bridges, shared by the consumers (generated; the bundle stays
folded). Single home for the `commit_*` stacks formerly copy-pasted per consumer file. -/

derive_contract_bridges commit (G : Generators) (ns : List ℕ) (R : FixedBase)
  (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ []) := commit G ns R Q hQ hns

end Halo2.Ironwood.Sinsemilla.CommitDomain
