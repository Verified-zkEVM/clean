import Clean.Ironwood.CommitIvk.Composite
import Clean.Ironwood.NoteCommit.Main
import Clean.Ironwood.Sinsemilla.CommitDomain
import Clean.Ironwood.CommitIvk.MainTheorems
import Clean.Ironwood.Specs.SinsemillaBreak
import Clean.Halo2.CircuitTypeDeriving

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs` `gadgets::commit_ivk` (`commit_ivk.rs:261-414`).

# The CommitIvk main circuit

The full `Commit^ivk` flow, region-for-region:

1. **Pieces** (7 regions, `commit_ivk.rs:289-350`): witness piece `a = ak[0..250)`;
   short checks `b_0 = ak[250..254)` (4 bits) and `b_2 = nk[0..5)` (5 bits); piece
   `b = b_0 + 2⁴·b_1 + 2⁵·b_2`; piece `c = nk[5..245)`; short check
   `d_0 = nk[245..254)` (9 bits); piece `d = d_0 + 2⁹·d_1`.
2. **Commit** (4 regions, `commit_ivk.rs:357-366` → `CommitDomain::short_commit`,
   which is `commit` + `extract_p` — no extra regions): the `[rivk]R` blind
   (full-width fixed-base mul, 2 regions), `hash_to_point`, the complete addition.
3. **Canonicity** (3 regions, `commit_ivk.rs:375-411`): the `a'`/`b2_c'` shift
   `witness_check`s and the two-row canonicity gate region — the proven
   `CommitIvk` composite, called as a unit (contiguous in Rust).

The output is the extracted `x`-coordinate (`ivk`). `Spec` is the breaks-as-data
`Commit^ivk` relation at the extracted `rivk` window scalar (zcash/ironwood#45).
-/

namespace Zcash.Circuits.CommitIvk.Main

open Halo2
open Sinsemilla.HashToPoint (witnessMessagePiece)
open Ecc.MulFixed (FixedBase)
open Specs (bitrange)
open Specs.Sinsemilla (Generators)
open NoteCommit.Main (brWit currentRegion)

/-- Piece word counts minus one, per the chain convention: `a` = 25 words, `b` = 1,
`c` = 24, `d` = 1 (`I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk)` split at `250/10/240/10` bits). -/
def ns : List ℕ := [24, 0, 23, 0]

theorem ns_ne_nil : ns ≠ [] := by simp [ns]

/-- The main circuit's inputs: the `ak`/`nk` field-element cells and the blinding
scalar's nat-valued reading program `rivk` (a prover hint). -/
structure Inputs (F : Type) where
  ak : F
  nk : F
  rivk : UnconstrainedNat F
deriving CircuitType

/-! ## Witness programs (the canonical bit-slice values; Rust computes the same from
the corresponding `Value`s) -/

/-- Piece `b = b_0 + 2⁴·b_1 + 2⁵·b_2` (`commit_ivk.rs:315-320`). -/
def bWit (ak nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env ak).val 250 4 : ℕ) : Fp)
      + ((bitrange (readCell env ak).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
      + ((bitrange (readCell env nk).val 0 5 : ℕ) : Fp) * (2 ^ 5 : Fp)]

@[circuit_norm]
theorem bWit_eval (ak nk : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((bWit ak nk).eval env)[j]
      = ((bitrange (readCell env ak).val 250 4 : ℕ) : Fp)
        + ((bitrange (readCell env ak).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
        + ((bitrange (readCell env nk).val 0 5 : ℕ) : Fp) * (2 ^ 5 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [bWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `d = d_0 + 2⁹·d_1` (`commit_ivk.rs:343-347`). -/
def dWit (nk : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env nk).val 245 9 : ℕ) : Fp)
      + ((bitrange (readCell env nk).val 254 1 : ℕ) : Fp) * (2 ^ 9 : Fp)]

@[circuit_norm]
theorem dWit_eval (nk : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((dWit nk).eval env)[j]
      = ((bitrange (readCell env nk).val 245 9 : ℕ) : Fp)
        + ((bitrange (readCell env nk).val 254 1 : ℕ) : Fp) * (2 ^ 9 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [dWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-! ## Config and layout -/

structure Config where
  gate : CommitIvk.Config
  hashConfig : Sinsemilla.HashPiece.Config
  lookupConfig : LookupRangeCheck.Config 10
  mulConfig : Ecc.MulFixed.FullWidth.Config
  addConfig : Ecc.Add.Config

/-- The hash running-sum cell `zs[i][j]`: row `prefixRows ns i + j` of the `bits`
column inside the `hash_to_point` region. -/
def zCell (hcfg : Sinsemilla.HashPiece.Config) (iHash : RegionIndex) (i j : ℕ) :
    AssignedCell Fp :=
  .of iHash (Sinsemilla.Chain.prefixRows ns i + j) hcfg.bits

/-- The piece cells stage 1 hands to the later stages. -/
structure PieceCells where
  a : AssignedCell Fp
  b : AssignedCell Fp
  c : AssignedCell Fp
  d : AssignedCell Fp
  b0 : AssignedCell Fp
  b2 : AssignedCell Fp
  d0 : AssignedCell Fp

/-- Stage 1 (7 regions): the four message pieces interleaved with the three
sub-piece short checks (`commit_ivk.rs:289-350`). -/
def synthPieces (cfg : Config) (ak nk : AssignedCell Fp) :
    Circuit Fp PieceCells := do
  let a ← witnessMessagePiece cfg.hashConfig (brWit ak 0 250)
  let b0 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit ak 250 4)
  let b2 ← LookupRangeCheck.witnessShortCheck 10 5 cfg.lookupConfig
    (brWit nk 0 5)
  let b ← witnessMessagePiece cfg.hashConfig (bWit ak nk)
  let c ← witnessMessagePiece cfg.hashConfig (brWit nk 5 240)
  let d0 ← LookupRangeCheck.witnessShortCheck 10 9 cfg.lookupConfig
    (brWit nk 245 9)
  let d ← witnessMessagePiece cfg.hashConfig (dWit nk)
  pure { a, b, c, d, b0, b2, d0 }

/-- The full flow: pieces, the 4-region commit, the 3-region canonicity composite.
Output: the extracted `x`-coordinate (`ivk`). -/
def synth (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) : Circuit Fp (Var field Fp) := do
  let i₀ ← currentRegion
  let iHash := i₀ + 9
  let pcs ← synthPieces cfg input.ak input.nk
  let cm ← (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d], r := input.rivk }
  let _ ← (CommitIvk.Canonicity.circuit (brWit input.ak 254 1) (brWit input.nk 254 1)).call
    (cfg.gate, cfg.lookupConfig)
    { ak := input.ak, a := pcs.a, bWhole := pcs.b, b0 := pcs.b0, b2 := pcs.b2,
      z13A := zCell cfg.hashConfig iHash 0 13,
      nk := input.nk, c := pcs.c, dWhole := pcs.d, d0 := pcs.d0,
      z13C := zCell cfg.hashConfig iHash 2 13 }
  pure cm.x

/-! ## Region counts and stage outputs -/

theorem synthPieces_regionCount (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    Operations.regionCount ((synthPieces cfg ak nk).operations i) = 7 := by
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

/-- The region count of the flow: 7 piece/short regions, the 4-region commit, the
3-region canonicity composite — 14. -/
theorem synth_regionCount (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synth G R Q hQ cfg input).operations i) = 14 := by
  -- lean explicit set: `circuit_norm`'s dsimp-normalization of op payloads is
  -- kernel-expensive now that call chunks are kernel-transparent (no constructor head)
  simp only [synth, Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.nextRegionIndex_call', FormalCircuit.output_call',
    NoteCommit.Main.currentRegion_operations]
  rw [synthPieces_regionCount, Sinsemilla.CommitDomain.commit_call_regionCount, Canonicity.circuit_call_regionCount]

theorem synthPieces_nextRegionIndex (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    (synthPieces cfg ak nk).nextRegionIndex i = i + 7 := by
  rfl

theorem synthPieces_output (cfg : Config) (ak nk : AssignedCell Fp)
    (i : RegionIndex) :
    (synthPieces cfg ak nk).output i
      = { a := .of i 0 cfg.hashConfig.witnessPieces,
          b := .of (i + 3) 0 cfg.hashConfig.witnessPieces,
          c := .of (i + 4) 0 cfg.hashConfig.witnessPieces,
          d := .of (i + 6) 0 cfg.hashConfig.witnessPieces,
          b0 := .of (i + 1) 0 cfg.lookupConfig.runningSum,
          b2 := .of (i + 2) 0 cfg.lookupConfig.runningSum,
          d0 := .of (i + 5) 0 cfg.lookupConfig.runningSum } := by
  rfl

/-! ## The bundle contract -/

open Specs.Sinsemilla (hashToPoint HashGuarded commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

@[keygen_norm]
def keygenRequirements (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) : KeygenRequirements Fp Config where
  configLawful cfg :=
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).Configured
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
  gates cfg configured :=
    [LookupRangeCheck.bitshiftGate 10 cfg.lookupConfig, CommitIvk.gate cfg.gate] ++
      configured.gates
  lookups cfg configured :=
    [LookupRangeCheck.rangeCheckLookup 10 cfg.lookupConfig] ++ configured.lookups

instance elaborated (G : Generators) (R : FixedBase) (Q : Point Fp)
    (hQ : Q.OnCurve) :
    ElaboratedCircuit Fp Config Config Inputs field
      (fun config => pure config) (synth G R Q hQ) where
  keygenRequirements := keygenRequirements G R Q hQ
  registered := by
    keygen_registration [
      synth,
      synthPieces,
      Sinsemilla.HashToPoint.witnessMessagePiece]
  output cfg input i := (synth G R Q hQ cfg input).output i
  regionCount _ := 14
  output_eq := by intro _ _ _; rfl
  regionCount_eq cfg input i :=
    (synth_regionCount G R Q hQ cfg input i).symm

def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  Sinsemilla.GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.mulConfig env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- The extracted `rivk` window data: the fixed-base mul's window readings and the
scalar they encode, inside the commit child (regions `i₀+7`/`i₀+8`). -/
def rivkExtract (cfg : Config) (_ : Var Inputs Fp) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : Vector Fp 85 × Fq :=
  Ecc.MulFixed.FullWidth.fwExtract cfg.mulConfig (i₀ + 7) env

/-- The `Commit^ivk` contract in the specification's guarded ⊥-model (§4.17.4's
`ivk ∈ {…, ⊥}`): whenever the Sinsemilla chain over the canonical `commit_ivk`
chunks of `ak`/`nk` is defined, the output is the extracted short commitment
`(B + [rivk]R).x`. Exceptional chains are not constrained here; the security layer
recomputes them from the same chunks and consumes them as breaks
(`specOrBreak_hashToPointB_iff_guarded`). -/
def Spec (G : Generators) (Q : Point Fp) (R : FixedBase)
    (input : Value Inputs Fp) (output : Value field Fp)
    (rivk : Vector Fp 85 × Fq) : Prop :=
  HashGuarded G.S Q
    (commitIvkChunks (show Fp from input.ak).val (show Fp from input.nk).val)
    (fun B => (output : Fp) = (B + (rivk.2 • R : Point Fp)).x)

/-- Honest-prover precondition: the canonical message hash is defined. The full-width
child derives and proves the 3-bit bounds for its scalar windows. -/
def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Inputs Fp) (_ : Vector Fp 85 × Fq)
    (_ : ProverHint Fp) : Prop :=
  ∃ B, hashToPoint G.S Q
    (commitIvkChunks (show Fp from input.ak).val (show Fp from input.nk).val) = some B

end Zcash.Circuits.CommitIvk.Main
