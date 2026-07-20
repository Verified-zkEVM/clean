import Clean.Ironwood.NoteCommit.Gates
import Clean.Ironwood.NoteCommit.Decompose
import Clean.Ironwood.NoteCommit.Canonicity
import Clean.Ironwood.Specs.SinsemillaBreak
import Clean.Ironwood.NoteCommit.Composites
import Clean.Ironwood.NoteCommit.YComposite
import Clean.Ironwood.Sinsemilla.CommitDomain
import Clean.Ironwood.NoteCommit.MainTheorems
import Clean.Halo2.CircuitTypeDeriving

/-!
# NoteCommit main circuit (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs` — `NoteCommitChip::commit` (lines 1596-1798).
The full flow, in exact region-creation order (VK layout is order-sensitive):

1. witness pieces `a..h` interleaved with the sub-piece short checks
   (`MessagePiece::from_subpieces` / `RangeConstrained::witness_short`),
2. the two `y_canonicity` flows (`y(g_d)` with `b_2`, `y(pk_d)` with `d_1`),
3. `CommitDomain::commit` (the `[rcm]R` blind, `hash_to_point`, the final addition),
4. the four canonicity `witness_check`s (`a'`, `b3_c'`, `e1_f'`, `g1_g2'`),
5. the ten gate regions (`b`/`d`/`e`/`g`/`h` decompositions, then
   `g_d`/`pk_d`/`value`/`rho`/`psi` canonicity).

The hash running-sum cells the gates copy (`z13_a`, `z13_c`, `z1_d`, `z13_f`, `z1_g`,
`z13_g`) are referenced positionally inside the `hash_to_point` region (`Chain`'s
`bits` column at `prefixRows ns i + j`).
-/

namespace Halo2.Ironwood.NoteCommit.Main

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Sinsemilla.HashToPoint (witnessMessagePiece)
open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Specs (bitrange)
open Halo2.Ironwood.Specs.Sinsemilla (Generators)

/-- The NoteCommit message piece lengths in `K = 10`-bit words:
`a(250) ‖ b(10) ‖ c(250) ‖ d(60) ‖ e(10) ‖ f(250) ‖ g(250) ‖ h(10)` — the chain
convention counts words − 1 per piece. -/
def ns : List ℕ := [24, 0, 24, 5, 0, 24, 24, 0]

theorem ns_ne_nil : ns ≠ [] := by simp [ns]

/-- The circuit inputs: the note's field-element cells (`x/y(g_d)`, `x/y(pk_d)`, the
64-bit value, `rho`, `psi`) and the blinding scalar's nat-valued reading program `rcm`
(a prover hint — Rust `Value<pallas::Scalar>`; the fixed-base mul child derives its 85
window witnesses from it and the scalar it encodes is extraction data). -/
structure Inputs (F : Type) where
  gdX : F
  gdY : F
  pkdX : F
  pkdY : F
  value : F
  rho : F
  psi : F
  rcm : UnconstrainedNat F
deriving CircuitType

/-! ## Witness programs

Every piece/sub-piece is witnessed by its canonical bit-slice program over the input
cells (Rust computes the same values from the corresponding `Value`s). -/

/-- A single bit-slice witness: `↑(bitrange cell.val s n)`. -/
def brWit (c : AssignedCell Fp) (s n : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (readCell env c).val s n : ℕ) : Fp)]

@[circuit_norm]
theorem brWit_eval (c : AssignedCell Fp) (s n : ℕ) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((brWit c s n).eval env)[j] = ((bitrange (readCell env c).val s n : ℕ) : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [brWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `b = b_0 + 2⁴·b_1 + 2⁵·b_2 + 2⁶·b_3` (`note_commit.rs:170-174`). -/
def bWit (gdX gdY pkdX : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env gdX).val 250 4 : ℕ) : Fp)
      + ((bitrange (readCell env gdX).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
      + ((bitrange (readCell env gdY).val 0 1 : ℕ) : Fp) * (2 ^ 5 : Fp)
      + ((bitrange (readCell env pkdX).val 0 4 : ℕ) : Fp) * (2 ^ 6 : Fp)]

@[circuit_norm]
theorem bWit_eval (gdX gdY pkdX : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((bWit gdX gdY pkdX).eval env)[j]
      = ((bitrange (readCell env gdX).val 250 4 : ℕ) : Fp)
        + ((bitrange (readCell env gdX).val 254 1 : ℕ) : Fp) * (2 ^ 4 : Fp)
        + ((bitrange (readCell env gdY).val 0 1 : ℕ) : Fp) * (2 ^ 5 : Fp)
        + ((bitrange (readCell env pkdX).val 0 4 : ℕ) : Fp) * (2 ^ 6 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [bWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `d = d_0 + 2·d_1 + 2²·d_2 + 2¹⁰·d_3` (`note_commit.rs:308-314`). -/
def dWit (pkdX pkdY value : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env pkdX).val 254 1 : ℕ) : Fp)
      + ((bitrange (readCell env pkdY).val 0 1 : ℕ) : Fp) * 2
      + ((bitrange (readCell env value).val 0 8 : ℕ) : Fp) * (2 ^ 2 : Fp)
      + ((bitrange (readCell env value).val 8 50 : ℕ) : Fp) * (2 ^ 10 : Fp)]

@[circuit_norm]
theorem dWit_eval (pkdX pkdY value : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((dWit pkdX pkdY value).eval env)[j]
      = ((bitrange (readCell env pkdX).val 254 1 : ℕ) : Fp)
        + ((bitrange (readCell env pkdY).val 0 1 : ℕ) : Fp) * 2
        + ((bitrange (readCell env value).val 0 8 : ℕ) : Fp) * (2 ^ 2 : Fp)
        + ((bitrange (readCell env value).val 8 50 : ℕ) : Fp) * (2 ^ 10 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [dWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `e = e_0 + 2⁶·e_1` (`note_commit.rs:434-438`). -/
def eWit (value rho : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env value).val 58 6 : ℕ) : Fp)
      + ((bitrange (readCell env rho).val 0 4 : ℕ) : Fp) * (2 ^ 6 : Fp)]

@[circuit_norm]
theorem eWit_eval (value rho : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((eWit value rho).eval env)[j]
      = ((bitrange (readCell env value).val 58 6 : ℕ) : Fp)
        + ((bitrange (readCell env rho).val 0 4 : ℕ) : Fp) * (2 ^ 6 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [eWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `g = g_0 + 2·g_1 + 2¹⁰·g_2` (`note_commit.rs:655-659`). -/
def gWit (rho psi : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env rho).val 254 1 : ℕ) : Fp)
      + ((bitrange (readCell env psi).val 0 9 : ℕ) : Fp) * 2
      + ((bitrange (readCell env psi).val 9 240 : ℕ) : Fp) * (2 ^ 10 : Fp)]

@[circuit_norm]
theorem gWit_eval (rho psi : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((gWit rho psi).eval env)[j]
      = ((bitrange (readCell env rho).val 254 1 : ℕ) : Fp)
        + ((bitrange (readCell env psi).val 0 9 : ℕ) : Fp) * 2
        + ((bitrange (readCell env psi).val 9 240 : ℕ) : Fp) * (2 ^ 10 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [gWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Piece `h = h_0 + 2⁵·h_1` (four trailing zero bits; `note_commit.rs:786-792`). -/
def hWit (psi : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (readCell env psi).val 249 5 : ℕ) : Fp)
      + ((bitrange (readCell env psi).val 254 1 : ℕ) : Fp) * (2 ^ 5 : Fp)]

@[circuit_norm]
theorem hWit_eval (psi : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((hWit psi).eval env)[j]
      = ((bitrange (readCell env psi).val 249 5 : ℕ) : Fp)
        + ((bitrange (readCell env psi).val 254 1 : ℕ) : Fp) * (2 ^ 5 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [hWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-! ## The main flow -/

/-- The combined config: the eleven NoteCommit gates, the Sinsemilla hash config, the
10-bit lookup config, the fixed-base mul config, and the complete-addition config. -/
structure Config where
  gates : NoteCommit.Config
  hashConfig : Sinsemilla.HashPiece.Config
  lookupConfig : LookupRangeCheck.Config 10
  mulConfig : Ecc.MulFixed.FullWidth.Config
  addConfig : Ecc.Add.Config

/-- The hash running-sum cell `zs[i][j]`: row `prefixRows ns i + j` of the `bits`
column inside the `hash_to_point` region. -/
def zCell (hcfg : Sinsemilla.HashPiece.Config) (iHash : RegionIndex) (i j : ℕ) : AssignedCell Fp :=
  .of iHash (Sinsemilla.Chain.prefixRows ns i + j) hcfg.bits

/-- Read the current region counter (no ops emitted) — anchors the positional
`zCell` references to the flow's starting index. -/
def currentRegion : Circuit Fp RegionIndex := fun i => (i, [], i)

@[circuit_norm]
theorem currentRegion_operations (i : RegionIndex) :
    currentRegion.operations i = [] := by
  with_unfolding_all rfl

@[circuit_norm]
theorem currentRegion_nextRegionIndex (i : RegionIndex) :
    currentRegion.nextRegionIndex i = i := by
  with_unfolding_all rfl

@[circuit_norm]
theorem currentRegion_output (i : RegionIndex) :
    currentRegion.output i = i := by
  with_unfolding_all rfl

/-- The piece/sub-piece cells stage 1 hands to the later stages. -/
structure PieceCells where
  a : AssignedCell Fp
  b : AssignedCell Fp
  c : AssignedCell Fp
  d : AssignedCell Fp
  e : AssignedCell Fp
  f : AssignedCell Fp
  g : AssignedCell Fp
  h : AssignedCell Fp
  b0 : AssignedCell Fp
  b3 : AssignedCell Fp
  d2 : AssignedCell Fp
  e0 : AssignedCell Fp
  e1 : AssignedCell Fp
  g1 : AssignedCell Fp
  h0 : AssignedCell Fp

/-- Stage 1 (15 regions): the eight message pieces interleaved with the seven
sub-piece short checks (`note_commit.rs:1608-1653`). -/
def synthPieces (cfg : Config) (input : Var Inputs Fp) :
    Circuit Fp PieceCells := do
  let a ← witnessMessagePiece cfg.hashConfig (brWit input.gdX 0 250)
  let b0 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit input.gdX 250 4)
  let b3 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit input.pkdX 0 4)
  let b ← witnessMessagePiece cfg.hashConfig (bWit input.gdX input.gdY input.pkdX)
  let c ← witnessMessagePiece cfg.hashConfig (brWit input.pkdX 4 250)
  let d2 ← LookupRangeCheck.witnessShortCheck 10 8 cfg.lookupConfig
    (brWit input.value 0 8)
  let d ← witnessMessagePiece cfg.hashConfig (dWit input.pkdX input.pkdY input.value)
  let e0 ← LookupRangeCheck.witnessShortCheck 10 6 cfg.lookupConfig
    (brWit input.value 58 6)
  let e1 ← LookupRangeCheck.witnessShortCheck 10 4 cfg.lookupConfig
    (brWit input.rho 0 4)
  let e ← witnessMessagePiece cfg.hashConfig (eWit input.value input.rho)
  let f ← witnessMessagePiece cfg.hashConfig (brWit input.rho 4 250)
  let g1 ← LookupRangeCheck.witnessShortCheck 10 9 cfg.lookupConfig
    (brWit input.psi 0 9)
  let g ← witnessMessagePiece cfg.hashConfig (gWit input.rho input.psi)
  let h0 ← LookupRangeCheck.witnessShortCheck 10 5 cfg.lookupConfig
    (brWit input.psi 249 5)
  let h ← witnessMessagePiece cfg.hashConfig (hWit input.psi)
  pure { a, b, c, d, e, f, g, h, b0, b3, d2, e0, e1, g1, h0 }

/-- The cells stage 2 hands to the gate stage. -/
structure CheckCells where
  b2 : AssignedCell Fp
  d1 : AssignedCell Fp
  cm : Var Point Fp
  aZs : Var LookupRangeCheck.Output Fp
  bZs : Var LookupRangeCheck.Output Fp
  eZs : Var LookupRangeCheck.Output Fp
  gZs : Var LookupRangeCheck.Output Fp

/-- Stage 2 (18 regions): the two y-canonicity flows, `CommitDomain::commit`, and the
four canonicity `witness_check`s (`note_commit.rs:1654-1737`). -/
def synthChecks (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (iHash : RegionIndex) : Circuit Fp CheckCells := do
  let b2 ← (YCanonicityCheck.circuit (brWit input.gdY 0 1)).call
    (cfg.gates.y, cfg.lookupConfig) { y := input.gdY }
  let d1 ← (YCanonicityCheck.circuit (brWit input.pkdY 0 1)).call
    (cfg.gates.y, cfg.lookupConfig) { y := input.pkdY }
  let cm ← (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm }
  let aZs ← LookupRangeCheck.witnessCheck 10 13 false cfg.lookupConfig
    (GdCanonicityCheck.aPrimeWit pcs.a)
  let bZs ← LookupRangeCheck.witnessCheck 10 14 false cfg.lookupConfig
    (PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c)
  let eZs ← LookupRangeCheck.witnessCheck 10 14 false cfg.lookupConfig
    (RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f)
  let gZs ← LookupRangeCheck.witnessCheck 10 13 false cfg.lookupConfig
    (PsiCanonicityCheck.g1G2PrimeWit pcs.g1 (zCell cfg.hashConfig iHash 6 1))
  pure { b2, d1, cm, aZs, bZs, eZs, gZs }

/-- Stage 3 (10 regions): the gate regions (`note_commit.rs:1739-1795`). -/
def synthGates (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash : RegionIndex) : Circuit Fp Unit := do
  let b1 ← ((DecomposeB.bundle (brWit input.gdX 254 1)).toFormal
    "NoteCommit MessagePiece b").call cfg.gates.b
    { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 }
  let d0 ← ((DecomposeD.bundle (brWit input.pkdX 254 1)).toFormal
    "NoteCommit MessagePiece d").call cfg.gates.d
    { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2, d3 := zCell cfg.hashConfig iHash 3 1 }
  let _ ← (DecomposeE.bundle.toFormal "NoteCommit MessagePiece e").call cfg.gates.e
    { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 }
  let g0 ← ((DecomposeG.bundle (brWit input.rho 254 1)).toFormal
    "NoteCommit MessagePiece g").call cfg.gates.g
    { g := pcs.g, g1 := pcs.g1, g2 := zCell cfg.hashConfig iHash 6 1 }
  let h1 ← ((DecomposeH.bundle (brWit input.psi 254 1)).toFormal
    "NoteCommit MessagePiece h").call cfg.gates.h { h := pcs.h, h0 := pcs.h0 }
  let _ ← (GdCanonicity.bundle.toFormal "NoteCommit input g_d").call cfg.gates.gd
    { gdX := input.gdX, b0 := pcs.b0, b1, a := pcs.a, aPrime := ccs.aZs.z0,
      z13A := zCell cfg.hashConfig iHash 0 13, z13APrime := ccs.aZs.zLast }
  let _ ← (PkdCanonicity.bundle.toFormal "NoteCommit input pk_d").call cfg.gates.pkd
    { pkdX := input.pkdX, b3 := pcs.b3, d0, c := pcs.c, b3CPrime := ccs.bZs.z0,
      z13C := zCell cfg.hashConfig iHash 2 13, z14B3CPrime := ccs.bZs.zLast }
  let _ ← (ValueCanonicity.bundle.toFormal "NoteCommit input value").call cfg.gates.value
    { value := input.value, d2 := pcs.d2, d3 := zCell cfg.hashConfig iHash 3 1,
      e0 := pcs.e0 }
  let _ ← (RhoCanonicity.bundle.toFormal "NoteCommit input rho").call cfg.gates.rho
    { rho := input.rho, e1 := pcs.e1, g0, f := pcs.f, e1FPrime := ccs.eZs.z0,
      z13F := zCell cfg.hashConfig iHash 5 13, z14E1FPrime := ccs.eZs.zLast }
  let _ ← (PsiCanonicity.bundle.toFormal "NoteCommit input psi").call cfg.gates.psi
    { psi := input.psi, h0 := pcs.h0, g1 := pcs.g1, h1,
      g2 := zCell cfg.hashConfig iHash 6 1, g1G2Prime := ccs.gZs.z0,
      z13G := zCell cfg.hashConfig iHash 6 13, z13G1G2Prime := ccs.gZs.zLast }
  pure ()

/-- Rust `NoteCommitChip::commit` (`note_commit.rs:1596-1798`), in exact region order.
The `rcm` blinding scalar enters as the input's nat-valued reading program. -/
def synth (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) : Circuit Fp (Var Point Fp) := do
  let i₀ ← currentRegion
  -- the `hash_to_point` region of the `CommitDomain::commit` in stage 2 (region 28 of
  -- the flow: 15 piece/short regions, two 5-region y-canonicity flows, the 2-region
  -- blind)
  let iHash := i₀ + 27
  let pcs ← synthPieces cfg input
  let ccs ← synthChecks G R Q hQ cfg input pcs iHash
  synthGates cfg input pcs ccs iHash
  pure ccs.cm

/-! ## Region counts -/

/-- A `toFormal`-lifted region bundle's call chunk is exactly one region. -/
private theorem toFormal_call_regionCount {CI Cfg : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (b : FormalRegionCircuit Fp CI Cfg Input Output) (name : String) (cfg : Cfg)
    (inp : Var Input Fp) (j : RegionIndex) :
    Operations.regionCount (((b.toFormal name).call cfg inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

/-- The y-canonicity flow's call chunk spans its five regions. -/
private theorem yc_call_regionCount (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (j : RegionIndex) :
    Operations.regionCount
      (((YCanonicityCheck.circuit w).call c inp).operations j) = 5 := by
  rw [FormalCircuit.call_regionCount]
  rfl

/-- The commit call chunk spans its four regions. -/
private theorem commit_call_regionCount (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
        c inp).operations j) = 4 := by
  rw [FormalCircuit.call_regionCount]
  rfl

theorem synthPieces_regionCount (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    Operations.regionCount ((synthPieces cfg input).operations i) = 15 := by
  simp only [synthPieces, LookupRangeCheck.witnessShortCheck,
    Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

theorem synthChecks_regionCount (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash : RegionIndex)
    (i : RegionIndex) :
    Operations.regionCount
      ((synthChecks G R Q hQ cfg input pcs iHash).operations i) = 18 := by
  simp only [synthChecks, LookupRangeCheck.witnessCheck, circuit_norm,
    Circuit.operations_bind, operations_assignRegion, Operations.regionCount_append,
    Operations.regionCount]
  rw [yc_call_regionCount, yc_call_regionCount, commit_call_regionCount]

theorem synthGates_regionCount (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthGates cfg input pcs ccs iHash).operations i) = 10 := by
  simp only [synthGates, circuit_norm, Circuit.operations_bind,
    Operations.regionCount_append]
  rw [toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount, toFormal_call_regionCount, toFormal_call_regionCount,
    toFormal_call_regionCount]

/-- The region count of the flow: 15 piece/short regions, the 18-region check stage,
the 10 gate regions — 43. -/
theorem synth_regionCount (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synth G R Q hQ cfg input).operations i) = 43 := by
  simp only [synth, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append]
  rw [synthPieces_regionCount, synthChecks_regionCount, synthGates_regionCount]

theorem synthPieces_nextRegionIndex (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    (synthPieces cfg input).nextRegionIndex i = i + 15 := by
  with_unfolding_all rfl

theorem synthChecks_nextRegionIndex (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash : RegionIndex)
    (i : RegionIndex) :
    (synthChecks G R Q hQ cfg input pcs iHash).nextRegionIndex i = i + 18 := by
  with_unfolding_all rfl

theorem synthPieces_output (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    (synthPieces cfg input).output i
      = { a := .of i 0 cfg.hashConfig.witnessPieces,
          b := .of (i + 3) 0 cfg.hashConfig.witnessPieces,
          c := .of (i + 4) 0 cfg.hashConfig.witnessPieces,
          d := .of (i + 6) 0 cfg.hashConfig.witnessPieces,
          e := .of (i + 9) 0 cfg.hashConfig.witnessPieces,
          f := .of (i + 10) 0 cfg.hashConfig.witnessPieces,
          g := .of (i + 12) 0 cfg.hashConfig.witnessPieces,
          h := .of (i + 14) 0 cfg.hashConfig.witnessPieces,
          b0 := .of (i + 1) 0 cfg.lookupConfig.runningSum,
          b3 := .of (i + 2) 0 cfg.lookupConfig.runningSum,
          d2 := .of (i + 5) 0 cfg.lookupConfig.runningSum,
          e0 := .of (i + 7) 0 cfg.lookupConfig.runningSum,
          e1 := .of (i + 8) 0 cfg.lookupConfig.runningSum,
          g1 := .of (i + 11) 0 cfg.lookupConfig.runningSum,
          h0 := .of (i + 13) 0 cfg.lookupConfig.runningSum } := by
  with_unfolding_all rfl

theorem synthChecks_output (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash : RegionIndex)
    (i : RegionIndex) :
    (synthChecks G R Q hQ cfg input pcs iHash).output i
      = { b2 := .of (i + 4) 0 (cfg.gates.y.advices 6),
          d1 := .of (i + 5 + 4) 0 (cfg.gates.y.advices 6),
          cm := (Sinsemilla.CommitDomain.commit G ns R Q hQ
            ns_ne_nil).output (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
            { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
              r := input.rcm }
            (i + 10),
          aZs := { z0 := .of (i + 14) 0 cfg.lookupConfig.runningSum,
                   zLast := .of (i + 14) 13 cfg.lookupConfig.runningSum },
          bZs := { z0 := .of (i + 15) 0 cfg.lookupConfig.runningSum,
                   zLast := .of (i + 15) 14 cfg.lookupConfig.runningSum },
          eZs := { z0 := .of (i + 16) 0 cfg.lookupConfig.runningSum,
                   zLast := .of (i + 16) 14 cfg.lookupConfig.runningSum },
          gZs := { z0 := .of (i + 17) 0 cfg.lookupConfig.runningSum,
                   zLast := .of (i + 17) 13 cfg.lookupConfig.runningSum } } := by
  with_unfolding_all rfl

/-! ## The bundle (factored: standalone elaborated/contract/proofs) -/

open Halo2.Ironwood.Specs.Sinsemilla (hashToPoint hashToPointB SpecOrBreak)
open CompElliptic.Fields.Pasta (Fq)

/-- The elaborated metadata, standalone (the factored soundness statement needs the
instance). -/
instance elaborated (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config) :
    ElaboratedCircuit Fp Inputs Point (synth G R Q hQ cfg) where
  output input i := (synth G R Q hQ cfg input).output i
  regionCount _ := 43
  output_eq := by intro _ _; rfl
  regionCount_eq input i := (synth_regionCount G R Q hQ cfg input i).symm

def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  Sinsemilla.GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.mulConfig env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

def Assumptions (input : Value Inputs Fp) : Prop :=
  Halo2.Ironwood.Point.OnCurve ⟨input.gdX, input.gdY⟩ ∧
  Halo2.Ironwood.Point.OnCurve ⟨input.pkdX, input.pkdY⟩

/-- The extracted `rcm` window data: the fixed-base mul's window readings and the scalar
they encode, inside the commit child (regions `i₀+25`/`i₀+26`). -/
def rcmExtract (cfg : Config) (_ : Var Inputs Fp) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : Vector Fp 85 × Fq :=
  Ecc.MulFixed.FullWidth.fwExtract cfg.mulConfig (i₀ + 25) env

/-- Breaks-as-data commitment contract (zcash/ironwood#45): either the Sinsemilla
chain over the note's canonical chunks is defined and the output is the commitment
`B + [rcm]R`, or the incomplete-addition escape is exhibited as a valid break
(`Halo2.Ironwood.Specs.Sinsemilla.ValidBreak`).

The 64-bit value bound is exported (from the `ValueCanonicity` gate): without it the
statement can't type `v` as §4.17.4 does — `noteScalars` bitranges truncate `v` at 64
bits, so the commitment equation alone does not bound the field element. -/
def Spec (G : Generators) (Q : Point Fp) (R : FixedBase)
    (input : Value Inputs Fp) (output : Value Point Fp)
    (rcm : Vector Fp 85 × Fq) : Prop :=
  (show Fp from input.value).val < 2 ^ 64 ∧
  SpecOrBreak G.S Q (fun B => output = B + (rcm.2 • R : Halo2.Ironwood.Point Fp))
    (hashToPointB G.S Q
      (Halo2.Ironwood.NoteCommit.noteScalars ⟨input.gdX, input.gdY⟩
        ⟨input.pkdX, input.pkdY⟩ input.value input.rho input.psi).chunks)

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Inputs Fp) (_ : Vector Fp 85 × Fq)
    (_ : ProverHint Fp) : Prop :=
  Halo2.Ironwood.Point.OnCurve ⟨input.gdX, input.gdY⟩ ∧
  Halo2.Ironwood.Point.OnCurve ⟨input.pkdX, input.pkdY⟩ ∧
  (show Fp from input.value).val < 2 ^ 64 ∧
  (∃ B, hashToPoint G.S Q
    (Halo2.Ironwood.NoteCommit.noteScalars ⟨input.gdX, input.gdY⟩
      ⟨input.pkdX, input.pkdY⟩ input.value input.rho input.psi).chunks = some B)

end Halo2.Ironwood.NoteCommit.Main
