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

namespace Zcash.Circuits.NoteCommit.Main

open Halo2
open Sinsemilla.HashToPoint (witnessMessagePiece)
open Ecc.MulFixed (FixedBase)
open Specs (bitrange)
open Specs.Sinsemilla (Generators)

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
  rfl

@[circuit_norm]
theorem currentRegion_nextRegionIndex (i : RegionIndex) :
    currentRegion.nextRegionIndex i = i := by
  rfl

@[circuit_norm]
theorem currentRegion_output (i : RegionIndex) :
    currentRegion.output i = i := by
  rfl

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

/-- Columns of the stage-1 cells consumed by later copy operations. -/
@[keygen_norm]
def PieceCells.permutationColumns (cells : PieceCells) : List AnyColumn :=
  [cells.a.cell.column, cells.b.cell.column, cells.c.cell.column,
    cells.d.cell.column, cells.e.cell.column, cells.f.cell.column,
    cells.g.cell.column, cells.h.cell.column, cells.b0.cell.column,
    cells.b3.cell.column, cells.d2.cell.column, cells.e0.cell.column,
    cells.e1.cell.column, cells.g1.cell.column, cells.h0.cell.column]

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

/-- Columns of the stage-2 cells consumed by the final gate stage. -/
@[keygen_norm]
def CheckCells.permutationColumns (cells : CheckCells) : List AnyColumn :=
  [cells.b2.cell.column, cells.d1.cell.column,
    cells.aZs.z0.cell.column, cells.aZs.zLast.cell.column,
    cells.bZs.z0.cell.column, cells.bZs.zLast.cell.column,
    cells.eZs.z0.cell.column, cells.eZs.zLast.cell.column,
    cells.gZs.z0.cell.column, cells.gZs.zLast.cell.column]

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

/-- Outputs of the five message-decomposition regions consumed by the five canonicity
regions. -/
structure GateCells where
  b1 : AssignedCell Fp
  d0 : AssignedCell Fp
  g0 : AssignedCell Fp
  h1 : AssignedCell Fp

@[keygen_norm]
def GateCells.permutationColumns (cells : GateCells) : List AnyColumn :=
  [cells.b1.cell.column, cells.d0.cell.column,
    cells.g0.cell.column, cells.h1.cell.column]

/-- The five message-decomposition regions at the start of stage 3. -/
def synthDecompositions (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash : RegionIndex) : Circuit Fp GateCells := do
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
  pure { b1, d0, g0, h1 }

private theorem decomposeB_toFormal_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeB.Config) (input : Var DecomposeB.Inputs Fp) (i : RegionIndex) :
    ((DecomposeB.bundle w).toFormal name).output cfg input i =
      AssignedCell.of i 0 cfg.colR := by
  show (((DecomposeB.bundle w).synthesize cfg 0 input)).output i = _
  simp only [DecomposeB.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeD_toFormal_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeD.Config) (input : Var DecomposeD.Inputs Fp) (i : RegionIndex) :
    ((DecomposeD.bundle w).toFormal name).output cfg input i =
      AssignedCell.of i 0 cfg.colM := by
  show (((DecomposeD.bundle w).synthesize cfg 0 input)).output i = _
  simp only [DecomposeD.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeG_toFormal_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeG.Config) (input : Var DecomposeG.Inputs Fp) (i : RegionIndex) :
    ((DecomposeG.bundle w).toFormal name).output cfg input i =
      AssignedCell.of i 0 cfg.colM := by
  show (((DecomposeG.bundle w).synthesize cfg 0 input)).output i = _
  simp only [DecomposeG.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

private theorem decomposeH_toFormal_output (w : WitgenIR Fp 1) (name : String)
    (cfg : DecomposeH.Config) (input : Var DecomposeH.Inputs Fp) (i : RegionIndex) :
    ((DecomposeH.bundle w).toFormal name).output cfg input i =
      AssignedCell.of i 0 cfg.colR := by
  show (((DecomposeH.bundle w).synthesize cfg 0 input)).output i = _
  simp only [DecomposeH.bundle, circuit_norm, RegionCircuit.output_bind]

@[keygen_output_norm]
theorem synthDecompositions_output (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (iHash i : RegionIndex) :
    (synthDecompositions cfg input pcs ccs iHash).output i =
      { b1 := .of i 0 cfg.gates.b.colR
        d0 := .of (i + 1) 0 cfg.gates.d.colM
        g0 := .of (i + 3) 0 cfg.gates.g.colM
        h1 := .of (i + 4) 0 cfg.gates.h.colR } := by
  simp only [synthDecompositions, circuit_norm,
    decomposeB_toFormal_output, decomposeD_toFormal_output,
    decomposeG_toFormal_output, decomposeH_toFormal_output]

/-- Canonicity regions for the diversified base point, recipient key, and value. -/
def synthGdPkdValueCanonicity (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (gcs : GateCells)
    (iHash : RegionIndex) : Circuit Fp Unit := do
  let _ ← (GdCanonicity.bundle.toFormal "NoteCommit input g_d").call cfg.gates.gd
    { gdX := input.gdX, b0 := pcs.b0, b1 := gcs.b1, a := pcs.a, aPrime := ccs.aZs.z0,
      z13A := zCell cfg.hashConfig iHash 0 13, z13APrime := ccs.aZs.zLast }
  let _ ← (PkdCanonicity.bundle.toFormal "NoteCommit input pk_d").call cfg.gates.pkd
    { pkdX := input.pkdX, b3 := pcs.b3, d0 := gcs.d0, c := pcs.c, b3CPrime := ccs.bZs.z0,
      z13C := zCell cfg.hashConfig iHash 2 13, z14B3CPrime := ccs.bZs.zLast }
  let _ ← (ValueCanonicity.bundle.toFormal "NoteCommit input value").call cfg.gates.value
    { value := input.value, d2 := pcs.d2, d3 := zCell cfg.hashConfig iHash 3 1,
      e0 := pcs.e0 }
  pure ()

/-- Canonicity regions for rho and psi. -/
def synthRhoPsiCanonicity (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (gcs : GateCells)
    (iHash : RegionIndex) : Circuit Fp Unit := do
  let _ ← (RhoCanonicity.bundle.toFormal "NoteCommit input rho").call cfg.gates.rho
    { rho := input.rho, e1 := pcs.e1, g0 := gcs.g0, f := pcs.f, e1FPrime := ccs.eZs.z0,
      z13F := zCell cfg.hashConfig iHash 5 13, z14E1FPrime := ccs.eZs.zLast }
  let _ ← (PsiCanonicity.bundle.toFormal "NoteCommit input psi").call cfg.gates.psi
    { psi := input.psi, h0 := pcs.h0, g1 := pcs.g1, h1 := gcs.h1,
      g2 := zCell cfg.hashConfig iHash 6 1, g1G2Prime := ccs.gZs.z0,
      z13G := zCell cfg.hashConfig iHash 6 13, z13G1G2Prime := ccs.gZs.zLast }
  pure ()

/-- The five canonicity regions at the end of stage 3. -/
def synthCanonicity (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash : RegionIndex) : Circuit Fp Unit := do
  synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash
  synthRhoPsiCanonicity cfg input pcs ccs gcs iHash

/-- Stage 3 (10 regions): the gate regions (`note_commit.rs:1739-1795`). -/
def synthGates (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash : RegionIndex) : Circuit Fp Unit := do
  let gcs ← synthDecompositions cfg input pcs ccs iHash
  synthCanonicity cfg input pcs ccs gcs iHash

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

/-! The generic `toFormal` contract-transfer bridges, generic over the lifted bundle —
the single userland home (the per-file copies were Category-2 duplicates); their final
home should be framework-side (`Clean/Halo2/Subcircuit.lean`). -/

/-- A `toFormal`-lifted region bundle's call chunk is exactly one region. For manual
`rw`s only — simp-side folding is the generic `foldCallRegionCount` simproc. -/
theorem toFormal_call_regionCount {CI Cfg : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (b : FormalRegionCircuit Fp CI Cfg Input Output) (name : String) (cfg : Cfg)
    (inp : Var Input Fp) (j : RegionIndex) :
    Operations.regionCount (((b.toFormal name).call cfg inp).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

theorem toFormal_spec_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Spec = b.Spec := rfl

theorem toFormal_assumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).Assumptions = b.Assumptions := rfl

theorem toFormal_envAssumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).EnvAssumptions = b.EnvAssumptions := rfl

theorem toFormal_proverAssumptions_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) :
    (b.toFormal name).ProverAssumptions = b.ProverAssumptions := rfl

/-- Pointwise contract transport for a lifted region circuit. This keeps a caller's
possibly large concrete input opaque while crossing the `toFormal` boundary. -/
theorem toFormal_proverAssumptions_iff {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String)
    (input : Value In Fp) (witness : b.Witness Fp) (hint : ProverHint Fp) :
    (b.toFormal name).ProverAssumptions input witness hint ↔
      b.ProverAssumptions input witness hint := Iff.rfl

theorem toFormal_extract_eq {CI Cfg : Type} {In Out : TypeMap}
    [ProvableType In] [ProvableType Out]
    (b : FormalRegionCircuit Fp CI Cfg In Out) (name : String) (cfg : Cfg)
    (inp : Var In Fp) (i : RegionIndex) (env : Placed Environment Fp) :
    (b.toFormal name).extract cfg inp i env = b.extract cfg 0 inp i env := rfl

/-- `nextRegionIndex` of a y-canonicity call, closed form (for the symbolic `nextRegionIndex`/
`output` walks — the opaque `call` barrier is not evaluable). -/
private theorem yc_call_nextRegionIndex (w : WitgenIR Fp 1)
    (c : YCanonicity.Config × LookupRangeCheck.Config 10)
    (inp : Var YCanonicityCheck.Inputs Fp) (j : RegionIndex) :
    ((YCanonicityCheck.circuit w).call c inp).nextRegionIndex j = j + 5 := by
  rw [FormalCircuit.nextRegionIndex_call, YCanonicityCheck.circuit_call_regionCount]

/-- `nextRegionIndex` of the commit call, closed form. -/
private theorem commit_call_nextRegionIndex (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (j : RegionIndex) :
    ((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
      c inp).nextRegionIndex j = j + 4 := by
  rw [FormalCircuit.nextRegionIndex_call, Sinsemilla.CommitDomain.commit_call_regionCount]

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

theorem synthDecompositions_regionCount (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthDecompositions cfg input pcs ccs iHash).operations i) = 5 := by
  simp only [synthDecompositions, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append]

@[circuit_norm]
theorem synthDecompositions_nextRegionIndex (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (iHash i : RegionIndex) :
    (synthDecompositions cfg input pcs ccs iHash).nextRegionIndex i = i + 5 := by
  simp only [synthDecompositions, circuit_norm]

theorem synthGdPkdValueCanonicity_regionCount (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (gcs : GateCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).operations i) = 3 := by
  simp only [synthGdPkdValueCanonicity, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append]

@[circuit_norm]
theorem synthGdPkdValueCanonicity_nextRegionIndex (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (gcs : GateCells) (iHash i : RegionIndex) :
    (synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).nextRegionIndex i =
      i + 3 := by
  simp only [synthGdPkdValueCanonicity, circuit_norm]

theorem synthRhoPsiCanonicity_regionCount (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (gcs : GateCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthRhoPsiCanonicity cfg input pcs ccs gcs iHash).operations i) = 2 := by
  simp only [synthRhoPsiCanonicity, circuit_norm, Circuit.operations_bind,
    Circuit.operations_pure, Operations.regionCount_append]

theorem synthCanonicity_regionCount (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (gcs : GateCells)
    (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthCanonicity cfg input pcs ccs gcs iHash).operations i) = 5 := by
  simp only [synthCanonicity, circuit_norm, Circuit.operations_bind,
    Operations.regionCount_append]
  rw [synthGdPkdValueCanonicity_regionCount,
    synthRhoPsiCanonicity_regionCount]

theorem synthGates_regionCount (cfg : Config) (input : Var Inputs Fp)
    (pcs : PieceCells) (ccs : CheckCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.regionCount
      ((synthGates cfg input pcs ccs iHash).operations i) = 10 := by
  simp only [synthGates, circuit_norm, Circuit.operations_bind,
    Operations.regionCount_append]
  rw [synthDecompositions_regionCount, synthCanonicity_regionCount]

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
  rfl

theorem synthChecks_nextRegionIndex (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash : RegionIndex)
    (i : RegionIndex) :
    (synthChecks G R Q hQ cfg input pcs iHash).nextRegionIndex i = i + 18 := by
  -- The opaque `call` barrier is not evaluable, so this is no longer a pure defeq walk — but
  -- no call OUTPUT feeds the index chain, so the goal defeq-reduces (binds/assignRegions/pure,
  -- structure-eta through the folded calls) to the three calls' `nextRegionIndex` compositions
  -- plus the four witnessCheck regions. `show` that spelling (single kernel defeq, the
  -- `synthPieces` grade — a simp walk here blows the kernel's timeout), then rewrite only the
  -- three call boundaries.
  show (((Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).call
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
          r := input.rcm }).nextRegionIndex
      (((YCanonicityCheck.circuit (brWit input.pkdY 0 1)).call
          (cfg.gates.y, cfg.lookupConfig) { y := input.pkdY }).nextRegionIndex
        (((YCanonicityCheck.circuit (brWit input.gdY 0 1)).call
            (cfg.gates.y, cfg.lookupConfig) { y := input.gdY }).nextRegionIndex i)))
      + 1 + 1 + 1 + 1 = i + 18
  rw [yc_call_nextRegionIndex, yc_call_nextRegionIndex, commit_call_nextRegionIndex]

/-- Fully reduced footprint of the fifteen piece-witnessing regions. -/
def synthPiecesSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let piece := Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
    cfg.hashConfig
  let short := LookupRangeCheck.witnessShortCheckSynthesisSummary
    10 cfg.lookupConfig
  [piece, short, short, piece, piece, short, piece, short, short,
    piece, piece, short, piece, short, piece].foldr
      FloorPlanner.SynthesisSummary.combine {}

/-- Fully reduced footprint of the two y checks, commitment, and four word checks. -/
def synthChecksSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let y := YCanonicityCheck.synthesisSummary
    cfg.gates.y cfg.lookupConfig
  [y, y,
    Sinsemilla.CommitDomain.commitSynthesisSummary ns
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig),
    LookupRangeCheck.witnessCheckSynthesisSummary
      10 13 false cfg.lookupConfig,
    LookupRangeCheck.witnessCheckSynthesisSummary
      10 14 false cfg.lookupConfig,
    LookupRangeCheck.witnessCheckSynthesisSummary
      10 14 false cfg.lookupConfig,
    LookupRangeCheck.witnessCheckSynthesisSummary
      10 13 false cfg.lookupConfig].foldr
        FloorPlanner.SynthesisSummary.combine {}

/-- Fully reduced footprint of the five decomposition and five canonicity regions. -/
def synthGatesSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  let region (summary : FloorPlanner.RegionSynthesisSummary) :=
    FloorPlanner.SynthesisSummary.ofRegion summary
  [region (DecomposeB.synthesisSummary cfg.gates.b 0),
    region (DecomposeD.synthesisSummary cfg.gates.d 0),
    region (DecomposeE.synthesisSummary cfg.gates.e 0),
    region (DecomposeG.synthesisSummary cfg.gates.g 0),
    region (DecomposeH.synthesisSummary cfg.gates.h 0),
    region (GdCanonicity.synthesisSummary cfg.gates.gd 0),
    region (PkdCanonicity.synthesisSummary cfg.gates.pkd 0),
    region (ValueCanonicity.synthesisSummary cfg.gates.value 0),
    region (RhoCanonicity.synthesisSummary cfg.gates.rho 0),
    region (PsiCanonicity.synthesisSummary cfg.gates.psi 0)].foldr
      FloorPlanner.SynthesisSummary.combine {}

/-- Exact reduced footprint of the complete 43-region NoteCommit flow. -/
def synthesisSummary (cfg : Config) : FloorPlanner.SynthesisSummary :=
  (synthPiecesSynthesisSummary cfg).combine
    ((synthChecksSynthesisSummary cfg).combine
      (synthGatesSynthesisSummary cfg))

@[synthesis_summary_norm]
theorem synthPiecesSynthesisSummary_hasNoFixedWrites (cfg : Config) :
    (synthPiecesSynthesisSummary cfg).HasNoFixedWrites := by
  simp only [synthPiecesSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem synthGatesSynthesisSummary_hasNoFixedWrites (cfg : Config) :
    (synthGatesSynthesisSummary cfg).HasNoFixedWrites := by
  simp only [synthGatesSynthesisSummary, List.foldr_cons, List.foldr_nil,
    synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem synthesisSummary_tableRowExtent_eq (cfg : Config) :
    (synthesisSummary cfg).tableRowExtent = 0 := by
  simp only [synthesisSummary, synthPiecesSynthesisSummary,
    synthChecksSynthesisSummary, synthGatesSynthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckDecomposedSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    YCanonicityCheck.synthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesisSummary_instanceRowExtent_eq (cfg : Config) :
    (synthesisSummary cfg).instanceRowExtent = 0 := by
  simp only [synthesisSummary, synthPiecesSynthesisSummary,
    synthChecksSynthesisSummary, synthGatesSynthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckDecomposedSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    YCanonicityCheck.synthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    DecomposeB.synthesisSummary, DecomposeD.synthesisSummary,
    DecomposeE.synthesisSummary, DecomposeG.synthesisSummary,
    DecomposeH.synthesisSummary, GdCanonicity.synthesisSummary,
    PkdCanonicity.synthesisSummary, ValueCanonicity.synthesisSummary,
    RhoCanonicity.synthesisSummary, PsiCanonicity.synthesisSummary,
    YCanonicity.synthesisSummary,
    List.foldr_cons, List.foldr_nil, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthPieces_synthesisSummary_eq (cfg : Config)
    (input : Var Inputs Fp) (region : RegionIndex) :
    FloorPlanner.synthesisSummary ((synthPieces cfg input).operations region) =
      synthPiecesSynthesisSummary cfg := by
  simp only [synthPiecesSynthesisSummary, synthPieces, circuit_norm,
    synthesis_summary_norm, List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

@[synthesis_summary_norm]
theorem synthChecks_synthesisSummary_eq
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthChecks G R Q hQ cfg input pcs iHash).operations region) =
      synthChecksSynthesisSummary cfg := by
  simp only [synthChecksSynthesisSummary, synthChecks, circuit_norm,
    synthesis_summary_norm,
    List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]
  rw [LookupRangeCheck.witnessCheck_synthesisSummary,
    LookupRangeCheck.witnessCheck_synthesisSummary,
    LookupRangeCheck.witnessCheck_synthesisSummary,
    LookupRangeCheck.witnessCheck_synthesisSummary]

@[synthesis_summary_norm]
theorem synthGates_synthesisSummary_eq (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (iHash region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synthGates cfg input pcs ccs iHash).operations region) =
      synthGatesSynthesisSummary cfg := by
  simp only [synthGatesSynthesisSummary, synthGates, synthDecompositions,
    synthCanonicity, synthGdPkdValueCanonicity,
    synthRhoPsiCanonicity, circuit_norm, synthesis_summary_norm,
    List.foldr_cons, List.foldr_nil,
    FloorPlanner.SynthesisSummary.combine_empty]

@[synthesis_summary_norm]
theorem synth_synthesisSummary_eq
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
        ((synth G R Q hQ cfg input).operations region) =
      synthesisSummary cfg := by
  simp only [synthesisSummary, synth, circuit_norm, synthesis_summary_norm]

@[keygen_output_norm]
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
  rfl

@[circuit_norm] theorem synthPieces_output_a (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).a =
      .of i 0 cfg.hashConfig.witnessPieces := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_b0 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).b0 =
      .of (i + 1) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_b3 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).b3 =
      .of (i + 2) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_c (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).c =
      .of (i + 4) 0 cfg.hashConfig.witnessPieces := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_d2 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).d2 =
      .of (i + 5) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_e0 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).e0 =
      .of (i + 7) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_e1 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).e1 =
      .of (i + 8) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_f (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).f =
      .of (i + 10) 0 cfg.hashConfig.witnessPieces := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_g1 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).g1 =
      .of (i + 11) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[circuit_norm] theorem synthPieces_output_h0 (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synthPieces cfg input).output i).h0 =
      .of (i + 13) 0 cfg.lookupConfig.runningSum := by
  rw [synthPieces_output]

@[keygen_output_norm]
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
  -- symbolic walk (the opaque `call` barrier is not evaluable): the accessor algebra lands
  -- each call component on its `output` metadata (`output_call`/`output_call'`) at its
  -- threaded region index; the final `rfl` reduces the (non-opaque) metadata to the cells.
  -- Minimal lemma set — the full `circuit_norm` bloats past the kernel's timeout here.
  simp only [synthChecks, LookupRangeCheck.witnessCheck, Circuit.output_bind,
    Circuit.output_pure, output_assignRegion, nextRegionIndex_assignRegion,
    RegionCircuit.output_bind, FormalCircuit.output_call',
    FormalRegionCircuit.output_call', FormalCircuit.nextRegionIndex_call']
  rw [YCanonicityCheck.circuit_call_regionCount, YCanonicityCheck.circuit_call_regionCount, Sinsemilla.CommitDomain.commit_call_regionCount]
  rfl

@[circuit_norm] theorem synthChecks_output_aZs_z0
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).aZs.z0 =
      .of (i + 14) 0 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_aZs_zLast
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).aZs.zLast =
      .of (i + 14) 13 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_bZs_z0
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).bZs.z0 =
      .of (i + 15) 0 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_bZs_zLast
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).bZs.zLast =
      .of (i + 15) 14 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_eZs_z0
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).eZs.z0 =
      .of (i + 16) 0 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_eZs_zLast
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).eZs.zLast =
      .of (i + 16) 14 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_gZs_z0
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).gZs.z0 =
      .of (i + 17) 0 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

@[circuit_norm] theorem synthChecks_output_gZs_zLast
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).gZs.zLast =
      .of (i + 17) 13 cfg.lookupConfig.runningSum := by
  rw [synthChecks_output]

/-! ## The bundle (factored: standalone elaborated/contract/proofs) -/

open Specs.Sinsemilla (hashToPoint hashToPointB SpecOrBreak)
open CompElliptic.Fields.Pasta (Fq)

/-- Equality-enabled columns used by NoteCommit's local copy operations, together with
the columns required by its commitment child. -/
def permutationColumns (cfg : Config) (childColumns : List AnyColumn) : List AnyColumn :=
  ([cfg.hashConfig.witnessPieces, cfg.hashConfig.bits,
    cfg.lookupConfig.runningSum] : List AnyColumn) ++
    NoteCommit.permutationColumns cfg.gates ++ childColumns

theorem synthPieces_output_permutationColumns (cfg : Config)
    (input : Var Inputs Fp) (childColumns : List AnyColumn) (i : RegionIndex) :
    ∀ column, column ∈ ((synthPieces cfg input).output i).permutationColumns →
      column ∈ permutationColumns cfg childColumns := by
  intro column hcolumn
  simp only [synthPieces_output, PieceCells.permutationColumns,
    AssignedCell.of_cell, Cell.of_column, List.mem_cons,
    List.not_mem_nil, or_false, or_self] at hcolumn
  have : column = cfg.hashConfig.witnessPieces.toAny ∨
      column = cfg.lookupConfig.runningSum.toAny := by
    grind
  rcases this with rfl | rfl <;> simp [permutationColumns, NoteCommit.permutationColumns]

theorem synthChecks_output_permutationColumns (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash i : RegionIndex)
    (childColumns : List AnyColumn) :
    ∀ column,
      column ∈
        ((synthChecks G R Q hQ cfg input pcs iHash).output i).permutationColumns →
      column ∈ permutationColumns cfg childColumns := by
  intro column hcolumn
  simp only [synthChecks_output, CheckCells.permutationColumns,
    AssignedCell.of_cell, Cell.of_column, List.mem_cons,
    List.not_mem_nil, or_false, or_self] at hcolumn
  have : column = (cfg.gates.y.advices 6).toAny ∨
      column = cfg.lookupConfig.runningSum.toAny := by
    grind
  rcases this with rfl | rfl <;> simp [permutationColumns, NoteCommit.permutationColumns]

/-- The final commitment result occupies the complete-addition output columns. -/
theorem synthChecks_output_cm (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (iHash i : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).output i).cm =
      (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
          r := input.rcm }
        (i + 10) := by
  exact congrArg CheckCells.cm
    (synthChecks_output G R Q hQ cfg input pcs iHash i)

private theorem output_property_bind {α β : Type} (P : β → Prop)
    (x : Circuit Fp α) (f : α → Circuit Fp β) (i : RegionIndex)
    (h : ∀ a j, P ((f a).output j)) : P ((x >>= f).output i) := by
  rw [Circuit.output_bind]
  exact h _ _

theorem synth_output_columns (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synth G R Q hQ cfg input).output i).x.cell.column = cfg.addConfig.xQR.toAny ∧
      ((synth G R Q hQ cfg input).output i).y.cell.column = cfg.addConfig.yQR.toAny := by
  simp only [synth]
  refine output_property_bind
    (fun output : Var Point Fp =>
      output.x.cell.column = cfg.addConfig.xQR.toAny ∧
        output.y.cell.column = cfg.addConfig.yQR.toAny)
    currentRegion (fun i₀ => do
      let pcs ← synthPieces cfg input
      let ccs ← synthChecks G R Q hQ cfg input pcs (i₀ + 27)
      synthGates cfg input pcs ccs (i₀ + 27)
      pure ccs.cm) i ?_
  intro i₀ j₀
  refine output_property_bind
    (fun output : Var Point Fp =>
      output.x.cell.column = cfg.addConfig.xQR.toAny ∧
        output.y.cell.column = cfg.addConfig.yQR.toAny)
    (synthPieces cfg input) (fun pcs => do
    let ccs ← synthChecks G R Q hQ cfg input pcs (i₀ + 27)
    synthGates cfg input pcs ccs (i₀ + 27)
    pure ccs.cm) j₀ ?_
  intro pcs j₁
  simp only [Circuit.output_bind, Circuit.output_pure]
  rw [synthChecks_output_cm]
  simp only [Sinsemilla.CommitDomain.commit_output_cells,
    AssignedCell.of_cell, Cell.of_column]
  exact ⟨trivial, trivial⟩

theorem synth_output_x_column (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synth G R Q hQ cfg input).output i).x.cell.column = cfg.addConfig.xQR.toAny :=
  (synth_output_columns G R Q hQ cfg input i).1

theorem synth_output_y_column (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    ((synth G R Q hQ cfg input).output i).y.cell.column = cfg.addConfig.yQR.toAny :=
  (synth_output_columns G R Q hQ cfg input i).2

theorem mem_permutationColumns_of_child {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈ childColumns) :
    column ∈ permutationColumns cfg childColumns := by
  exact List.mem_append_right _ hcolumn

theorem mem_permutationColumns_of_decomposeB {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.b.colL, cfg.gates.b.colM, cfg.gates.b.colR] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_decomposeD {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.d.colL, cfg.gates.d.colM, cfg.gates.d.colR] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_decomposeE {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.e.colL, cfg.gates.e.colM, cfg.gates.e.colR] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_decomposeG {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.g.colL, cfg.gates.g.colM] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl <;> simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_decomposeH {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.h.colL, cfg.gates.h.colM, cfg.gates.h.colR] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_gd {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.gd.colL, cfg.gates.gd.colM,
        cfg.gates.gd.colR, cfg.gates.gd.colZ] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_pkd {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.pkd.colL, cfg.gates.pkd.colM,
        cfg.gates.pkd.colR, cfg.gates.pkd.colZ] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_value {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.value.colL, cfg.gates.value.colM,
        cfg.gates.value.colR, cfg.gates.value.colZ] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_rho {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.rho.colL, cfg.gates.rho.colM,
        cfg.gates.rho.colR, cfg.gates.rho.colZ] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_psi {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.psi.colL, cfg.gates.psi.colM,
        cfg.gates.psi.colR, cfg.gates.psi.colZ] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem mem_permutationColumns_of_y {column : AnyColumn}
    (cfg : Config) (childColumns : List AnyColumn)
    (hcolumn : column ∈
      ([cfg.gates.y.advices 5, cfg.gates.y.advices 6,
        cfg.gates.y.advices 7, cfg.gates.y.advices 8,
        cfg.gates.y.advices 9, cfg.lookupConfig.runningSum] : List AnyColumn)) :
    column ∈ permutationColumns cfg childColumns := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [permutationColumns, NoteCommit.permutationColumns]

theorem zCell_column_mem_permutationColumns (cfg : Config)
    (childColumns : List AnyColumn) (iHash : RegionIndex) (i j : ℕ) :
    (zCell cfg.hashConfig iHash i j).cell.column ∈
      permutationColumns cfg childColumns := by
  simp [zCell, AssignedCell.of_cell, Cell.of_column, permutationColumns]

@[keygen_norm]
def keygenRequirements (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) :
    KeygenRequirements Fp Config (Var Inputs Fp) where
  configLawful cfg :=
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).Configured
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
  gates cfg configured :=
    [LookupRangeCheck.bitshiftGate 10 cfg.lookupConfig,
      YCanonicity.gate cfg.gates.y,
      DecomposeB.gate cfg.gates.b,
      DecomposeD.gate cfg.gates.d,
      DecomposeE.gate cfg.gates.e,
      DecomposeG.gate cfg.gates.g,
      DecomposeH.gate cfg.gates.h,
      GdCanonicity.gate cfg.gates.gd,
      PkdCanonicity.gate cfg.gates.pkd,
      ValueCanonicity.gate cfg.gates.value,
      RhoCanonicity.gate cfg.gates.rho,
      PsiCanonicity.gate cfg.gates.psi] ++ configured.gates
  lookups cfg configured :=
    [LookupRangeCheck.rangeCheckLookup 10 cfg.lookupConfig] ++
      configured.lookups
  fixedColumns _ configured := configured.fixedColumns
  permutationColumns cfg configured := permutationColumns cfg configured.permutationColumns
  inputCells _ _ input :=
    [input.gdX.cell, input.gdY.cell, input.pkdX.cell, input.pkdY.cell,
      input.value.cell, input.rho.cell, input.psi.cell]

@[keygen_helper]
theorem synthPieces_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthPieces cfg input).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input) := by
  have hBitshift : LookupRangeCheck.bitshiftGate 10 cfg.lookupConfig ∈
      (keygenRequirements G R Q hQ).gates cfg configured := by
    simp [keygenRequirements]
  have hLookup : LookupRangeCheck.rangeCheckLookup 10 cfg.lookupConfig ∈
      (keygenRequirements G R Q hQ).lookups cfg configured := by
    simp [keygenRequirements]
  have hRunningSum : cfg.lookupConfig.runningSum.toAny ∈
      (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input := by
    simp [keygenRequirements, permutationColumns]
  keygen_registration

@[keygen_helper]
theorem synthChecks_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthChecks G R Q hQ cfg input pcs iHash).operations
      self).KeygenRegistered
        ((keygenRequirements G R Q hQ).gates cfg configured)
        ((keygenRequirements G R Q hQ).lookups cfg configured)
        ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
          (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
          pcs.permutationColumns) := by
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    Operations.KeygenRegistered.append,
    Operations.KeygenRegistered.nil, and_true]
  constructor
  · apply FormalCircuit.call_keygenRegistered_ofOutput
      (YCanonicityCheck.circuit (brWit input.gdY 0 1))
      (cfg.gates.y, cfg.lookupConfig) {} ()
    · intro gate h
      simp [YCanonicityCheck.circuit, keygenRequirements,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      aesop
    · intro argument h
      simp [YCanonicityCheck.circuit, keygenRequirements,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      exact Or.inl h
    · intro column h
      simp [YCanonicityCheck.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h
    · intro column h
      simp [YCanonicityCheck.circuit, keygenRequirements, permutationColumns,
        NoteCommit.permutationColumns,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      aesop
    · simp only [YCanonicityCheck.circuit,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.forall_cons,
        List.forall_nil, and_true]
      apply List.mem_append_left
      apply List.mem_append_right
      simp [keygenRequirements, KeygenRequirements.inputPermutationColumns]
  constructor
  · apply FormalCircuit.call_keygenRegistered_ofOutput
      (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
      (cfg.gates.y, cfg.lookupConfig) {} ()
    · intro gate h
      simp [YCanonicityCheck.circuit, keygenRequirements,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      aesop
    · intro argument h
      simp [YCanonicityCheck.circuit, keygenRequirements,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      exact Or.inl h
    · intro column h
      simp [YCanonicityCheck.circuit, FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h
    · intro column h
      simp [YCanonicityCheck.circuit, keygenRequirements, permutationColumns,
        NoteCommit.permutationColumns,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements] at h ⊢
      aesop
    · simp only [YCanonicityCheck.circuit,
        FormalCircuit.keygenRequirements,
        ElaboratedCircuit.keygenRequirements, List.forall_cons,
        List.forall_nil, and_true]
      apply List.mem_append_left
      apply List.mem_append_right
      simp [keygenRequirements, KeygenRequirements.inputPermutationColumns]
  constructor
  · apply FormalCircuit.call_keygenRegistered
      (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      _ configured
    · intro gate h
      simp only [keygenRequirements, List.mem_append]
      exact Or.inr h
    · intro argument h
      simp only [keygenRequirements, List.mem_append]
      exact Or.inr h
    · intro column h
      exact h
    · intro column h
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ h))
    · rw [Sinsemilla.CommitDomain.commit_inputCells,
        List.forall_iff_forall_mem]
      intro cell hcell
      apply List.mem_append_right
      simp only [Vector.toList, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hcell
      rcases hcell with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [PieceCells.permutationColumns]
  have hRunningSum : cfg.lookupConfig.runningSum.toAny ∈
      (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns := by
    simp [keygenRequirements, permutationColumns]
  constructor
  · apply LookupRangeCheck.witnessCheck_keygenRegistered
    · simp [keygenRequirements]
    · exact hRunningSum
  constructor
  · apply LookupRangeCheck.witnessCheck_keygenRegistered
    · simp [keygenRequirements]
    · exact hRunningSum
  constructor
  · apply LookupRangeCheck.witnessCheck_keygenRegistered
    · simp [keygenRequirements]
    · exact hRunningSum
  · apply LookupRangeCheck.witnessCheck_keygenRegistered
    · simp [keygenRequirements]
    · exact hRunningSum

private theorem pureRegionCall_keygenRegistered
    {Config : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (child : FormalRegionCircuit Fp Config Config Input Output)
    (name : String) (cfg : Config) (input : Var Input Fp) (self : RegionIndex)
    (hconfigured : child.keygenRequirements.configLawful cfg)
    (hconfigure : child.configure cfg = pure cfg)
    {targetGates : List (Gate Fp)} {targetLookups : List (LookupArgument Fp)}
    {targetFixedColumns : List (Column .fixed)}
    {targetPermutationColumns : List AnyColumn}
    (hgates : ∀ gate, gate ∈ child.keygenRequirements.gates cfg hconfigured →
      gate ∈ targetGates)
    (hlookups : ∀ lookup, lookup ∈ child.keygenRequirements.lookups cfg hconfigured →
      lookup ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ child.keygenRequirements.fixedColumns cfg hconfigured →
        column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ child.keygenRequirements.permutationColumns cfg hconfigured →
        column ∈ targetPermutationColumns)
    (hinputCells : (child.keygenRequirements.inputCells cfg hconfigured input).Forall
      fun cell => cell.column ∈ targetPermutationColumns) :
    (((child.toFormal name).call cfg input).operations self).KeygenRegistered
      targetGates targetLookups targetFixedColumns targetPermutationColumns := by
  let lifted := child.toFormal name
  have hliftedConfigure : lifted.configure cfg = pure cfg := by
    simpa only [lifted, FormalRegionCircuit.toFormal] using hconfigure
  let configured := FormalCircuit.Configured.ofPure
    lifted cfg hconfigured hliftedConfigure
  apply lifted.call_keygenRegistered cfg configured input self
  · simpa only [configured, lifted, FormalCircuit.Configured.ofPure_gates,
      FormalRegionCircuit.toFormal_keygenRequirements] using hgates
  · simpa only [configured, lifted, FormalCircuit.Configured.ofPure_lookups,
      FormalRegionCircuit.toFormal_keygenRequirements] using hlookups
  · simpa only [configured, lifted, FormalCircuit.Configured.ofPure_fixedColumns,
      FormalRegionCircuit.toFormal_keygenRequirements] using hfixedColumns
  · simpa only [configured, lifted,
      FormalCircuit.Configured.ofPure_permutationColumns,
      FormalRegionCircuit.toFormal_keygenRequirements] using hpermutationColumns
  · simpa only [configured, lifted, FormalCircuit.Configured.ofPure_inputCells,
      FormalRegionCircuit.toFormal_keygenRequirements] using hinputCells

private theorem pureRegionCall_lookupSelectorAssignmentsAgree
    {Config : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (child : FormalRegionCircuit Fp Config Config Input Output)
    (name : String) (cfg : Config) (input : Var Input Fp) (self : RegionIndex)
    (hconfigured : child.keygenRequirements.configLawful cfg)
    (hconfigure : child.configure cfg = pure cfg) :
    (((child.toFormal name).call cfg input).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  let lifted := child.toFormal name
  have hliftedConfigure : lifted.configure cfg = pure cfg := by
    simpa only [lifted, FormalRegionCircuit.toFormal] using hconfigure
  exact lifted.call_lookupSelectorAssignmentsAgree cfg
    (FormalCircuit.Configured.ofPure lifted cfg hconfigured hliftedConfigure)
    input self

theorem synthDecompositions_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthDecompositions cfg input pcs ccs iHash).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns ++ ccs.permutationColumns) := by
  have hB : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.b.colL, cfg.gates.b.colM,
        cfg.gates.b.colR] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_decomposeB cfg configured.permutationColumns
  have hD : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.d.colL, cfg.gates.d.colM,
        cfg.gates.d.colR] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_decomposeD cfg configured.permutationColumns
  have hE : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.e.colL, cfg.gates.e.colM,
        cfg.gates.e.colR] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_decomposeE cfg configured.permutationColumns
  have hG : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.g.colL, cfg.gates.g.colM] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_decomposeG cfg configured.permutationColumns
  have hH : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.h.colL, cfg.gates.h.colM,
        cfg.gates.h.colR] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_decomposeH cfg configured.permutationColumns
  have hZ : ∀ i j,
      (zCell cfg.hashConfig iHash i j).cell.column ∈
        permutationColumns cfg configured.permutationColumns :=
    zCell_column_mem_permutationColumns cfg configured.permutationColumns iHash
  simp only [synthDecompositions, Circuit.operations_bind,
    Operations.KeygenRegistered.append]
  repeat' apply And.intro
  · apply pureRegionCall_keygenRegistered
      (DecomposeB.bundle (brWit input.gdX 254 1))
      "NoteCommit MessagePiece b" cfg.gates.b
      { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 }
      _ () (by rfl)
    keygen_registration
  · apply pureRegionCall_keygenRegistered
      (DecomposeD.bundle (brWit input.pkdX 254 1))
      "NoteCommit MessagePiece d" cfg.gates.d
      { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
        d3 := zCell cfg.hashConfig iHash 3 1 }
      _ () (by rfl)
    keygen_registration
  · apply pureRegionCall_keygenRegistered
      DecomposeE.bundle "NoteCommit MessagePiece e" cfg.gates.e
      { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 } _ () (by rfl)
    · intro gate hgate
      simp only [DecomposeE.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_singleton] at hgate
      subst gate
      simp [keygenRequirements]
    · intro lookup hlookup
      simp only [DecomposeE.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hlookup
    · intro column hcolumn
      simp only [DecomposeE.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hcolumn
    · intro column hcolumn
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact hE hcolumn
    · simp only [DecomposeE.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.forall_cons,
        List.forall_nil, and_true]
      repeat' apply And.intro
      all_goals apply List.mem_append_left
      all_goals apply List.mem_append_right
      all_goals simp [PieceCells.permutationColumns]
  · apply pureRegionCall_keygenRegistered
      (DecomposeG.bundle (brWit input.rho 254 1))
      "NoteCommit MessagePiece g" cfg.gates.g
      { g := pcs.g, g1 := pcs.g1,
        g2 := zCell cfg.hashConfig iHash 6 1 }
      _ () (by rfl)
    · intro gate hgate
      simp only [DecomposeG.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_singleton] at hgate
      subst gate
      simp [keygenRequirements]
    · intro lookup hlookup
      simp only [DecomposeG.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hlookup
    · intro column hcolumn
      simp only [DecomposeG.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hcolumn
    · intro column hcolumn
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact hG hcolumn
    · simp only [DecomposeG.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.forall_cons,
        List.forall_nil, and_true]
      refine ⟨?_, ?_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (hZ 6 1)))⟩
      · apply List.mem_append_left
        apply List.mem_append_right
        simp only [PieceCells.permutationColumns, List.mem_cons, true_or,
          or_true]
      · apply List.mem_append_left
        apply List.mem_append_right
        simp only [PieceCells.permutationColumns, List.mem_cons, true_or, or_true]
  · apply pureRegionCall_keygenRegistered
      (DecomposeH.bundle (brWit input.psi 254 1))
      "NoteCommit MessagePiece h" cfg.gates.h
      { h := pcs.h, h0 := pcs.h0 } _ () (by rfl)
    · intro gate hgate
      simp only [DecomposeH.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.mem_singleton] at hgate
      subst gate
      simp [keygenRequirements]
    · intro lookup hlookup
      simp only [DecomposeH.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hlookup
    · intro column hcolumn
      simp only [DecomposeH.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.not_mem_nil] at hcolumn
    · intro column hcolumn
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      simpa only [keygenRequirements] using
        mem_permutationColumns_of_decomposeH
          cfg configured.permutationColumns hcolumn
    · simp only [DecomposeH.bundle, FormalRegionCircuit.keygenRequirements,
        ElaboratedRegionCircuit.keygenRequirements, List.forall_cons,
        List.forall_nil, and_true]
      constructor <;> apply List.mem_append_left <;>
        apply List.mem_append_right <;> simp [PieceCells.permutationColumns]
  · simp only [Circuit.operations_pure, Operations.KeygenRegistered.nil]

theorem synthGdPkdValueCanonicity_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).operations
      self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns ++ ccs.permutationColumns ++
        gcs.permutationColumns) := by
  have hGd : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.gd.colL, cfg.gates.gd.colM,
        cfg.gates.gd.colR, cfg.gates.gd.colZ] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_gd cfg configured.permutationColumns
  have hPkd : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.pkd.colL, cfg.gates.pkd.colM,
        cfg.gates.pkd.colR, cfg.gates.pkd.colZ] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_pkd cfg configured.permutationColumns
  have hValue : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.value.colL, cfg.gates.value.colM,
        cfg.gates.value.colR, cfg.gates.value.colZ] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_value cfg configured.permutationColumns
  have hZ : ∀ i j,
      (zCell cfg.hashConfig iHash i j).cell.column ∈
        permutationColumns cfg configured.permutationColumns :=
    zCell_column_mem_permutationColumns cfg configured.permutationColumns iHash
  simp only [synthGdPkdValueCanonicity, Circuit.operations_bind,
    Operations.KeygenRegistered.append]
  repeat' apply And.intro
  · apply pureRegionCall_keygenRegistered
      GdCanonicity.bundle "NoteCommit input g_d" cfg.gates.gd
      { gdX := input.gdX, b0 := pcs.b0, b1 := gcs.b1, a := pcs.a,
        aPrime := ccs.aZs.z0,
        z13A := zCell cfg.hashConfig iHash 0 13,
        z13APrime := ccs.aZs.zLast }
      _ () (by rfl)
    keygen_registration
  · apply pureRegionCall_keygenRegistered
      PkdCanonicity.bundle "NoteCommit input pk_d" cfg.gates.pkd
      { pkdX := input.pkdX, b3 := pcs.b3, d0 := gcs.d0, c := pcs.c,
        b3CPrime := ccs.bZs.z0,
        z13C := zCell cfg.hashConfig iHash 2 13,
        z14B3CPrime := ccs.bZs.zLast }
      _ () (by rfl)
    keygen_registration
  · apply pureRegionCall_keygenRegistered
      ValueCanonicity.bundle "NoteCommit input value" cfg.gates.value
      { value := input.value, d2 := pcs.d2,
        d3 := zCell cfg.hashConfig iHash 3 1, e0 := pcs.e0 }
      _ () (by rfl)
    keygen_registration
  · simp only [Circuit.operations_pure, Operations.KeygenRegistered.nil]

theorem synthRhoPsiCanonicity_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthRhoPsiCanonicity cfg input pcs ccs gcs iHash).operations
      self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns ++ ccs.permutationColumns ++
        gcs.permutationColumns) := by
  have hRho : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.rho.colL, cfg.gates.rho.colM,
        cfg.gates.rho.colR, cfg.gates.rho.colZ] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_rho cfg configured.permutationColumns
  have hPsi : ∀ {column : AnyColumn},
      column ∈ ([cfg.gates.psi.colL, cfg.gates.psi.colM,
        cfg.gates.psi.colR, cfg.gates.psi.colZ] : List AnyColumn) →
      column ∈ permutationColumns cfg configured.permutationColumns :=
    mem_permutationColumns_of_psi cfg configured.permutationColumns
  have hZ : ∀ i j,
      (zCell cfg.hashConfig iHash i j).cell.column ∈
        permutationColumns cfg configured.permutationColumns :=
    zCell_column_mem_permutationColumns cfg configured.permutationColumns iHash
  simp only [synthRhoPsiCanonicity, Circuit.operations_bind,
    Operations.KeygenRegistered.append]
  repeat' apply And.intro
  · apply pureRegionCall_keygenRegistered
      RhoCanonicity.bundle "NoteCommit input rho" cfg.gates.rho
      { rho := input.rho, e1 := pcs.e1, g0 := gcs.g0, f := pcs.f,
        e1FPrime := ccs.eZs.z0,
        z13F := zCell cfg.hashConfig iHash 5 13,
        z14E1FPrime := ccs.eZs.zLast }
      _ () (by rfl)
    keygen_registration
  · apply pureRegionCall_keygenRegistered
      PsiCanonicity.bundle "NoteCommit input psi" cfg.gates.psi
      { psi := input.psi, h0 := pcs.h0, g1 := pcs.g1, h1 := gcs.h1,
        g2 := zCell cfg.hashConfig iHash 6 1,
        g1G2Prime := ccs.gZs.z0,
        z13G := zCell cfg.hashConfig iHash 6 13,
        z13G1G2Prime := ccs.gZs.zLast }
      _ () (by rfl)
    keygen_registration
  · simp only [Circuit.operations_pure, Operations.KeygenRegistered.nil]

theorem synthCanonicity_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthCanonicity cfg input pcs ccs gcs iHash).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns ++ ccs.permutationColumns ++
        gcs.permutationColumns) := by
  simp only [synthCanonicity, Circuit.operations_bind,
    Operations.KeygenRegistered.append]
  constructor
  · apply synthGdPkdValueCanonicity_keygenRegistered
  · apply synthRhoPsiCanonicity_keygenRegistered

@[keygen_helper]
theorem synthGates_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synthGates cfg input pcs ccs iHash).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input ++
        pcs.permutationColumns ++ ccs.permutationColumns) := by
  simp only [synthGates, Circuit.operations_bind,
    Operations.KeygenRegistered.append]
  constructor
  · exact synthDecompositions_keygenRegistered
      G R Q hQ cfg input pcs ccs iHash self configured
  · apply (synthCanonicity_keygenRegistered
      G R Q hQ cfg input pcs ccs _ iHash _ configured).mono
      (fun _ h => h) (fun _ h => h) (fun _ h => h)
    intro column hcolumn
    rw [List.mem_append] at hcolumn
    rcases hcolumn with hcolumn | hcolumn
    · exact hcolumn
    · simp only [synthDecompositions_output, GateCells.permutationColumns,
        AssignedCell.of_cell, Cell.of_column, List.mem_cons,
        List.not_mem_nil, or_false] at hcolumn
      have hParent : ∀ {column : AnyColumn},
          column ∈ permutationColumns cfg configured.permutationColumns →
          column ∈
            (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
              (keygenRequirements G R Q hQ).inputPermutationColumns
                cfg configured input ++ pcs.permutationColumns ++
                  ccs.permutationColumns := by
        intro column hcolumn
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        simpa only [keygenRequirements] using hcolumn
      rcases hcolumn with rfl | rfl | rfl | rfl
      · apply hParent
        apply mem_permutationColumns_of_decomposeB
        simp
      · apply hParent
        apply mem_permutationColumns_of_decomposeD
        simp
      · apply hParent
        apply mem_permutationColumns_of_decomposeG
        simp
      · apply hParent
        apply mem_permutationColumns_of_decomposeH
        simp

@[keygen_helper]
theorem synth_keygenRegistered
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synth G R Q hQ cfg input).operations self).KeygenRegistered
      ((keygenRequirements G R Q hQ).gates cfg configured)
      ((keygenRequirements G R Q hQ).lookups cfg configured)
      ((keygenRequirements G R Q hQ).fixedColumns cfg configured)
      ((keygenRequirements G R Q hQ).permutationColumns cfg configured ++
        (keygenRequirements G R Q hQ).inputPermutationColumns cfg configured input) := by
  simp only [synth, Circuit.operations_bind, currentRegion_operations,
    currentRegion_nextRegionIndex, currentRegion_output,
    Circuit.operations_pure, Operations.KeygenRegistered.append,
    Operations.KeygenRegistered.nil, true_and, and_true]
  have hParent : ∀ {column : AnyColumn},
      column ∈ permutationColumns cfg configured.permutationColumns →
      column ∈
        (keygenRequirements G R Q hQ).permutationColumns cfg configured ++
          (keygenRequirements G R Q hQ).inputPermutationColumns
            cfg configured input := by
    intro column hcolumn
    apply List.mem_append_left
    simpa only [keygenRequirements] using hcolumn
  constructor
  · exact synthPieces_keygenRegistered G R Q hQ cfg input self configured
  constructor
  · apply (synthChecks_keygenRegistered G R Q hQ cfg input _ _ _ configured).mono
      (fun _ h => h) (fun _ h => h) (fun _ h => h)
    intro column hcolumn
    rw [List.mem_append] at hcolumn
    rcases hcolumn with hcolumn | hcolumn
    · exact hcolumn
    · apply hParent
      exact synthPieces_output_permutationColumns
        cfg input configured.permutationColumns self column hcolumn
  · apply (synthGates_keygenRegistered G R Q hQ cfg input _ _ _ _ configured).mono
      (fun _ h => h) (fun _ h => h) (fun _ h => h)
    intro column hcolumn
    rw [List.mem_append] at hcolumn
    rcases hcolumn with hcolumn | hcolumn
    · rw [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact hcolumn
      · apply hParent
        exact synthPieces_output_permutationColumns
          cfg input configured.permutationColumns self column hcolumn
    · apply hParent
      exact synthChecks_output_permutationColumns
        G R Q hQ cfg input ((synthPieces cfg input).output self)
          (self + 27) ((synthPieces cfg input).nextRegionIndex self)
          configured.permutationColumns column hcolumn

/-- The reduced output metadata exported to parent circuits. -/
def output (cfg : Config) (self : RegionIndex) : Var Point Fp :=
  { x := .of (self + 28) 1 cfg.addConfig.xQR
    y := .of (self + 28) 1 cfg.addConfig.yQR }

@[keygen_output_norm]
theorem output_x_column (cfg : Config) (self : RegionIndex) :
    (output cfg self).x.cell.column = cfg.addConfig.xQR := rfl

@[keygen_output_norm]
theorem output_y_column (cfg : Config) (self : RegionIndex) :
    (output cfg self).y.cell.column = cfg.addConfig.yQR := rfl

theorem synth_output_eq_commit_output
    (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (self : RegionIndex) :
    (synth G R Q hQ cfg input).output self
      = (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).output
          (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
          { pieces :=
              #v[AssignedCell.of self 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 1 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 2 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 4 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 7 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 8 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 10 + 2) 0 cfg.hashConfig.witnessPieces,
                AssignedCell.of (self + 12 + 2) 0 cfg.hashConfig.witnessPieces],
            r := input.rcm }
          (self + 15 + 5 + 5) := by
  show ((synthChecks G R Q hQ cfg input
      ((synthPieces cfg input).output self) (self + 27)).output
    ((synthPieces cfg input).nextRegionIndex self)).cm = _
  rw [synthChecks_output]
  rfl

theorem synth_output_eq (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Var Inputs Fp) (self : RegionIndex) :
    (synth G R Q hQ cfg input).output self = output cfg self := by
  rw [synth_output_eq_commit_output G R Q hQ cfg input self,
    Sinsemilla.CommitDomain.commit_output_cells]
  simp only [output, Nat.reduceAdd, Nat.add_assoc]

private theorem synthPieces_copyCellsAssigned
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input).operations self).CopyCellsAssigned self
      [input.gdX.cell, input.gdY.cell, input.pkdX.cell, input.pkdY.cell,
        input.value.cell, input.rho.cell, input.psi.cell] := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply Operations.CopyCellsAssignedFrom.append
  · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
  · apply Operations.CopyCellsAssignedFrom.append
    · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
    · apply Operations.CopyCellsAssignedFrom.append
      · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
      · apply Operations.CopyCellsAssignedFrom.append
        · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
        · apply Operations.CopyCellsAssignedFrom.append
          · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
          · apply Operations.CopyCellsAssignedFrom.append
            · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
            · apply Operations.CopyCellsAssignedFrom.append
              · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
              · apply Operations.CopyCellsAssignedFrom.append
                · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
                · apply Operations.CopyCellsAssignedFrom.append
                  · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
                  · apply Operations.CopyCellsAssignedFrom.append
                    · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
                    · apply Operations.CopyCellsAssignedFrom.append
                      · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
                      · apply Operations.CopyCellsAssignedFrom.append
                        · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
                        · apply Operations.CopyCellsAssignedFrom.append
                          · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom
                          · apply Operations.CopyCellsAssignedFrom.append
                            · apply LookupRangeCheck.witnessShortCheck_copyCellsAssignedFrom
                            · apply Sinsemilla.HashToPoint.witnessMessagePiece_copyCellsAssignedFrom

private theorem synthPieces_output_cells_assigned
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    let pcs := (synthPieces cfg input).output self
    [pcs.a.cell, pcs.b.cell, pcs.c.cell, pcs.d.cell, pcs.e.cell,
      pcs.f.cell, pcs.g.cell, pcs.h.cell, pcs.b0.cell, pcs.b3.cell,
      pcs.d2.cell, pcs.e0.cell, pcs.e1.cell, pcs.g1.cell,
      pcs.h0.cell].Forall fun cell =>
        cell ∈ ((synthPieces cfg input).operations self).assignedCellsFrom self := by
  rw [synthPieces_output]
  simp only [synthPieces, Sinsemilla.HashToPoint.witnessMessagePiece,
    LookupRangeCheck.witnessShortCheck, circuit_norm,
    Operations.assignedCellsFrom, RegionOperations.assignedCells,
    RegionOperation.assignedCells,
    List.flatMap_cons, List.mem_append, List.mem_cons, true_or]

private theorem synthChecks_copyCellsAssignedFrom
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex) (available : List Cell)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg)
    (havailable : [input.gdY.cell, input.pkdY.cell, pcs.a.cell,
      pcs.b.cell, pcs.c.cell, pcs.d.cell, pcs.e.cell, pcs.f.cell,
      pcs.g.cell, pcs.h.cell].Forall fun cell => cell ∈ available) :
    ((synthChecks G R Q hQ cfg input pcs iHash).operations self)
      |>.CopyCellsAssignedFrom self available := by
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, yc_call_nextRegionIndex, commit_call_nextRegionIndex,
    LookupRangeCheck.witnessCheck_nextRegionIndex]
  apply Operations.CopyCellsAssignedFrom.append
  · apply (YCanonicityCheck.circuit (brWit input.gdY 0 1))
      |>.call_copyCellsAssignedFrom _
        (FormalCircuit.Configured.ofPure
          (YCanonicityCheck.circuit (brWit input.gdY 0 1))
          (cfg.gates.y, cfg.lookupConfig) () rfl) _ _
    intro cell hcell
    rw [YCanonicityCheck.circuit_inputCells] at hcell
    simp only [List.mem_singleton] at hcell
    subst cell
    exact havailable.1
  · apply Operations.CopyCellsAssignedFrom.append
    · rw [YCanonicityCheck.circuit_call_regionCount]
      apply (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
        |>.call_copyCellsAssignedFrom _
          (FormalCircuit.Configured.ofPure
            (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
            (cfg.gates.y, cfg.lookupConfig) () rfl) _ _
      intro cell hcell
      rw [YCanonicityCheck.circuit_inputCells] at hcell
      simp only [List.mem_singleton] at hcell
      subst cell
      exact List.mem_append_left _ havailable.2.1
    · rw [YCanonicityCheck.circuit_call_regionCount]
      apply Operations.CopyCellsAssignedFrom.append
      · rw [YCanonicityCheck.circuit_call_regionCount]
        apply (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
          |>.call_copyCellsAssignedFrom _ configured _ _
        rw [Sinsemilla.CommitDomain.commit_inputCells]
        intro cell hcell
        simp only [Vector.toList, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hcell
        rcases hcell with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals apply List.mem_append_left
        all_goals apply List.mem_append_left
        · exact havailable.2.2.1
        · exact havailable.2.2.2.1
        · exact havailable.2.2.2.2.1
        · exact havailable.2.2.2.2.2.1
        · exact havailable.2.2.2.2.2.2.1
        · exact havailable.2.2.2.2.2.2.2.1
        · exact havailable.2.2.2.2.2.2.2.2.1
        · exact havailable.2.2.2.2.2.2.2.2.2
      · rw [YCanonicityCheck.circuit_call_regionCount,
          Sinsemilla.CommitDomain.commit_call_regionCount]
        apply Operations.CopyCellsAssignedFrom.append
        · apply LookupRangeCheck.witnessCheck_copyCellsAssignedFrom
        · rw [LookupRangeCheck.witnessCheck_regionCount]
          apply Operations.CopyCellsAssignedFrom.append
          · apply LookupRangeCheck.witnessCheck_copyCellsAssignedFrom
          · rw [LookupRangeCheck.witnessCheck_regionCount]
            apply Operations.CopyCellsAssignedFrom.append
            · apply LookupRangeCheck.witnessCheck_copyCellsAssignedFrom
            · rw [LookupRangeCheck.witnessCheck_regionCount]
              apply LookupRangeCheck.witnessCheck_copyCellsAssignedFrom

/-- The stage-2 outputs consumed by decomposition were assigned by their
respective child calls. -/
private theorem synthChecks_decomposition_cells_assigned
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex) (hiHash : iHash = self + 12) :
    let ccs := (synthChecks G R Q hQ cfg input pcs iHash).output self
    [ccs.b2.cell, ccs.d1.cell,
      (zCell cfg.hashConfig iHash 3 1).cell,
      (zCell cfg.hashConfig iHash 6 1).cell].Forall fun cell =>
        cell ∈ (((synthChecks G R Q hQ cfg input pcs iHash).operations self)
          |>.assignedCellsFrom self) := by
  subst iHash
  have hy1 := YCanonicityCheck.circuit_call_output_cell_assigned
    (brWit input.gdY 0 1) (cfg.gates.y, cfg.lookupConfig)
    { y := input.gdY } self
  have hy2 := YCanonicityCheck.circuit_call_output_cell_assigned
    (brWit input.pkdY 0 1) (cfg.gates.y, cfg.lookupConfig)
    { y := input.pkdY } (self + 5)
  have hz3 := Sinsemilla.CommitDomain.commit_call_hash_z1_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10) ⟨3, by norm_num [ns]⟩ (by norm_num [ns])
  have hz6 := Sinsemilla.CommitDomain.commit_call_hash_z1_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10) ⟨6, by norm_num [ns]⟩ (by norm_num [ns])
  simp only [YCanonicityCheck.circuit_output] at hy1 hy2
  simp only [Sinsemilla.HashToPoint.hashCircuit_output_z1s,
    Fin.getElem_fin, Vector.getElem_ofFn, Nat.zero_add,
    Nat.add_assoc] at hz3 hz6
  rw [synthChecks_output]
  simp only [List.forall_cons, List.forall_nil, and_true]
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, Operations.assignedCellsFrom_append,
    FormalCircuit.nextRegionIndex_call,
    YCanonicityCheck.circuit_call_regionCount,
    Sinsemilla.CommitDomain.commit_call_regionCount,
    LookupRangeCheck.witnessCheck_regionCount, List.mem_append,
    Nat.add_assoc]
  exact ⟨Or.inl hy1, Or.inr (Or.inl hy2),
    Or.inr (Or.inr (Or.inl hz3)),
    Or.inr (Or.inr (Or.inl hz6))⟩

/-- Both coordinates returned by the commitment child are assigned in stage 2. -/
theorem synthChecks_output_cm_cells_assigned
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex) :
    let cm := (synthChecks G R Q hQ cfg input pcs iHash).output self |>.cm
    cm.x.cell ∈ ((synthChecks G R Q hQ cfg input pcs iHash).operations self
        |>.assignedCellsFrom self) ∧
      cm.y.cell ∈ ((synthChecks G R Q hQ cfg input pcs iHash).operations self
        |>.assignedCellsFrom self) := by
  have hcommit := Sinsemilla.CommitDomain.commit_call_output_cells_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
  rw [synthChecks_output]
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, Operations.assignedCellsFrom_append,
    FormalCircuit.nextRegionIndex_call,
    YCanonicityCheck.circuit_call_regionCount,
    Sinsemilla.CommitDomain.commit_call_regionCount,
    LookupRangeCheck.witnessCheck_regionCount, List.mem_append,
    Nat.add_assoc]
  exact ⟨Or.inr (Or.inr (Or.inl hcommit.1)),
    Or.inr (Or.inr (Or.inl hcommit.2))⟩

/-- The stage-2 range-check and hash cells consumed by canonicity were assigned
by their respective children. -/
private theorem synthChecks_canonicity_cells_assigned
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex) (hiHash : iHash = self + 12) :
    let ccs := (synthChecks G R Q hQ cfg input pcs iHash).output self
    [ccs.aZs.z0.cell, ccs.aZs.zLast.cell,
      ccs.bZs.z0.cell, ccs.bZs.zLast.cell,
      ccs.eZs.z0.cell, ccs.eZs.zLast.cell,
      ccs.gZs.z0.cell, ccs.gZs.zLast.cell,
      (zCell cfg.hashConfig iHash 0 13).cell,
      (zCell cfg.hashConfig iHash 2 13).cell,
      (zCell cfg.hashConfig iHash 3 1).cell,
      (zCell cfg.hashConfig iHash 5 13).cell,
      (zCell cfg.hashConfig iHash 6 1).cell,
      (zCell cfg.hashConfig iHash 6 13).cell].Forall fun cell =>
        cell ∈ (((synthChecks G R Q hQ cfg input pcs iHash).operations self)
          |>.assignedCellsFrom self) := by
  subst iHash
  have ha := LookupRangeCheck.witnessCheck_output_cells_assigned
    10 13 false (by simp) cfg.lookupConfig
    (GdCanonicityCheck.aPrimeWit pcs.a) (self + 14)
  have hb := LookupRangeCheck.witnessCheck_output_cells_assigned
    10 14 false (by simp) cfg.lookupConfig
    (PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c) (self + 15)
  have he := LookupRangeCheck.witnessCheck_output_cells_assigned
    10 14 false (by simp) cfg.lookupConfig
    (RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f) (self + 16)
  have hg := LookupRangeCheck.witnessCheck_output_cells_assigned
    10 13 false (by simp) cfg.lookupConfig
    (PsiCanonicityCheck.g1G2PrimeWit pcs.g1
      (zCell cfg.hashConfig (self + 12) 6 1)) (self + 17)
  have hz0 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨0, by norm_num [ns]⟩ ⟨13, by norm_num [ns]⟩
  have hz2 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨2, by norm_num [ns]⟩ ⟨13, by norm_num [ns]⟩
  have hz3 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨3, by norm_num [ns]⟩ ⟨1, by norm_num [ns]⟩
  have hz5 := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨5, by norm_num [ns]⟩ ⟨13, by norm_num [ns]⟩
  have hz6a := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨6, by norm_num [ns]⟩ ⟨1, by norm_num [ns]⟩
  have hz6b := Sinsemilla.CommitDomain.commit_call_hash_z_cell_assigned
    G ns R Q hQ ns_ne_nil (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
      r := input.rcm } (self + 10)
    ⟨6, by norm_num [ns]⟩ ⟨13, by norm_num [ns]⟩
  simp only [LookupRangeCheck.witnessCheck_output] at ha hb he hg
  rw [synthChecks_output]
  simp only [List.forall_cons, List.forall_nil, and_true]
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, Operations.assignedCellsFrom_append,
    FormalCircuit.nextRegionIndex_call,
    YCanonicityCheck.circuit_call_regionCount,
    Sinsemilla.CommitDomain.commit_call_regionCount,
    LookupRangeCheck.witnessCheck_regionCount, List.mem_append,
    Nat.add_assoc]
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ha.1))),
    Or.inr (Or.inr (Or.inr (Or.inl ha.2))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb.1)))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb.2)))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he.1))))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he.2))))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hg.1))))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hg.2))))),
    Or.inr (Or.inr (Or.inl hz0)), Or.inr (Or.inr (Or.inl hz2)),
    Or.inr (Or.inr (Or.inl hz3)), Or.inr (Or.inr (Or.inl hz5)),
    Or.inr (Or.inr (Or.inl hz6a)), Or.inr (Or.inr (Or.inl hz6b))⟩

private def synthDecompositionsInputCells (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (iHash : RegionIndex) : List Cell :=
  [input.gdX.cell, input.pkdX.cell, input.rho.cell, input.psi.cell,
    pcs.b.cell, pcs.b0.cell, ccs.b2.cell, pcs.b3.cell,
    pcs.d.cell, ccs.d1.cell, pcs.d2.cell,
    (zCell cfg.hashConfig iHash 3 1).cell,
    pcs.e.cell, pcs.e0.cell, pcs.e1.cell,
    pcs.g.cell, pcs.g1.cell, (zCell cfg.hashConfig iHash 6 1).cell,
    pcs.h.cell, pcs.h0.cell]

private theorem pureRegionCall_copyCellsAssignedFrom
    {Config : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (child : FormalRegionCircuit Fp Config Config Input Output)
    (name : String) (cfg : Config) (input : Var Input Fp)
    (self : RegionIndex) (available : List Cell)
    (hconfigured : child.keygenRequirements.configLawful cfg)
    (hconfigure : child.configure cfg = pure cfg)
    (hinputCells : (child.keygenRequirements.inputCells cfg hconfigured input).Forall
      fun cell => cell ∈ available) :
    (((child.toFormal name).call cfg input).operations self)
      |>.CopyCellsAssignedFrom self available := by
  let lifted := child.toFormal name
  have hliftedConfigure : lifted.configure cfg = pure cfg := by
    simpa only [lifted, FormalRegionCircuit.toFormal] using hconfigure
  let configured := FormalCircuit.Configured.ofPure
    lifted cfg hconfigured hliftedConfigure
  apply lifted.call_copyCellsAssignedFrom cfg configured input self
  simpa only [configured, lifted, FormalCircuit.Configured.ofPure_inputCells,
    FormalRegionCircuit.toFormal_keygenRequirements,
    List.forall_iff_forall_mem] using
      List.forall_iff_forall_mem.mp hinputCells

private theorem synthDecompositions_copyCellsAssignedFrom
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex) :
    ((synthDecompositions cfg input pcs ccs iHash).operations self)
      |>.CopyCellsAssignedFrom self
        (synthDecompositionsInputCells cfg input pcs ccs iHash) := by
  simp only [synthDecompositions, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.nextRegionIndex_call', Nat.add_assoc]
  apply Operations.CopyCellsAssignedFrom.append
  · apply pureRegionCall_copyCellsAssignedFrom
      (DecomposeB.bundle (brWit input.gdX 254 1))
      "NoteCommit MessagePiece b" cfg.gates.b
      { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 } _
      (synthDecompositionsInputCells cfg input pcs ccs iHash) () (by rfl)
    keygen_registration [synthDecompositionsInputCells]
  · rw [toFormal_call_regionCount]
    apply Operations.CopyCellsAssignedFrom.append
    · apply (pureRegionCall_copyCellsAssignedFrom
        (DecomposeD.bundle (brWit input.pkdX 254 1))
        "NoteCommit MessagePiece d" cfg.gates.d
        { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
          d3 := zCell cfg.hashConfig iHash 3 1 } _
        (synthDecompositionsInputCells cfg input pcs ccs iHash) () (by rfl)
        (by keygen_registration [synthDecompositionsInputCells])).mono
      intro cell hcell
      exact List.mem_append_left _ hcell
    · rw [toFormal_call_regionCount]
      apply Operations.CopyCellsAssignedFrom.append
      · apply (pureRegionCall_copyCellsAssignedFrom DecomposeE.bundle
          "NoteCommit MessagePiece e" cfg.gates.e
          { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 } _
          (synthDecompositionsInputCells cfg input pcs ccs iHash) () (by rfl)
          (by keygen_registration [synthDecompositionsInputCells])).mono
        intro cell hcell
        exact List.mem_append_left _ (List.mem_append_left _ hcell)
      · rw [toFormal_call_regionCount]
        apply Operations.CopyCellsAssignedFrom.append
        · apply (pureRegionCall_copyCellsAssignedFrom
            (DecomposeG.bundle (brWit input.rho 254 1))
            "NoteCommit MessagePiece g" cfg.gates.g
            { g := pcs.g, g1 := pcs.g1,
              g2 := zCell cfg.hashConfig iHash 6 1 } _
            (synthDecompositionsInputCells cfg input pcs ccs iHash) () (by rfl)
            (by keygen_registration [synthDecompositionsInputCells])).mono
          intro cell hcell
          exact List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ hcell))
        · rw [toFormal_call_regionCount]
          apply (pureRegionCall_copyCellsAssignedFrom
            (DecomposeH.bundle (brWit input.psi 254 1))
            "NoteCommit MessagePiece h" cfg.gates.h
            { h := pcs.h, h0 := pcs.h0 } _
            (synthDecompositionsInputCells cfg input pcs ccs iHash) () (by rfl)
            (by keygen_registration [synthDecompositionsInputCells])).mono
          intro cell hcell
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _ hcell)))

/-- The four cells returned by the decomposition children were assigned by
those child calls. -/
private theorem synthDecompositions_output_cells_assigned
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex) :
    let gcs := (synthDecompositions cfg input pcs ccs iHash).output self
    [gcs.b1.cell, gcs.d0.cell, gcs.g0.cell, gcs.h1.cell].Forall fun cell =>
      cell ∈ (((synthDecompositions cfg input pcs ccs iHash).operations self)
        |>.assignedCellsFrom self) := by
  have hb := DecomposeB.bundle_call_output_cell_assigned
    (brWit input.gdX 254 1) "NoteCommit MessagePiece b" cfg.gates.b
    { b := pcs.b, b0 := pcs.b0, b2 := ccs.b2, b3 := pcs.b3 } self
  have hd := DecomposeD.bundle_call_output_cell_assigned
    (brWit input.pkdX 254 1) "NoteCommit MessagePiece d" cfg.gates.d
    { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
      d3 := zCell cfg.hashConfig iHash 3 1 } (self + 1)
  have hg := DecomposeG.bundle_call_output_cell_assigned
    (brWit input.rho 254 1) "NoteCommit MessagePiece g" cfg.gates.g
    { g := pcs.g, g1 := pcs.g1,
      g2 := zCell cfg.hashConfig iHash 6 1 } (self + 3)
  have hh := DecomposeH.bundle_call_output_cell_assigned
    (brWit input.psi 254 1) "NoteCommit MessagePiece h" cfg.gates.h
    { h := pcs.h, h0 := pcs.h0 } (self + 4)
  simp only [decomposeB_toFormal_output, decomposeD_toFormal_output,
    decomposeG_toFormal_output, decomposeH_toFormal_output] at hb hd hg hh
  rw [synthDecompositions_output]
  simp only [List.forall_cons, List.forall_nil, and_true]
  simp only [synthDecompositions, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.nextRegionIndex_call']
  repeat' rw [toFormal_call_regionCount]
  simp only [Operations.assignedCellsFrom_append, List.mem_append]
  repeat' rw [toFormal_call_regionCount]
  simp only [Nat.add_assoc]
  exact ⟨Or.inl hb, Or.inr (Or.inl hd),
    Or.inr (Or.inr (Or.inr (Or.inl hg))),
    Or.inr (Or.inr (Or.inr (Or.inr hh)))⟩

private def synthCanonicityInputCells (cfg : Config)
    (input : Var Inputs Fp) (pcs : PieceCells) (ccs : CheckCells)
    (gcs : GateCells) (iHash : RegionIndex) : List Cell :=
  [input.gdX.cell, pcs.b0.cell, gcs.b1.cell, pcs.a.cell,
    ccs.aZs.z0.cell, (zCell cfg.hashConfig iHash 0 13).cell,
    ccs.aZs.zLast.cell,
    input.pkdX.cell, pcs.b3.cell, gcs.d0.cell, pcs.c.cell,
    ccs.bZs.z0.cell, (zCell cfg.hashConfig iHash 2 13).cell,
    ccs.bZs.zLast.cell,
    input.value.cell, pcs.d2.cell,
    (zCell cfg.hashConfig iHash 3 1).cell, pcs.e0.cell,
    input.rho.cell, pcs.e1.cell, gcs.g0.cell, pcs.f.cell,
    ccs.eZs.z0.cell, (zCell cfg.hashConfig iHash 5 13).cell,
    ccs.eZs.zLast.cell,
    input.psi.cell, pcs.h0.cell, pcs.g1.cell, gcs.h1.cell,
    (zCell cfg.hashConfig iHash 6 1).cell, ccs.gZs.z0.cell,
    (zCell cfg.hashConfig iHash 6 13).cell, ccs.gZs.zLast.cell]

private theorem synthGdPkdValueCanonicity_copyCellsAssignedFrom
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.CopyCellsAssignedFrom self
        (synthCanonicityInputCells cfg input pcs ccs gcs iHash) := by
  simp only [synthGdPkdValueCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.nextRegionIndex_call', Nat.add_assoc]
  apply Operations.CopyCellsAssignedFrom.append
  · apply pureRegionCall_copyCellsAssignedFrom
      GdCanonicity.bundle "NoteCommit input g_d" cfg.gates.gd
      { gdX := input.gdX, b0 := pcs.b0, b1 := gcs.b1, a := pcs.a,
        aPrime := ccs.aZs.z0,
        z13A := zCell cfg.hashConfig iHash 0 13,
        z13APrime := ccs.aZs.zLast }
      _ (synthCanonicityInputCells cfg input pcs ccs gcs iHash)
      () (by rfl)
    keygen_registration [synthCanonicityInputCells]
  · rw [toFormal_call_regionCount]
    apply Operations.CopyCellsAssignedFrom.append
    · apply (pureRegionCall_copyCellsAssignedFrom
        PkdCanonicity.bundle "NoteCommit input pk_d" cfg.gates.pkd
        { pkdX := input.pkdX, b3 := pcs.b3, d0 := gcs.d0, c := pcs.c,
          b3CPrime := ccs.bZs.z0,
          z13C := zCell cfg.hashConfig iHash 2 13,
          z14B3CPrime := ccs.bZs.zLast }
        _ (synthCanonicityInputCells cfg input pcs ccs gcs iHash)
        () (by rfl)
        (by keygen_registration [synthCanonicityInputCells])).mono
      intro cell hcell
      exact List.mem_append_left _ hcell
    · rw [toFormal_call_regionCount]
      apply (pureRegionCall_copyCellsAssignedFrom
        ValueCanonicity.bundle "NoteCommit input value" cfg.gates.value
        { value := input.value, d2 := pcs.d2,
          d3 := zCell cfg.hashConfig iHash 3 1, e0 := pcs.e0 }
        _ (synthCanonicityInputCells cfg input pcs ccs gcs iHash)
        () (by rfl)
        (by keygen_registration [synthCanonicityInputCells])).mono
      intro cell hcell
      exact List.mem_append_left _ (List.mem_append_left _ hcell)

private theorem synthRhoPsiCanonicity_copyCellsAssignedFrom
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthRhoPsiCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.CopyCellsAssignedFrom self
        (synthCanonicityInputCells cfg input pcs ccs gcs iHash) := by
  simp only [synthRhoPsiCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, List.append_nil,
    FormalCircuit.nextRegionIndex_call', Nat.add_assoc]
  apply Operations.CopyCellsAssignedFrom.append
  · apply pureRegionCall_copyCellsAssignedFrom
      RhoCanonicity.bundle "NoteCommit input rho" cfg.gates.rho
      { rho := input.rho, e1 := pcs.e1, g0 := gcs.g0, f := pcs.f,
        e1FPrime := ccs.eZs.z0,
        z13F := zCell cfg.hashConfig iHash 5 13,
        z14E1FPrime := ccs.eZs.zLast }
      _ (synthCanonicityInputCells cfg input pcs ccs gcs iHash)
      () (by rfl)
    keygen_registration [synthCanonicityInputCells]
  · rw [toFormal_call_regionCount]
    apply (pureRegionCall_copyCellsAssignedFrom
      PsiCanonicity.bundle "NoteCommit input psi" cfg.gates.psi
      { psi := input.psi, h0 := pcs.h0, g1 := pcs.g1, h1 := gcs.h1,
        g2 := zCell cfg.hashConfig iHash 6 1,
        g1G2Prime := ccs.gZs.z0,
        z13G := zCell cfg.hashConfig iHash 6 13,
        z13G1G2Prime := ccs.gZs.zLast }
      _ (synthCanonicityInputCells cfg input pcs ccs gcs iHash)
      () (by rfl)
      (by keygen_registration [synthCanonicityInputCells])).mono
    intro cell hcell
    exact List.mem_append_left _ hcell

private theorem synthCanonicity_copyCellsAssignedFrom
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.CopyCellsAssignedFrom self
        (synthCanonicityInputCells cfg input pcs ccs gcs iHash) := by
  simp only [synthCanonicity, Circuit.operations_bind]
  apply Operations.CopyCellsAssignedFrom.append
  · apply synthGdPkdValueCanonicity_copyCellsAssignedFrom
  · rw [synthGdPkdValueCanonicity_regionCount,
      synthGdPkdValueCanonicity_nextRegionIndex]
    apply (synthRhoPsiCanonicity_copyCellsAssignedFrom
      cfg input pcs ccs gcs iHash _).mono
    intro cell hcell
    exact List.mem_append_left _ hcell

private theorem synth_copyCellsAssigned
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (configured : (keygenRequirements G R Q hQ).configLawful cfg) :
    ((synth G R Q hQ cfg input).operations self).CopyCellsAssigned self
      ((keygenRequirements G R Q hQ).inputCells cfg configured input) := by
  simp only [keygenRequirements, synth, currentRegion_operations,
    currentRegion_nextRegionIndex, currentRegion_output,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil,
    List.nil_append]
  apply Operations.CopyCellsAssignedFrom.append
  · exact synthPieces_copyCellsAssigned cfg input self
  · apply Operations.CopyCellsAssignedFrom.append
    · rw [synthPieces_regionCount]
      apply synthChecks_copyCellsAssignedFrom G R Q hQ cfg input _ _ _ _ configured
      rw [synthPieces_output]
      have hpieces := synthPieces_output_cells_assigned cfg input self
      simp only [List.forall_cons, List.forall_nil, and_true] at hpieces ⊢
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨Or.inl (by simp), Or.inl (by simp), Or.inr hpieces.1,
        Or.inr hpieces.2.1, Or.inr hpieces.2.2.1,
        Or.inr hpieces.2.2.2.1, Or.inr hpieces.2.2.2.2.1,
        Or.inr hpieces.2.2.2.2.2.1, Or.inr hpieces.2.2.2.2.2.2.1,
        Or.inr hpieces.2.2.2.2.2.2.2.1⟩
    · simp only [synthGates, Circuit.operations_bind]
      apply Operations.CopyCellsAssignedFrom.append
      · rw [synthPieces_regionCount, synthChecks_regionCount,
          synthPieces_nextRegionIndex, synthChecks_nextRegionIndex]
        have hpieces := synthPieces_output_cells_assigned cfg input self
        have hchecks := synthChecks_decomposition_cells_assigned
          G R Q hQ cfg input ((synthPieces cfg input).output self)
          (self + 27) (self + 15) (by norm_num [Nat.add_assoc])
        apply (synthDecompositions_copyCellsAssignedFrom
          cfg input _ _ _ _).mono
        intro cell hcell
        simp only [synthDecompositionsInputCells, List.mem_cons,
          List.not_mem_nil, or_false] at hcell
        simp only [List.forall_cons, List.forall_nil, and_true] at hpieces hchecks
        rcases hpieces with
          ⟨ha, hb, hc, hd, he, hf, hg, hh, hb0, hb3, hd2, he0, he1, hg1, hh0⟩
        rcases hchecks with ⟨hb2, hd1, hz3, hz6⟩
        simp only [List.mem_append]
        aesop
      · have hpieces := synthPieces_output_cells_assigned cfg input self
        have hchecks := synthChecks_canonicity_cells_assigned
          G R Q hQ cfg input ((synthPieces cfg input).output self)
          (self + 27) (self + 15) (by norm_num [Nat.add_assoc])
        have hgates := synthDecompositions_output_cells_assigned
          cfg input ((synthPieces cfg input).output self)
          ((synthChecks G R Q hQ cfg input
            ((synthPieces cfg input).output self) (self + 27)).output
              (self + 15))
          (self + 27) (self + 33)
        rw [synthPieces_regionCount, synthChecks_regionCount,
          synthDecompositions_regionCount, synthPieces_nextRegionIndex,
          synthChecks_nextRegionIndex, synthDecompositions_nextRegionIndex]
        apply (synthCanonicity_copyCellsAssignedFrom
          cfg input _ _ _ _ _).mono
        intro cell hcell
        simp only [synthCanonicityInputCells, List.mem_cons,
          List.not_mem_nil, or_false] at hcell
        simp only [List.forall_cons, List.forall_nil, and_true] at hpieces hchecks hgates
        rcases hpieces with
          ⟨ha, hb, hc, hd, he, hf, hg, hh, hb0, hb3, hd2, he0, he1, hg1, hh0⟩
        rcases hchecks with
          ⟨haz0, hazLast, hbz0, hbzLast, hez0, hezLast, hgz0, hgzLast,
            hz0, hz2, hz3, hz5, hz6, hz6Last⟩
        rcases hgates with ⟨hb1, hd0, hg0, hh1⟩
        simp only [List.mem_append]
        aesop

private theorem synthPieces_lookupActivationsWellFormed
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input).operations self).LookupActivationsWellFormed := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    Operations.LookupActivationsWellFormed, List.forall_append,
    List.forall_nil, and_true]
  exact ⟨
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (brWit input.gdX 0 250) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 4 cfg.lookupConfig (brWit input.gdX 250 4) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 4 cfg.lookupConfig (brWit input.pkdX 0 4) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (bWit input.gdX input.gdY input.pkdX) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (brWit input.pkdX 4 250) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 8 cfg.lookupConfig (brWit input.value 0 8) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (dWit input.pkdX input.pkdY input.value) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 6 cfg.lookupConfig (brWit input.value 58 6) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 4 cfg.lookupConfig (brWit input.rho 0 4) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (eWit input.value input.rho) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (brWit input.rho 4 250) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 9 cfg.lookupConfig (brWit input.psi 0 9) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (gWit input.rho input.psi) _,
    LookupRangeCheck.witnessShortCheck_lookupActivationsWellFormed
      10 5 cfg.lookupConfig (brWit input.psi 249 5) _,
    Sinsemilla.HashToPoint.witnessMessagePiece_lookupActivationsWellFormed
      cfg.hashConfig (hWit input.psi) _⟩

private theorem synthChecks_lookupActivationsWellFormed
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex) :
    ((synthChecks G R Q hQ cfg input pcs iHash).operations self)
      |>.LookupActivationsWellFormed := by
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    Operations.LookupActivationsWellFormed, List.forall_append,
    List.forall_nil, and_true]
  exact ⟨
    (YCanonicityCheck.circuit (brWit input.gdY 0 1))
      |>.call_lookupActivationsWellFormed _ _ _,
    (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
      |>.call_lookupActivationsWellFormed _ _ _,
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      |>.call_lookupActivationsWellFormed _ _ _,
    LookupRangeCheck.witnessCheck_lookupActivationsWellFormed
      10 13 false _ cfg.lookupConfig (GdCanonicityCheck.aPrimeWit pcs.a) _,
    LookupRangeCheck.witnessCheck_lookupActivationsWellFormed
      10 14 false _ cfg.lookupConfig
        (PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c) _,
    LookupRangeCheck.witnessCheck_lookupActivationsWellFormed
      10 14 false _ cfg.lookupConfig
        (RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f) _,
    LookupRangeCheck.witnessCheck_lookupActivationsWellFormed
      10 13 false _ cfg.lookupConfig
        (PsiCanonicityCheck.g1G2PrimeWit pcs.g1
          (zCell cfg.hashConfig iHash 6 1)) _⟩

private theorem synthPieces_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    ((synthPieces cfg input).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthPieces, Circuit.operations_bind, Circuit.operations_pure,
    keygen_norm, keygen_spine]

private theorem synthChecks_lookupSelectorAssignmentsAgree
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex)
    (configured : (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).Configured
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)) :
    ((synthChecks G R Q hQ cfg input pcs iHash).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    keygen_norm, keygen_spine]
  exact ⟨
    (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
      |>.call_lookupSelectorAssignmentsAgree _
        (FormalCircuit.Configured.ofPure _ _ () (by rfl)) _ _,
    (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      |>.call_lookupSelectorAssignmentsAgree _ configured _ _⟩

private theorem synthDecompositions_lookupActivationsWellFormed
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex) :
    ((synthDecompositions cfg input pcs ccs iHash).operations self)
      |>.LookupActivationsWellFormed := by
  simp only [synthDecompositions, Circuit.operations_bind,
    Circuit.operations_pure, Operations.LookupActivationsWellFormed,
    List.forall_append, List.forall_nil, and_true]
  exact ⟨
    ((DecomposeB.bundle (brWit input.gdX 254 1)).toFormal
      "NoteCommit MessagePiece b").call_lookupActivationsWellFormed _ _ _,
    ((DecomposeD.bundle (brWit input.pkdX 254 1)).toFormal
      "NoteCommit MessagePiece d").call_lookupActivationsWellFormed _ _ _,
    (DecomposeE.bundle.toFormal
      "NoteCommit MessagePiece e").call_lookupActivationsWellFormed _ _ _,
    ((DecomposeG.bundle (brWit input.rho 254 1)).toFormal
      "NoteCommit MessagePiece g").call_lookupActivationsWellFormed _ _ _,
    ((DecomposeH.bundle (brWit input.psi 254 1)).toFormal
      "NoteCommit MessagePiece h").call_lookupActivationsWellFormed _ _ _⟩

private theorem synthDecompositions_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex) :
    ((synthDecompositions cfg input pcs ccs iHash).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthDecompositions, Circuit.operations_bind,
    Circuit.operations_pure, keygen_norm, keygen_spine]
  exact ⟨
    pureRegionCall_lookupSelectorAssignmentsAgree
      (DecomposeD.bundle (brWit input.pkdX 254 1))
      "NoteCommit MessagePiece d" cfg.gates.d
      { d := pcs.d, d1 := ccs.d1, d2 := pcs.d2,
        d3 := zCell cfg.hashConfig iHash 3 1 } _ () (by rfl),
    pureRegionCall_lookupSelectorAssignmentsAgree
      DecomposeE.bundle "NoteCommit MessagePiece e" cfg.gates.e
      { e := pcs.e, e0 := pcs.e0, e1 := pcs.e1 } _ () (by rfl),
    pureRegionCall_lookupSelectorAssignmentsAgree
      (DecomposeG.bundle (brWit input.rho 254 1))
      "NoteCommit MessagePiece g" cfg.gates.g
      { g := pcs.g, g1 := pcs.g1,
        g2 := zCell cfg.hashConfig iHash 6 1 } _ () (by rfl),
    pureRegionCall_lookupSelectorAssignmentsAgree
      (DecomposeH.bundle (brWit input.psi 254 1))
      "NoteCommit MessagePiece h" cfg.gates.h
      { h := pcs.h, h0 := pcs.h0 } _ () (by rfl)⟩

private theorem synthGdPkdValueCanonicity_lookupActivationsWellFormed
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.LookupActivationsWellFormed := by
  simp only [synthGdPkdValueCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, Operations.LookupActivationsWellFormed,
    List.forall_append, List.forall_nil, and_true]
  exact ⟨
    (GdCanonicity.bundle.toFormal
      "NoteCommit input g_d").call_lookupActivationsWellFormed _ _ _,
    (PkdCanonicity.bundle.toFormal
      "NoteCommit input pk_d").call_lookupActivationsWellFormed _ _ _,
    (ValueCanonicity.bundle.toFormal
      "NoteCommit input value").call_lookupActivationsWellFormed _ _ _⟩

private theorem synthRhoPsiCanonicity_lookupActivationsWellFormed
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthRhoPsiCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.LookupActivationsWellFormed := by
  simp only [synthRhoPsiCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, Operations.LookupActivationsWellFormed,
    List.forall_append, List.forall_nil, and_true]
  exact ⟨
    (RhoCanonicity.bundle.toFormal
      "NoteCommit input rho").call_lookupActivationsWellFormed _ _ _,
    (PsiCanonicity.bundle.toFormal
      "NoteCommit input psi").call_lookupActivationsWellFormed _ _ _⟩

private theorem synthGdPkdValueCanonicity_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthGdPkdValueCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthGdPkdValueCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, keygen_norm, keygen_spine]
  exact ⟨
    pureRegionCall_lookupSelectorAssignmentsAgree PkdCanonicity.bundle
      "NoteCommit input pk_d" cfg.gates.pkd _ _ () (by rfl),
    pureRegionCall_lookupSelectorAssignmentsAgree ValueCanonicity.bundle
      "NoteCommit input value" cfg.gates.value _ _ () (by rfl)⟩

private theorem synthRhoPsiCanonicity_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (gcs : GateCells) (iHash self : RegionIndex) :
    ((synthRhoPsiCanonicity cfg input pcs ccs gcs iHash).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthRhoPsiCanonicity, Circuit.operations_bind,
    Circuit.operations_pure, keygen_norm, keygen_spine]
  exact pureRegionCall_lookupSelectorAssignmentsAgree PsiCanonicity.bundle
    "NoteCommit input psi" cfg.gates.psi _ _ () (by rfl)

private theorem synthGates_lookupSelectorAssignmentsAgree
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex) :
    ((synthGates cfg input pcs ccs iHash).operations self)
      |>.LookupSelectorAssignmentsAgree := by
  simp only [synthGates, synthCanonicity, Circuit.operations_bind,
    Operations.lookupSelectorAssignmentsAgree_append]
  exact ⟨synthDecompositions_lookupSelectorAssignmentsAgree
      cfg input pcs ccs iHash self,
    synthGdPkdValueCanonicity_lookupSelectorAssignmentsAgree
      cfg input pcs ccs _ iHash _,
    synthRhoPsiCanonicity_lookupSelectorAssignmentsAgree
      cfg input pcs ccs _ iHash _⟩

private theorem synthPieces_fixedWritesLawful
    (cfg : Config) (input : Var Inputs Fp) (self : RegionIndex)
    (constantColumns : List (Column .fixed)) :
    ((synthPieces cfg input).operations self)
      |>.FixedWritesLawful constantColumns := by
  apply Operations.HasNoFixedWrites.fixedWritesLawful
  apply FloorPlanner.SynthesisSummary.HasNoFixedWrites.hasNoFixedWrites
  rw [synthPieces_synthesisSummary_eq]
  exact synthPiecesSynthesisSummary_hasNoFixedWrites cfg

private theorem synthChecks_fixedAssignmentsAgree
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash self : RegionIndex)
    (configured : (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil).Configured
      (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)) :
    ((synthChecks G R Q hQ cfg input pcs iHash).operations self).Forall
      Operation.FixedAssignmentsAgree := by
  simp only [synthChecks, Circuit.operations_bind, Circuit.operations_pure,
    List.forall_append, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only using (YCanonicityCheck.circuit (brWit input.gdY 0 1))
      |>.call_fixedAssignmentsAgree (cfg.gates.y, cfg.lookupConfig)
        (FormalCircuit.Configured.ofPure _ _ () (by rfl))
        { y := input.gdY } self
  · simpa only using (YCanonicityCheck.circuit (brWit input.pkdY 0 1))
      |>.call_fixedAssignmentsAgree (cfg.gates.y, cfg.lookupConfig)
        (FormalCircuit.Configured.ofPure _ _ () (by rfl))
        { y := input.pkdY } (self + 5)
  · simpa only using (Sinsemilla.CommitDomain.commit G ns R Q hQ ns_ne_nil)
      |>.call_fixedAssignmentsAgree
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) configured
        { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h],
          r := input.rcm } (self + 5 + 5)
  · exact (LookupRangeCheck.witnessCheck_fixedWritesLawful
      10 13 false (by simp) cfg.lookupConfig
      (GdCanonicityCheck.aPrimeWit pcs.a) _ []).regionAssignmentsAgree
  · exact (LookupRangeCheck.witnessCheck_fixedWritesLawful
      10 14 false (by simp) cfg.lookupConfig
      (PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c) _ []).regionAssignmentsAgree
  · exact (LookupRangeCheck.witnessCheck_fixedWritesLawful
      10 14 false (by simp) cfg.lookupConfig
      (RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f) _ []).regionAssignmentsAgree
  · exact (LookupRangeCheck.witnessCheck_fixedWritesLawful
      10 13 false (by simp) cfg.lookupConfig
      (PsiCanonicityCheck.g1G2PrimeWit pcs.g1
        (zCell cfg.hashConfig iHash 6 1)) _ []).regionAssignmentsAgree

private theorem synthGates_fixedWritesLawful
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash self : RegionIndex)
    (constantColumns : List (Column .fixed)) :
    ((synthGates cfg input pcs ccs iHash).operations self)
      |>.FixedWritesLawful constantColumns := by
  apply Operations.HasNoFixedWrites.fixedWritesLawful
  apply FloorPlanner.SynthesisSummary.HasNoFixedWrites.hasNoFixedWrites
  rw [synthGates_synthesisSummary_eq]
  exact synthGatesSynthesisSummary_hasNoFixedWrites cfg

/-- Canonical elaborated metadata, with fully reduced output and synthesis summary. -/
instance elaborated (G : Generators) (R : FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) :
    ElaboratedCircuit Fp Config Config Inputs Point
      (fun config => pure config) (synth G R Q hQ) where
  keygenRequirements := keygenRequirements G R Q hQ
  registered configInput _ configured input self := by
    simpa using synth_keygenRegistered
      G R Q hQ configInput input self configured
  copyCellsAssigned cfg _ configured input self :=
    synth_copyCellsAssigned G R Q hQ cfg input self configured
  lookupSelectorAssignmentsAgree_of_registered := by
    intro cfg counts hconfig input self program operations _hregistered
    simp only [operations, program, Configure.output_pure, synth,
      currentRegion_operations, Circuit.operations_bind,
      Circuit.operations_pure, keygen_norm, keygen_spine]
    exact ⟨synthPieces_lookupSelectorAssignmentsAgree cfg input self,
      synthChecks_lookupSelectorAssignmentsAgree
        G R Q hQ cfg input _ _ _ hconfig,
      synthGates_lookupSelectorAssignmentsAgree cfg input _ _ _ _⟩
  fixedWritesLawful := by
    intro cfg counts hconfig input self
    simp only [Configure.output_pure] at hconfig ⊢
    apply Operations.FixedWritesLawful.ofRegionAssignmentsAgree
    · simp only [synth, currentRegion_operations, Circuit.operations_bind,
        Circuit.operations_pure, List.forall_append, circuit_norm]
      exact ⟨(synthPieces_fixedWritesLawful cfg input self [])
          |>.regionAssignmentsAgree,
        synthChecks_fixedAssignmentsAgree G R Q hQ cfg input
          ((synthPieces cfg input).output self) (self + 27)
          ((synthPieces cfg input).nextRegionIndex self) hconfig,
        (synthGates_fixedWritesLawful cfg input _ _ _ _ [])
          |>.regionAssignmentsAgree⟩
    · rw [synth_synthesisSummary_eq]
      exact synthesisSummary_tableRowExtent_eq cfg
  lookupActivationsWellFormed config input region := by
    simp only [synth, Circuit.operations_bind, currentRegion_operations,
      Circuit.operations_pure, Operations.LookupActivationsWellFormed,
      List.forall_append, List.forall_nil, true_and, and_true]
    refine ⟨synthPieces_lookupActivationsWellFormed config input region,
      synthChecks_lookupActivationsWellFormed G R Q hQ config input _ _ _, ?_⟩
    · simp only [synthGates, Circuit.operations_bind,
        List.forall_append]
      refine ⟨synthDecompositions_lookupActivationsWellFormed
        config input _ _ _ _, ?_⟩
      simp only [synthCanonicity, Circuit.operations_bind,
        List.forall_append]
      exact ⟨synthGdPkdValueCanonicity_lookupActivationsWellFormed
          config input _ _ _ _ _,
        synthRhoPsiCanonicity_lookupActivationsWellFormed
          config input _ _ _ _ _⟩
  output cfg _ self := output cfg self
  regionCount _ := 43
  synthesisSummary cfg _ _ := synthesisSummary cfg
  output_eq cfg input self := (synth_output_eq G R Q hQ cfg input self).symm
  regionCount_eq cfg input i :=
    (synth_regionCount G R Q hQ cfg input i).symm
  synthesisSummary_eq cfg input region :=
    (synth_synthesisSummary_eq G R Q hQ cfg input region).symm

def EnvAssumptions (G : Generators) (cfg : Config)
    (env : Placed Environment Fp) : Prop :=
  Sinsemilla.GeneratorTableLoaded G cfg.hashConfig.generatorTable env.env ∧
  Ecc.MulFixed.FullWidth.EnvAssumptions cfg.mulConfig env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

def Assumptions (input : Value Inputs Fp) : Prop :=
  Point.OnCurve ⟨input.gdX, input.gdY⟩ ∧
  Point.OnCurve ⟨input.pkdX, input.pkdY⟩

/-- The extracted `rcm` window data: the fixed-base mul's window readings and the scalar
they encode, inside the commit child (regions `i₀+25`/`i₀+26`). -/
def rcmExtract (cfg : Config) (_ : Var Inputs Fp) (i₀ : RegionIndex)
    (env : Placed Environment Fp) : Vector Fp 85 × Fq :=
  Ecc.MulFixed.FullWidth.fwExtract cfg.mulConfig (i₀ + 25) env

/-- Breaks-as-data commitment contract (zcash/ironwood#45): either the Sinsemilla
chain over the note's canonical chunks is defined and the output is the commitment
`B + [rcm]R`, or the incomplete-addition escape is exhibited as a valid break
(`Specs.Sinsemilla.ValidBreak`).

The 64-bit value bound is exported (from the `ValueCanonicity` gate): without it the
statement can't type `v` as §4.17.4 does — `noteScalars` bitranges truncate `v` at 64
bits, so the commitment equation alone does not bound the field element. -/
def Spec (G : Generators) (Q : Point Fp) (R : FixedBase)
    (input : Value Inputs Fp) (output : Value Point Fp)
    (rcm : Vector Fp 85 × Fq) : Prop :=
  (show Fp from input.value).val < 2 ^ 64 ∧
  SpecOrBreak G.S Q (fun B => output = B + (rcm.2 • R : Point Fp))
    (hashToPointB G.S Q
      (NoteCommit.noteScalars ⟨input.gdX, input.gdY⟩
        ⟨input.pkdX, input.pkdY⟩ input.value input.rho input.psi).chunks)

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Inputs Fp) (_ : Vector Fp 85 × Fq)
    (_ : ProverHint Fp) : Prop :=
  Point.OnCurve ⟨input.gdX, input.gdY⟩ ∧
  Point.OnCurve ⟨input.pkdX, input.pkdY⟩ ∧
  (show Fp from input.value).val < 2 ^ 64 ∧
  (∃ B, hashToPoint G.S Q
    (NoteCommit.noteScalars ⟨input.gdX, input.gdY⟩
      ⟨input.pkdX, input.pkdY⟩ input.value input.rho input.psi).chunks = some B)

end Zcash.Circuits.NoteCommit.Main
