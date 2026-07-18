import Clean.Ironwood.NoteCommit.Gates
import Clean.Ironwood.NoteCommit.Decompose
import Clean.Ironwood.NoteCommit.Canonicity
import Clean.Ironwood.NoteCommit.Composites
import Clean.Ironwood.NoteCommit.YComposite
import Clean.Ironwood.Sinsemilla.CommitDomain

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
open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Specs (bitrange)
open Orchard.Specs.Sinsemilla (Generators)

/-- The NoteCommit message piece lengths in `K = 10`-bit words:
`a(250) ‖ b(10) ‖ c(250) ‖ d(60) ‖ e(10) ‖ f(250) ‖ g(250) ‖ h(10)`. -/
def ns : List ℕ := [25, 1, 25, 6, 1, 25, 25, 1]

theorem ns_ne_nil : ns ≠ [] := by simp [ns]

theorem ns_pos : ∀ x ∈ ns, 0 < x := by simp [ns]

/-- The circuit inputs: the note's field-element cells (`x/y(g_d)`, `x/y(pk_d)`, the
64-bit value, `rho`, `psi`). The blinding scalar `rcm` enters through the fixed-base
mul's window programs (a `Main` parameter, like the child bundle). -/
structure Inputs (F : Type) where
  gdX : F
  gdY : F
  pkdX : F
  pkdY : F
  value : F
  rho : F
  psi : F
deriving ProvableStruct

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

/-- Rust `NoteCommitChip::commit` (`note_commit.rs:1596-1798`), in exact region order.
Parameterized (like the fixed-base mul bundle) by the `rcm` window programs. -/
def synth (G : Generators) (R : FixedBase) (windows : Vector (FExpr Fp) 85)
    (Q : Point Fp) (hQ : Q.OnCurve) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp (Var Point Fp) := do
  let i₀ ← currentRegion
  -- the `hash_to_point` region of the `CommitDomain::commit` below (region 28 of the
  -- flow: 15 piece/short regions, two 5-region y-canonicity flows, the 2-region blind)
  let iHash := i₀ + 27
  -- ── pieces and sub-piece range checks (`note_commit.rs:1608-1653`) ──
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
  -- ── the two y-canonicity flows (`note_commit.rs:1654-1670`) ──
  let b2 ← (YCanonicityCheck.circuit (brWit input.gdY 0 1)).call
    (cfg.gates.y, cfg.lookupConfig) { y := input.gdY }
  let d1 ← (YCanonicityCheck.circuit (brWit input.pkdY 0 1)).call
    (cfg.gates.y, cfg.lookupConfig) { y := input.pkdY }
  -- ── `cm = NoteCommit(rcm, a‖b‖c‖d‖e‖f‖g‖h)` (`note_commit.rs:1672-1698`) ──
  let cm ← (Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).call
    (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
    { pieces := #v[a, b, c, d, e, f, g, h] }
  -- ── the four canonicity witness_checks (`note_commit.rs:1710-1737`) ──
  let aZs ← LookupRangeCheck.witnessCheck 10 13 false cfg.lookupConfig
    (GdCanonicityCheck.aPrimeWit a)
  let bZs ← LookupRangeCheck.witnessCheck 10 14 false cfg.lookupConfig
    (PkdCanonicityCheck.b3CPrimeWit b3 c)
  let eZs ← LookupRangeCheck.witnessCheck 10 14 false cfg.lookupConfig
    (RhoCanonicityCheck.e1FPrimeWit e1 f)
  let gZs ← LookupRangeCheck.witnessCheck 10 13 false cfg.lookupConfig
    (PsiCanonicityCheck.g1G2PrimeWit g1 (zCell cfg.hashConfig iHash 6 1))
  -- ── the ten gate regions (`note_commit.rs:1739-1795`) ──
  let b1 ← ((DecomposeB.bundle (brWit input.gdX 254 1)).toFormal
    "NoteCommit MessagePiece b").call cfg.gates.b { b, b0, b2, b3 }
  let d0 ← ((DecomposeD.bundle (brWit input.pkdX 254 1)).toFormal
    "NoteCommit MessagePiece d").call cfg.gates.d
    { d, d1, d2, d3 := zCell cfg.hashConfig iHash 3 1 }
  let _ ← (DecomposeE.bundle.toFormal "NoteCommit MessagePiece e").call cfg.gates.e
    { e, e0, e1 }
  let g0 ← ((DecomposeG.bundle (brWit input.rho 254 1)).toFormal
    "NoteCommit MessagePiece g").call cfg.gates.g
    { g, g1, g2 := zCell cfg.hashConfig iHash 6 1 }
  let h1 ← ((DecomposeH.bundle (brWit input.psi 254 1)).toFormal
    "NoteCommit MessagePiece h").call cfg.gates.h { h, h0 }
  let _ ← (GdCanonicity.bundle.toFormal "NoteCommit input g_d").call cfg.gates.gd
    { gdX := input.gdX, b0, b1, a, aPrime := aZs.z0,
      z13A := zCell cfg.hashConfig iHash 0 13, z13APrime := aZs.zLast }
  let _ ← (PkdCanonicity.bundle.toFormal "NoteCommit input pk_d").call cfg.gates.pkd
    { pkdX := input.pkdX, b3, d0, c, b3CPrime := bZs.z0,
      z13C := zCell cfg.hashConfig iHash 2 13, z14B3CPrime := bZs.zLast }
  let _ ← (ValueCanonicity.bundle.toFormal "NoteCommit input value").call cfg.gates.value
    { value := input.value, d2, d3 := zCell cfg.hashConfig iHash 3 1, e0 }
  let _ ← (RhoCanonicity.bundle.toFormal "NoteCommit input rho").call cfg.gates.rho
    { rho := input.rho, e1, g0, f, e1FPrime := eZs.z0,
      z13F := zCell cfg.hashConfig iHash 5 13, z14E1FPrime := eZs.zLast }
  let _ ← (PsiCanonicity.bundle.toFormal "NoteCommit input psi").call cfg.gates.psi
    { psi := input.psi, h0, g1, h1, g2 := zCell cfg.hashConfig iHash 6 1,
      g1G2Prime := gZs.z0, z13G := zCell cfg.hashConfig iHash 6 13,
      z13G1G2Prime := gZs.zLast }
  pure cm

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
    (windows : Vector (FExpr Fp) 85) (Q : Point Fp) (hQ : Q.OnCurve)
    (c : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (inp : Var (Sinsemilla.CommitDomain.Input ns.length) Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Sinsemilla.CommitDomain.commit G ns R windows Q hQ ns_ne_nil ns_pos).call
        c inp).operations j) = 4 := by
  rw [FormalCircuit.call_regionCount]
  rfl

end Halo2.Ironwood.NoteCommit.Main
