import Clean.Orchard.NoteCommit
import Clean.Orchard.Sinsemilla.Domain
import Clean.Orchard.Utilities

/-!
# `gadgets::note_commit` synthesis-level entry

Port of `orchard@0.14.0/src/circuit/note_commit.rs` `gadgets::note_commit` and its
synthesis helpers (`canon_bitshift_130`, `pkd_x_canonicity`, `rho_canonicity`,
`psi_canonicity`, `y_canonicity`, the `Decompose*::decompose` message-piece builders).

This lives in its own module — separate from `Clean.Orchard.NoteCommit` (the custom-gate
`FormalAssertion`s) — because `NoteCommit.lean` is a low-level dependency of
`Ecc.ScalarMul.Defs`, whereas the gadget needs `Sinsemilla.Domain` (the
`CommitDomain.WithZs` hash that exposes the running sums) which sits above `ScalarMul`.
-/

namespace Orchard.NoteCommit

open Utilities.LookupRangeCheck (K)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Ecc (Point)
open Orchard.Ecc.ScalarMul
open Orchard.Sinsemilla

/-- Telescoping a `K`-bit running-sum chain: `f 0` splits into `K·k` low bits and
`2^(K·k) · f k`. (Mirrors `Mul.OverflowCheck.chain_telescope`.) -/
private theorem chain_telescope (f : ℕ → Ecc.Fp) :
    ∀ k : ℕ,
    (∀ i, i < k → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Ecc.Fp)) →
    ∃ lo : ℕ, lo < 2 ^ (K * k) ∧ f 0 = (lo : Ecc.Fp) + 2 ^ (K * k) * f k
  | 0, _ => ⟨0, by norm_num, by norm_num⟩
  | k + 1, h => by
    obtain ⟨lo, hlt, heq⟩ := chain_telescope f k fun i hi => h i (by omega)
    obtain ⟨w, hw, hstep⟩ := h k (by omega)
    refine ⟨lo + w * 2 ^ (K * k), ?_, ?_⟩
    · have hbound : lo + w * 2 ^ (K * k) < (w + 1) * 2 ^ (K * k) := by
        have := Nat.two_pow_pos (K * k); nlinarith
      have : (w + 1) * 2 ^ (K * k) ≤ 2 ^ K * 2 ^ (K * k) :=
        Nat.mul_le_mul_right _ (by omega)
      have hsplit : (2 : ℕ) ^ (K * (k + 1)) = 2 ^ K * 2 ^ (K * k) := by
        rw [← pow_add]; ring_nf
      omega
    · rw [heq, hstep]; push_cast
      rw [show K * (k + 1) = K * k + K from by ring, pow_add]; ring

/-! ### Canonicity bound helpers (note_commit.rs:1804-1954)

Each witnesses a "prime" value (the element shifted up by `2^130`/`2^140` minus `t_P`)
and runs a `LookupRangeCheck` running-sum decomposition (`CopyCheck`), returning the
prime cell (`z_0`) and the final running sum (`z_13`/`z_14`). `prime` decomposes as
`prime = lo + 2^(K·n) · z_last` with `lo < 2^(K·n)`, so `z_last = 0 ⟹ prime < 2^(K·n)` —
the canonicity bound the `*Canonicity` gates consume. These are plain synthesis helpers
(not bundled circuits): the `prime = element + 2^… - t_P` link is enforced by the gate.

`copyCheck` is `LookupRangeCheck.CopyCheck.circuit`. `tP = T_P`. -/

/-- `canon_bitshift_130(a)`: returns `(a_prime, z_13)` for `a_prime = a + 2^130 - t_P`. -/
def canonBitshift130 (a : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let aPrime ← witnessField fun env => env a + (2 ^ 130 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 aPrime
  return (zs[0], zs[13])

/-- `pkd_x_canonicity(b_3, c)`: returns `(b3_c_prime, z_14)` for
`b3_c_prime = b_3 + 2^4·c + 2^140 - t_P`. -/
def pkdXCanonicity (b3 c : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env b3 + (2 ^ 4 : Ecc.Fp) * env c + (2 ^ 140 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 prime
  return (zs[0], zs[14])

/-- `rho_canonicity(e_1, f)`: returns `(e1_f_prime, z_14)` for
`e1_f_prime = e_1 + 2^4·f + 2^140 - t_P`. -/
def rhoCanonicity (e1 f : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env e1 + (2 ^ 4 : Ecc.Fp) * env f + (2 ^ 140 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 14 prime
  return (zs[0], zs[14])

/-- `psi_canonicity(g_1, g_2)`: returns `(g1_g2_prime, z_13)` for
`g1_g2_prime = g_1 + 2^9·g_2 + 2^130 - t_P`. -/
def psiCanonicity (g1 g2 : Var field Ecc.Fp) :
    Circuit Ecc.Fp (Var field Ecc.Fp × Var field Ecc.Fp) := do
  let prime ← witnessField fun env =>
    env g1 + (2 ^ 9 : Ecc.Fp) * env g2 + (2 ^ 130 : Ecc.Fp) - tP
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 prime
  return (zs[0], zs[13])

/-! ### Subpiece witnessing helpers -/

/-- `bitrangeSubset value start numBits = (value.val >> start) mod 2^numBits`. -/
abbrev bitrangeSubset : Ecc.Fp → ℕ → ℕ → Ecc.Fp :=
  Utilities.LookupRangeCheck.WitnessShort.bitrangeSubset

/-- `RangeConstrained::witness_short` reading the source from a constrained cell:
witness `bitrangeSubset src start numBits` and short-range-check it to `numBits`. -/
def witnessShort (src : Var field Ecc.Fp) (start numBits : ℕ) (h : numBits ≤ Utilities.LookupRangeCheck.K) :
    Circuit Ecc.Fp (Var field Ecc.Fp) := do
  Utilities.LookupRangeCheck.WitnessShort.circuit start numBits h
    (fun env => bitrangeSubset (Expression.eval env src) start numBits)

/-- `RangeConstrained::bitrange_of`: witness `bitrangeSubset src start numBits` with no
range check (it is bool/decomposition-constrained downstream). -/
def witnessBitrange (src : Var field Ecc.Fp) (start numBits : ℕ) :
    Circuit Ecc.Fp (Var field Ecc.Fp) :=
  witnessField fun env => bitrangeSubset (Expression.eval env src) start numBits

/-! ### `y_canonicity` (note_commit.rs:1962)

Decomposes `y = lsb || k_0 || k_1 || k_2 || k_3`, range-decomposes `j = lsb + 2·k_0 +
2^10·k_1` (strict, 25 words), reuses `canon_bitshift_130` on `j`, and wires the
`YCanonicity` gate. Returns the `lsb` (the `ỹ` sign bit) it was given. -/
def yCanonicity (y lsb : Var field Ecc.Fp) : Circuit Ecc.Fp (Var field Ecc.Fp) := do
  let k0 ← witnessShort y 1 9 (by norm_num [K])
  let k2 ← witnessShort y 250 4 (by norm_num [K])
  let k3 ← witnessBitrange y 254 1
  let j ← witnessField fun env =>
    env lsb + 2 * env k0 + (2 ^ 10 : Ecc.Fp) * bitrangeSubset (Expression.eval env y) 10 240
  let zs ← Utilities.LookupRangeCheck.CopyCheck.circuit 25 j
  -- strict: the running sum must vanish (the value fits exactly in 250 bits)
  assertZero zs[25]
  let (jPrime, z13JPrime) ← canonBitshift130 zs[0]
  let yrow : Var NoteCommit.YCanonicity.Row Ecc.Fp :=
    { y := y, lsb := lsb, k0 := k0, k2 := k2, k3 := k3, j := zs[0], z1J := zs[1],
      z13J := zs[13], jPrime := jPrime, z13JPrime := z13JPrime }
  NoteCommit.YCanonicity.circuit yrow
  return lsb

instance witnessShortExplicit (src : Var field Ecc.Fp) (start numBits : ℕ)
    (h : numBits ≤ Utilities.LookupRangeCheck.K) :
    ExplicitCircuit (witnessShort src start numBits h) := by
  unfold witnessShort
  infer_explicit_circuit

instance witnessBitrangeExplicit (src : Var field Ecc.Fp) (start numBits : ℕ) :
    ExplicitCircuit (witnessBitrange src start numBits) := by
  unfold witnessBitrange
  infer_explicit_circuit

instance canonBitshift130Explicit (a : Var field Ecc.Fp) :
    ExplicitCircuit (canonBitshift130 a) := by
  unfold canonBitshift130
  infer_explicit_circuit

instance pkdXCanonicityExplicit (b3 c : Var field Ecc.Fp) :
    ExplicitCircuit (pkdXCanonicity b3 c) := by
  unfold pkdXCanonicity
  infer_explicit_circuit

instance rhoCanonicityExplicit (e1 f : Var field Ecc.Fp) :
    ExplicitCircuit (rhoCanonicity e1 f) := by
  unfold rhoCanonicity
  infer_explicit_circuit

instance psiCanonicityExplicit (g1 g2 : Var field Ecc.Fp) :
    ExplicitCircuit (psiCanonicity g1 g2) := by
  unfold psiCanonicity
  infer_explicit_circuit

instance yCanonicityExplicit (y lsb : Var field Ecc.Fp) :
    ExplicitCircuit (yCanonicity y lsb) := by
  unfold yCanonicity
  infer_explicit_circuit

attribute [explicit_circuit_no_unfold] witnessShort witnessBitrange canonBitshift130
  pkdXCanonicity rhoCanonicity psiCanonicity yCanonicity

/-! ### `gadgets::note_commit` (note_commit.rs:1594) -/

/-- Inputs of `gadgets::note_commit`: the note's `g_d`, `pk_d` points, the value/`rho`/`psi`
field cells, and the prover-side commitment randomness `rcm`. -/
structure Input (F : Type) where
  gd : Point F
  pkd : Point F
  value : F
  rho : F
  psi : F
  rcm : Unconstrained Fq F
deriving CircuitType

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ gd := default, pkd := default, value := default, rho := default, psi := default,
     rcm := fun _ => default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) (input : Var Input Ecc.Fp) :
    Circuit Ecc.Fp (Var Point Ecc.Fp) := do
  let gdX := input.gd.x
  let gdY := input.gd.y
  let pkdX := input.pkd.x
  let pkdY := input.pkd.y
  let v := input.value
  let rho := input.rho
  let psi := input.psi
  -- range-checked subpieces
  let b0 ← witnessShort gdX 250 4 (by norm_num [K])
  let b3 ← witnessShort pkdX 0 4 (by norm_num [K])
  let d2 ← witnessShort v 0 8 (by norm_num [K])
  let e0 ← witnessShort v 58 6 (by norm_num [K])
  let e1 ← witnessShort rho 0 4 (by norm_num [K])
  let g1 ← witnessShort psi 0 9 (by norm_num [K])
  let h0 ← witnessShort psi 249 5 (by norm_num [K])
  -- bitrange-only subpieces (bool/decomposition-constrained in the gates)
  let b1 ← witnessBitrange gdX 254 1
  let b2 ← witnessBitrange gdY 0 1
  let d0 ← witnessBitrange pkdX 254 1
  let d1 ← witnessBitrange pkdY 0 1
  let g0 ← witnessBitrange rho 254 1
  let h1 ← witnessBitrange psi 254 1
  -- y-coordinate canonicity (ties b_2 = ỹ(g_d), d_1 = ỹ(pk_d) to the y decompositions)
  let b2 ← yCanonicity gdY b2
  let d1 ← yCanonicity pkdY d1
  -- the message pieces (honest packed values; the Decompose* gates constrain the packing)
  let a ← witnessBitrange gdX 0 250
  let b ← witnessField fun env => env b0 + env b1 * 2 ^ 4 + env b2 * 2 ^ 5 + env b3 * 2 ^ 6
  let c ← witnessBitrange pkdX 4 250
  let d ← witnessField fun env => env d0 + env d1 * 2 + env d2 * 2 ^ 2 +
    bitrangeSubset (Expression.eval env v) 8 50 * 2 ^ 10
  let e ← witnessField fun env => env e0 + env e1 * 2 ^ 6
  let f ← witnessBitrange rho 4 250
  let g ← witnessField fun env => env g0 + env g1 * 2 +
    bitrangeSubset (Expression.eval env psi) 9 240 * 2 ^ 10
  let h ← witnessField fun env => env h0 + env h1 * 2 ^ 5
  -- cm = NoteCommit_rcm(message); zs are the per-piece running sums
  let out ← _root_.Orchard.Sinsemilla.CommitDomain.WithZs.circuit G Q hQ R 25
    [1, 25, 6, 1, 25, 25, 1]
    { pieces := #v[a, b, c, d, e, f, g, h], r := input.rcm }
  let cm := out.point
  -- running-sum cells needed for canonicity (note_commit.rs:1702-1708)
  let z13a := (HVec.get _ out.zs ⟨0, by decide⟩)[13]
  let z13c := (HVec.get _ out.zs ⟨2, by decide⟩)[13]
  let z1d := (HVec.get _ out.zs ⟨3, by decide⟩)[1]
  let z13f := (HVec.get _ out.zs ⟨5, by decide⟩)[13]
  let z1g := (HVec.get _ out.zs ⟨6, by decide⟩)[1]
  let z13g := (HVec.get _ out.zs ⟨6, by decide⟩)[13]
  -- canonicity bounds
  let (aPrime, z13aPrime) ← canonBitshift130 a
  let (b3cPrime, z14b3c) ← pkdXCanonicity b3 c
  let (e1fPrime, z14e1f) ← rhoCanonicity e1 f
  let (g1g2Prime, z13g1g2) ← psiCanonicity g1 z1g
  -- the NoteCommit decomposition + canonicity gates
  NoteCommit.DecomposeB.circuit { b := b, b0 := b0, b1 := b1, b2 := b2, b3 := b3 }
  NoteCommit.DecomposeD.circuit { d := d, d0 := d0, d1 := d1, d2 := d2, d3 := z1d }
  NoteCommit.DecomposeE.circuit { e := e, e0 := e0, e1 := e1 }
  NoteCommit.DecomposeG.circuit { g := g, g0 := g0, g1 := g1, g2 := z1g }
  NoteCommit.DecomposeH.circuit { h := h, h0 := h0, h1 := h1 }
  NoteCommit.GdCanonicity.circuit
    { gdX := gdX, b0 := b0, b1 := b1, a := a, aPrime := aPrime, z13A := z13a,
      z13APrime := z13aPrime }
  NoteCommit.PkdCanonicity.circuit
    { pkdX := pkdX, b3 := b3, c := c, d0 := d0, b3CPrime := b3cPrime, z13C := z13c,
      z14B3CPrime := z14b3c }
  NoteCommit.ValueCanonicity.circuit { value := v, d2 := d2, d3 := z1d, e0 := e0 }
  NoteCommit.RhoCanonicity.circuit
    { rho := rho, e1 := e1, f := f, g0 := g0, e1FPrime := e1fPrime, z13F := z13f,
      z14E1FPrime := z14e1f }
  NoteCommit.PsiCanonicity.circuit
    { psi := psi, h0 := h0, g1 := g1, h1 := h1, g2 := z1g, g1G2Prime := g1g2Prime,
      z13G := z13g, z13G1G2Prime := z13g1g2 }
  return cm

instance mainExplicit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (R : MulFixed.FixedBase) : ExplicitCircuits (main G Q hQ R) := by
  infer_explicit_circuits

/-- The note's seven field-element scalars, as `ℕ`, extracted from a circuit value.
`g_d`/`pk_d` contribute their `x` and the `ỹ` sign bit (`y mod 2`). -/
def noteScalars (input : Value Input Ecc.Fp) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let gdX : Ecc.Fp := input.gd.x
  let gdY : Ecc.Fp := input.gd.y
  let pkdX : Ecc.Fp := input.pkd.x
  let pkdY : Ecc.Fp := input.pkd.y
  let v : Ecc.Fp := input.value
  let rho : Ecc.Fp := input.rho
  let psi : Ecc.Fp := input.psi
  (gdX.val, gdY.val % 2, pkdX.val, pkdY.val % 2, v.val, rho.val, psi.val)

def proverNoteScalars (input : ProverValue Input Ecc.Fp) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let gdX : Ecc.Fp := input.gd.x
  let gdY : Ecc.Fp := input.gd.y
  let pkdX : Ecc.Fp := input.pkd.x
  let pkdY : Ecc.Fp := input.pkd.y
  let v : Ecc.Fp := input.value
  let rho : Ecc.Fp := input.rho
  let psi : Ecc.Fp := input.psi
  (gdX.val, gdY.val % 2, pkdX.val, pkdY.val % 2, v.val, rho.val, psi.val)

/-- `g_d` and `pk_d` enter the Halo2 gadget as already-assigned non-identity points. In
Clean's point model this is the on-curve half of `NonIdentityEccPoint`; identity is not
representable as an affine point in the source API at this boundary. -/
def Assumptions (input : Value Input Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧ Pallas.OnCurve input.pkd.coords

/-- `cm` is the Orchard note commitment of the note `(g_d, pk_d, value, rho, psi)` with
randomness `rcm`: `cm = NoteCommit^Orchard_rcm(g★_d || pk★_d || v || rho || psi)`. The
message is the `Sinsemilla` hash of the canonical 109-chunk encoding (the canonicity
gates force the field inputs into that canonical bit-layout) translated by `[rcm] R`. -/
def Spec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : Value Input Ecc.Fp) (cm : Point Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := noteScalars input
  ∃ rcm : Fq, ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi)
      = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue rcm).coords

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve)
    (input : ProverValue Input Ecc.Fp) (_ : ProverData Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  Pallas.OnCurve input.gd.coords ∧
  Pallas.OnCurve input.pkd.coords ∧
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := proverNoteScalars input
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (R : MulFixed.FixedBase)
    (input : ProverValue Input Ecc.Fp) (cm : ProverValue Point Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  let (gdX, gdYbit, pkdX, pkdYbit, v, rho, psi) := proverNoteScalars input
  ∀ B : SWPoint Pallas.curve,
    Orchard.Specs.Sinsemilla.hashToPoint G.S Q
        (Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi)
      = some B →
      cm.coords = Pallas.add (B.x, B.y) (R.mulValue input.rcm).coords

-- TODO(note_commit): bundle into a `GeneralFormalCircuit.WithHint`. Blocked on:
--   (1) `ElaboratedCircuit`: `mainExplicit` is inferable, but the generated metadata is
--       still too large for the default `ExplicitCircuits.IsElaborated` proof. Provide a
--       controlled offset-independence proof or an explicit data override for
--       `localLength`/`output` (output = `out.point`, a clean point).
--   (2) `soundness` (prime-`p` canonicity: the gates force the inputs canonical, and the
--       pieces equal `noteCommitChunks`'s tiling via `noteCommitChunks_tiling`) +
--       `completeness`. This is the largest remaining proof.

end Orchard.NoteCommit
