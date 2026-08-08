import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Specs.Pallas

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs`
- `DecomposeB::configure` (lines 84-130), `DecomposeD` (229-275), `DecomposeE` (365-396),
  `DecomposeG` (483-521), `DecomposeH` (606-644): the five MessagePiece decomposition
  gates on `col_l/col_m/col_r = advices[6..9]`.
- `GdCanonicity::configure` (725-789), `PkdCanonicity` (842-905),
  `ValueCanonicity` (957-994), `RhoCanonicity` (1036-1098), `PsiCanonicity` (1151-1240):
  the five input gates on `col_l/col_m/col_r/col_z = advices[6..10]`.
- `YCanonicity::configure` (1275-1345): the `"y coordinate checks"` gate on
  `advices[5..10]`.
- `NoteCommitConfig::configure` (1456-1560): the eleven sub-configures in registration
  order b, d, e, g, h, g_d, pk_d, value, rho, psi, y.

All gate polynomials are written in the source's exact orientation (`expr * const` for
`Scaled`, `Expression::Constant` sums via the `F → Expression` coercion, `bool_check(v) =
v·(1−v)`, source constraint names). The semantic per-gate contracts live in the sibling
bundle files; this file is the VK-facing surface only.
-/

namespace Zcash.Circuits.NoteCommit

open Halo2

/-- Rust `bool_check` (`utilities.rs:141-143`): `v · (1 − v)`. -/
@[selector_free, query_correct]
def boolCheck (v : Expression Fp Query) : Expression Fp Query :=
  v * ((1 : Fp) - v)

/-! ## The five MessagePiece decomposition gates -/

namespace DecomposeB

/-- Rust `DecomposeB` (`note_commit.rs:70-130`). -/
structure Config where
  qNotecommitB : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice

/-- `"NoteCommit MessagePiece b"` (`note_commit.rs:95-121`):
`b = b_0 + 2⁴·b_1 + 2⁵·b_2 + 2⁶·b_3` with `b_1`, `b_2` boolean. -/
def gate (cfg : Config) : Gate Fp :=
  let b : Expression Fp Query := queryAdvice cfg.colL 0
  let b0 : Expression Fp Query := queryAdvice cfg.colM 0
  let b1 : Expression Fp Query := queryAdvice cfg.colR 0
  let b2 : Expression Fp Query := queryAdvice cfg.colM 1
  let b3 : Expression Fp Query := queryAdvice cfg.colR 1
  Gate.withSelector "NoteCommit MessagePiece b" cfg.qNotecommitB
    [b, b0, b1, b2, b3]
    [("bool_check b_1", boolCheck b1),
     ("bool_check b_2", boolCheck b2),
     ("decomposition",
      b - (b0 + b1 * (2 ^ 4 : Fp) + b2 * (2 ^ 5 : Fp) + b3 * (2 ^ 6 : Fp)))]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitB := rfl

def configure (colL colM colR : Column .advice) : Configure Fp Config := do
  let qNotecommitB ← selector
  let cfg : Config := { qNotecommitB, colL, colM, colR }
  createGate (gate cfg)
  return cfg

instance (colL colM colR : Column .advice) :
    ElaboratedConfigure (configure colL colM colR) := by
  unfold configure
  infer_instance

end DecomposeB

namespace DecomposeD

/-- Rust `DecomposeD` (`note_commit.rs:215-275`). -/
structure Config where
  qNotecommitD : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice

/-- `"NoteCommit MessagePiece d"` (`note_commit.rs:240-266`):
`d = d_0 + 2·d_1 + 2²·d_2 + 2¹⁰·d_3` with `d_0`, `d_1` boolean. -/
def gate (cfg : Config) : Gate Fp :=
  let d : Expression Fp Query := queryAdvice cfg.colL 0
  let d0 : Expression Fp Query := queryAdvice cfg.colM 0
  let d1 : Expression Fp Query := queryAdvice cfg.colR 0
  let d2 : Expression Fp Query := queryAdvice cfg.colM 1
  let d3 : Expression Fp Query := queryAdvice cfg.colR 1
  Gate.withSelector "NoteCommit MessagePiece d" cfg.qNotecommitD
    [d, d0, d1, d2, d3]
    [("bool_check d_0", boolCheck d0),
     ("bool_check d_1", boolCheck d1),
     ("decomposition",
      d - (d0 + d1 * (2 : Fp) + d2 * (2 ^ 2 : Fp) + d3 * (2 ^ 10 : Fp)))]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitD := rfl

def configure (colL colM colR : Column .advice) : Configure Fp Config := do
  let qNotecommitD ← selector
  let cfg : Config := { qNotecommitD, colL, colM, colR }
  createGate (gate cfg)
  return cfg

instance (colL colM colR : Column .advice) :
    ElaboratedConfigure (configure colL colM colR) := by
  unfold configure
  infer_instance

end DecomposeD

namespace DecomposeE

/-- Rust `DecomposeE` (`note_commit.rs:351-396`). -/
structure Config where
  qNotecommitE : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice

/-- `"NoteCommit MessagePiece e"` (`note_commit.rs:374-388`): `e = e_0 + 2⁶·e_1`. -/
def gate (cfg : Config) : Gate Fp :=
  let e : Expression Fp Query := queryAdvice cfg.colL 0
  let e0 : Expression Fp Query := queryAdvice cfg.colM 0
  let e1 : Expression Fp Query := queryAdvice cfg.colR 0
  Gate.withSelector "NoteCommit MessagePiece e" cfg.qNotecommitE
    [e, e0, e1]
    [("decomposition", e - (e0 + e1 * (2 ^ 6 : Fp)))]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitE := rfl

def configure (colL colM colR : Column .advice) : Configure Fp Config := do
  let qNotecommitE ← selector
  let cfg : Config := { qNotecommitE, colL, colM, colR }
  createGate (gate cfg)
  return cfg

instance (colL colM colR : Column .advice) :
    ElaboratedConfigure (configure colL colM colR) := by
  unfold configure
  infer_instance

end DecomposeE

namespace DecomposeG

/-- Rust `DecomposeG` (`note_commit.rs:469-521`). -/
structure Config where
  qNotecommitG : Selector
  colL : Column .advice
  colM : Column .advice

/-- `"NoteCommit MessagePiece g"` (`note_commit.rs:492-514`):
`g = g_0 + 2·g_1 + 2¹⁰·g_2` with `g_0` boolean. -/
def gate (cfg : Config) : Gate Fp :=
  let g : Expression Fp Query := queryAdvice cfg.colL 0
  let g0 : Expression Fp Query := queryAdvice cfg.colM 0
  let g1 : Expression Fp Query := queryAdvice cfg.colL 1
  let g2 : Expression Fp Query := queryAdvice cfg.colM 1
  Gate.withSelector "NoteCommit MessagePiece g" cfg.qNotecommitG
    [g, g0, g1, g2]
    [("bool_check g_0", boolCheck g0),
     ("decomposition", g - (g0 + g1 * (2 : Fp) + g2 * (2 ^ 10 : Fp)))]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitG := rfl

def configure (colL colM : Column .advice) : Configure Fp Config := do
  let qNotecommitG ← selector
  let cfg : Config := { qNotecommitG, colL, colM }
  createGate (gate cfg)
  return cfg

instance (colL colM : Column .advice) :
    ElaboratedConfigure (configure colL colM) := by
  unfold configure
  infer_instance

end DecomposeG

namespace DecomposeH

/-- Rust `DecomposeH` (`note_commit.rs:592-644`). -/
structure Config where
  qNotecommitH : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice

/-- `"NoteCommit MessagePiece h"` (`note_commit.rs:615-636`):
`h = h_0 + 2⁵·h_1` with `h_1` boolean. -/
def gate (cfg : Config) : Gate Fp :=
  let h : Expression Fp Query := queryAdvice cfg.colL 0
  let h0 : Expression Fp Query := queryAdvice cfg.colM 0
  let h1 : Expression Fp Query := queryAdvice cfg.colR 0
  Gate.withSelector "NoteCommit MessagePiece h" cfg.qNotecommitH
    [h, h0, h1]
    [("bool_check h_1", boolCheck h1),
     ("decomposition", h - (h0 + h1 * (2 ^ 5 : Fp)))]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitH := rfl

def configure (colL colM colR : Column .advice) : Configure Fp Config := do
  let qNotecommitH ← selector
  let cfg : Config := { qNotecommitH, colL, colM, colR }
  createGate (gate cfg)
  return cfg

instance (colL colM colR : Column .advice) :
    ElaboratedConfigure (configure colL colM colR) := by
  unfold configure
  infer_instance

end DecomposeH

/-! ## The five input-canonicity gates -/

namespace GdCanonicity

/-- Rust `GdCanonicity` (`note_commit.rs:711-789`). -/
structure Config where
  qNotecommitGd : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice
  colZ : Column .advice

/-- `"NoteCommit input g_d"` (`note_commit.rs:738-780`): `x(g_d) = a + 2²⁵⁰·b_0 +
2²⁵⁴·b_1`, the canonicity shift `a' = a + 2¹³⁰ − t_P`, and the three `b_1 = 1`-gated
canonicity zeros. -/
def gate (cfg : Config) : Gate Fp :=
  let gdX : Expression Fp Query := queryAdvice cfg.colL 0
  let b0 : Expression Fp Query := queryAdvice cfg.colM 0
  let b1 : Expression Fp Query := queryAdvice cfg.colM 1
  let a : Expression Fp Query := queryAdvice cfg.colR 0
  let aPrime : Expression Fp Query := queryAdvice cfg.colR 1
  let z13A : Expression Fp Query := queryAdvice cfg.colZ 0
  let z13APrime : Expression Fp Query := queryAdvice cfg.colZ 1
  Gate.withSelector "NoteCommit input g_d" cfg.qNotecommitGd
    [gdX, b0, b1, a, aPrime, z13A, z13APrime]
    [("decomposition", a + b0 * (2 ^ 250 : Fp) + b1 * (2 ^ 254 : Fp) - gdX),
     ("a_prime_check", a + (2 ^ 130 : Fp) - (tP : Fp) - aPrime),
     ("b_1 = 1 => b_0", b1 * b0),
     ("b_1 = 1 => z13_a", b1 * z13A),
     ("b_1 = 1 => z13_a_prime", b1 * z13APrime)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitGd := rfl

def configure (colL colM colR colZ : Column .advice) : Configure Fp Config := do
  let qNotecommitGd ← selector
  let cfg : Config := { qNotecommitGd, colL, colM, colR, colZ }
  createGate (gate cfg)
  return cfg

instance (colL colM colR colZ : Column .advice) :
    ElaboratedConfigure (configure colL colM colR colZ) := by
  unfold configure
  infer_instance

end GdCanonicity

namespace PkdCanonicity

/-- Rust `PkdCanonicity` (`note_commit.rs:828-905`). -/
structure Config where
  qNotecommitPkd : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice
  colZ : Column .advice

/-- `"NoteCommit input pk_d"` (`note_commit.rs:855-896`): `x(pk_d) = b_3 + 2⁴·c +
2²⁵⁴·d_0`, the shift `b3_c' = b_3 + 2⁴·c + 2¹⁴⁰ − t_P`, and the two `d_0 = 1`-gated
canonicity zeros. -/
def gate (cfg : Config) : Gate Fp :=
  let pkdX : Expression Fp Query := queryAdvice cfg.colL 0
  let b3 : Expression Fp Query := queryAdvice cfg.colM 0
  let d0 : Expression Fp Query := queryAdvice cfg.colM 1
  let c : Expression Fp Query := queryAdvice cfg.colR 0
  let b3CPrime : Expression Fp Query := queryAdvice cfg.colR 1
  let z13C : Expression Fp Query := queryAdvice cfg.colZ 0
  let z14B3CPrime : Expression Fp Query := queryAdvice cfg.colZ 1
  Gate.withSelector "NoteCommit input pk_d" cfg.qNotecommitPkd
    [pkdX, b3, d0, c, b3CPrime, z13C, z14B3CPrime]
    [("decomposition", b3 + c * (2 ^ 4 : Fp) + d0 * (2 ^ 254 : Fp) - pkdX),
     ("b3_c_prime_check",
      b3 + c * (2 ^ 4 : Fp) + (2 ^ 140 : Fp) - (tP : Fp) - b3CPrime),
     ("d_0 = 1 => z13_c", d0 * z13C),
     ("d_0 = 1 => z14_b3_c_prime", d0 * z14B3CPrime)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitPkd := rfl

def configure (colL colM colR colZ : Column .advice) : Configure Fp Config := do
  let qNotecommitPkd ← selector
  let cfg : Config := { qNotecommitPkd, colL, colM, colR, colZ }
  createGate (gate cfg)
  return cfg

instance (colL colM colR colZ : Column .advice) :
    ElaboratedConfigure (configure colL colM colR colZ) := by
  unfold configure
  infer_instance

end PkdCanonicity

namespace ValueCanonicity

/-- Rust `ValueCanonicity` (`note_commit.rs:943-994`). -/
structure Config where
  qNotecommitValue : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice
  colZ : Column .advice

/-- `"NoteCommit input value"` (`note_commit.rs:968-984`):
`value = d_2 + 2⁸·d_3 + 2⁵⁸·e_0` (with `d_3 = z1_d`). -/
def gate (cfg : Config) : Gate Fp :=
  let value : Expression Fp Query := queryAdvice cfg.colL 0
  let d2 : Expression Fp Query := queryAdvice cfg.colM 0
  let d3 : Expression Fp Query := queryAdvice cfg.colR 0
  let e0 : Expression Fp Query := queryAdvice cfg.colZ 0
  Gate.withSelector "NoteCommit input value" cfg.qNotecommitValue
    [value, d2, d3, e0]
    [("value_check", d2 + d3 * (2 ^ 8 : Fp) + e0 * (2 ^ 58 : Fp) - value)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitValue := rfl

def configure (colL colM colR colZ : Column .advice) : Configure Fp Config := do
  let qNotecommitValue ← selector
  let cfg : Config := { qNotecommitValue, colL, colM, colR, colZ }
  createGate (gate cfg)
  return cfg

instance (colL colM colR colZ : Column .advice) :
    ElaboratedConfigure (configure colL colM colR colZ) := by
  unfold configure
  infer_instance

end ValueCanonicity

namespace RhoCanonicity

/-- Rust `RhoCanonicity` (`note_commit.rs:1022-1098`). -/
structure Config where
  qNotecommitRho : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice
  colZ : Column .advice

/-- `"NoteCommit input rho"` (`note_commit.rs:1049-1089`): `rho = e_1 + 2⁴·f +
2²⁵⁴·g_0`, the shift `e1_f' = e_1 + 2⁴·f + 2¹⁴⁰ − t_P`, and the two `g_0 = 1`-gated
canonicity zeros. -/
def gate (cfg : Config) : Gate Fp :=
  let rho : Expression Fp Query := queryAdvice cfg.colL 0
  let e1 : Expression Fp Query := queryAdvice cfg.colM 0
  let g0 : Expression Fp Query := queryAdvice cfg.colM 1
  let f : Expression Fp Query := queryAdvice cfg.colR 0
  let e1FPrime : Expression Fp Query := queryAdvice cfg.colR 1
  let z13F : Expression Fp Query := queryAdvice cfg.colZ 0
  let z14E1FPrime : Expression Fp Query := queryAdvice cfg.colZ 1
  Gate.withSelector "NoteCommit input rho" cfg.qNotecommitRho
    [rho, e1, g0, f, e1FPrime, z13F, z14E1FPrime]
    [("decomposition", e1 + f * (2 ^ 4 : Fp) + g0 * (2 ^ 254 : Fp) - rho),
     ("e1_f_prime_check",
      e1 + f * (2 ^ 4 : Fp) + (2 ^ 140 : Fp) - (tP : Fp) - e1FPrime),
     ("g_0 = 1 => z13_f", g0 * z13F),
     ("g_0 = 1 => z14_e1_f_prime", g0 * z14E1FPrime)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitRho := rfl

def configure (colL colM colR colZ : Column .advice) : Configure Fp Config := do
  let qNotecommitRho ← selector
  let cfg : Config := { qNotecommitRho, colL, colM, colR, colZ }
  createGate (gate cfg)
  return cfg

instance (colL colM colR colZ : Column .advice) :
    ElaboratedConfigure (configure colL colM colR colZ) := by
  unfold configure
  infer_instance

end RhoCanonicity

namespace PsiCanonicity

/-- Rust `PsiCanonicity` (`note_commit.rs:1137-1240`). -/
structure Config where
  qNotecommitPsi : Selector
  colL : Column .advice
  colM : Column .advice
  colR : Column .advice
  colZ : Column .advice

/-- `"NoteCommit input psi"` (`note_commit.rs:1165-1230`): `psi = g_1 + 2⁹·g_2 +
2²⁴⁹·h_0 + 2²⁵⁴·h_1` (with `g_2 = z1_g`), the shift `g1_g2' = g_1 + 2⁹·g_2 + 2¹³⁰ −
t_P`, and the three `h_1 = 1`-gated canonicity zeros. -/
def gate (cfg : Config) : Gate Fp :=
  let psi : Expression Fp Query := queryAdvice cfg.colL 0
  let h0 : Expression Fp Query := queryAdvice cfg.colL 1
  let g1 : Expression Fp Query := queryAdvice cfg.colM 0
  let h1 : Expression Fp Query := queryAdvice cfg.colM 1
  let g2 : Expression Fp Query := queryAdvice cfg.colR 0
  let g1G2Prime : Expression Fp Query := queryAdvice cfg.colR 1
  let z13G : Expression Fp Query := queryAdvice cfg.colZ 0
  let z13G1G2Prime : Expression Fp Query := queryAdvice cfg.colZ 1
  Gate.withSelector "NoteCommit input psi" cfg.qNotecommitPsi
    [psi, h0, g1, h1, g2, g1G2Prime, z13G, z13G1G2Prime]
    [("decomposition",
      g1 + g2 * (2 ^ 9 : Fp) + h0 * (2 ^ 249 : Fp) + h1 * (2 ^ 254 : Fp) - psi),
     ("g1_g2_prime_check",
      g1 + g2 * (2 ^ 9 : Fp) + (2 ^ 130 : Fp) - (tP : Fp) - g1G2Prime),
     ("h_1 = 1 => h_0", h1 * h0),
     ("h_1 = 1 => z13_g", h1 * z13G),
     ("h_1 = 1 => z13_g1_g2_prime", h1 * z13G1G2Prime)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qNotecommitPsi := rfl

def configure (colL colM colR colZ : Column .advice) : Configure Fp Config := do
  let qNotecommitPsi ← selector
  let cfg : Config := { qNotecommitPsi, colL, colM, colR, colZ }
  createGate (gate cfg)
  return cfg

instance (colL colM colR colZ : Column .advice) :
    ElaboratedConfigure (configure colL colM colR colZ) := by
  unfold configure
  infer_instance

end PsiCanonicity

namespace YCanonicity

/-- Rust `YCanonicity` (`note_commit.rs:1261-1345`). -/
structure Config where
  qYCanon : Selector
  advices : Fin 10 → Column .advice

/-- `"y coordinate checks"` (`note_commit.rs:1287-1342`): `k_3` boolean, `j = LSB + 2·k_0
+ 2¹⁰·k_1` (with `k_1 = z1_j`), `y = j + 2²⁵⁰·k_2 + 2²⁵⁴·k_3`, the shift `j' = j + 2¹³⁰
− t_P`, and the three `k_3 = 1`-gated canonicity zeros. -/
def gate (cfg : Config) : Gate Fp :=
  let y : Expression Fp Query := queryAdvice (cfg.advices 5) 0
  let lsb : Expression Fp Query := queryAdvice (cfg.advices 6) 0
  let k0 : Expression Fp Query := queryAdvice (cfg.advices 7) 0
  let k2 : Expression Fp Query := queryAdvice (cfg.advices 8) 0
  let k3 : Expression Fp Query := queryAdvice (cfg.advices 9) 0
  let j : Expression Fp Query := queryAdvice (cfg.advices 5) 1
  let z1J : Expression Fp Query := queryAdvice (cfg.advices 6) 1
  let z13J : Expression Fp Query := queryAdvice (cfg.advices 7) 1
  let jPrime : Expression Fp Query := queryAdvice (cfg.advices 8) 1
  let z13JPrime : Expression Fp Query := queryAdvice (cfg.advices 9) 1
  Gate.withSelector "y coordinate checks" cfg.qYCanon
    [y, lsb, k0, k2, k3, j, z1J, z13J, jPrime, z13JPrime]
    [("k3_check", boolCheck k3),
     ("j_check", j - (lsb + k0 * (2 : Fp) + z1J * (2 ^ 10 : Fp))),
     ("y_check", y - (j + k2 * (2 ^ 250 : Fp) + k3 * (2 ^ 254 : Fp))),
     ("j_prime_check", j + (2 ^ 130 : Fp) - (tP : Fp) - jPrime),
     ("k_3 = 1 => k_2 = 0", k3 * k2),
     ("k_3 = 1 => z13_j = 0", k3 * z13J),
     ("k_3 = 1 => z13_j_prime = 0", k3 * z13JPrime)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem gate_selector (cfg : Config) : (gate cfg).selector = cfg.qYCanon := rfl

def configure (advices : Fin 10 → Column .advice) : Configure Fp Config := do
  let qYCanon ← selector
  let cfg : Config := { qYCanon, advices }
  createGate (gate cfg)
  return cfg

instance (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configure advices) := by
  unfold configure
  infer_instance

end YCanonicity

/-! ## The combined configure (`NoteCommitConfig::configure`, `note_commit.rs:1456-1560`) -/

/-- Rust `NoteCommitConfig` (gate part): the eleven sub-configs. -/
structure Config where
  b : DecomposeB.Config
  d : DecomposeD.Config
  e : DecomposeE.Config
  g : DecomposeG.Config
  h : DecomposeH.Config
  gd : GdCanonicity.Config
  pkd : PkdCanonicity.Config
  value : ValueCanonicity.Config
  rho : RhoCanonicity.Config
  psi : PsiCanonicity.Config
  y : YCanonicity.Config

/-- Equality-enabled columns used by the configured NoteCommit gates. -/
def permutationColumns (cfg : Config) : List AnyColumn :=
  [cfg.b.colL, cfg.b.colM, cfg.b.colR,
    cfg.d.colL, cfg.d.colM, cfg.d.colR,
    cfg.e.colL, cfg.e.colM, cfg.e.colR,
    cfg.g.colL, cfg.g.colM,
    cfg.h.colL, cfg.h.colM, cfg.h.colR,
    cfg.gd.colL, cfg.gd.colM, cfg.gd.colR, cfg.gd.colZ,
    cfg.pkd.colL, cfg.pkd.colM, cfg.pkd.colR, cfg.pkd.colZ,
    cfg.value.colL, cfg.value.colM, cfg.value.colR, cfg.value.colZ,
    cfg.rho.colL, cfg.rho.colM, cfg.rho.colR, cfg.rho.colZ,
    cfg.psi.colL, cfg.psi.colM, cfg.psi.colR, cfg.psi.colZ,
    cfg.y.advices 5, cfg.y.advices 6, cfg.y.advices 7,
      cfg.y.advices 8, cfg.y.advices 9]

/-- Rust `NoteCommitConfig::configure` (`note_commit.rs:1456-1560`), VK-exact: `col_l/m/r/z
= advices[6..10]`, the eleven gates in registration order. -/
def configure (advices : Fin 10 → Column .advice) : Configure Fp Config := do
  let colL := advices 6
  let colM := advices 7
  let colR := advices 8
  let colZ := advices 9
  let b ← DecomposeB.configure colL colM colR
  let d ← DecomposeD.configure colL colM colR
  let e ← DecomposeE.configure colL colM colR
  let g ← DecomposeG.configure colL colM
  let h ← DecomposeH.configure colL colM colR
  let gd ← GdCanonicity.configure colL colM colR colZ
  let pkd ← PkdCanonicity.configure colL colM colR colZ
  let value ← ValueCanonicity.configure colL colM colR colZ
  let rho ← RhoCanonicity.configure colL colM colR colZ
  let psi ← PsiCanonicity.configure colL colM colR colZ
  let y ← YCanonicity.configure advices
  return { b, d, e, g, h, gd, pkd, value, rho, psi, y }

@[configure_selector_norm, keygen_norm] theorem configure_delta_lookups
    (advices : Fin 10 → Column .advice) (counts) :
    ((configure advices).delta counts).lookups = [] := by
  simp [configure, DecomposeB.configure, DecomposeD.configure,
    DecomposeE.configure, DecomposeG.configure, DecomposeH.configure,
    GdCanonicity.configure, PkdCanonicity.configure,
    ValueCanonicity.configure, RhoCanonicity.configure,
    PsiCanonicity.configure, YCanonicity.configure]

@[reducible] private def configureInferred (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configure advices) := by
  unfold configure
  infer_instance

private theorem configure_selectorRequirements
    (advices : Fin 10 → Column .advice) (counts) :
    (configureInferred advices).selectorRequirements counts := by
  dsimp only [configureInferred, configure]
  simp [configure_selector_norm, ConfigureDelta.LookupSelectorsCrossCompatible,
    DecomposeB.configure, DecomposeD.configure, DecomposeE.configure,
    DecomposeG.configure, DecomposeH.configure, GdCanonicity.configure,
    PkdCanonicity.configure, ValueCanonicity.configure,
    RhoCanonicity.configure, PsiCanonicity.configure,
    YCanonicity.configure]

instance (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configure advices) :=
  (configureInferred advices).closeSelectorRequirements
    (configure_selectorRequirements advices)

/-- Every local copy column produced by NoteCommit configure is one of advices 5–9. -/
theorem mem_adviceColumns_of_mem_configure_output_permutationColumns
    (advices : Fin 10 → Column .advice) (counts : ConfigureCounts)
    (column : AnyColumn)
    (hcolumn : column ∈ permutationColumns ((configure advices).output counts)) :
    column ∈ ([advices 5, advices 6, advices 7, advices 8, advices 9] :
      List AnyColumn) := by
  simp [permutationColumns, configure, DecomposeB.configure, DecomposeD.configure,
    DecomposeE.configure, DecomposeG.configure, DecomposeH.configure,
    GdCanonicity.configure, PkdCanonicity.configure, ValueCanonicity.configure,
    RhoCanonicity.configure, PsiCanonicity.configure, YCanonicity.configure] at hcolumn ⊢
  grind

@[keygen_norm]
theorem configure_delta_gates (advices : Fin 10 → Column .advice)
    (counts : ConfigureCounts) :
    ((configure advices).delta counts).gates =
      [DecomposeB.gate ((configure advices).output counts).b,
        DecomposeD.gate ((configure advices).output counts).d,
        DecomposeE.gate ((configure advices).output counts).e,
        DecomposeG.gate ((configure advices).output counts).g,
        DecomposeH.gate ((configure advices).output counts).h,
        GdCanonicity.gate ((configure advices).output counts).gd,
        PkdCanonicity.gate ((configure advices).output counts).pkd,
        ValueCanonicity.gate ((configure advices).output counts).value,
        RhoCanonicity.gate ((configure advices).output counts).rho,
        PsiCanonicity.gate ((configure advices).output counts).psi,
        YCanonicity.gate ((configure advices).output counts).y] := by
  unfold configure
  rfl

end Zcash.Circuits.NoteCommit
