import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Orchard.Utilities
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Sinsemilla gates

Clean approximations of Sinsemilla custom arithmetic gates.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `DoubleAndAdd::x_r`
- `DoubleAndAdd::Y_A`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip.rs`
- `Initial y_Q`
- `Sinsemilla gate`

These gadgets model the arithmetic constraints, not the Halo2 selector, fixed-column,
lookup, or row-layout machinery.
-/

namespace Orchard
namespace Sinsemilla

variable {F : Type} [Field F]

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

structure DoubleAndAddRow (F : Type) where
  xA : F
  xP : F
  lambda1 : F
  lambda2 : F
deriving ProvableStruct

namespace DoubleAndAdd

def xR {K : Type} [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  row.lambda1 * row.lambda1 - row.xA - row.xP

def yA {K : Type} [Add K] [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  (row.lambda1 + row.lambda2) * (row.xA - xR row)

end DoubleAndAdd

namespace InitialYQ

structure Row (F : Type) where
  yQ : F
  doubleAndAdd : DoubleAndAddRow F
deriving ProvableStruct

def poly {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * row.yQ - DoubleAndAdd.yA row.doubleAndAdd

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  DoubleAndAdd.yA row.doubleAndAdd = 2 * row.yQ

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (2 * row.yQ - DoubleAndAdd.yA row.doubleAndAdd)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, poly, DoubleAndAdd.yA, DoubleAndAdd.xR]
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)).symm
  completeness := by
    circuit_proof_start [main, Spec, poly, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end InitialYQ

/-!
`hash_to_point` initial-`Q` wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
- `public_q_initialization`
- `private_q_initialization`

Both source paths assign/copy `x_Q` into the initial accumulator `x_A`, provide `y_Q`
to the `Initial y_Q` gate, and rely on that gate to constrain the first doubled
accumulator. This assertion records the copy/equality wiring around `InitialYQ.circuit`;
whether `y_Q` came from a fixed column or the previous advice row is a Halo2 layout
detail outside this approximation.
-/
namespace InitWiring

structure Row (F : Type) where
  qX : F
  qY : F
  init : InitialYQ.Row F
deriving ProvableStruct

def xCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.init.doubleAndAdd.xA - row.qX

def yCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.init.yQ - row.qY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  InitialYQ.Spec row.init ∧
    row.init.doubleAndAdd.xA = row.qX ∧
    row.init.yQ = row.qY

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  InitialYQ.circuit row.init
  assertZero (xCheck row)
  assertZero (yCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, InitialYQ.circuit,
      InitialYQ.Spec, DoubleAndAdd.yA, DoubleAndAdd.xR]
    rcases h_holds with ⟨hInit, hX, hY⟩
    exact ⟨hInit, left_eq_of_add_neg_eq_zero hX, left_eq_of_add_neg_eq_zero hY⟩
  completeness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, InitialYQ.circuit,
      InitialYQ.Spec, DoubleAndAdd.yA, DoubleAndAdd.xR]
    rcases h_spec with ⟨hInit, hX, hY⟩
    rw [← hX, ← hY]
    constructor
    · exact hInit
    constructor <;> ring

end InitWiring

namespace Gate

structure Row (F : Type) where
  qS2 : F
  cur : DoubleAndAddRow F
  next : DoubleAndAddRow F
deriving ProvableStruct

def qS3 {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  row.qS2 * (row.qS2 - 1)

def secantLine {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  row.cur.lambda2 * row.cur.lambda2 -
    (row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA)

def yLhs {K : Type} [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  4 * row.cur.lambda2 * (row.cur.xA - row.next.xA)

def yRhs {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * DoubleAndAdd.yA row.cur +
    (2 - qS3 row) * DoubleAndAdd.yA row.next +
    qS3 row * 2 * row.next.lambda1

def yCheck {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 4]
    (row : Row K) : K :=
  yLhs row - yRhs row

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.cur.lambda2 * row.cur.lambda2 =
    row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA ∧
  yLhs row = yRhs row

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (secantLine row)
  assertZero (yCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, secantLine, yCheck, yLhs, yRhs, qS3,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    constructor
    · have hSec :
          input_cur_lambda2 * input_cur_lambda2 -
              (input_next_xA +
                (input_cur_lambda1 * input_cur_lambda1 - input_cur_xA - input_cur_xP) +
                input_cur_xA) = 0 := by
        simp_all [sub_eq_add_neg]
      exact sub_eq_zero.mp hSec
    · have hY :
          4 * input_cur_lambda2 * (input_cur_xA - input_next_xA) -
              (2 *
                  ((input_cur_lambda1 + input_cur_lambda2) *
                    (input_cur_xA -
                      (input_cur_lambda1 * input_cur_lambda1 - input_cur_xA - input_cur_xP))) +
                (2 - input_qS2 * (input_qS2 - 1)) *
                  ((input_next_lambda1 + input_next_lambda2) *
                    (input_next_xA -
                      (input_next_lambda1 * input_next_lambda1 - input_next_xA - input_next_xP))) +
                input_qS2 * (input_qS2 - 1) * 2 * input_next_lambda1) = 0 := by
        simp_all [sub_eq_add_neg]
      exact sub_eq_zero.mp hY
  completeness := by
    circuit_proof_start [main, Spec, secantLine, yCheck, yLhs, yRhs, qS3,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
    constructor <;> ring

end Gate

/-!
Sinsemilla commitment output wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`
- `CommitDomain::commit`
- `CommitDomain::short_commit`

The source computes a hash point `M`, a fixed-base blinding factor `[r] R`, and then
returns `M + [r] R`. `short_commit` extracts the x-coordinate from that commitment. The
hash point and blinding factor are explicit row values here; their internal arithmetic is
represented by the lower-level Sinsemilla and fixed-base scalar-multiplication assertions.
-/
namespace Commit

structure Row (F : Type) where
  hashX : F
  hashY : F
  blindX : F
  blindY : F
  commitmentX : F
  commitmentY : F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

def addRow {K : Type} (row : Row K) : Ecc.CompleteAddRow K where
  p := { x := row.hashX, y := row.hashY }
  q := { x := row.blindX, y := row.blindY }
  r := { x := row.commitmentX, y := row.commitmentY }
  lambda := row.lambda
  alpha := row.alpha
  beta := row.beta
  gamma := row.gamma
  delta := row.delta

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.CompleteAdd.Spec (addRow row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Ecc.CompleteAdd.circuit (addRow row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit,
      Ecc.CompleteAdd.Spec, Ecc.CompleteAdd.slopeLine, Ecc.CompleteAdd.tangentLine,
      Ecc.CompleteAdd.nonexceptionalResult, Ecc.CompleteAdd.leftIdentityResult,
      Ecc.CompleteAdd.rightIdentityResult, Ecc.CompleteAdd.inverseResult,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    exact h_holds
  completeness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit,
      Ecc.CompleteAdd.Spec, Ecc.CompleteAdd.slopeLine, Ecc.CompleteAdd.tangentLine,
      Ecc.CompleteAdd.nonexceptionalResult, Ecc.CompleteAdd.leftIdentityResult,
      Ecc.CompleteAdd.rightIdentityResult, Ecc.CompleteAdd.inverseResult,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    exact h_spec

namespace Entry

structure Row (F : Type) where
  hashX : F
  hashY : F
  blindX : F
  blindY : F
  commitmentX : F
  commitmentY : F
deriving ProvableStruct

def addInput {K : Type} (row : Row K) : Ecc.AddInputs K where
  p := { x := row.hashX, y := row.hashY }
  q := { x := row.blindX, y := row.blindY }

def output {K : Type} (row : Row K) : Ecc.Point K where
  x := row.commitmentX
  y := row.commitmentY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.pointCoords (output row) =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Ecc.PallasBaseField)
      (Ecc.pointCoords (addInput row).p)
      (Ecc.pointCoords (addInput row).q)

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.CompleteAdd.Entry.Assumptions (addInput row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  let commitment ← Ecc.CompleteAdd.Entry.circuit (addInput row)
  assertZero (commitment.x - row.commitmentX)
  assertZero (commitment.y - row.commitmentY)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec]
    rcases h_holds with ⟨hAdd, hX, hY⟩
    have hx : env.get i₀ = input_commitmentX := by linear_combination hX
    have hy : env.get (i₀ + 1) = input_commitmentY := by linear_combination hY
    have hAdd' := hAdd h_assumptions
    rw [← hAdd']
    simp [Ecc.pointCoords, hx, hy]
  completeness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec,
      Ecc.CompleteAdd.Entry.Assumptions]
    constructor
    · exact h_assumptions
    · have hAdd := h_env h_assumptions
      have hPoint : Ecc.pointCoords { x := env.get i₀, y := env.get (i₀ + 1) } =
          Ecc.pointCoords { x := input_commitmentX, y := input_commitmentY } :=
        hAdd.trans h_spec.symm
      constructor
      · have hx := congrArg Prod.fst hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hx
      · have hy := congrArg Prod.snd hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hy

end Entry

end Commit

namespace ShortCommit

structure Row (F : Type) where
  commit : Commit.Row F
  extracted : F
deriving ProvableStruct

def extractCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.commit.commitmentX - row.extracted

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Commit.Spec row.commit ∧ row.extracted = row.commit.commitmentX

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Commit.circuit row.commit
  assertZero (extractCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, extractCheck, Commit.circuit, Commit.Spec,
      Commit.addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec,
      Ecc.CompleteAdd.slopeLine, Ecc.CompleteAdd.tangentLine,
      Ecc.CompleteAdd.nonexceptionalResult, Ecc.CompleteAdd.leftIdentityResult,
      Ecc.CompleteAdd.rightIdentityResult, Ecc.CompleteAdd.inverseResult,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    rcases h_holds with ⟨hCommit, hExtract⟩
    exact ⟨hCommit, (left_eq_of_add_neg_eq_zero hExtract).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, extractCheck, Commit.circuit, Commit.Spec,
      Commit.addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec,
      Ecc.CompleteAdd.slopeLine, Ecc.CompleteAdd.tangentLine,
      Ecc.CompleteAdd.nonexceptionalResult, Ecc.CompleteAdd.leftIdentityResult,
      Ecc.CompleteAdd.rightIdentityResult, Ecc.CompleteAdd.inverseResult,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    rcases h_spec with ⟨hCommit, hExtract⟩
    constructor
    · exact hCommit
    · rw [hExtract]
      ring

namespace Entry

structure Row (F : Type) where
  commit : Commit.Entry.Row F
  extracted : F
deriving ProvableStruct

def extractCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.commit.commitmentX - row.extracted

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Commit.Entry.Spec row.commit ∧ row.extracted = row.commit.commitmentX

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Commit.Entry.Assumptions row.commit

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Commit.Entry.circuit row.commit
  assertZero (extractCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, extractCheck, Assumptions,
      Commit.Entry.circuit, Commit.Entry.Spec]
    rcases h_holds with ⟨hCommit, hExtract⟩
    exact ⟨hCommit h_assumptions,
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hExtract)).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, extractCheck, Assumptions,
      Commit.Entry.circuit, Commit.Entry.Spec, Commit.Entry.Assumptions]
    rcases h_spec with ⟨hCommit, hExtract⟩
    exact ⟨⟨h_assumptions, hCommit⟩,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hExtract.symm⟩

end Entry

end ShortCommit

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `Decomposition check`
- `MerkleInstructions::hash_layer`

This ports the MerkleCRH decomposition gate that connects the three Sinsemilla message
pieces `a`, `b`, `c` to `(l, left, right)`.
-/

namespace Merkle

structure DecompositionRow (F : Type) where
  aWhole : F
  bWhole : F
  cWhole : F
  leftNode : F
  rightNode : F
  z1A : F
  z1B : F
  b1 : F
  b2 : F
  lWhole : F
deriving ProvableStruct

def twoPow5 {K : Type} [OfNat K (2 ^ 5)] : K := OfNat.ofNat (2 ^ 5)

def twoPow10 {K : Type} [OfNat K (2 ^ 10)] : K := OfNat.ofNat (2 ^ 10)

def twoPow240 {K : Type} [OfNat K (2 ^ 240)] : K := OfNat.ofNat (2 ^ 240)

def a0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : DecompositionRow K) : K :=
  row.aWhole - row.z1A * twoPow10

def b1B2Check {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : DecompositionRow K) : K :=
  row.z1B - (row.b1 + row.b2 * twoPow5)

def b0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : DecompositionRow K) : K :=
  row.bWhole - row.z1B * twoPow10

def leftCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 10)]
    [OfNat K (2 ^ 240)] (row : DecompositionRow K) : K :=
  let reconstructed := row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240
  reconstructed - row.leftNode

def rightCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : DecompositionRow K) : K :=
  row.b2 + row.cWhole * twoPow5 - row.rightNode

def Spec (row : DecompositionRow Ecc.PallasBaseField) : Prop :=
  row.lWhole = a0 row ∧
  row.leftNode = row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240 ∧
  row.rightNode = row.b2 + row.cWhole * twoPow5 ∧
  row.z1B = row.b1 + row.b2 * twoPow5

def main (row : Var DecompositionRow Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (a0 row - row.lWhole)
  assertZero (leftCheck row)
  assertZero (rightCheck row)
  assertZero (b1B2Check row)

def circuit : FormalAssertion Ecc.PallasBaseField DecompositionRow where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_holds with ⟨hl, hleft, hright, hb⟩
    constructor
    · rw [sub_eq_add_neg]
      exact (left_eq_of_add_neg_eq_zero hl).symm
    constructor
    · rw [sub_eq_add_neg]
      exact (left_eq_of_add_neg_eq_zero hleft).symm
    constructor
    · exact (left_eq_of_add_neg_eq_zero hright).symm
    · exact left_eq_of_add_neg_eq_zero hb
  completeness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_spec with ⟨hl, hleft, hright, hb⟩
    constructor
    · rw [hl]
      ring
    constructor
    · rw [hleft]
      ring
    constructor
    · rw [hright]
      ring
    · rw [hb]
      ring

/-!
`hash_layer` source-level wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `MerkleInstructions::hash_layer`

The Rust gadget builds message pieces `a`, `b`, and `c`, calls
`SinsemillaChip::hash_to_point`, extracts the x-coordinate, and assigns the
decomposition row above from the message pieces, running-sum endpoints, and short
subpieces. The variable-length `hash_to_point` loop is represented by an explicit
`computedHash` row value.
-/
namespace Wiring

structure Row (F : Type) where
  decomposition : DecompositionRow F
  computedHash : F
  hash : F
deriving ProvableStruct

def hashCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.computedHash - row.hash

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Merkle.Spec row.decomposition ∧ row.hash = row.computedHash

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Merkle.circuit row.decomposition
  assertZero (hashCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, hashCheck, Merkle.circuit, Merkle.Spec, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    rcases h_holds with ⟨hMerkle, hHash⟩
    exact ⟨hMerkle, (left_eq_of_add_neg_eq_zero hHash).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, hashCheck, Merkle.circuit, Merkle.Spec, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    rcases h_spec with ⟨hMerkle, hHash⟩
    rw [hHash]
    exact ⟨hMerkle, by ring⟩

end Wiring

/-!
Merkle-path per-layer wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle.rs`
- `MerklePath::calculate_root`

For each layer, the source conditionally swaps `(node, sibling)` according to the
little-endian position bit, then hashes `(left, right)` with `hash_layer`. This assertion
models one such layer. Repeating it outside this assertion models the full path.
-/
namespace PathStep

structure Row (F : Type) where
  node : F
  sibling : F
  posBit : F
  left : F
  right : F
  layer : Wiring.Row F
  nextNode : F
deriving ProvableStruct

def boolPoly {K : Type} [One K] [Sub K] [Mul K] (x : K) : K :=
  x * (x - 1)

def swapInput {K : Type} (row : Row K) : Utilities.CondSwapInputs K where
  a := row.node
  b := row.sibling
  swap := row.posBit

def layerLeftCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.layer.decomposition.leftNode - row.left

def layerRightCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.layer.decomposition.rightNode - row.right

def nextCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.layer.hash - row.nextNode

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  (row.posBit = 0 ∨ row.posBit = 1) ∧
    row.left = (if row.posBit = 1 then row.sibling else row.node) ∧
    row.right = (if row.posBit = 1 then row.node else row.sibling) ∧
    Wiring.Spec row.layer ∧
    row.layer.decomposition.leftNode = row.left ∧
    row.layer.decomposition.rightNode = row.right ∧
    row.nextNode = row.layer.hash

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (boolPoly row.posBit)
  let swapped ← Utilities.CondSwap.circuit (swapInput row)
  assertZero (row.left - swapped.aSwapped)
  assertZero (row.right - swapped.bSwapped)
  Wiring.circuit row.layer
  assertZero (layerLeftCheck row)
  assertZero (layerRightCheck row)
  assertZero (nextCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, swapInput, layerLeftCheck,
      layerRightCheck, nextCheck, boolPoly,
      Utilities.CondSwap.circuit, Utilities.CondSwap.Spec,
      Wiring.circuit, Wiring.Spec, Wiring.hashCheck, Merkle.circuit, Merkle.Spec, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    rcases h_holds with ⟨hBoolPoly, hSwap, hLeft, hRight, hLayer,
      hLayerLeft, hLayerRight, hNext⟩
    have hBool : input_posBit = 0 ∨ input_posBit = 1 := by
      rcases mul_eq_zero.mp hBoolPoly with hZero | hOne
      · exact Or.inl hZero
      · exact Or.inr (left_eq_of_add_neg_eq_zero hOne)
    have hSwapRel := hSwap hBool
    constructor
    · exact hBool
    constructor
    · have hLeftOut := left_eq_of_add_neg_eq_zero hLeft
      rcases hBool with hZero | hOne
      · simp [hZero, hLeftOut] at hSwapRel ⊢
        exact hSwapRel.1
      · simp [hOne, hLeftOut] at hSwapRel ⊢
        exact hSwapRel.1
    constructor
    · have hRightOut := left_eq_of_add_neg_eq_zero hRight
      rcases hBool with hZero | hOne
      · simp [hZero, hRightOut] at hSwapRel ⊢
        exact hSwapRel.2
      · simp [hOne, hRightOut] at hSwapRel ⊢
        exact hSwapRel.2
    exact ⟨hLayer, left_eq_of_add_neg_eq_zero hLayerLeft,
      left_eq_of_add_neg_eq_zero hLayerRight, (left_eq_of_add_neg_eq_zero hNext).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, swapInput, layerLeftCheck,
      layerRightCheck, nextCheck, boolPoly,
      Utilities.CondSwap.circuit, Utilities.CondSwap.Spec,
      Wiring.circuit, Wiring.Spec, Wiring.hashCheck, Merkle.circuit, Merkle.Spec, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    rcases h_spec with ⟨hBool, hLeft, hRight, hLayer, hLayerLeft, hLayerRight, hNext⟩
    constructor
    · rcases hBool with hZero | hOne
      · rw [hZero]
        ring
      · rw [hOne]
        ring
    constructor
    · exact hBool
    constructor
    · have hSwap := h_env hBool
      have hLeftOut : env.get i₀ = input_left := by
        rcases hBool with hZero | hOne
        · simp [hZero] at hSwap hLeft ⊢
          exact hSwap.1.trans hLeft.symm
        · simp [hOne] at hSwap hLeft ⊢
          exact hSwap.1.trans hLeft.symm
      rw [hLeftOut]
      ring
    constructor
    · have hSwap := h_env hBool
      have hRightOut : env.get (i₀ + 1) = input_right := by
        rcases hBool with hZero | hOne
        · simp [hZero] at hSwap hRight ⊢
          exact hSwap.2.trans hRight.symm
        · simp [hOne] at hSwap hRight ⊢
          exact hSwap.2.trans hRight.symm
      rw [hRightOut]
      ring
    constructor
    · exact hLayer
    constructor
    · rw [hLayerLeft, hLeft]
      ring
    constructor
    · rw [hLayerRight, hRight]
      ring
    · rw [hNext]
      ring

end PathStep

end Merkle

end Sinsemilla
end Orchard
