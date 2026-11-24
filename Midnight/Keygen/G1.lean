import Midnight.Keygen.BasePrime
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Curves.Pasta.Fast.Msm
import CompPoly.Data.Bytes.LittleEndian

/-! BLS12-381 G1, `y² = x³ + 4` over the base field, as a CompElliptic short-Weierstrass curve,
with BLST's two point encodings. CompElliptic has no BLS12-381 curve, only the generic form. -/
namespace Midnight.Keygen.G1
open CompElliptic.CurveForms.ShortWeierstrass

abbrev Fp := ZMod basePrime

def curve : SWCurve Fp where
  A := 0
  B := 4
  IsElliptic := by rw [isUnit_iff_ne_zero]; decide
  B_nonzero := by decide

abbrev Point := SWPoint curve

/-- The point `(x, y)` if it is on the curve. -/
def ofFp? (x y : Fp) : Option Point :=
  if h : OnCurve curve.A curve.B (x, y) then some ⟨x, y, Or.inl h⟩ else none

/-- The point with canonical coordinates `(x, y)`, if it is on the curve. -/
def ofCoords? (x y : Nat) : Option Point :=
  if x < basePrime ∧ y < basePrime then ofFp? x y else none

/-- Big-endian, `width` bytes. -/
def bytesBE (width n : Nat) : List UInt8 := (CompPoly.Bytes.toListLE width n).reverse

/-- BLST's uncompressed encoding (`RawBytes`): x then y; the identity sets bit 6. -/
def encodeRaw (p : Point) : ByteArray :=
  if p = 0 then ⟨#[0x40] ++ Array.replicate 95 0⟩
  else ⟨(bytesBE 48 p.x.val ++ bytesBE 48 p.y.val).toArray⟩

/-- BLST's compressed encoding (`Processed`): x with compression, infinity and sign in bits 7/6/5. -/
def encodeCompressed (p : Point) : ByteArray :=
  if p = 0 then ⟨#[0xc0] ++ Array.replicate 47 0⟩
  else match bytesBE 48 p.x.val with
    | b :: rest => ⟨((b ||| if p.y.val > basePrime / 2 then 0xa0 else 0x80) :: rest).toArray⟩
    | [] => .empty

/-- Pippenger window for `n` terms. -/
def window (n : Nat) : Nat :=
  if n < 32 then 3 else if n < 256 then 5 else if n < 1024 then 7 else 10

end Midnight.Keygen.G1
