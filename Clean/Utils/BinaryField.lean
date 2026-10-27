module

public import Clean.Utils.FiniteField
public import CompPoly.Fields.Binary.BF64

@[expose] public section

/-!
# Binary fields

`BF64` is CompPoly's `GF(2^64)`, stored in a polynomial basis over `GF(2)`. Its `FiniteField`
embedding reads the 64 polynomial coefficients as the bits of a natural number.
-/

instance : FiniteField BF64 where
  val x := x.toBitVec.toNat
  fromNat n := BF64.ofBitVec (BitVec.ofNat 64 n)
  size := 2 ^ 64
  val_lt x := x.toBitVec.isLt
  val_injective _ _ h := BF64.ext (BitVec.eq_of_toNat_eq h)
  val_fromNat n hn := by simp [Nat.mod_eq_of_lt hn]
  val_zero := rfl
  val_one := rfl
