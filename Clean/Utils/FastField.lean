/-
CompPoly's 32-bit Montgomery fields `FastField p` as Clean finite fields, with their word
conversions.
-/
module

public import Clean.Utils.FiniteField
public import CompPoly.Fields.Montgomery.Native32Bytes

@[expose] public section

namespace Montgomery.Native32.FastField

variable {p : ℕ} [P : Mont32Field p]

theorem toField_val (x : FastField p) : (toField x).val = toNat x :=
  ZMod.val_natCast_of_lt toNat_lt_modulus

instance instFiniteField : FiniteField (FastField p) :=
  { instField with
    val := toNat
    fromNat := ofNat p
    size := p
    val_lt := fun _ => toNat_lt_modulus
    val_injective := fun x y h => toField_injective (by simp only [toField, h])
    val_fromNat := fun n hn => by
      simp only [ofNat, toNat_ofCanonicalNat, Nat.mod_eq_of_lt hn]
    val_zero := by rw [← toField_val, toField_zero, ZMod.val_zero]
    val_one := by rw [← toField_val, toField_one, ZMod.val_one] }

theorem toUInt64_eq_ofNat (x : UInt32) : x.toUInt64 = UInt64.ofNat x.toNat :=
  UInt64.toNat_inj.mp (by
    rw [UInt32.toNat_toUInt64, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by have := x.toNat_lt; omega)])

theorem ofUInt32_eq_ofCanonicalNat (x : UInt32) (h : x.toNat < p) :
    ofUInt32 p x = ofCanonicalNat x.toNat h := by
  apply Subtype.ext
  simp only [ofUInt32, ofCanonicalNat, reduce]
  congr 1
  rw [toUInt64_eq_ofNat]

/-- The element of a word below `2 ^ 32`, by one Montgomery multiplication. -/
@[inline] def ofSmallWord (n : UInt64) : FastField p := ofUInt32 p n.toUInt32

/-- The element of a word, reduced modulo `p` first. -/
@[inline] def ofWord (n : UInt64) : FastField p := ofSmallWord (n % P.modulus64)

theorem ofSmallWord_eq (n : UInt64) (h : n.toNat < p) :
    (ofSmallWord n : FastField p) = ofNat p n.toNat := by
  have hn : n.toUInt32.toNat = n.toNat := by
    rw [UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt (by have := P.modulus_lt_two_pow_32; omega)
  rw [ofSmallWord, ofUInt32_eq_ofCanonicalNat _ (hn ▸ h), ofNat]
  simp only [hn, Nat.mod_eq_of_lt h]

instance instWordField : WordField (FastField p) where
  toWord x := x.toUInt32.toUInt64
  ofWord := ofWord
  ofSmallWord := ofSmallWord
  toWord_eq x := by
    show x.toUInt32.toUInt64 = UInt64.ofNat (toNat x)
    rw [toNat, toUInt64_eq_ofNat]
  ofWord_eq n := by
    have hlt : (n % P.modulus64).toNat < p := by
      rw [UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.modulus_pos
    show ofSmallWord (n % P.modulus64) = ofNat p n.toNat
    rw [ofSmallWord_eq _ hlt, ofNat, ofNat]
    congr 1
    rw [UInt64.toNat_mod, P.modulus64_toNat, Nat.mod_mod]
  ofSmallWord_eq n h := ofSmallWord_eq n h

end Montgomery.Native32.FastField

namespace Montgomery.Native32.FastField

/-- `ZMod p` in Montgomery form. -/
def ofZMod (p : ℕ) [Mont32Field p] : ZMod p →+* FastField p := (ringEquiv p).symm.toRingHom

end Montgomery.Native32.FastField
