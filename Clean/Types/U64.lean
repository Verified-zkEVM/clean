import Clean.Gadgets.ByteLookup
import Clean.Circuit.Extensions
import Clean.Utils.Bitwise
import Clean.Circuit.Provable
import Clean.Utils.Primes
import Clean.Circuit.SubCircuit

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  A 64-bit unsigned integer is represented using eight limbs of 8 bits each.
-/
structure U64 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T
  x4 : T
  x5 : T
  x6 : T
  x7 : T

instance : LawfulProvableType U64 where
  size := 8
  to_elements x := #v[x.x0, x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7]
  from_elements v :=
    let ⟨.mk [v0, v1, v2, v3, v4, v5, v6, v7], _⟩ := v
    ⟨ v0, v1, v2, v3, v4, v5, v6, v7 ⟩

instance : NonEmptyProvableType U64 where
  nonempty := by simp only [size, Nat.reduceGT]

instance (T: Type) [Repr T] : Repr (U64 T) where
  reprPrec x _ := "⟨" ++ repr x.x0 ++ ", " ++ repr x.x1 ++ ", " ++ repr x.x2 ++ ", " ++ repr x.x3 ++ ", " ++ repr x.x4 ++ ", " ++ repr x.x5 ++ ", " ++ repr x.x6 ++ ", " ++ repr x.x7 ++ "⟩"

namespace U64

omit [Fact (Nat.Prime p)] p_large_enough in
/--
  Extensionality principle for U64
-/
@[ext]
lemma ext {x y : U64 (F p)}
    (h0 : x.x0 = y.x0)
    (h1 : x.x1 = y.x1)
    (h2 : x.x2 = y.x2)
    (h3 : x.x3 = y.x3)
    (h4 : x.x4 = y.x4)
    (h5 : x.x5 = y.x5)
    (h6 : x.x6 = y.x6)
    (h7 : x.x7 = y.x7)
    : x = y :=
  by match x, y with
  | ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩, ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩ =>
    simp only [h0, h1, h2, h3, h4, h5, h6, h7] at *
    simp only [h0, h1, h2, h3, h4, h5, h6, h7]


/--
  A 64-bit unsigned integer is normalized if all its limbs are less than 256.
-/
def is_normalized (x: U64 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256 ∧
  x.x4.val < 256 ∧ x.x5.val < 256 ∧ x.x6.val < 256 ∧ x.x7.val < 256

/--
  Return the value of a 64-bit unsigned integer over the natural numbers.
-/
def value (x: U64 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3 +
  x.x4.val * 256^4 + x.x5.val * 256^5 + x.x6.val * 256^6 + x.x7.val * 256^7

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_lt_of_normalized {x : U64 (F p)} (hx: x.is_normalized) : x.value < 2^64 := by
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  simp_all only [value, is_normalized]
  linarith

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_horner (x : U64 (F p)) : x.value =
    x.x0.val + 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * (x.x3.val +
      2^8 * (x.x4.val + 2^8 * (x.x5.val + 2^8 * (x.x6.val + 2^8 * x.x7.val)))))) := by
  simp only [value]
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_xor_horner {x : U64 (F p)} (hx: x.is_normalized) : x.value =
    x.x0.val ^^^ 2^8 * (x.x1.val ^^^ 2^8 * (x.x2.val ^^^ 2^8 * (x.x3.val ^^^
      2^8 * (x.x4.val ^^^ 2^8 * (x.x5.val ^^^ 2^8 * (x.x6.val ^^^ 2^8 * x.x7.val)))))) := by
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  simp_all only [is_normalized, value_horner]
  let ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := hx
  repeat rw [Bitwise.xor_eq_add 8]
  repeat assumption

def value_nat (x: U64 ℕ) :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3 +
  x.x4 * 256^4 + x.x5 * 256^5 + x.x6 * 256^6 + x.x7 * 256^7

/--
  Return a 64-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat (x: ℕ) : U64 (F p) :=
  let x0 := FieldUtils.mod x 256 (by linarith [p_large_enough.elim])
  let x1 := FieldUtils.mod (FieldUtils.floordiv x 256) 256 (by linarith [p_large_enough.elim])
  let x2 := FieldUtils.mod (FieldUtils.floordiv x 256^2) 256 (by linarith [p_large_enough.elim])
  let x3 := FieldUtils.mod (FieldUtils.floordiv x 256^3) 256 (by linarith [p_large_enough.elim])
  let x4 := FieldUtils.mod (FieldUtils.floordiv x 256^4) 256 (by linarith [p_large_enough.elim])
  let x5 := FieldUtils.mod (FieldUtils.floordiv x 256^5) 256 (by linarith [p_large_enough.elim])
  let x6 := FieldUtils.mod (FieldUtils.floordiv x 256^6) 256 (by linarith [p_large_enough.elim])
  let x7 := FieldUtils.mod (FieldUtils.floordiv x 256^7) 256 (by linarith [p_large_enough.elim])
  ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩

/--
  Return a 64-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat_nat (x: ℕ) : U64 ℕ :=
  let x0 := x % 256
  let x1 := (x / 256) % 256
  let x2 := (x / 256^2) % 256
  let x3 := (x / 256^3) % 256
  let x4 := (x / 256^4) % 256
  let x5 := (x / 256^5) % 256
  let x6 := (x / 256^6) % 256
  let x7 := (x / 256^7) % 256
  ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩

/--
  Return a 64-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat_expr (x: ℕ) : U64 (Expression (F p)) :=
  let (⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ : U64 (F p)) := decompose_nat x
  ⟨ x0, x1, x2, x3 , x4, x5, x6, x7 ⟩

omit [Fact (Nat.Prime p)] p_large_enough in
lemma normalized_u64 (x : U64 (F p)) : x.is_normalized → x.value < 2^64 := by
  simp [is_normalized, value]
  intros
  linarith

def value_u64 (x : U64 (F p)) (h : x.is_normalized) : UInt64 :=
  UInt64.ofNatCore x.value (normalized_u64 x h)


end U64

namespace U64.AssertNormalized

/--
  Assert that a 64-bit unsigned integer is normalized.
  This means that all its limbs are less than 256.
-/
def u64_assert_normalized (inputs : Var U64 (F p)) : Circuit (F p) Unit  := do
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := inputs
  lookup (Gadgets.ByteLookup x0)
  lookup (Gadgets.ByteLookup x1)
  lookup (Gadgets.ByteLookup x2)
  lookup (Gadgets.ByteLookup x3)
  lookup (Gadgets.ByteLookup x4)
  lookup (Gadgets.ByteLookup x5)
  lookup (Gadgets.ByteLookup x6)
  lookup (Gadgets.ByteLookup x7)

def assumptions (_input : U64 (F p)) := True

def spec (inputs : U64 (F p)) := inputs.is_normalized

def circuit : FormalAssertion (F p) U64 where
  main := u64_assert_normalized
  assumptions := assumptions
  spec := spec
  soundness := by
    rintro i0 env x_var
    rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [spec, circuit_norm, u64_assert_normalized, Gadgets.ByteLookup, is_normalized]
    repeat rw [Gadgets.ByteTable.equiv]
    simp_all [circuit_norm, eval]

  completeness := by
    rintro i0 env x_var
    rintro _ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [spec, circuit_norm, u64_assert_normalized, Gadgets.ByteLookup, is_normalized]
    repeat rw [Gadgets.ByteTable.equiv]
    simp_all [circuit_norm, eval]

end U64.AssertNormalized


/--
  Witness a 64-bit unsigned integer.
-/
def U64.witness (compute : Environment (F p) → U64 (F p)) := do
  let x ← ProvableType.witness compute
  assertion U64.AssertNormalized.circuit x
  return x

end
