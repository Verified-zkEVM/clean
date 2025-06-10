import Clean.Gadgets.ByteLookup
import Clean.Utils.Bitwise
import Clean.Circuit.Provable
import Clean.Utils.Primes
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Equality

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

instance : ProvableType U64 where
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
def map {α β : Type} (x : U64 α) (f : α → β) : U64 β :=
  ⟨ f x.x0, f x.x1, f x.x2, f x.x3, f x.x4, f x.x5, f x.x6, f x.x7 ⟩

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
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  let x4 : ℕ := (x / 256^4) % 256
  let x5 : ℕ := (x / 256^5) % 256
  let x6 : ℕ := (x / 256^6) % 256
  let x7 : ℕ := (x / 256^7) % 256
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

def from_u64 (x : UInt64) : U64 (F p) :=
  decompose_nat x.toFin

def value_u64 (x : U64 (F p)) (h : x.is_normalized) : UInt64 :=
  UInt64.ofNatLT x.value (normalized_u64 x h)

lemma from_u64_normalized (x : UInt64) : (from_u64 (p:=p) x).is_normalized := by
  simp only [is_normalized, from_u64, decompose_nat]
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [FieldUtils.val_lt_p]
    assumption
    linarith [p_large_enough.elim]
  simp [h]

theorem value_from_u64_eq (x : UInt64) : value (from_u64 (p:=p) x) = x.toNat := by
  simp only [value_u64, value_horner, from_u64, decompose_nat, UInt64.toFin_val]
  set x := x.toNat
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) = x % 256 := by
    rw [ZMod.val_cast_of_lt]
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    linarith [p_large_enough.elim]
  simp only [h]
  have : 2^8 = 256 := rfl
  simp only [this]
  have : x < 256^8 := by simp [x, UInt64.toNat_lt_size]
  have : x / 256^7 % 256 = x / 256^7 := by rw [Nat.mod_eq_of_lt]; omega
  rw [this]
  have div_succ_pow (n : ℕ) : x / 256^(n + 1) = (x / 256^n) / 256 := by rw [Nat.div_div_eq_div_mul]; rfl
  have mod_add_div (n : ℕ) : x / 256^n % 256 + 256 * (x / 256^(n + 1)) = x / 256^n := by
    rw [div_succ_pow n, Nat.mod_add_div]
  simp only [mod_add_div]
  rw [div_succ_pow 1, Nat.pow_one, Nat.mod_add_div, Nat.mod_add_div]
end U64

namespace U64.AssertNormalized
open Gadgets (ByteLookup ByteTable)

/--
  Assert that a 64-bit unsigned integer is normalized.
  This means that all its limbs are less than 256.
-/
def u64_assert_normalized (inputs : Var U64 (F p)) : Circuit (F p) Unit  := do
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := inputs
  lookup (ByteLookup x0)
  lookup (ByteLookup x1)
  lookup (ByteLookup x2)
  lookup (ByteLookup x3)
  lookup (ByteLookup x4)
  lookup (ByteLookup x5)
  lookup (ByteLookup x6)
  lookup (ByteLookup x7)

def assumptions (_input : U64 (F p)) := True

def spec (inputs : U64 (F p)) := inputs.is_normalized

def circuit : FormalAssertion (F p) U64 where
  main := u64_assert_normalized
  assumptions := assumptions
  spec := spec
  soundness := by
    rintro i0 env x_var
    rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [spec, circuit_norm, u64_assert_normalized, ByteLookup, is_normalized]
    repeat rw [ByteTable.equiv]
    simp_all [circuit_norm, eval]

  completeness := by
    rintro i0 env x_var
    rintro _ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [spec, circuit_norm, u64_assert_normalized, ByteLookup, is_normalized]
    repeat rw [ByteTable.equiv]
    simp_all [circuit_norm, eval]

end U64.AssertNormalized


/--
  Witness a 64-bit unsigned integer.
-/
def U64.witness (compute : Environment (F p) → U64 (F p)) := do
  let x ← ProvableType.witness compute
  assertion U64.AssertNormalized.circuit x
  return x


namespace U64.Copy

def u64_copy (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let y ← ProvableType.witness fun env =>
    U64.mk (env x.x0) (env x.x1) (env x.x2) (env x.x3) (env x.x4) (env x.x5) (env x.x6) (env x.x7)
  assert_equals x y
  return y

def assumptions (_input : U64 (F p)) := True

def spec (x y : U64 (F p)) := x = y

def circuit : FormalCircuit (F p) U64 U64 where
  main := u64_copy
  assumptions := assumptions
  spec := spec
  local_length := 8
  output inputs i0 := var_from_offset U64 i0
  soundness := by
    rintro i0 env x_var
    rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [circuit_norm, u64_copy, spec, h_eval, eval, var_from_offset]
    injections h_eval
    intros h0 h1 h2 h3 h4 h5 h6 h7
    aesop

  completeness := by
    rintro i0 env x_var
    rintro h ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp [circuit_norm, u64_copy, spec, h_eval]
    simp [circuit_norm, u64_copy, Gadgets.Equality.elaborated] at h
    simp [subcircuit_norm, eval] at h
    simp_all [eval, Expression.eval, circuit_norm, h, var_from_offset, Vector.mapRange]
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp only [Fin.isValue, Fin.val_zero, add_zero, List.getElem_cons_zero] at h0
    simp only [Fin.isValue, Fin.val_one, List.getElem_cons_succ, List.getElem_cons_zero] at h1
    simp only [Fin.isValue, Fin.val_two, List.getElem_cons_succ, List.getElem_cons_zero] at h2
    simp only [Fin.isValue, show @Fin.val 8 3 = 3 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h3
    simp only [Fin.isValue, show @Fin.val 8 4 = 4 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h4
    simp only [Fin.isValue, show @Fin.val 8 5 = 5 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h5
    simp only [Fin.isValue, show @Fin.val 8 6 = 6 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h6
    simp only [Fin.isValue, show @Fin.val 8 7 = 7 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h7
    simp_all

end U64.Copy

@[reducible]
def U64.copy (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  subcircuit U64.Copy.circuit x

end
