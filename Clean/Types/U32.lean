import Clean.Gadgets.ByteLookup
import Clean.Circuit.Extensions
import Clean.Utils.Bitwise
import Clean.Circuit.Provable
import Clean.Utils.Primes
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Equality

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  A 32-bit unsigned integer is represented using four limbs of 8 bits each.
-/
structure U32 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T

instance : ProvableType U32 where
  size := 4
  to_elements x := #v[x.x0, x.x1, x.x2, x.x3]
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩

instance : NonEmptyProvableType U32 where
  nonempty := by simp only [size, Nat.reduceGT]

instance (T: Type) [Repr T] : Repr (U32 T) where
  reprPrec x _ := "⟨" ++ repr x.x0 ++ ", " ++ repr x.x1 ++ ", " ++ repr x.x2 ++ ", " ++ repr x.x3 ++ "⟩"

namespace U32
def map {α β : Type} (x : U32 α) (f : α → β) : U32 β :=
  ⟨ f x.x0, f x.x1, f x.x2, f x.x3 ⟩

omit [Fact (Nat.Prime p)] p_large_enough in
/--
  Extensionality principle for U32
-/
@[ext]
lemma ext {x y : U32 (F p)}
    (h0 : x.x0 = y.x0)
    (h1 : x.x1 = y.x1)
    (h2 : x.x2 = y.x2)
    (h3 : x.x3 = y.x3)
    : x = y :=
  by match x, y with
  | ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩ =>
    simp only [h0, h1, h2, h3] at *
    simp only [h0, h1, h2, h3]

/--
  A 32-bit unsigned integer is normalized if all its limbs are less than 256.
-/
def is_normalized (x: U32 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256

/--
  Return the value of a 32-bit unsigned integer over the natural numbers.
-/
def value (x: U32 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_lt_of_normalized {x : U32 (F p)} (hx: x.is_normalized) : x.value < 2^32 := by
  simp_all only [value, is_normalized]
  linarith

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_horner (x : U32 (F p)) : x.value =
    x.x0.val + 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * x.x3.val)) := by
  simp only [value]
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_xor_horner {x : U32 (F p)} (hx: x.is_normalized) : x.value =
    x.x0.val ^^^ 2^8 * (x.x1.val ^^^ 2^8 * (x.x2.val ^^^ 2^8 * x.x3.val)) := by
  let ⟨ x0, x1, x2, x3 ⟩ := x
  simp_all only [is_normalized, value_horner]
  let ⟨ hx0, hx1, hx2, hx3 ⟩ := hx
  repeat rw [Bitwise.xor_eq_add 8]
  repeat assumption

def value_nat (x: U32 ℕ) :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat (x: ℕ) : U32 (F p) :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat_nat (x: ℕ) : U32 ℕ :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat_expr (x: ℕ) : U32 (Expression (F p)) :=
  let (⟨x0, x1, x2, x3⟩ : U32 (F p)) := decompose_nat x
  ⟨ x0, x1, x2, x3 ⟩

omit [Fact (Nat.Prime p)] p_large_enough in
def normalized_u32 (x : U32 (F p)) : x.is_normalized → x.value < 2^32 := by
  simp [is_normalized, value]
  intros
  linarith

def from_u32 (x : UInt32) : U32 (F p) :=
  decompose_nat x.toFin

def value_u32 (x : U32 (F p)) (h : x.is_normalized) : UInt32 :=
  UInt32.ofNatLT x.value (normalized_u32 x h)

lemma from_u32_normalized (x : UInt32) : (from_u32 (p:=p) x).is_normalized := by
  simp only [is_normalized, from_u32, decompose_nat]
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [FieldUtils.val_lt_p]
    assumption
    linarith [p_large_enough.elim]
  simp [h]

theorem value_from_u32_eq (x : UInt32) : value (from_u32 (p:=p) x) = x.toNat := by
  simp only [value_u32, value_horner, from_u32, decompose_nat, UInt32.toFin_val]
  set x := x.toNat
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) = x % 256 := by
    rw [ZMod.val_cast_of_lt]
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    linarith [p_large_enough.elim]
  simp only [h]
  have : 2^8 = 256 := rfl
  simp only [this]
  have : x < 256^4 := by simp [x, UInt32.toNat_lt_size]
  have : x / 256^3 % 256 = x / 256^3 := by rw [Nat.mod_eq_of_lt]; omega
  rw [this]
  have div_succ_pow (n : ℕ) : x / 256^(n + 1) = (x / 256^n) / 256 := by rw [Nat.div_div_eq_div_mul]; rfl
  have mod_add_div (n : ℕ) : x / 256^n % 256 + 256 * (x / 256^(n + 1)) = x / 256^n := by
    rw [div_succ_pow n, Nat.mod_add_div]
  simp only [mod_add_div]
  rw [div_succ_pow 1, Nat.pow_one, Nat.mod_add_div, Nat.mod_add_div]

def from_byte (x: Fin 256) : U32 (F p) :=
  ⟨ x.val, 0, 0, 0 ⟩

lemma from_byte_value {x : Fin 256} : (from_byte x).value (p:=p) = x := by
  simp [value, from_byte]
  apply FieldUtils.val_lt_p x
  linarith [x.is_lt, p_large_enough.elim]

lemma from_byte_is_normalized {x : Fin 256} : (from_byte x).is_normalized (p:=p) := by
  simp [is_normalized, from_byte]
  rw [FieldUtils.val_lt_p x]
  repeat linarith [x.is_lt, p_large_enough.elim]
end U32

namespace U32.AssertNormalized
open Gadgets (ByteLookup ByteTable)

/--
  Assert that a 32-bit unsigned integer is normalized.
  This means that all its limbs are less than 256.
-/
def u32_assert_normalized (inputs : Var U32 (F p)) : Circuit (F p) Unit  := do
  let ⟨ x0, x1, x2, x3 ⟩ := inputs
  lookup (ByteLookup x0)
  lookup (ByteLookup x1)
  lookup (ByteLookup x2)
  lookup (ByteLookup x3)

def assumptions (_input : U32 (F p)) := True

def spec (inputs : U32 (F p)) := inputs.is_normalized

def circuit : FormalAssertion (F p) U32 where
  main := u32_assert_normalized
  assumptions := assumptions
  spec := spec
  soundness := by
    rintro i0 env x_var
    rintro ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [spec, circuit_norm, u32_assert_normalized, ByteLookup, is_normalized]
    repeat rw [ByteTable.equiv]
    simp_all [circuit_norm, eval]

  completeness := by
    rintro i0 env x_var
    rintro _ ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [spec, circuit_norm, u32_assert_normalized, ByteLookup, is_normalized]
    repeat rw [ByteTable.equiv]
    simp_all [circuit_norm, eval]

end U32.AssertNormalized

/--
  Witness a 32-bit unsigned integer.
-/
def U32.witness (compute : Environment (F p) → U32 (F p)) := do
  let x ← ProvableType.witness compute
  assertion U32.AssertNormalized.circuit x
  return x

namespace U32.Copy

def u32_copy (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let y ← ProvableType.witness fun env =>
    U32.mk (env x.x0) (env x.x1) (env x.x2) (env x.x3)
  assert_equals x y
  return y

def assumptions (_input : U32 (F p)) := True

def spec (x y : U32 (F p)) := x = y

def circuit : FormalCircuit (F p) U32 U32 where
  main := u32_copy
  assumptions := assumptions
  spec := spec
  local_length := 4
  output inputs i0 := var_from_offset U32 i0
  soundness := by
    rintro i0 env x_var
    rintro ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [circuit_norm, u32_copy, spec, h_eval, eval, var_from_offset]
    injections h_eval
    intros h0 h1 h2 h3
    aesop
  completeness := by
    rintro i0 env x_var
    rintro h ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [circuit_norm, u32_copy, spec, h_eval]
    simp [circuit_norm, u32_copy, Gadgets.Equality.elaborated] at h
    simp [subcircuit_norm, eval] at h
    simp_all [eval, Expression.eval, circuit_norm, h, var_from_offset, Vector.mapRange]
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp only [Fin.isValue, Fin.val_zero, add_zero, List.getElem_cons_zero] at h0
    simp only [Fin.isValue, Fin.val_one, List.getElem_cons_succ, List.getElem_cons_zero] at h1
    simp only [Fin.isValue, Fin.val_two, List.getElem_cons_succ, List.getElem_cons_zero] at h2
    simp only [Fin.isValue, show @Fin.val 4 3 = 3 by rfl, List.getElem_cons_succ,
      List.getElem_cons_zero] at h3
    simp_all

end U32.Copy

@[reducible]
def U32.copy (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) :=
  subcircuit U32.Copy.circuit x

end
