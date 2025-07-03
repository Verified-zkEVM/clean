import Clean.Gadgets.ByteLookup
import Clean.Utils.Bitwise
import Clean.Circuit.Provable
import Clean.Utils.Primes
import Clean.Circuit.Subcircuit
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
  toElements x := #v[x.x0, x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7]
  fromElements v :=
    let ⟨.mk [v0, v1, v2, v3, v4, v5, v6, v7], _⟩ := v
    ⟨ v0, v1, v2, v3, v4, v5, v6, v7 ⟩

instance : NonEmptyProvableType U64 where
  nonempty := by simp only [size, Nat.reduceGT]

instance (T: Type) [Repr T] : Repr (U64 T) where
  reprPrec x _ := "⟨" ++ repr x.x0 ++ ", " ++ repr x.x1 ++ ", " ++ repr x.x2 ++ ", " ++ repr x.x3 ++ ", " ++ repr x.x4 ++ ", " ++ repr x.x5 ++ ", " ++ repr x.x6 ++ ", " ++ repr x.x7 ++ "⟩"

namespace U64
def toLimbs {F} (x : U64 F) : Vector F 8 := toElements x
def fromLimbs {F} (v : Vector F 8) : U64 F := fromElements v

def map {α β : Type} (x : U64 α) (f : α → β) : U64 β :=
  ⟨ f x.x0, f x.x1, f x.x2, f x.x3, f x.x4, f x.x5, f x.x6, f x.x7 ⟩

def vals (x : U64 (F p)) : U64 ℕ := x.map ZMod.val

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
def Normalized (x: U64 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256 ∧
  x.x4.val < 256 ∧ x.x5.val < 256 ∧ x.x6.val < 256 ∧ x.x7.val < 256

/--
  Return the value of a 64-bit unsigned integer over the natural numbers.
-/
def value (x: U64 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3 +
  x.x4.val * 256^4 + x.x5.val * 256^5 + x.x6.val * 256^6 + x.x7.val * 256^7

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_lt_of_normalized {x : U64 (F p)} (hx: x.Normalized) : x.value < 2^64 := by
  simp_all only [value, Normalized]
  linarith

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_horner (x : U64 (F p)) : x.value =
    x.x0.val + 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * (x.x3.val +
      2^8 * (x.x4.val + 2^8 * (x.x5.val + 2^8 * (x.x6.val + 2^8 * x.x7.val)))))) := by
  simp only [value]
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_xor_horner {x : U64 (F p)} (hx: x.Normalized) : x.value =
    x.x0.val ^^^ 2^8 * (x.x1.val ^^^ 2^8 * (x.x2.val ^^^ 2^8 * (x.x3.val ^^^
      2^8 * (x.x4.val ^^^ 2^8 * (x.x5.val ^^^ 2^8 * (x.x6.val ^^^ 2^8 * x.x7.val)))))) := by
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  simp_all only [Normalized, value_horner]
  let ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := hx
  repeat rw [Bitwise.xor_eq_add 8]
  repeat assumption

def valueNat (x: U64 ℕ) :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3 +
  x.x4 * 256^4 + x.x5 * 256^5 + x.x6 * 256^6 + x.x7 * 256^7

omit [Fact (Nat.Prime p)] p_large_enough in
lemma vals_valueNat (x : U64 (F p)) : x.vals.valueNat = x.value := rfl

/--
  Return a 64-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNat (x: ℕ) : U64 (F p) :=
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
def decomposeNatNat (x: ℕ) : U64 ℕ :=
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
def decomposeNatExpr (x: ℕ) : U64 (Expression (F p)) :=
  let (⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ : U64 (F p)) := decomposeNat x
  ⟨ x0, x1, x2, x3 , x4, x5, x6, x7 ⟩

def fromUInt64 (x : UInt64) : U64 (F p) :=
  decomposeNat x.toFin

def valueU64 (x : U64 (F p)) (h : x.Normalized) : UInt64 :=
  UInt64.ofNatLT x.value (value_lt_of_normalized h)

lemma fromUInt64_normalized (x : UInt64) : (fromUInt64 (p:=p) x).Normalized := by
  simp only [Normalized, fromUInt64, decomposeNat]
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [FieldUtils.val_lt_p]
    assumption
    linarith [p_large_enough.elim]
  simp [h]

theorem value_fromUInt64 (x : UInt64) : value (fromUInt64 (p:=p) x) = x.toNat := by
  simp only [valueU64, value_horner, fromUInt64, decomposeNat, UInt64.toFin_val]
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
open Gadgets (ByteTable)

/--
  Assert that a 64-bit unsigned integer is normalized.
  This means that all its limbs are less than 256.
-/
def main (inputs : Var U64 (F p)) : Circuit (F p) Unit  := do
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := inputs
  lookup ByteTable x0
  lookup ByteTable x1
  lookup ByteTable x2
  lookup ByteTable x3
  lookup ByteTable x4
  lookup ByteTable x5
  lookup ByteTable x6
  lookup ByteTable x7

def circuit : FormalAssertion (F p) U64 where
  main

  Assumptions _ := True
  Spec inputs := inputs.Normalized

  soundness := by
    rintro i0 env x_var
    rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]

  completeness := by
    rintro i0 env x_var
    rintro _ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval _as
    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]

end U64.AssertNormalized

/--
  Witness a 64-bit unsigned integer.
-/
def U64.witness (compute : Environment (F p) → U64 (F p)) := do
  let x ← ProvableType.witness compute
  assertion U64.AssertNormalized.circuit x
  return x

namespace U64
def fromByte (x: Fin 256) : U64 (F p) :=
  ⟨ x.val, 0, 0, 0, 0, 0, 0, 0 ⟩

lemma fromByte_value {x : Fin 256} : (fromByte x).value (p:=p) = x := by
  simp [value, fromByte]
  apply FieldUtils.val_lt_p x
  linarith [x.is_lt, p_large_enough.elim]

lemma fromByte_normalized {x : Fin 256} : (fromByte x).Normalized (p:=p) := by
  simp [Normalized, fromByte]
  rw [FieldUtils.val_lt_p x]
  repeat linarith [x.is_lt, p_large_enough.elim]

namespace ByteVector
-- results about U64 when viewed as a vector of bytes, via `toLimbs` and `fromLimbs`

theorem fromLimbs_toLimbs {F} (x : U64 F) :
    U64.fromLimbs x.toLimbs = x := rfl

theorem toLimbs_fromLimbs {F} (v : Vector F 8) :
    (U64.fromLimbs v).toLimbs = v := ProvableType.toElements_fromElements ..

theorem ext_iff {F} {x y : U64 F} :
    x = y ↔ ∀ i (_ : i < 8), x.toLimbs[i] = y.toLimbs[i] := by
  simp only [U64.toLimbs, ProvableType.ext_iff, size]

omit [Fact (Nat.Prime p)] p_large_enough in
theorem normalized_iff {x : U64 (F p)} :
    x.Normalized ↔ ∀ i (_ : i < 8), x.toLimbs[i].val < 256 := by
  rcases x with ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
  simp only [toLimbs, Normalized, toElements, size, Vector.getElem_mk, List.getElem_toArray]
  constructor
  · intro h i hi
    repeat (rcases hi with _ | hi; try simp [*, size])
  · intro h
    let h0 := h 0 (by decide)
    let h1 := h 1 (by decide)
    let h2 := h 2 (by decide)
    let h3 := h 3 (by decide)
    let h4 := h 4 (by decide)
    let h5 := h 5 (by decide)
    let h6 := h 6 (by decide)
    let h7 := h 7 (by decide)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7
    simp_all

lemma toLimbs_map {α β : Type} (x : U64 α) (f : α → β) :
  toLimbs (map x f) = (toLimbs x).map f := rfl

lemma getElem_eval_toLimbs {F} [Field F] {env : Environment F} {x : U64 (Expression F)} {i : ℕ} (hi : i < 8) :
    Expression.eval env x.toLimbs[i] = (eval env x).toLimbs[i] := by
  simp only [toLimbs, eval, size, toVars, ProvableType.toElements_fromElements, Vector.getElem_map]

lemma eval_fromLimbs {F} [Field F] {env : Environment F} {v : Vector (Expression F) 8} :
    eval env (U64.fromLimbs v) = .fromLimbs (v.map env) := by
  simp only [U64.fromLimbs, ProvableType.eval_fromElements]
end ByteVector
end U64
