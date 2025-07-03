import Clean.Gadgets.ByteLookup
import Clean.Circuit.Extensions
import Clean.Utils.Bitwise
import Clean.Circuit.Provable
import Clean.Utils.Primes
import Clean.Circuit.Subcircuit
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
  toElements x := #v[x.x0, x.x1, x.x2, x.x3]
  fromElements v :=
    let ⟨ .mk [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩

instance : NonEmptyProvableType U32 where
  nonempty := by simp only [size, Nat.reduceGT]

instance (T: Type) [Inhabited T] : Inhabited (U32 T) where
  default := ⟨ default, default, default, default ⟩

instance (T: Type) [Repr T] : Repr (U32 T) where
  reprPrec x _ := "⟨" ++ repr x.x0 ++ ", " ++ repr x.x1 ++ ", " ++ repr x.x2 ++ ", " ++ repr x.x3 ++ "⟩"

namespace U32
def toLimbs {F} (x : U32 F) : Vector F 4 := toElements x
def fromLimbs {F} (v : Vector F 4) : U32 F := fromElements v

def map {α β : Type} (x : U32 α) (f : α → β) : U32 β :=
  ⟨ f x.x0, f x.x1, f x.x2, f x.x3 ⟩

def vals (x : U32 (F p)) : U32 ℕ := x.map ZMod.val

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
def Normalized (x: U32 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256

/--
  Return the value of a 32-bit unsigned integer over the natural numbers.
-/
def value (x: U32 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_lt_of_normalized {x : U32 (F p)} (hx: x.Normalized) : x.value < 2^32 := by
  simp_all only [value, Normalized]
  linarith

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_horner (x : U32 (F p)) : x.value =
    x.x0.val + 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * x.x3.val)) := by
  simp only [value]
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_xor_horner {x : U32 (F p)} (hx: x.Normalized) : x.value =
    x.x0.val ^^^ 2^8 * (x.x1.val ^^^ 2^8 * (x.x2.val ^^^ 2^8 * x.x3.val)) := by
  let ⟨ x0, x1, x2, x3 ⟩ := x
  simp_all only [Normalized, value_horner]
  let ⟨ hx0, hx1, hx2, hx3 ⟩ := hx
  repeat rw [Bitwise.xor_eq_add 8]
  repeat assumption

def valueNat (x: U32 ℕ) :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3

omit [Fact (Nat.Prime p)] p_large_enough in
lemma vals_valueNat (x : U32 (F p)) : x.vals.valueNat = x.value := rfl

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNat (x: ℕ) : U32 (F p) :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNatNat (x: ℕ) : U32 ℕ :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNatExpr (x: ℕ) : U32 (Expression (F p)) :=
  let (⟨x0, x1, x2, x3⟩ : U32 (F p)) := decomposeNat x
  ⟨ x0, x1, x2, x3 ⟩

def fromUInt32 (x : UInt32) : U32 (F p) :=
  decomposeNat x.toFin

def valueU32 (x : U32 (F p)) (h : x.Normalized) : UInt32 :=
  UInt32.ofNatLT x.value (value_lt_of_normalized h)

lemma fromUInt32_normalized (x : UInt32) : (fromUInt32 (p:=p) x).Normalized := by
  simp only [Normalized, fromUInt32, decomposeNat]
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [FieldUtils.val_lt_p]
    assumption
    linarith [p_large_enough.elim]
  simp [h]

theorem value_fromUInt32 (x : UInt32) : value (fromUInt32 (p:=p) x) = x.toNat := by
  simp only [valueU32, value_horner, fromUInt32, decomposeNat, UInt32.toFin_val]
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

def fromByte (x: Fin 256) : U32 (F p) :=
  ⟨ x.val, 0, 0, 0 ⟩

lemma fromByte_value {x : Fin 256} : (fromByte x).value (p:=p) = x := by
  simp [value, fromByte]
  apply FieldUtils.val_lt_p x
  linarith [x.is_lt, p_large_enough.elim]

lemma fromByte_normalized {x : Fin 256} : (fromByte x).Normalized (p:=p) := by
  simp [Normalized, fromByte]
  rw [FieldUtils.val_lt_p x]
  repeat linarith [x.is_lt, p_large_enough.elim]
end U32

namespace U32.AssertNormalized
open Gadgets (ByteTable)

/--
  Assert that a 32-bit unsigned integer is normalized.
  This means that all its limbs are less than 256.
-/
def main (inputs : Var U32 (F p)) : Circuit (F p) Unit  := do
  let ⟨ x0, x1, x2, x3 ⟩ := inputs
  lookup ByteTable x0
  lookup ByteTable x1
  lookup ByteTable x2
  lookup ByteTable x3

def circuit : FormalAssertion (F p) U32 where
  main
  Assumptions _ := True
  Spec inputs := inputs.Normalized

  soundness := by
    rintro i0 env x_var ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp_all [main, circuit_norm, ByteTable, Normalized, explicit_provable_type]

  completeness := by
    rintro i0 env x_var _ ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp_all [main, circuit_norm, ByteTable, Normalized, explicit_provable_type]

end U32.AssertNormalized

/--
  Witness a 32-bit unsigned integer.
-/
def U32.witness (compute : Environment (F p) → U32 (F p)) := do
  let x ← ProvableType.witness compute
  assertion U32.AssertNormalized.circuit x
  return x

namespace U32.Copy

def main (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let y <== x
  return y

def Assumptions (_input : U32 (F p)) := True

def Spec (x y : U32 (F p)) := x = y

def circuit : FormalCircuit (F p) U32 U32 where
  main := main
  Assumptions
  Spec
  localLength _ := 4
  output inputs i0 := varFromOffset U32 i0
  soundness := by
    rintro i0 env x_var
    rintro ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [circuit_norm, main, Spec, h_eval, explicit_provable_type]
    injections h_eval
    intros h0 h1 h2 h3
    aesop
  completeness := by
    rintro i0 env x_var
    rintro h ⟨ x0, x1, x2, x3 ⟩ h_eval _as
    simp [circuit_norm, main, Spec, h_eval]
    simp [circuit_norm, main, Gadgets.Equality.elaborated] at h
    simp_all [circuit_norm, explicit_provable_type]
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

end Copy

@[reducible]
def copy (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) :=
  subcircuit Copy.circuit x

namespace ByteVector
-- results about U32 when viewed as a vector of bytes, via `toLimbs` and `fromLimbs`

theorem fromLimbs_toLimbs {F} (x : U32 F) :
    U32.fromLimbs x.toLimbs = x := rfl

theorem toLimbs_fromLimbs {F} (v : Vector F 4) :
    (U32.fromLimbs v).toLimbs = v := ProvableType.toElements_fromElements ..

theorem ext_iff {F} {x y : U32 F} :
    x = y ↔ ∀ i (_ : i < 4), x.toLimbs[i] = y.toLimbs[i] := by
  simp only [U32.toLimbs, ProvableType.ext_iff, size]

omit [Fact (Nat.Prime p)] p_large_enough in
theorem normalized_iff {x : U32 (F p)} :
    x.Normalized ↔ ∀ i (_ : i < 4), x.toLimbs[i].val < 256 := by
  rcases x with ⟨ x0, x1, x2, x3 ⟩
  simp only [toLimbs, Normalized, toElements, size, Vector.getElem_mk, List.getElem_toArray]
  constructor
  · intro h i hi
    repeat (rcases hi with _ | hi; try simp [*, size])
  · intro h
    let h0 := h 0 (by decide)
    let h1 := h 1 (by decide)
    let h2 := h 2 (by decide)
    let h3 := h 3 (by decide)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
    simp_all

lemma toLimbs_map {α β : Type} (x : U32 α) (f : α → β) :
  toLimbs (map x f) = (toLimbs x).map f := rfl

lemma getElem_eval_toLimbs {F} [Field F] {env : Environment F} {x : U32 (Expression F)} {i : ℕ} (hi : i < 4) :
    Expression.eval env x.toLimbs[i] = (eval env x).toLimbs[i] := by
  simp only [toLimbs, eval, size, toVars, ProvableType.toElements_fromElements, Vector.getElem_map]

lemma eval_fromLimbs {F} [Field F] {env : Environment F} {v : Vector (Expression F) 4} :
    eval env (U32.fromLimbs v) = .fromLimbs (v.map env) := by
  simp only [U32.fromLimbs, ProvableType.eval_fromElements]
end ByteVector
end U32
