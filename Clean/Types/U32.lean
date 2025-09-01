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
structure U32 (T : Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T
deriving DecidableEq

instance : ProvableType U32 where
  size := 4
  toElements x := #v[x.x0, x.x1, x.x2, x.x3]
  fromElements v :=
    let ⟨ .mk [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩

instance : NonEmptyProvableType U32 where
  nonempty := by simp only [size, Nat.reduceGT]

instance (T : Type) [Inhabited T] : Inhabited (U32 T) where
  default := ⟨ default, default, default, default ⟩

instance (T : Type) [Repr T] : Repr (U32 T) where
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
def Normalized (x : U32 (F p)) :=
  x.x0.val < 256 ∧ x.x1.val < 256 ∧ x.x2.val < 256 ∧ x.x3.val < 256

/--
  Return the value of a 32-bit unsigned integer over the natural numbers.
-/
def value (x : U32 (F p)) :=
  x.x0.val + x.x1.val * 256 + x.x2.val * 256^2 + x.x3.val * 256^3

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_lt_of_normalized {x : U32 (F p)} (hx : x.Normalized) : x.value < 2^32 := by
  simp_all only [value, Normalized]
  linarith

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_horner (x : U32 (F p)) : x.value =
    x.x0.val + 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * x.x3.val)) := by
  simp only [value]
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
theorem value_xor_horner {x : U32 (F p)} (hx : x.Normalized) : x.value =
    x.x0.val ^^^ 2^8 * (x.x1.val ^^^ 2^8 * (x.x2.val ^^^ 2^8 * x.x3.val)) := by
  let ⟨ x0, x1, x2, x3 ⟩ := x
  simp_all only [Normalized, value_horner]
  let ⟨ hx0, hx1, hx2, hx3 ⟩ := hx
  repeat rw [xor_eq_add 8]
  repeat assumption

def valueNat (x : U32 ℕ) :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3

omit [Fact (Nat.Prime p)] p_large_enough in
lemma vals_valueNat (x : U32 (F p)) : x.vals.valueNat = x.value := rfl

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNat (x : ℕ) : U32 (F p) :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNatNat (x : ℕ) : U32 ℕ :=
  let x0 := x % 256
  let x1 : ℕ := (x / 256) % 256
  let x2 : ℕ := (x / 256^2) % 256
  let x3 : ℕ := (x / 256^3) % 256
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decomposeNatExpr (x : ℕ) : U32 (Expression (F p)) :=
  let (⟨x0, x1, x2, x3⟩ : U32 (F p)) := decomposeNat x
  ⟨ x0, x1, x2, x3 ⟩

def fromUInt32 (x : UInt32) : U32 (F p) :=
  decomposeNat x.toFin

def valueU32 (x : U32 (F p)) (h : x.Normalized) : UInt32 :=
  UInt32.ofNatLT x.value (value_lt_of_normalized h)

lemma value_of_decomposedNat_of_small (x : ℕ) :
    x < 256^4 ->
    (decomposeNat (p:=p) x).value = x := by
  intro hx
  simp only [value, decomposeNat]
  -- Need to show that ZMod.val of each component equals the component itself
  have h (y : ℕ) : y < 256 → ZMod.val (n:=p) (y : ℕ) = y := by
    intro hy
    rw [ZMod.val_cast_of_lt]
    linarith [p_large_enough.elim]
  -- Apply h to each component
  rw [h (x % 256) (Nat.mod_lt _ (by norm_num : 256 > 0))]
  rw [h (x / 256 % 256) (Nat.mod_lt _ (by norm_num : 256 > 0))]
  rw [h (x / 256^2 % 256) (Nat.mod_lt _ (by norm_num : 256 > 0))]
  rw [h (x / 256^3 % 256) (Nat.mod_lt _ (by norm_num : 256 > 0))]

  have h1 := Nat.div_add_mod x 256
  have h2 := Nat.div_add_mod (x / 256) 256
  have h3 := Nat.div_add_mod (x / 256 ^ 2) 256
  have h4 := Nat.div_add_mod (x / 256 ^ 3) 256
  omega

lemma fromUInt32_normalized (x : UInt32) : (fromUInt32 (p:=p) x).Normalized := by
  simp only [Normalized, fromUInt32, decomposeNat]
  have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
    have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [FieldUtils.val_lt_p]
    assumption
    linarith [p_large_enough.elim]
  simp [h]

theorem value_fromUInt32 (x : UInt32) : value (fromUInt32 (p:=p) x) = x.toNat := by
  simp only [fromUInt32, UInt32.toFin_val]
  apply value_of_decomposedNat_of_small
  simp [UInt32.toNat_lt_size]

def fromByte (x : Fin 256) : U32 (F p) :=
  ⟨ x.val, 0, 0, 0 ⟩

lemma fromByte_value {x : Fin 256} : (fromByte x).value (p:=p) = x := by
  simp [value, fromByte]
  apply FieldUtils.val_lt_p x
  linarith [x.is_lt, p_large_enough.elim]

lemma fromByte_normalized {x : Fin 256} : (fromByte x).Normalized (p:=p) := by
  simp [Normalized, fromByte]
  rw [FieldUtils.val_lt_p x]
  repeat linarith [x.is_lt, p_large_enough.elim]

omit p_large_enough in
lemma value_injective_on_normalized (x y : U32 (F p))
    (hx : x.Normalized) (hy : y.Normalized) :
    x.value = y.value → x = y := by
  intro h_eq
  -- Use horner form of value
  have hx_value := U32.value_horner x
  have hy_value := U32.value_horner y

  simp only [U32.Normalized] at hx hy

  have : x.x0 = y.x0 := by apply ZMod.val_injective; omega
  have : x.x1 = y.x1 := by apply ZMod.val_injective; omega
  have : x.x2 = y.x2 := by apply ZMod.val_injective; omega
  have : x.x3 = y.x3 := by apply ZMod.val_injective; omega

  cases x; cases y
  simp_all

omit [Fact (Nat.Prime p)] p_large_enough in
@[circuit_norm]
lemma value_of_literal (a b c d : F p) :
  (U32.mk a b c d).value =
    a.val + b.val * 256 + c.val * 256^2 + d.val * 256^3 := by rfl

omit [Fact (Nat.Prime p)] p_large_enough in
@[circuit_norm]
lemma value_of_literal' (a b c d : field (F p)) :
  @U32.value p (@U32.mk (field (F p)) a b c d)  =
    a.val + b.val * 256 + c.val * 256^2 + d.val * 256^3 := by rfl

omit p_large_enough in
@[circuit_norm]
lemma eval_of_literal (env : Environment (F p)) (a b c d : Var field (F p)) :
    eval env (U32.mk a b c d) =
    U32.mk (eval env a) (eval env b) (eval env c) (eval env d) := by
  simp only [explicit_provable_type, circuit_norm]

omit p_large_enough in
omit [Fact (Nat.Prime p)] in
@[circuit_norm]
lemma Normalized_componentwise (a b c d : F p):
    (U32.mk a b c d).Normalized ↔
    (a.val < 256 ∧ b.val < 256 ∧ c.val < 256 ∧ d.val < 256) := by
  simp only [explicit_provable_type, circuit_norm, U32.Normalized]

omit p_large_enough in
omit [Fact (Nat.Prime p)] in
@[circuit_norm]
lemma Normalized_componentwise' (a b c d : field (F p)):
    (U32.mk a b c d).Normalized ↔
    (a.val < 256 ∧ b.val < 256 ∧ c.val < 256 ∧ d.val < 256) := by
  simp only [explicit_provable_type, circuit_norm, U32.Normalized]

omit p_large_enough in
@[circuit_norm]
lemma value_zero :
    (0 : U32 (F p)) = U32.mk 0 0 0 0 := by
  aesop

omit p_large_enough in
@[circuit_norm]
lemma value_zero_iff_zero {x : U32 (F p)} (hx : x.Normalized) :
    x.value = 0 ↔ x = U32.mk 0 0 0 0 := by
  have := U32.value_injective_on_normalized (x:=x) (y:=U32.mk 0 0 0 0) hx (by
    simp only [U32.Normalized, ZMod.val_zero]
    norm_num)
  constructor
  · intro h_val_zero
    simp only [h_val_zero, circuit_norm, ZMod.val_zero] at this
    specialize this (by trivial)
    assumption
  · intro h_zero
    simp only [h_zero, circuit_norm, ZMod.val_zero]
    ring

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
  U32.AssertNormalized.circuit x
  return x

namespace U32.ByteVector
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

-- Bitwise operations on U32
section Bitwise

-- helper lemma to prepare the goal for testBit_two_pow_mul_add
private lemma reorganize_value (a b c d : ℕ) :
  a + 256 * (b + 256 * (c + 256 * d)) =
  2^8 * (2^8 * (2^8 * d + c) + b) + a := by ring

private lemma reorganize_value' (a b c d : ℕ) :
  a + b * 256 + c * 256 ^ 2 + d * 256 ^ 3 =
  2^8 * (2^8 * (2^8 * d + c) + b) + a := by ring

-- General lemma: operations defined with bitwise can be computed componentwise on U32
omit [Fact (Nat.Prime p)] p_large_enough in
lemma bitwise_componentwise (f : Bool → Bool → Bool)
    {x y : U32 (F p)} (x_norm : x.Normalized) (y_norm : y.Normalized) :
    f false false = false →
    Nat.bitwise f x.value y.value =
      Nat.bitwise f x.x0.val y.x0.val + 256 *
        (Nat.bitwise f x.x1.val y.x1.val + 256 *
          (Nat.bitwise f x.x2.val y.x2.val + 256 * Nat.bitwise f x.x3.val y.x3.val)) := by
  intro _
  simp only [value]

  have ⟨_, _, _, _⟩ := x_norm
  have ⟨_, _, _, _⟩ := y_norm
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [reorganize_value, reorganize_value']
  rw [Nat.testBit_bitwise] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val x.x0)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val y.x0)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=Nat.bitwise f (ZMod.val x.x0) (ZMod.val y.x0))] <;> try (apply Nat.bitwise_lt_two_pow <;> assumption)
  split
  · simp_all only [Nat.testBit_bitwise]
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val x.x1)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val y.x1)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=Nat.bitwise f (ZMod.val x.x1) (ZMod.val y.x1))] <;> try (apply Nat.bitwise_lt_two_pow <;> assumption)
  split
  · simp_all only [not_lt, Nat.testBit_bitwise]
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val x.x2)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=ZMod.val y.x2)] <;> try assumption
  rw [Nat.testBit_two_pow_mul_add (i:=8) (b:=Nat.bitwise f (ZMod.val x.x2) (ZMod.val y.x2))] <;> try (apply Nat.bitwise_lt_two_pow <;> assumption)
  aesop

omit [Fact (Nat.Prime p)] p_large_enough in
lemma or_componentwise {x y : U32 (F p)} (x_norm : x.Normalized) (y_norm : y.Normalized) :
    x.value ||| y.value =
    (x.x0.val ||| y.x0.val) + 256 *
      ((x.x1.val ||| y.x1.val) + 256 *
        ((x.x2.val ||| y.x2.val) + 256 * (x.x3.val ||| y.x3.val))) := by
  show Nat.bitwise _ _ _ = _
  rw [bitwise_componentwise or x_norm y_norm] <;> rfl

end Bitwise

end U32
