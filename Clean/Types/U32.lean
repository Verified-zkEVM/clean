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

section ValueInjectivity
-- Helper lemma: injectivity of two-component base-256 representation
lemma base256_two_injective (a0 a1 b0 b1 : ℕ)
    (ha0 : a0 < 256) (hb0 : b0 < 256)
    (h : a0 + 256 * a1 = b0 + 256 * b1) :
    a0 = b0 ∧ a1 = b1 := by
  -- First component: use mod 256
  have h0 : a0 = b0 := by
    have : a0 % 256 = b0 % 256 := by
      calc a0 % 256 = (a0 + 256 * a1) % 256 := by simp [Nat.add_mul_mod_self_left]
        _ = (b0 + 256 * b1) % 256 := by rw [h]
        _ = b0 % 256 := by simp [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0] at this
    exact this

  -- Second component: divide by 256
  have h1 : a1 = b1 := by
    have : (a0 + 256 * a1) / 256 = (b0 + 256 * b1) / 256 := by
      rw [h]
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)] at this
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)] at this
    have ha0_div : a0 / 256 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr ha0)
    have hb0_div : b0 / 256 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hb0)
    rw [ha0_div, hb0_div] at this
    simp at this
    exact this

  exact ⟨h0, h1⟩

-- Injectivity of four-component base-256 representation
lemma base256_four_injective (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (_ : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (_ : b3 < 256)
    (h : a0 + 256 * (a1 + 256 * (a2 + 256 * a3)) = b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  -- Apply base256_two_injective repeatedly
  -- First, view as a0 + 256 * (rest)
  have h_outer := base256_two_injective a0 (a1 + 256 * (a2 + 256 * a3))
                                        b0 (b1 + 256 * (b2 + 256 * b3))
                                        ha0 hb0 h
  obtain ⟨h0, h_rest⟩ := h_outer

  -- Now apply to the remaining components
  have h_inner := base256_two_injective a1 (a2 + 256 * a3) b1 (b2 + 256 * b3)
                                        ha1 hb1 h_rest
  obtain ⟨h1, h_rest2⟩ := h_inner

  -- Finally, the last two components
  have h_final := base256_two_injective a2 a3 b2 b3 ha2 hb2 h_rest2
  obtain ⟨h2, h3⟩ := h_final

  exact ⟨h0, h1, h2, h3⟩

lemma value_injective_on_normalized (x y : U32 (F p))
    (hx : x.Normalized) (hy : y.Normalized) :
    x.value = y.value → x = y := by
  intro h_eq
  -- Use horner form of value
  have hx_value : x.value = x.x0.val + 256 * (x.x1.val + 256 * (x.x2.val + 256 * x.x3.val)) := by
    exact U32.value_horner x
  have hy_value : y.value = y.x0.val + 256 * (y.x1.val + 256 * (y.x2.val + 256 * y.x3.val)) := by
    exact U32.value_horner y
  rw [hx_value, hy_value] at h_eq

  -- Extract bounds from normalization
  simp only [U32.Normalized] at hx hy
  have ⟨hx0, hx1, hx2, hx3⟩ := hx
  have ⟨hy0, hy1, hy2, hy3⟩ := hy

  -- Apply base256_four_injective
  have ⟨h0, h1, h2, h3⟩ := base256_four_injective _ _ _ _ _ _ _ _ hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3 h_eq

  -- Now show the U32s are equal using ZMod.val_injective
  have hp : 256 < p := by
    have : Fact (p > 512) := inferInstance
    have : p > 512 := this.out
    omega

  -- Show equality component by component
  have : x.x0 = y.x0 := ZMod.val_injective (n := p) h0
  have : x.x1 = y.x1 := ZMod.val_injective (n := p) h1
  have : x.x2 = y.x2 := ZMod.val_injective (n := p) h2
  have : x.x3 = y.x3 := ZMod.val_injective (n := p) h3

  -- Reconstruct equality
  cases x; cases y
  simp_all

end ValueInjectivity

omit p_large_enough in
/--
Lemma showing that U32 Normalized property is equivalent to all components being < 256
-/
@[circuit_norm]
lemma Normalized_componentwise (env : Environment (F p)) (a b c d : Var field (F p)):
    (eval (α := U32) env
    { x0 := a, x1 := b, x2 := c, x3 := d }).Normalized ↔
    ((eval env a).val < 256 ∧ (eval env b).val < 256 ∧ (eval env c).val < 256 ∧ (eval env d).val < 256) := by
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval, fromElements, toVars, toElements, Vector.map]
  simp only [List.map_toArray, List.map_cons, List.map_nil, U32.Normalized]

/--
Lemma: For a normalized U32, value = 0 iff all components are 0
-/
lemma value_zero_iff_components_zero {x : U32 (F p)} (hx : x.Normalized) :
    x.value = 0 ↔ (∀ i : Fin (size U32), (toElements x)[i] = 0) := by
  have := U32.value_injective_on_normalized (x:=x) (y:=U32.mk 0 0 0 0) hx (by
    simp only [U32.Normalized, ZMod.val_zero]
    norm_num)
  constructor
  · intro h_val_zero
    simp only [h_val_zero] at this
    specialize this (by
      simp only [U32.value, ZMod.val_zero]
      omega)
    simp only [this, Fin.getElem_fin, size, toElements, Vector.getElem_mk, List.getElem_toArray]
    intro i
    fin_cases i <;> rfl
  · simp only [size, toElements]
    intro h_elements
    simp only [U32.value]
    have h_0 := h_elements 0
    have h_1 := h_elements 1
    have h_2 := h_elements 2
    have h_3 := h_elements 3
    simp only [Fin.isValue, Fin.getElem_fin, Fin.val_zero, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, Fin.val_one, List.getElem_cons_succ, Fin.val_two] at h_0 h_1 h_2 h_3
    have : (3 : Fin 4).val = 3 := rfl
    simp only [this] at h_3
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_3
    simp only [h_0, h_1, h_2, h_3, ZMod.val_zero]
    norm_num

lemma constU32_value (env : Environment (F p)) (n0 n1 n2 n3 : ℕ)
    (h0 : n0 < 256) (h1 : n1 < 256) (h2 : n2 < 256) (h3 : n3 < 256) :
    (eval (α := U32) env { x0 := Expression.const ↑n0, x1 := Expression.const ↑n1,
                           x2 := Expression.const ↑n2, x3 := Expression.const ↑n3 }).value =
    n0 + n1 * 256 + n2 * 256^2 + n3 * 256^3 := by
  simp only [explicit_provable_type, toVars, toElements]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval, fromElements, U32.value]
  cases p_large_enough
  norm_num
  repeat rw [ZMod.val_natCast_of_lt] <;> try omega

lemma zero_value (env : Environment (F p)) :
    (eval (α := U32) env { x0 := 0, x1 := 0, x2 := 0, x3 := 0 }).value = 0 := by
  have : (0 : Expression (F p)) = Expression.const ↑0 := by rfl
  repeat rw [this]
  have h := constU32_value env 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h <;> simp

lemma one_value (env : Environment (F p)) :
    (eval (α := U32) env { x0 := 1, x1 := 0, x2 := 0, x3 := 0 }).value = 1 := by
  have h := constU32_value env 1 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp at h
  exact h

lemma const_value (env : Environment (F p)) (n : ℕ) (h : n < 256) :
    (eval (α := U32) env { x0 := Expression.const ↑n, x1 := 0, x2 := 0, x3 := 0 }).value = n := by
  have h' := constU32_value env n 0 0 0 h (by norm_num) (by norm_num) (by norm_num)
  simp at h'
  exact h'

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
end U32
