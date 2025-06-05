import Clean.Gadgets.ByteLookup
import Clean.Circuit.Extensions
import Clean.Gadgets.Equality

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]
open Gadgets

/--
  A 32-bit unsigned integer is represented using four limbs of 8 bits each.
-/
structure U32 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T
deriving Repr

namespace U32

instance : LawfulProvableType U32 where
  size := 4
  to_elements x := #v[x.x0, x.x1, x.x2, x.x3]
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩

instance : NonEmptyProvableType U32 where
  nonempty := by simp only [size, Nat.reduceGT]

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
  Witness a 32-bit unsigned integer.
-/
def witness (compute : Environment (F p) → U32 (F p)) := do
  let ⟨ x0, x1, x2, x3 ⟩ ← ProvableType.witness compute

  lookup (ByteLookup x0)
  lookup (ByteLookup x1)
  lookup (ByteLookup x2)
  lookup (ByteLookup x3)

  return U32.mk x0 x1 x2 x3

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

/--
Return the value of a 32-bit unsigned integer as a field element.
-/
def value_field (x: U32 (F p)) : F p :=
  x.x0 + x.x1 * 256 + x.x2 * 256^2 + x.x3 * 256^3

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat (x: ℕ) : U32 (F p) :=
  let x0 := FieldUtils.mod x 256 (by linarith [p_large_enough.elim])
  let x1 := FieldUtils.mod (FieldUtils.floordiv x 256) 256 (by linarith [p_large_enough.elim])
  let x2 := FieldUtils.mod (FieldUtils.floordiv x 256^2) 256 (by linarith [p_large_enough.elim])
  let x3 := FieldUtils.mod (FieldUtils.floordiv x 256^3) 256 (by linarith [p_large_enough.elim])
  ⟨ x0, x1, x2, x3 ⟩

/--
  Return a 32-bit unsigned integer from a natural number, by decomposing
  it into four limbs of 8 bits each.
-/
def decompose_nat_expr (x: ℕ) : U32 (Expression (F p)) :=
  let x0 := FieldUtils.mod x 256 (by linarith [p_large_enough.elim])
  let x1 := FieldUtils.mod (FieldUtils.floordiv x 256) 256 (by linarith [p_large_enough.elim])
  let x2 := FieldUtils.mod (FieldUtils.floordiv x 256^2) 256 (by linarith [p_large_enough.elim])
  let x3 := FieldUtils.mod (FieldUtils.floordiv x 256^3) 256 (by linarith [p_large_enough.elim])
  ⟨ x0, x1, x2, x3 ⟩

/--
  Add two 32-bit unsigned integers, wrapping around on overflow over 2^32.
-/
def wrapping_add (x y: U32 (F p)) : U32 (F p) :=
  let val_x := x.value
  let val_y := y.value
  let val_out := (val_x + val_y) % 2^32
  U32.decompose_nat val_out

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

-- TODO: Maybe add U32.witness here?

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

end
