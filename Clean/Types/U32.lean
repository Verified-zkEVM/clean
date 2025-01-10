import Clean.GadgetsNew.ByteLookup

section
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

/--
  A 32-bit unsigned integer is represented using four limbs of 8 bits each.
-/
structure U32 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T

namespace U32

/--
  Witness a 32-bit unsigned integer.
-/
def witness (compute : Unit → U32 (F p)) := do
  let val := compute ()
  let x0 ←  witness_var (fun _ => val.x0)
  let x1 ←  witness_var (fun _ => val.x1)
  let x2 ←  witness_var (fun _ => val.x2)
  let x3 ←  witness_var (fun _ => val.x3)

  byte_lookup x0
  byte_lookup x1
  byte_lookup x2
  byte_lookup x3

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
Return the value of a 32-bit unsigned integer as a field
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
  Add two 32-bit unsigned integers, wrapping around on overflow over 2^32.
-/
def wrapping_add (x y: U32 (F p)) : U32 (F p) :=
  let val_x := x.value
  let val_y := y.value
  let val_out := (val_x + val_y) % 2^32
  U32.decompose_nat val_out


lemma wrapping_add_correct (x y z: U32 (F p)) :
    x.wrapping_add y = z ↔ z.value = (x.value + y.value) % 2^32 := by
  sorry

-- U32-related Nat lemmas
variable [p_large_enough': Fact (p > 2*256^2)]

lemma val_eq_256 {p} [Fact (p.Prime)] [pl : Fact (p > 512)] : (256 : F p).val = 256 :=
  FieldUtils.val_lt_p 256 (by linarith [pl.elim])

-- TODO how can this be so hard???
lemma value_lt_1 {x0 x1: F p} (h0 : x0.val < 256) (h1 : x1.val < 256) :
  (x0 + x1 * 256).val < 256^2 ∧ x0.val + x1.val * 256 = (x0 + x1 * 256).val
:= by
  have : x1.val * 256 ≤ 255 * 256 := by linarith [h1, p_large_enough.elim]
  have : x1.val * (256 : F p).val < p := by rw [val_eq_256]; linarith [this, p_large_enough'.elim]
  have : x1.val * (256 : F p).val = (x1 * 256).val := ZMod.val_mul_of_lt this |>.symm
  have : x1.val * 256 = (x1 * 256).val := by rw [← this, val_eq_256]
  sorry

lemma value_eq {x0 x1 x2 x3: F p} (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256) :
  x0.val + x1.val * 256 + x2.val * 256^2 + x3.val * 256^3 = (x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3).val  := by
  sorry

end U32
end
