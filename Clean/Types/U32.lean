import Clean.GadgetsNew.ByteLookup

section
variable {p : ℕ} [NeZero p] [Fact p.Prime]
variable [p_large_enough: Fact (p > 2*256^4)]

instance : Fact (p > 512) := by apply Fact.mk; linarith [p_large_enough.elim]

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
omit [NeZero p]

lemma val_eq_256 : (256 : F p).val = 256 := FieldUtils.val_lt_p 256 (by linarith [p_large_enough.elim])
lemma val_eq_256p2 : (256^2 : F p).val = 256^2 := by ring_nf; exact FieldUtils.val_lt_p (256^2) (by linarith [p_large_enough.elim])
lemma val_eq_256p3 : (256^3 : F p).val = 256^3 := by ring_nf; exact FieldUtils.val_lt_p (256^3) (by linarith [p_large_enough.elim])
lemma val_eq_256p4 : (256^4 : F p).val = 256^4 := by ring_nf; exact FieldUtils.val_lt_p (256^4) (by linarith [p_large_enough.elim])

/--
tactic script to fully rewrite a ZMod expression to its Nat version, given that
the expression is smaller than the modulus.

```
example (x y : F p) (hx: x.val < 256) (hy: y.val < 256) :
  (x + y * 256).val = x.val + y.val * 256 := by field_to_nat_u32
```

expected context:
- the equation to prove as the goal
- size assumptions on variables and a sufficient `p > ...` instance

if no sufficient inequalities are in the context, then the tactic will leave an equation of the form `expr : Nat < p` unsolved

note: this version is optimized for uint32 arithmetic:
- specifically handles field constants 256, 256^2, 256^3, 256^4
- expects `[Fact (p > 2*256^4)]` in the context
-/
syntax "field_to_nat_u32" : tactic
macro_rules
  | `(tactic|field_to_nat_u32) =>
    `(tactic|(
      repeat rw [ZMod.val_add]
      repeat rw [ZMod.val_mul]
      repeat rw [U32.val_eq_256]
      repeat rw [U32.val_eq_256p2]
      repeat rw [U32.val_eq_256p3]
      repeat rw [U32.val_eq_256p4]
      simp only [Nat.reducePow, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mod_eq_of_lt _]
      repeat linarith [‹Fact (_ > 2 * 256^4)›.elim]))

lemma value_eq {x0 x1 x2 x3: F p} (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256) :
  (x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3).val = x0.val + x1.val * 256 + x2.val * 256^2 + x3.val * 256^3 := by
  field_to_nat_u32
end U32
end
