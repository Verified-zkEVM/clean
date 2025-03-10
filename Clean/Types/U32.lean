import Clean.Gadgets.ByteLookup
import Clean.Circuit.Extensions

section
variable {p : ℕ} [Fact p.Prime]
-- TODO: this assumption is false in practice, need to change some proofs to not need it
variable [p_large_enough: Fact (p > 512)]

instance : NeZero p := ⟨‹Fact p.Prime›.elim.ne_zero⟩
instance : Fact (p > 512) := by apply Fact.mk; linarith [p_large_enough.elim]

/--
  A 32-bit unsigned integer is represented using four limbs of 8 bits each.
-/
structure U32 (T: Type) where
  x0 : T
  x1 : T
  x2 : T
  x3 : T

instance {F : Type} : StructuredElements U32 F where
  size := 4
  to_elements x := vec [x.x0, x.x1, x.x2, x.x3]
  from_elements v := ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩, v.get ⟨ 3, by norm_num ⟩ ⟩

namespace U32

instance : ProvableType U32 where
  size := 4
  to_vars x := vec [x.x0, x.x1, x.x2, x.x3]
  to_values x := vec [x.x0, x.x1, x.x2, x.x3]
  from_vars v :=
    let ⟨ [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩
  from_values v :=
    let ⟨ [x0, x1, x2, x3], _ ⟩ := v
    ⟨ x0, x1, x2, x3 ⟩

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
  let ⟨ x0, x1, x2, x3 ⟩ ← Provable.witness U32 compute

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


lemma wrapping_add_correct (x y z: U32 (F p)) :
    x.wrapping_add y = z ↔ z.value = (x.value + y.value) % 2^32 := by
  sorry

-- U32-related tactic and lemmas
lemma val_eq_256 : (256 : F p).val = 256 := FieldUtils.val_lt_p 256 (by linarith [p_large_enough.elim])

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

if no sufficient inequalities are in the context, then the tactic will leave an equation of the form `expr : Nat < p` unsolved.

note: this version is optimized for uint32 arithmetic:
- specifically handles field constants 256
- expects `[Fact (p > 512)]` in the context
-/
syntax "field_to_nat" : tactic
macro_rules
  | `(tactic|field_to_nat) =>
    `(tactic|(
      repeat rw [ZMod.val_add] -- (a + b).val = (a.val + b.val) % p
      repeat rw [ZMod.val_mul] -- (a * b).val = (a.val * b.val) % p
      repeat rw [U32.val_eq_256]
      simp only [Nat.reducePow, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mod_eq_of_lt _]
      repeat linarith [‹Fact (_ > 512)›.elim]))

end U32
end
