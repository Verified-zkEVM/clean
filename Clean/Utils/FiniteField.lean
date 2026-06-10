/-
This file defines a typeclass `FiniteField` that abstracts the properties of finite fields
needed by circuit gadgets. The goal is to provide a common interface that both prime fields
(`ZMod p`) and binary fields (`GF(2^n)`) can satisfy, enabling gadgets to be written
generically over any finite field.

The key abstraction: every finite field element has a canonical embedding into `ℕ`
(for prime fields, this is `ZMod.val`; for binary fields, this interprets the
polynomial coefficients as a binary number). This embedding enables bit decomposition,
range checks, and size-dependent reasoning.

Part of issue #154: Generalize prime field assumption to cover binary fields.
-/
import Mathlib.Algebra.Field.ZMod
import Clean.Utils.Field

/--
`FiniteField` extends `Field` with a canonical embedding into `ℕ` and finiteness.
This captures the shared structure of prime fields and binary fields that circuit
gadgets rely on: the ability to decompose field elements into bits and reason
about their numeric value.
-/
class FiniteField (F : Type) extends Field F, Fintype F where
  /-- Canonical embedding of field elements into natural numbers. -/
  val : F → ℕ
  /-- Inverse of `val`: interpret a natural number (below the field size) as a field
  element. For prime fields this is `Nat.cast`; for binary fields it interprets the
  binary digits as polynomial coefficients. Note that `Nat.cast` would be wrong there:
  it reduces via the characteristic, collapsing `GF(2^n)` to `{0, 1}`. -/
  fromNat : ℕ → F
  /-- Every element's value is less than the field size. -/
  val_lt : ∀ x : F, val x < Fintype.card F
  /-- The embedding is injective (distinct elements have distinct values). -/
  val_injective : Function.Injective val
  /-- `fromNat` inverts `val` on naturals below the field size. -/
  val_fromNat : ∀ n < Fintype.card F, val (fromNat n) = n
  /-- Zero maps to zero. -/
  val_zero : val 0 = 0
  /-- One maps to one. -/
  val_one : val 1 = 1

namespace FiniteField

variable {F : Type} [FiniteField F]

/-- `fromNat` is a left inverse of `val`. -/
theorem fromNat_val (x : F) : fromNat (val x) = x :=
  val_injective (val_fromNat _ (val_lt x))

/-- The field has at least two elements (derived from `val_lt` and `val_one`). -/
theorem fieldSize_pos : Fintype.card F > 1 := by
  have := val_lt (1 : F); rwa [val_one] at this

/-- Two field elements are equal iff their values are equal. -/
theorem ext {x y : F} (h : val x = val y) : x = y :=
  val_injective h

/-- Two field elements are equal iff their values are equal. -/
theorem ext_iff {x y : F} : x = y ↔ val x = val y :=
  ⟨fun h => h ▸ rfl, ext⟩

end FiniteField

/-! ## Instance for prime fields (`F p = ZMod p`) -/

instance {p : ℕ} [Fact p.Prime] : FiniteField (F p) where
  val := ZMod.val
  fromNat n := (n : F p)
  val_lt := by
    intro x
    unfold F
    rw [ZMod.card]
    exact ZMod.val_lt x
  val_injective := by
    intro x y h
    exact FieldUtils.ext h
  val_fromNat := by
    intro n hn
    unfold F at *
    rw [ZMod.card] at hn
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  val_zero := ZMod.val_zero
  val_one := by
    rw [ZMod.val_one]

/-- On prime fields, `fromNat` is just `Nat.cast`. -/
@[simp] theorem FiniteField.fromNat_F {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (FiniteField.fromNat n : F p) = (n : F p) := rfl
