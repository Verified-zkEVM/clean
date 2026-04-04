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
  /-- Every element's value is less than the field size. -/
  val_lt : ∀ x : F, val x < Fintype.card F
  /-- The embedding is injective (distinct elements have distinct values). -/
  val_injective : Function.Injective val
  /-- Zero maps to zero. -/
  val_zero : val 0 = 0
  /-- One maps to one. -/
  val_one : val 1 = 1

namespace FiniteField

variable {F : Type} [FiniteField F]

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
  val_lt := by
    intro x
    rw [ZMod.card]
    exact ZMod.val_lt x
  val_injective := by
    intro x y h
    exact FieldUtils.ext h
  val_zero := ZMod.val_zero
  val_one := by
    rw [ZMod.val_one]
