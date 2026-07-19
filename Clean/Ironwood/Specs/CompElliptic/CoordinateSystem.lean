/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Coordinate systems

A `CoordinateSystem R` represents an abelian group by a carrier type `R`. It bundles a validity
predicate `Valid`, an equivalence `Rel` on valid representatives, and computable `zero` / `add` /
`neg`. The operations preserve `Valid`, respect `Rel`, and obey the abelian-group axioms up to `Rel`.

`Rel` is `Eq` for injective systems (typically affine coordinates). Otherwise it is non-trivial:
for projective or Jacobian coordinates it is the scaling equivalence, where `(X : Y : Z)` is a class.

`CoordinateSystem.Quot` is the group element type: valid representatives modulo `Rel`. Its
`AddCommGroup` is derived here, once. So a curve form gets its group by giving a `CoordinateSystem`;
the quotient machinery lives here, not in each form.

The name follows the [Explicit-Formulas Database](https://www.hyperelliptic.org/EFD/). This is *not*
a "represented group" in the sense of the
[Zcash Protocol Specification §5.4.9](https://zips.z.cash/protocol/protocol.pdf#concretepairing) —
that names a group with a bit-sequence `repr` / `abst` encoding, a separate abstraction. See
`../README.md` and `design/naming-survey.md`.
-/

namespace CompElliptic

universe u

/-- A coordinate system representing an abelian group by carrier type `R` (see the module doc). -/
structure CoordinateSystem (R : Type u) where
  /-- Which carrier values are representatives. -/
  Valid : R → Prop
  /-- When two valid representatives denote the same group element (`Eq` for injective systems). -/
  Rel : R → R → Prop
  zero : R
  add : R → R → R
  neg : R → R
  valid_zero : Valid zero
  valid_add : ∀ {a b : R}, Valid a → Valid b → Valid (add a b)
  valid_neg : ∀ {a : R}, Valid a → Valid (neg a)
  rel_refl : ∀ {a : R}, Valid a → Rel a a
  rel_symm : ∀ {a b : R}, Rel a b → Rel b a
  rel_trans : ∀ {a b c : R}, Rel a b → Rel b c → Rel a c
  add_congr : ∀ {a a' b b' : R}, Rel a a' → Rel b b' → Rel (add a b) (add a' b')
  neg_congr : ∀ {a a' : R}, Rel a a' → Rel (neg a) (neg a')
  zero_add : ∀ {a : R}, Valid a → Rel (add zero a) a
  add_zero : ∀ {a : R}, Valid a → Rel (add a zero) a
  add_assoc : ∀ {a b c : R}, Valid a → Valid b → Valid c →
    Rel (add (add a b) c) (add a (add b c))
  add_comm : ∀ {a b : R}, Valid a → Valid b → Rel (add a b) (add b a)
  neg_add : ∀ {a : R}, Valid a → Rel (add (neg a) a) zero

namespace CoordinateSystem

variable {R : Type u} (P : CoordinateSystem R)

/-- A representation: a valid carrier value. -/
def Repr : Type u := {a : R // P.Valid a}

/-- Representations, related when they denote the same group element. -/
instance setoid : Setoid P.Repr where
  r a b := P.Rel a.1 b.1
  iseqv := ⟨fun a => P.rel_refl a.2, fun h => P.rel_symm h, fun h₁ h₂ => P.rel_trans h₁ h₂⟩

/-- The group element type: representations modulo `Rel`. -/
def Quot : Type u := Quotient P.setoid

instance : Zero P.Quot := ⟨Quotient.mk _ ⟨P.zero, P.valid_zero⟩⟩

instance : Add P.Quot :=
  ⟨Quotient.lift₂ (fun a b => Quotient.mk _ ⟨P.add a.1 b.1, P.valid_add a.2 b.2⟩)
    (fun _ _ _ _ ha hb => Quotient.sound (P.add_congr ha hb))⟩

instance : Neg P.Quot :=
  ⟨Quotient.lift (fun a => Quotient.mk _ ⟨P.neg a.1, P.valid_neg a.2⟩)
    (fun _ _ ha => Quotient.sound (P.neg_congr ha))⟩

/-- The derived abelian-group structure on the group element type. -/
instance : AddCommGroup P.Quot where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    rintro x y z
    refine Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound (P.add_assoc a.2 b.2 c.2))
  zero_add := by
    rintro x
    refine Quotient.inductionOn x (fun a => Quotient.sound (P.zero_add a.2))
  add_zero := by
    rintro x
    refine Quotient.inductionOn x (fun a => Quotient.sound (P.add_zero a.2))
  add_comm := by
    rintro x y
    refine Quotient.inductionOn₂ x y (fun a b => Quotient.sound (P.add_comm a.2 b.2))
  neg_add_cancel := by
    rintro x
    refine Quotient.inductionOn x (fun a => Quotient.sound (P.neg_add a.2))

end CoordinateSystem

end CompElliptic
