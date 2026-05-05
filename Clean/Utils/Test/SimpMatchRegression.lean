/-!
Minimal reproducer for a Lean 4.29 simplification regression.

In Lean 4.28, `simp only [fromComponents, comps] at h` turns `h` into a
constructor equality. In Lean 4.29, it leaves a dependent `HList` match that is
definitionally equal to that constructor equality.
-/

namespace SimpMatchRegression

abbrev TypeMap := Type → Type

class ProvableType (M : TypeMap) where

structure WithProvableType where
  type : TypeMap
  provableType : ProvableType type

abbrev field : TypeMap := id

instance : ProvableType field where

inductive HList (F : Type) : List WithProvableType → Type 1 where
  | nil : HList F []
  | cons : ∀ {a as}, a.type F → HList F as → HList F (a :: as)

structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F

def comps (M : TypeMap) [ProvableType M] : List WithProvableType :=
  [{ type := field, provableType := inferInstance },
   { type := M, provableType := inferInstance },
   { type := M, provableType := inferInstance }]

def fromComponents {M : TypeMap} [ProvableType M] {F : Type} : HList F (comps M) → Inputs M F
  | .cons selector (.cons ifTrue (.cons ifFalse .nil)) => { selector, ifTrue, ifFalse }

-- set_option backward.isDefEq.respectTransparency false

example {M : TypeMap} [ProvableType M] {F : Type}
    (selector : F) (ifTrue ifFalse : M F) (input : Inputs M F)
    (h : fromComponents (.cons selector (.cons ifTrue (.cons ifFalse .nil))) = input) :
    True := by
  simp only [fromComponents, comps] at h
  rcases input with ⟨inputSelector, inputIfTrue, inputIfFalse⟩
  -- Lean 4.29 leaves a match here. This proves it is definitionally the
  -- constructor equality that Lean 4.28 exposed directly.
  change ({ selector := selector, ifTrue := ifTrue, ifFalse := ifFalse } : Inputs M F)
    = { selector := inputSelector, ifTrue := inputIfTrue, ifFalse := inputIfFalse } at h
  simp only [Inputs.mk.injEq] at h
  trivial

end SimpMatchRegression
