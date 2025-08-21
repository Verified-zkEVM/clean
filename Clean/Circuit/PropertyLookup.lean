import Clean.Circuit.Provable
variable {F : Type} [Field F] {n : ℕ}


/- Cross-circuit communication of values with properties

   where "how many times" isn't relevant to the application.
-/

/- Generalization of Lookup.lean, where operations can provide looked-up values. I'm trying to replace Lookup.lean with this. -/

structure Property (F : Type) where
  name : String
  arity : ℕ
  Pred : Vector F arity → Prop -- every use operation brings in Pred from external circuits & tables, every yield operation provides Pred externally

def Property.eval (property : Property F) (env : Environment F) (entry : Vector (Expression F) property.arity) :=
  property.Pred (entry.map env)

structure Use (F : Type) where
  property : Property F
  entry : Vector (Expression F) property.arity

structure Yield (F : Type) where
  property : Property F
  entry : Vector (Expression F) property.arity

def Yield.valid (y : Yield F) (env : Environment F) :=
  y.property.eval env y.entry

instance [Repr F] : Repr (Use F) where
  reprPrec u _ := "(Use " ++ u.property.name ++ " " ++ repr u.entry ++ ")"

instance [Repr F] : Repr (Yield F) where
  reprPrec y _ := "(Yield " ++ y.property.name ++ " " ++ repr y.entry ++ ")"

/- Avoiding circular reasoning.

  Problem

  When there's a property Odd for odd numbers, and when there are
  - (Use Odd 2)
  - (Yield Odd 2)
  we have to avoid doing this:
  1. (Use Odd 2) lets us prove the proposition 'Odd 2'
  2. The proposition 'Odd 2' lets us do (Yield Odd 2)

  Approach

  Keeping track of what's known to be yielded. During the soundness proof,
  * proving the property at the yield site produces an Yielded token.
  * using Yielded token at the use site produces the proven property.

  Alternative

  A well-founded relation on properties' would work, all specs will be relative to a
  downward-closed set of properties.
-/

def Yielded (y : Yield F) (env : Environment F) := y.valid env
