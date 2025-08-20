import Clean.Circuit.Provable
variable {F : Type} [Field F] {n : ℕ}


/- Cross-circuit communication of values with properties

   where "how many times" isn't relevant to the application.
-/

/- Generalization of Lookup.lean, where operations can provide looked-up values. I'm trying to replace Lookup.lean with this. -/

structure Property (F : Type) where
  name : String
  arity : ℕ
  Soundness : Vector F arity → Prop -- every use operation brings in Soundness from external circuits & tables
  Completeness : Vector F arity → Prop -- every yield operation provides Completeness to external circuits & tables
  imply_soundness : ∀ row, Completeness row → Soundness row

structure Use (F : Type) where
  property : Property F
  entry : Vector (Expression F) property.arity

structure Yield (F : Type) where
  property : Property F
  entry : Vector (Expression F) property.arity

instance [Repr F] : Repr (Use F) where
  reprPrec u _ := "(Use " ++ u.property.name ++ " " ++ repr u.entry ++ ")"

instance [Repr F] : Repr (Use F) where
  reprPrec y _ := "(Yield " ++ y.property.name ++ " " ++ repr y.entry ++ ")"
