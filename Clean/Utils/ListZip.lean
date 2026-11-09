import Mathlib.Data.List.Basic

namespace List

/-- Zipping a concatenation consumes the second list in matching prefixes. -/
theorem zip_append_drop {α β : Type*} (xs ys : List α) (zs : List β) :
    (xs ++ ys).zip zs = xs.zip zs ++ ys.zip (zs.drop xs.length) := by
  induction xs generalizing zs with
  | nil => simp
  | cons x xs ih =>
      cases zs <;> simp [ih]

end List
