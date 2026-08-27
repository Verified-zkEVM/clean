import Lean.Elab.Tactic
import Clean.Halo2.Expression

/-!
# Selector-freedom tactic

`selector_free` discharges the routine side condition that ungated constraint
expressions contain no selector queries. It structurally normalizes concrete expression
and list syntax; it does not use a decision procedure. Expression-building helpers can
join the structural reduction set with `@[selector_free]`.
-/

namespace Halo2

/-- A product fold is selector-free exactly when its seed and every factor are.

This covers gate helpers which construct a polynomial over a symbolic list or range,
without unfolding that list at the call site. -/
@[selector_free]
theorem Expression.selectorFree_foldl_mul {F α : Type}
    (xs : List α) (factor : α → Expression F Query)
    (acc : Expression F Query) :
    (xs.foldl (fun product x => product * factor x) acc).SelectorFree ↔
      acc.SelectorFree ∧ ∀ x ∈ xs, (factor x).SelectorFree := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, Expression.SelectorFree, and_assoc]

/-- Prove concrete selector-freedom goals built from the standard query helpers. -/
macro "selector_free" : tactic =>
  `(tactic| simp_all! +zetaDelta [selector_free])

end Halo2
