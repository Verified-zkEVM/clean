import Clean.Halo2.Configure

namespace Halo2.Tests.TestSelectorFree

variable {F : Type} [Field F]

/-! Representative shapes from gate bodies. -/

-- An ordinary arithmetic constraint.
example (a b c : Column .advice) :
    ∀ expression ∈
      ([queryAdvice a 0 * queryAdvice b 1 - queryAdvice c 0] :
        List (Expression F Query)),
      expression.SelectorFree := by
  selector_free

-- An advice-valued conditional/mux.
example (bit x y out : Column .advice) :
    ∀ expression ∈
      ([queryAdvice bit 0 * queryAdvice x 0 +
          (1 - queryAdvice bit 0) * queryAdvice y 0 -
          queryAdvice out 0] :
        List (Expression F Query)),
      expression.SelectorFree := by
  selector_free

-- A fixed column used as a boolean pseudo-selector is still selector-free.
example (q : Column .fixed) :
    ∀ expression ∈
      ([queryFixed q * (queryFixed q - 1)] :
        List (Expression F Query)),
      expression.SelectorFree := by
  selector_free

-- A mixture of all non-selector query kinds and rotations.
example (a : Column .advice) (q : Column .fixed) (i : Column .instance) :
    ∀ expression ∈
      ([queryFixed q * queryAdvice a (-1) +
          queryInstance i 1 * queryAdvice a 2] :
        List (Expression F Query)),
      expression.SelectorFree := by
  selector_free

-- The exact public API: the selector-freedom proof is inserted by default.
example (s : Selector) (a b c d : Column .advice) : Gate F :=
  Gate.withSelector "representative" s
    [queryAdvice a 0, queryAdvice b 0, queryAdvice c 0, queryAdvice d 0,
      queryAdvice a 1, queryAdvice b (-1)]
    [("product",
      (queryAdvice a 0 * queryAdvice b 0) *
        (queryAdvice c 0 - queryAdvice d 0)),
    ("sum", queryAdvice a 1 + queryAdvice b (-1))]

end Halo2.Tests.TestSelectorFree
