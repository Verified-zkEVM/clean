import Clean.Halo2.Keygen.Semantics

/-!
# Selector-compressed gate soundness

Halo 2 replaces every configured selector with a root-finding expression over a
packed fixed column. At a row where a gate is enabled, that expression is nonzero
but need not evaluate to one.

Every `Gate` carries exactly the one-sided semantic law needed at this boundary:
if its verifier-side polynomial vanishes with a nonzero value substituted for its
selector, then the same polynomial vanishes under Clean's selector-one,
foreign-selectors-zero valuation. No exact scaling equation or converse is required.
-/

namespace Halo2

namespace Expression

variable {F : Type} [Field F]

/--
If a verifier-side valuation agrees with a Clean environment on ordinary
queries, the enabled-gate valuation evaluates every expression exactly as
Clean's selector-one/foreign-selectors-zero valuation.
-/
theorem eval_enabledGateValuation_eq_queryEval
    (valuation : Query → F) (environment : Environment F)
    (selector : Selector) (row : ℤ)
    (expression : Expression F Query)
    (hfixed : ∀ column rotation,
      valuation (.fixed column rotation) =
        environment.fixed column (row + rotation))
    (hadvice : ∀ column rotation,
      valuation (.advice column rotation) =
        environment.advice column (row + rotation))
    (hinstance : ∀ column rotation,
      valuation (.instance column rotation) =
        environment.inst column (row + rotation)) :
    expression.eval (enabledGateValuation selector valuation) =
      expression.eval
        (Query.eval environment
          (fun index => if index = selector.index then 1 else 0) row) := by
  congr 1
  funext query
  cases query with
  | selector other =>
      simp [enabledGateValuation, Query.eval]
  | fixed column rotation =>
      exact hfixed column rotation
  | advice column rotation =>
      exact hadvice column rotation
  | «instance» column rotation =>
      exact hinstance column rotation

/--
The generic one-sided row-evaluation bridge for a well-formed gate constraint.

Selector compression supplies the substituted valuation and a nonzero value for
the gate's distinguished selector. The gate-owned law then transports verifier-side
vanishing to Clean's enabled-gate valuation.
-/
theorem eval_substSelectorMap_zero_imp_queryEval_zero
    (map : ℕ → Option SelCompress)
    (valuation : Query → F) (environment : Environment F)
    (expression : Expression F Query)
    (selector : Selector) (compressed : SelCompress) (row : ℤ)
    (hwellFormed :
      ∀ (base : Query → F) (scale : F), scale ≠ 0 →
        expression.eval (replaceSelectorValue selector scale base) = 0 →
          expression.eval (enabledGateValuation selector base) = 0)
    (hmap : map selector.index = some compressed)
    (hscale : (selReplacement compressed).eval valuation ≠ 0)
    (hfixed : ∀ column rotation,
      valuation (.fixed column rotation) =
        environment.fixed column (row + rotation))
    (hadvice : ∀ column rotation,
      valuation (.advice column rotation) =
        environment.advice column (row + rotation))
    (hinstance : ∀ column rotation,
      valuation (.instance column rotation) =
        environment.inst column (row + rotation))
    (hzero : (substSelectorMap map expression).eval valuation = 0) :
    expression.eval
      (Query.eval environment
        (fun index => if index = selector.index then 1 else 0) row) = 0 := by
  rw [substSelectorMap_eval] at hzero
  let scale := (selReplacement compressed).eval valuation
  have hreplace :
      replaceSelectorValue selector scale
          (substValuation map valuation) =
        substValuation map valuation := by
    funext query
    cases query with
    | selector other =>
        by_cases hindex : other.index = selector.index
        · simp [replaceSelectorValue, substValuation, scale,
            hindex, hmap]
        · simp [replaceSelectorValue, hindex]
    | fixed column rotation => rfl
    | advice column rotation => rfl
    | «instance» column rotation => rfl
  have henabled :
      enabledGateValuation selector (substValuation map valuation) =
        enabledGateValuation selector valuation := by
    funext query
    cases query <;> rfl
  have hclean :
      expression.eval
          (enabledGateValuation selector
            (substValuation map valuation)) = 0 := by
    apply hwellFormed (substValuation map valuation) scale hscale
    rw [hreplace]
    exact hzero
  rw [henabled] at hclean
  rw [eval_enabledGateValuation_eq_queryEval valuation environment
    selector row expression hfixed hadvice hinstance] at hclean
  exact hclean

end Expression

end Halo2
