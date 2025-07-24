import Clean.Utils.Tactics
import Clean.Circuit.Provable
import Clean.Circuit.Expression

namespace TestSimplifyProvableStructEval

-- Test structure with ProvableStruct instance
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F

instance : ProvableStruct TestInputs where
  components := [field, field, field]
  toComponents := fun { x, y, z } => .cons x (.cons y (.cons z .nil))
  fromComponents := fun (.cons x (.cons y (.cons z .nil))) => { x, y, z }

-- Another test structure
structure SimpleStruct (F : Type) where
  a : F
  b : F

instance : ProvableStruct SimpleStruct where
  components := [field, field]
  toComponents := fun { a, b } => .cons a (.cons b .nil)
  fromComponents := fun (.cons a (.cons b .nil)) => { a, b }

-- Test eval with struct literal on RHS
lemma test_eval_eq_struct_literal {F : Type} [Field F] (env : Environment F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3) :
    Expression.eval env x_var = 1 ∧ Expression.eval env y_var = 2 ∧ Expression.eval env z_var = 3 := by
  fail_if_no_progress simplify_provable_struct_eval
  -- Now h should be literal = literal
  rw [TestInputs.mk.injEq] at h
  exact h

-- Test eval with struct literal on LHS
theorem test_struct_literal_eq_eval {F : Type} [Field F] (env : Environment F)
    (x_var y_var z_var : Var field F)
    (h : TestInputs.mk 1 2 3 = eval env (TestInputs.mk x_var y_var z_var)) :
    1 = Expression.eval env x_var ∧ 2 = Expression.eval env y_var ∧ 3 = Expression.eval env z_var := by
  fail_if_no_progress simplify_provable_struct_eval
  -- Now h should be literal = literal
  rw [TestInputs.mk.injEq] at h
  exact h

-- Test eval with struct variable
theorem test_eval_eq_struct_variable {F : Type} [Field F] (env : Environment F) (input : TestInputs F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = input) :
    TestInputs.mk (Expression.eval env x_var) (Expression.eval env y_var) (Expression.eval env z_var) = input := by
  -- determine if should succeed or fail
  simplify_provable_struct_eval
  -- This should simplify the eval expression
  exact h

-- Test eval inside conjunctions
theorem test_eval_in_conjunction {F : Type} [Field F] (env : Environment F) (x : F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) :
    Expression.eval env x_var = 1 ∧ Expression.eval env y_var = 2 ∧ Expression.eval env z_var = 3 ∧ x = 7 := by
  simplify_provable_struct_eval
  -- now h should be literal = literal
  rw [TestInputs.mk.injEq] at h
  constructor
  · exact h.1.1
  · constructor
    · exact h.1.2.1
    · constructor
      · exact h.1.2.2
      · exact h.2

-- Test nested conjunctions with eval
theorem test_nested_conjunctions_with_eval {F : Type} [Field F] (env : Environment F) (x : F)
    (x_var y_var z_var a_var b_var : Var field F)
    (h : (eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) ∧
         eval env (SimpleStruct.mk a_var b_var) = SimpleStruct.mk 8 9) :
    Expression.eval env x_var = 1 ∧ Expression.eval env a_var = 8 := by
  simplify_provable_struct_eval
  -- now h should be a conjunction of literal = literal
  simp only [TestInputs.mk.injEq, SimpleStruct.mk.injEq] at h
  -- Both eval equalities should be simplified
  constructor
  · exact h.1.1.1
  · exact h.2.1

-- Test multiple eval expressions
theorem test_multiple_eval_expressions {F : Type} [Field F] (env1 env2 : Environment F)
    (x1_var y1_var z1_var : Var field F) (a2_var b2_var : Var field F)
    (h1 : eval env1 (TestInputs.mk x1_var y1_var z1_var) = TestInputs.mk 1 2 3)
    (h2 : eval env2 (SimpleStruct.mk a2_var b2_var) = SimpleStruct.mk 4 5) :
    Expression.eval env1 x1_var = 1 ∧ Expression.eval env2 b2_var = 5 := by
  simplify_provable_struct_eval
  -- now h should be a conjunction of literal = literal
  simp only [TestInputs.mk.injEq, SimpleStruct.mk.injEq] at h1 h2
  -- Both hypotheses should be simplified
  constructor
  · exact h1.1
  · exact h2.2

-- Test with complex eval expressions
theorem test_complex_eval {F : Type} [Field F] (env : Environment F)
    (a_var b_var c_var d_var e_var : Var field F)
    (h : eval env (TestInputs.mk (a_var + b_var) (c_var * d_var) e_var) = TestInputs.mk 5 6 7) :
    Expression.eval env (a_var + b_var) = 5 ∧
    Expression.eval env (c_var * d_var) = 6 ∧
    Expression.eval env e_var = 7 := by
  simplify_provable_struct_eval
  -- Should simplify the eval expression
  -- now h should be a conjunction of literal = literal
  simp only [TestInputs.mk.injEq, SimpleStruct.mk.injEq] at h
  exact h

-- Test conjunction with an eval to be decomposed and another eval not to be decomposed
theorem test_conjunction_with_base_and_non_base {F : Type} [Field F] (env : Environment F) (x : F)
    (x_var y_var z_var : Var field F) (s1 s2 : Var SimpleStruct F)
    (h : (eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) ∧
         eval env s1 = eval env s2) :
    Expression.eval env x_var = 1 := by
  simplify_provable_struct_eval
  -- eval env s1 = eval env s2 should be intact
  simp only [TestInputs.mk.injEq] at h
  -- Since eval env s1 = eval env s2 should be intact, this simplification should fail
  fail_if_success simp only [SimpleStruct.mk.injEq] at h
  -- Both eval equalities should be simplified
  exact h.1.1.1

end TestSimplifyProvableStructEval
