import Clean.Circuit
import Clean.Utils.Tactics

/-!
Tests for `provable_struct_simp`, covering its three jobs:

* splitting constructor equalities into field-wise conjunctions,
* destructuring struct variables that appear in projections or against constructor
  literals / folded evals in equations (with field-based names),
* decomposing `eval` of constructor literals field-wise, while leaving opaque
  row-level facts (`eval s1 = eval s2`, plain `x = y`) whole.

The `have`/`exact` bodies double as shape assertions on the resulting goal state.
-/

namespace TestProvableStructSimp

structure TestInputs (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

structure SimpleStruct (F : Type) where
  a : F
  b : F
deriving ProvableStruct

structure NestedInputs (F : Type) where
  first : TestInputs F
  second : TestInputs F
deriving ProvableStruct

structure VectorStruct (F : Type) where
  xs : Vector F 2
  y : F
deriving ProvableStruct

-- Structure without ProvableStruct instance
structure NonProvableStruct (F : Type) where
  a : F
  b : F

/-! ## Splitting constructor equalities -/

-- Ordinary records without ProvableStruct should remain opaque.
set_option linter.unusedTactic false in
theorem test_non_provable_struct_not_split {F : Type} [FiniteField F]
    (h : (NonProvableStruct.mk 1 2 : NonProvableStruct F) = NonProvableStruct.mk 3 4) :
    (NonProvableStruct.mk 1 2 : NonProvableStruct F) = NonProvableStruct.mk 3 4 := by
  provable_struct_simp
  -- h must still be the unsplit constructor equality
  exact h

theorem test_struct_literal_eq_literal {F : Type} [FiniteField F]
    (h : (TestInputs.mk 1 2 3 : TestInputs F) = TestInputs.mk 4 5 6) :
    (1 : F) = 4 := by
  provable_struct_simp
  -- h : 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

theorem test_struct_literal_eq_variable {F : Type} [FiniteField F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  provable_struct_simp
  -- input is destructured, h : 1 = input_x ∧ 2 = input_y ∧ 3 = input_z
  exact h.1.symm

theorem test_struct_variable_eq_literal {F : Type} [FiniteField F] (input : TestInputs F)
    (h : input = TestInputs.mk 1 2 3) :
    input.x = 1 := by
  provable_struct_simp
  -- h : input_x = 1 ∧ input_y = 2 ∧ input_z = 3
  exact h.1

theorem test_multiple_equalities {F : Type} [FiniteField F] (input1 input2 : TestInputs F)
    (h1 : TestInputs.mk 1 2 3 = input1)
    (h2 : input2 = TestInputs.mk 4 5 6) :
    input1.x = 1 ∧ input2.y = 5 := by
  provable_struct_simp
  constructor
  · exact h1.1.symm
  · exact h2.2.1

theorem test_conjunction_with_struct_eq {F : Type} [FiniteField F] (input : TestInputs F) (x : F)
    (h : TestInputs.mk 1 2 3 = input ∧ x = 7) :
    input.x = 1 ∧ x = 7 := by
  provable_struct_simp
  constructor
  · exact h.1.1.symm
  · exact h.2

theorem test_nested_conjunctions {F : Type} [FiniteField F] (input1 input2 : TestInputs F) (x : F)
    (h : (TestInputs.mk 1 2 3 = input1 ∧ x = 7) ∧ input2 = TestInputs.mk 4 5 6) :
    input1.x = 1 ∧ input2.y = 5 := by
  provable_struct_simp
  constructor
  · exact h.1.1.1.symm
  · exact h.2.2.1

-- A plain variable-variable equality stays whole.
theorem test_with_base_and_non_base {F : Type} [FiniteField F] (input1 input2 input3 : TestInputs F) (x : F)
    (h : (TestInputs.mk 1 2 3 = input1 ∧ x = 7) ∧ input2 = input3) :
    input1.x = 1 := by
  provable_struct_simp
  have : input2 = input3 := h.2
  exact h.1.1.1.symm

/-! ## Destructuring struct variables -/

theorem test_decompose_simple {F : Type} [FiniteField F] (input : TestInputs F) :
    input.x + input.y + input.z = input.z + input.y + input.x := by
  provable_struct_simp
  -- input is destructured into field-named variables and no longer exists
  fail_if_success (exact input)
  have : F := input_x
  have : F := input_y
  have : F := input_z
  ring

theorem test_decompose_nested {F : Type} [FiniteField F] (input : NestedInputs F) :
    input.first.x + input.second.y = input.second.y + input.first.x := by
  provable_struct_simp
  -- both levels are destructured: the loop re-runs on the projected components
  fail_if_success (exact input)
  have : F := input_first_x
  have : F := input_second_y
  ring

theorem test_decompose_multiple {F : Type} [FiniteField F] (a : TestInputs F) (b : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  provable_struct_simp
  fail_if_success (exact a)
  fail_if_success (exact b)
  have : F := a_x
  have : F := a_y
  have : F := a_z
  have : F := b_x
  have : F := b_y
  have : F := b_z
  ring

theorem test_decompose_from_hypothesis {F : Type} [FiniteField F] (input : TestInputs F)
    (h : input.x = 5) : input.y + input.z = input.z + input.y := by
  provable_struct_simp
  fail_if_success (exact input)
  have : input_x = 5 := h
  ring

theorem test_decompose_multiple_hypotheses {F : Type} [FiniteField F] (a : TestInputs F) (b : TestInputs F)
    (h1 : a.x = b.y) (h2 : b.z = 10) : a.x + b.z = b.z + a.x := by
  provable_struct_simp
  fail_if_success (exact a)
  fail_if_success (exact b)
  have : a_x = b_y := h1
  have : b_z = 10 := h2
  ring

-- Variables not involved in any struct-specific fact staying opaque is asserted by
-- `test_whole_struct_equality`, `test_struct_in_function` and the `c` in
-- `test_selective_decompose` below.

set_option linter.unusedVariables false in
theorem test_selective_decompose {F : Type} [FiniteField F] (a : TestInputs F) (b : TestInputs F) (c : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  provable_struct_simp
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- c is not involved in any projection or equation, so it stays
  have : TestInputs F := c
  have : F := a_x
  have : F := b_y
  ring

-- A variable equated with a literal is destructured and the equality split,
-- in the hypothesis and in the goal.
theorem test_variable_literal_equation_in_goal {F : Type} [FiniteField F] (input : TestInputs F)
    (h : input = ⟨5, 3, 1⟩) :
    input = ⟨5, 3, 1⟩ := by
  provable_struct_simp
  exact h

set_option linter.unusedTactic false in
theorem test_whole_struct_equality {F : Type} [FiniteField F]
    (x : TestInputs F) (y : TestInputs F) (h : x = y) :
    x = y := by
  provable_struct_simp
  have : TestInputs F := x
  have : TestInputs F := y
  assumption

def processStruct {F : Type} [FiniteField F] (input : TestInputs F) : F :=
  input.x + input.y + input.z

-- A struct used only whole, inside a function application, stays opaque.
set_option linter.unusedTactic false in
theorem test_struct_in_function {F : Type} [FiniteField F]
    (input : TestInputs F) (h : processStruct input = 10) :
    processStruct input = 10 := by
  provable_struct_simp
  have : TestInputs F := input
  assumption

/-! ## Decomposing struct evaluation -/

lemma test_eval_eq_struct_literal {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3) :
    Expression.eval env x_var = 1 ∧ Expression.eval env y_var = 2 ∧ Expression.eval env z_var = 3 := by
  provable_struct_simp
  exact h

theorem test_struct_literal_eq_eval {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (x_var y_var z_var : Var field F)
    (h : TestInputs.mk 1 2 3 = eval env (TestInputs.mk x_var y_var z_var)) :
    1 = Expression.eval env x_var ∧ 2 = Expression.eval env y_var ∧ 3 = Expression.eval env z_var := by
  provable_struct_simp
  exact h

theorem test_eval_eq_struct_variable {F : Type} [FiniteField F] (env : ProverEnvironment F) (input : TestInputs F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = input) :
    eval env (TestInputs.mk x_var y_var z_var) = input := by
  provable_struct_simp
  -- both sides decompose: h and the goal are the same field-wise conjunction
  exact h

theorem test_eval_eq_decomposed_struct_variable {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (input_var : TestInputs (Expression F)) (input : TestInputs F)
    (h : eval env input_var = input) :
    eval env input_var.x = input.x := by
  provable_struct_simp
  exact h.1

-- The same decomposition when the input is written through the public `Var` alias.
theorem test_eval_eq_decomposed_var_struct {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (input_var : Var TestInputs F) (input : TestInputs F)
    (h : eval env input_var = input) :
    eval env input_var.x = input.x := by
  provable_struct_simp
  exact h.1

theorem test_eval_eq_decomposed_struct_variable_conjunction {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (input_var : TestInputs (Expression F)) (input : TestInputs F)
    (h : eval env input_var = input ∧ True) :
    eval env input_var.y = input.y := by
  provable_struct_simp
  exact h.1.2.1

-- The same decomposition when a field is itself a provable vector.
theorem test_eval_eq_decomposed_vector_struct {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (input_var : VectorStruct (Expression F)) (input : VectorStruct F)
    (h : eval env input_var = input ∧ True) :
    eval env input_var.y = input.y := by
  provable_struct_simp
  exact h.1.2

-- Projected whole-struct evals are reduced to component evals after decomposition.
theorem test_eval_projection_uses_decomposed_struct_eq {F : Type} [FiniteField F] (env : Environment F)
    (input_var : VectorStruct (Expression F)) (input : VectorStruct F)
    (h : eval env input_var = input)
    (hh : (eval env input_var).y = 1) :
    input.y = 1 := by
  provable_struct_simp
  simp only [h] at hh ⊢
  exact hh

theorem test_eval_in_conjunction {F : Type} [FiniteField F] (env : ProverEnvironment F) (x : F)
    (x_var y_var z_var : Var field F)
    (h : eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) :
    Expression.eval env x_var = 1 ∧ Expression.eval env y_var = 2 ∧ Expression.eval env z_var = 3 ∧ x = 7 := by
  provable_struct_simp
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

theorem test_nested_conjunctions_with_eval {F : Type} [FiniteField F] (env : ProverEnvironment F) (x : F)
    (x_var y_var z_var a_var b_var : Var field F)
    (h : (eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) ∧
         eval env (SimpleStruct.mk a_var b_var) = SimpleStruct.mk 8 9) :
    Expression.eval env x_var = 1 ∧ Expression.eval env a_var = 8 := by
  provable_struct_simp
  exact ⟨h.1.1.1, h.2.1⟩

theorem test_multiple_eval_expressions {F : Type} [FiniteField F] (env1 env2 : ProverEnvironment F)
    (x1_var y1_var z1_var : Var field F) (a2_var b2_var : Var field F)
    (h1 : eval env1 (TestInputs.mk x1_var y1_var z1_var) = TestInputs.mk 1 2 3)
    (h2 : eval env2 (SimpleStruct.mk a2_var b2_var) = SimpleStruct.mk 4 5) :
    Expression.eval env1 x1_var = 1 ∧ Expression.eval env2 b2_var = 5 := by
  provable_struct_simp
  exact ⟨h1.1, h2.2⟩

theorem test_complex_eval {F : Type} [FiniteField F] (env : ProverEnvironment F)
    (a_var b_var c_var d_var e_var : Var field F)
    (h : eval env (TestInputs.mk (a_var + b_var) (c_var * d_var) e_var) = TestInputs.mk 5 6 7) :
    Expression.eval env (a_var + b_var) = 5 ∧
    Expression.eval env (c_var * d_var) = 6 ∧
    Expression.eval env e_var = 7 := by
  provable_struct_simp
  exact h

-- `eval = eval` between opaque structs is a row-level fact and stays whole.
theorem test_conjunction_with_base_and_non_base {F : Type} [FiniteField F] (env : ProverEnvironment F) (x : F)
    (x_var y_var z_var : Var field F) (s1 s2 : Var SimpleStruct F)
    (h : (eval env (TestInputs.mk x_var y_var z_var) = TestInputs.mk 1 2 3 ∧ x = 7) ∧
         eval env s1 = eval env s2) :
    Expression.eval env x_var = 1 := by
  provable_struct_simp
  -- normalized to the `ProvableStruct.eval` spelling, but not split
  have : ProvableStruct.eval env.toEnvironment s1 = ProvableStruct.eval env.toEnvironment s2 := h.2
  exact h.1.1.1

end TestProvableStructSimp
