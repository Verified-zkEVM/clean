import Clean.Circuit.EvalDerive
import Clean.Gadgets.Addition8.Addition8FullCarry

variable {F : Type} [Field F]

-- Test 1: Using the new lemmas with the pattern from Addition8FullCarry
example {env : Environment F} {input_var : Var fieldTriple F} 
    {x y carry_in : F}
    (h_inputs : eval env input_var = (x, y, carry_in))
    (h_x : IsBool x) (h_y : IsBool y) (h_carry : IsBool carry_in) :
    input_var.1.eval env = x ∧ input_var.2.1.eval env = y ∧ input_var.2.2.eval env = carry_in := by
  -- Method 1: Direct application
  constructor
  · rw [EvalDerive.eval_triple_1, h_inputs]
  constructor  
  · rw [EvalDerive.eval_triple_2_1, h_inputs]
  · rw [EvalDerive.eval_triple_2_2, h_inputs]

-- Test 2: Using the tactic
example {env : Environment F} {input_var : Var (ProvablePair (ProvablePair field field) field) F} 
    {x y z : F}
    (h_inputs : eval env input_var = ((x, y), z)) :
    eval env input_var.1 = (x, y) ∧ eval env input_var.2 = z := by
  eval_decompose h_inputs
  rw [h_inputs]
  exact ⟨rfl, rfl⟩

-- Test 3: Nested pairs
example {env : Environment F} {input_var : Var (ProvablePair (ProvablePair field field) field) F} 
    {x y z : F}
    (h_inputs : eval env input_var = ((x, y), z)) :
    eval env input_var.1.1 = x ∧ eval env input_var.1.2 = y ∧ eval env input_var.2 = z := by
  eval_decompose h_inputs
  rw [h_inputs]
  exact ⟨rfl, rfl, rfl⟩

-- Test 4: Vector indexing
example {env : Environment F} {vec_var : Var (fields 5) F} {vec : Vector F 5}
    (h_vec : eval env vec_var = vec) :
    vec_var[0].eval env = vec[0] ∧ vec_var[1].eval env = vec[1] := by
  constructor
  · rw [EvalDerive.eval_fields_index, h_vec]
  · rw [EvalDerive.eval_fields_index, h_vec]

-- Test 5: More complex example with ProvableVector
example {env : Environment F} {vec_var : Var (ProvableVector field 3) F} {vec : Vector F 3}
    (h_vec : eval env vec_var = vec) :
    eval env vec_var[0] = vec[0] ∧ eval env vec_var[1] = vec[1] ∧ eval env vec_var[2] = vec[2] := by
  constructor
  · rw [EvalDerive.eval_provable_vector_index, h_vec]
  constructor
  · rw [EvalDerive.eval_provable_vector_index, h_vec]
  · rw [EvalDerive.eval_provable_vector_index, h_vec]