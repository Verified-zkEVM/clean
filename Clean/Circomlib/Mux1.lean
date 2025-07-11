import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean


namespace Circomlib
open Circuit
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom
-/

namespace MultiMux1

structure Inputs (n : ℕ) (F : Type) where
  c : ProvableVector (ProvablePair field field) n F  -- n pairs of constants
  s : F                                               -- selector

instance {n : ℕ} : ProvableStruct (Inputs n) where
  components := [ProvableVector (ProvablePair field field) n, field]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template MultiMux1(n) {
    signal input c[n][2]; // Constants
    signal input s; // Selector
    signal output out[n];

    for (var i=0; i < n; i++) {
        out[i] <== (c[i][1] - c[i][0])*s + c[i][0];
    }
}
-/
def main (n: ℕ) (input : Var (Inputs n) (F p)) := do
  let { c, s } := input

  -- Witness and constrain output vector
  let out <== c.provable_map field fun (c0, c1) =>
    (c1 - c0) * s + c0
  return out

lemma Vector.mapRange_one {α : Type} (f : ℕ → α) :
  Vector.mapRange 1 f = #v[f 0] := by
  rfl

-- Helper lemmas for vector operations (to be proved later)
lemma Vector.getElem_flatten_singleton {α : Type} {n : ℕ} (v : Vector (Vector α 1) n) (i : ℕ) (hi : i < n) :
    v.flatten[i] = (v[i])[0] := by
  simp only [Vector.getElem_flatten, Nat.div_one]
  congr
  omega

lemma Vector.getElem_map_singleton_flatten {α β : Type} {n : ℕ} (v : Vector α n) (f : α → β) (i : ℕ) (hi : i < n) :
    (v.map (fun x => #v[f x])).flatten[i] = f (v[i]) := by
  rw [Vector.getElem_flatten_singleton (v.map (fun x => #v[f x])) i hi]
  simp only [Vector.getElem_map (fun x => #v[f x]) hi]
  rfl

-- Note: Use the existing lemma getElem_eval_vector from Provable.lean instead

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n
  localLength_eq := by
    intros input offset
    simp only [main, circuit_norm]
    ring
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]
    ring

  Assumptions input :=
    let ⟨c, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      output[i] = if s = 0 then (c[i]).1 else (c[i]).2

  soundness := by
    simp only [circuit_norm, main]
    intro offset env input_var input h_input h_assumptions h_output
    -- We need to show the spec holds for all i < n
    intro i hi
    -- The output at position i is (c[i][1] - c[i][0]) * s + c[i][0]
    -- We need to show this equals if s = 0 then c[i][0] else c[i][1]

    -- First, understand what h_output says
    -- eval env (varFromOffset (ProvableVector field n) offset) =
    -- eval env (input_var.c.provable_map field fun x => (x.2 - x.1) * input_var.s + x.1)

    -- This means the i-th elements are also equal
    have h_eq : eval env (varFromOffset (ProvableVector field n) offset) =
                eval env (input_var.c.provable_map field fun x => (x.2 - x.1) * input_var.s + x.1) := h_output

    -- Now get the i-th element equality
    have h_output_i : Expression.eval env ((varFromOffset (ProvableVector field n) offset)[i]) =
                      Expression.eval env ((input_var.c.provable_map field fun x => (x.2 - x.1) * input_var.s + x.1)[i]) := by
      simp only [eval_vector] at h_eq
      -- Extract the i-th element from both sides
      have h_vec := congrArg (fun v => v[i]) h_eq
      simp only [Vector.getElem_map] at h_vec
      exact h_vec

    -- The issue is that varFromOffset returns a Var (ProvableVector field n)
    -- which is Vector (field (Expression (F p))) n
    -- But in the goal we need Vector (Expression (F p)) n

    -- Let's unfold what varFromOffset actually gives us
    simp only [varFromOffset_vector, eval_vector] at h_output_i ⊢

    -- Simplify the left side first
    simp only [Vector.getElem_mapRange] at h_output_i ⊢
    simp only [size, mul_one] at h_output_i ⊢

    -- Now we can rewrite
    rw [h_output_i]
    -- Now simplify the right side step by step
    simp only [ProvableVector.provable_map, Vector.getElem_map]

    -- Extract values from h_input
    -- h_input says: { c := eval env input_var.c, s := Expression.eval env input_var.s } = input
    -- So: eval env input_var.c = input.c
    have h_c : eval env input_var.c = input.c := by
      rw [← h_input]
    have h_s : Expression.eval env input_var.s = input.s := by
      rw [← h_input]

    -- Now we need to evaluate the expression
    -- The goal is: Expression.eval env ((input_var.c[i].2 - input_var.c[i].1) * input_var.s + input_var.c[i].1)
    simp only [Expression.eval]

    -- We have input_var.c : Var (ProvableVector (ProvablePair field field) n)
    -- So eval env input_var.c : Vector (field (F p) × field (F p)) n
    -- And (eval env input_var.c)[i] : field (F p) × field (F p)

    -- Get the pair at index i
    have h_ci : (eval env input_var.c : ProvableVector _ _ _)[i] = input.c[i] := by
      rw [h_c]

    -- Now we can work with the components
    rw [← h_s]
    rw [← h_c]

    -- Extract the fact that s is boolean
    -- IsBool means s = 0 ∨ s = 1
    cases h_assumptions with
      | inl h0 =>
        -- When s = 0
        rw [← h_s] at h0
        rw [h0]
        simp only [mul_zero, add_zero, if_pos rfl]
        simp only [id_eq, zero_add, ↓reduceIte]
        symm
        calc
          _ = (eval (α := ProvablePair _ _) env input_var.c[i]).1 := by
            congr
            exact (getElem_eval_vector env input_var.c i hi).symm
          _ = _ := by
            -- eval on a pair evaluates each component
            rfl
      | inr h1 =>
        -- When s = 1
        rw [← h_s] at h1
        rw [h1]
        simp only [mul_one, if_neg (by norm_num : (1 : F p) ≠ 0)]
        simp only [id_eq, neg_mul, one_mul, neg_add_cancel_right]
        -- Need to show: Expression.eval env input_var.c[i].2 = (eval env input_var.c)[i].2
        symm
        calc
          _ = (eval (α := ProvablePair _ _) env input_var.c[i]).2 := by
            congr
            exact (getElem_eval_vector env input_var.c i hi).symm
          _ = _ := by
            rfl

  completeness := by
    simp only [circuit_norm, main]
    intro offset env input_var h_env input h_input h_assumptions
    -- We need to show that the witnessed values equal the computed expressions
    ext i hi
    -- Left side: eval of varFromOffset
    simp only [varFromOffset_vector, eval_vector, Vector.getElem_map, Vector.getElem_mapRange]
    simp only [varFromOffset, size, mul_one]
    -- Use eval_fromVars lemma
    rw [ProvableType.eval_fromVars]
    -- Now simplify fromElements for field (which has size 1)
    -- The mapRange has size 1, so we get a single element vector
    simp only [Vector.mapRange_one, Vector.map_singleton, add_zero]
    -- The match on a singleton vector returns the single element
    simp only [fromElements]
    -- Now simplify the left side: Expression.eval env (var { index := offset + 1 * i })
    simp only [Expression.eval, mul_one]
    -- Right side: eval of the computed expression
    simp only [eval_vector, Vector.getElem_map, ProvableVector.provable_map]
    -- Now we have env.get (offset + 1 * i) on the left
    -- Simplify 1 * i to i
    simp only [one_mul]
    -- Use h_env which tells us this equals the right side
    have h_env_i := h_env ⟨i, by simp only [mul_one]; exact hi⟩
    simp only [Fin.val_mk, mul_one] at h_env_i
    rw [h_env_i]
    -- Now we need to show the right side of h_env_i equals what we want
    -- toElements for ProvableVector field n creates a vector of singletons then flattens
    simp only [toElements]
    -- We need to show:
    -- (Vector.map toElements (eval env (provable_map ...))).flatten[i] = eval env (...)
    rw [Vector.getElem_map_singleton_flatten]
    -- Now we have: toElements (eval env (provable_map ...)[i]) = eval env (...)
    -- Since toElements for field is just #v[x], and we want the single element
    -- Left side: (eval env (input_var.c.provable_map field fun x ↦ (x.2 - x.1) * input_var.s + x.1))[i]
    · simp only [eval_vector, Vector.getElem_map, ProvableVector.provable_map]
      -- Now the goal is solved by definitional equality
    · exact hi

end MultiMux1

namespace Mux1

structure Inputs (F : Type) where
  c : fields 2 F  -- 2 constants
  s : F           -- selector

instance : ProvableStruct Inputs where
  components := [fields 2, field]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template Mux1() {
    var i;
    signal input c[2]; // Constants
    signal input s; // Selector
    signal output out;

    component mux = MultiMux1(1);

    for (i=0; i<2; i++) {
        mux.c[0][i] <== c[i];
    }

    s ==> mux.s;

    mux.out[0] ==> out;
}
-/
def main (input : Var Inputs (F p)) := do
  let { c, s } := input

  -- Call MultiMux1 with n=1
  let mux_out ← MultiMux1.circuit 1 { c := #v[(c[0], c[1])], s }
  return mux_out[0]

def circuit : FormalCircuit (F p) Inputs field where
  main := main

  localLength _ := 1
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    -- The goal is about MultiMux1.circuit's localLength with n=1
    -- which is defined as n = 1
    rfl
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    output = if s = 0 then c[0] else c[1]

  soundness := by
    simp only [circuit_norm, main]
    intro offset env input_var input h_input h_assumptions h_subcircuit_sound
    simp only [MultiMux1.circuit, subcircuit, circuit_norm, FormalCircuit.toSubcircuit] at h_subcircuit_sound h_assumptions ⊢
    have h_asm' : IsBool (Expression.eval env input_var.s) := by
      rw [← h_input] at h_assumptions
      exact h_assumptions
    specialize h_subcircuit_sound h_asm' 0 (by omega)
    rw [h_subcircuit_sound]
    -- Now we need to show the RHS equals our spec
    -- First, simplify the evaluation of the vector
    simp only [eval_vector, Vector.getElem_singleton]
    -- The goal is now about pairs (Expression.eval env input_var.c[0], Expression.eval env input_var.c[1])
    
    -- Connect the condition using h_input
    have h_s : Expression.eval env input_var.s = input.s := by
      rw [← h_input]
    rw [h_s]
    
    -- Now we need to show the branches match
    -- First simplify the vector map on the singleton vector
    simp only [Vector.getElem_map, Vector.getElem_singleton]
    -- Now we have (eval env (input_var.c[0], input_var.c[1])).1 or .2
    simp only [eval, Prod.fst, Prod.snd]
    
    split_ifs with h
    · -- Case: s = 0
      have h_c0 : Expression.eval env input_var.c[0] = input.c[0] := by
        have h := congrArg (fun x => x.c[0]) h_input
        simp only [Vector.getElem_map] at h
        exact h
      exact h_c0
    · -- Case: s ≠ 0  
      have h_c1 : Expression.eval env input_var.c[1] = input.c[1] := by
        have h := congrArg (fun x => x.c[1]) h_input
        simp only [Vector.getElem_map] at h
        exact h
      exact h_c1

  completeness := by
    simp only [circuit_norm, main]
    intros offset env input_var h_env input h_input h_s
    simp only [MultiMux1.circuit, subcircuit, circuit_norm, FormalCircuit.toSubcircuit]
    rw [← h_input] at h_s
    simp_all

end Mux1

end Circomlib
