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
  c : Vector (F × F) n  -- n pairs of constants
  s : F                 -- selector

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
  let out <== c.map fun (c0, c1) =>
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

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n
  localLength_eq := by
    intros input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by sorry -- TODO: prove

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
    have h_ci : (eval env input_var.c)[i] = input.c[i] := by
      rw [h_c]
    
    -- Now we can work with the components
    rw [← h_s]
    conv_lhs => 
      arg 1; arg 1; arg 2; rw [← h_ci]
      arg 1; arg 2; rw [← h_ci]
      arg 2; rw [← h_ci]

    -- Extract the fact that s is boolean
    -- IsBool means s = 0 ∨ s = 1
    cases h_assumptions with
      -- When s = 0 or s = 1
      cases hs with
      | inl h0 =>
        -- When s = 0
        rw [h0]
        simp only [mul_zero, add_zero, if_pos rfl]
      | inr h1 =>
        -- When s = 1
        rw [h1]
        simp only [mul_one, if_neg (by norm_num : (1 : F p) ≠ 0)]
        ring

  completeness := by
    simp only [circuit_norm, main]
    intro offset env input_var h_env input h_input h_assumptions
    -- We need to show that the witnessed values equal the computed expressions
    ext i hi
    -- Left side: eval of varFromOffset
    simp only [varFromOffset_vector, eval_vector, Vector.getElem_map, Vector.getElem_mapRange]
    -- Now simplify the left side: Expression.eval env (var { index := offset + 1 * i })
    simp only [Expression.eval, mul_one]
    -- Right side: eval of the computed expression
    have h_env_i := h_env ⟨i, hi⟩
    simp only [Fin.val_mk, mul_one] at h_env_i
    rw [h_env_i]
    norm_num

end MultiMux1

namespace Mux1

structure Inputs (F : Type) where
  c : Vector F 2  -- 2 constants
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
    simp only [circuit_norm, main, MultiMux1.circuit]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    intros offset env input_var h_env input h_input h_s
    simp only [MultiMux1.circuit, subcircuit, circuit_norm, FormalCircuit.toSubcircuit]
    rw [← h_input] at h_s
    simp_all

end Mux1

end Circomlib
