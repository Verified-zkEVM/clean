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
    sorry -- TODO: prove soundness

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
    simp only [circuit_norm, main, MultiMux1.circuit]
    sorry

  completeness := by
    simp only [circuit_norm, main, MultiMux1.circuit]
    sorry

end Mux1

end Circomlib
