import Clean.Circuit
import Clean.Utils.Field
import Clean.Utils.Tactics
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
  c : ProvableVector fieldPair n F  -- n pairs of constants
  s : F                              -- selector
deriving ProvableStruct
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
def main (n : ℕ) (input : Var (Inputs n) (F p)) := do
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

-- Note: Use the existing lemma getElem_eval_vector from Provable.lean instead

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  Assumptions input :=
    let ⟨c, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      output[i] = if s = 0 then (c[i]).1 else (c[i]).2

  soundness := by
    circuit_proof_start
    intro i hi
    have h_holds_i := congrArg (fun v => v[i]) h_holds
    simp only [circuit_norm, Vector.getElem_map, Vector.getElem_mapRange] at h_holds_i
    rw [h_holds_i, h_input.2, ← h_input.1]
    simp only [← getElem_eval_vector, circuit_norm]
    rcases h_assumptions with h0 | h1
    · simp [h0]
    · simp [h1]

  completeness := by
    circuit_proof_start
    -- We need to show that the witnessed values equal the computed expressions
    ext i hi
    -- Left side: eval of varFromOffset
    simp only [Vector.getElem_map, Vector.getElem_mapRange]
    -- Now simplify the left side: Expression.eval env (var { index := offset + 1 * i })
    simp only [circuit_norm]
    -- Right side: eval of the computed expression
    have h_env_i := h_env ⟨i, hi⟩
    rw [h_env_i, h_input.2]

end MultiMux1

namespace Mux1

structure Inputs (F : Type) where
  c : Vector F 2  -- 2 constants
  s : F           -- selector
deriving ProvableStruct

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

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    output = if s = 0 then c[0] else c[1]

  soundness := by
    circuit_proof_start [MultiMux1.circuit]
    specialize h_holds h_assumptions 0 (by omega)
    simp only [circuit_norm, eval_vector] at h_holds
    rw [← h_input.1]
    simp only [Vector.getElem_map]
    exact h_holds

  completeness := by
    circuit_proof_start [MultiMux1.circuit]
    exact h_assumptions

end Mux1

end Circomlib
