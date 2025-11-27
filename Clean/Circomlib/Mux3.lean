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
https://github.com/iden3/circomlib/blob/master/circuits/mux3.circom
-/

namespace MultiMux3

structure Inputs (n : ℕ) (F : Type) where
  c : ProvableVector (fields 8) n F  -- n vectors of 8 constants each
  s : Vector F 3                      -- 3-bit selector

instance {n : ℕ} : ProvableStruct (Inputs n) where
  components := [ProvableVector (fields 8) n, fields 3]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template MultiMux3(n) {
    signal input c[n][8];  // Constants
    signal input s[3];   // Selector
    signal output out[n];

    signal a210[n];
    signal a21[n];
    signal a20[n];
    signal a2[n];

    signal a10[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    // 4 constrains for the intermediary variables
    signal  s10;
    s10 <== s[1] * s[0];

    for (var i=0; i<n; i++) {

         a210[i] <==  ( c[i][ 7]-c[i][ 6]-c[i][ 5]+c[i][ 4] - c[i][ 3]+c[i][ 2]+c[i][ 1]-c[i][ 0] ) * s10;
          a21[i] <==  ( c[i][ 6]-c[i][ 4]-c[i][ 2]+c[i][ 0] ) * s[1];
          a20[i] <==  ( c[i][ 5]-c[i][ 4]-c[i][ 1]+c[i][ 0] ) * s[0];
           a2[i] <==  ( c[i][ 4]-c[i][ 0] );

          a10[i] <==  ( c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s10;
           a1[i] <==  ( c[i][ 2]-c[i][ 0] ) * s[1];
           a0[i] <==  ( c[i][ 1]-c[i][ 0] ) * s[0];
            a[i] <==  ( c[i][ 0] );

          out[i] <== ( a210[i] + a21[i] + a20[i] + a2[i] ) * s[2] +
                     (  a10[i] +  a1[i] +  a0[i] +  a[i] );

    }
}
-/
def main (n : ℕ) (input : Var (Inputs n) (F p)) := do
  let { c, s } := input

  let s10 <== s[1] * s[0]

  -- Witness and constrain output vector
  let out <== c.map fun ci =>
    let a210 := (ci[7] - ci[6] - ci[5] + ci[4] - ci[3] + ci[2] + ci[1] - ci[0]) * s10
    let a21 := (ci[6] - ci[4] - ci[2] + ci[0]) * s[1]
    let a20 := (ci[5] - ci[4] - ci[1] + ci[0]) * s[0]
    let a2 := (ci[4] - ci[0])

    let a10 := (ci[3] - ci[2] - ci[1] + ci[0]) * s10;
    let a1 := (ci[2] - ci[0]) * s[1];
    let a0 := (ci[1] - ci[0]) * s[0];
    let a := (ci[0]);

    (a210 + a21 + a20 + a2) * s[2] + (a10 + a1 + a0 + a);

  return out

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n + 1
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    omega

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1] ∧ IsBool s[2]

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      let s0 := (if s[0] = 0 then 0 else 1)
      let s1 := (if s[1] = 0 then 0 else 1)
      let s2 := (if s[2] = 0 then 0 else 1)
      let idx := 4 * s2 + 2 * s1 + s0
      have : idx < 8 := by
        simp only [idx, s0, s1, s2]
        split <;> split <;> split <;> decide
      output[i] = (c[i])[idx]

  soundness := by
    simp only [circuit_norm, main]
    intro offset env input_var input h_input h_assumptions h_output
    obtain ⟨h_s10, h_out_vec⟩ := h_output
    -- We need to show the spec holds for all i < n
    intro i hi
    -- The output at position i is computed from the multilinear interpolation formula
    -- We need to show this equals c[i][idx] where idx is determined by the selector bits

    -- Get the i-th element equality from h_output
    have h_output_i := congrArg (fun v => v[i]) h_out_vec
    simp only [Vector.getElem_map] at h_output_i
    simp only [Vector.getElem_mapRange] at h_output_i
    simp only [circuit_norm] at h_output_i
    simp only [h_output_i]

    rw [← h_input] at h_assumptions ⊢
    -- Extract boolean assumptions
    obtain ⟨h_s0, h_s1, h_s2⟩ := h_assumptions

    simp only [Vector.getElem_map] at h_s0 h_s1 h_s2
    simp only [Vector.getElem_map]

    -- Case analysis on s[0], s[1] and s[2]
    cases h_s0 <;> cases h_s1 <;> cases h_s2 <;>
      (rename_i h_s0 h_s1 h_s2
       simp only [h_s0, h_s1, h_s2, h_s10, circuit_norm]
       norm_num
       rw [ProvableType.getElem_eval_fields, getElem_eval_vector])

    all_goals ring_nf

  completeness := by
    circuit_proof_start
    obtain ⟨h_eq, h_env⟩ := h_env
    constructor
    · assumption
    · -- We need to show that the witnessed values equal the computed expressions
      ext i hi
      -- Left side: eval of varFromOffset
      simp only [Vector.getElem_map, Vector.getElem_mapRange]
      -- Now simplify the left side: Expression.eval env (var { index := offset + 1 * i })
      simp only [Expression.eval]
      -- Right side: eval of the computed expression
      have h_env_i := h_env ⟨i, hi⟩
      rw [h_env_i]
      norm_num

end MultiMux3

namespace Mux3

structure Inputs (F : Type) where
  c : Vector F 8  -- 8 constants
  s : Vector F 3  -- 3-bit selector

instance : ProvableStruct Inputs where
  components := [fields 8, fields 3]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template Mux3() {
    var i;
    signal input c[8];  // Constants
    signal input s[3];   // Selector
    signal output out;

    component mux = MultiMux3(1);

    for (i=0; i<8; i++) {
        mux.c[0][i] <== c[i];
    }

    for (i=0; i<3; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out[0] ==> out;
}
-/
def main (input : Var Inputs (F p)) := do
  let { c, s } := input

  -- Call MultiMux3 with n=1
  let mux_out ← MultiMux3.circuit 1 { c := #v[c], s }
  return mux_out[0]

def circuit : FormalCircuit (F p) Inputs field where
  main := main

  localLength _ := 2
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    rfl

  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1] ∧ IsBool s[2]

  Spec input output :=
    let ⟨c, s⟩ := input
    let s0 := (if s[0] = 0 then 0 else 1)
    let s1 := (if s[1] = 0 then 0 else 1)
    let s2 := (if s[2] = 0 then 0 else 1)
    let idx := 4 * s2 + 2 * s1 + s0
    have : idx < 8 := by
      simp only [idx, s0, s1, s2]
      split <;> split <;> split <;> decide
    output = c[idx]

  soundness := by
    simp only [circuit_norm, main]
    intro _ _ _ input h_input h_assumptions h_subcircuit_sound
    rw [← h_input] at *
    clear input h_input
    simp only [MultiMux3.circuit, circuit_norm] at h_subcircuit_sound h_assumptions ⊢
    specialize h_subcircuit_sound h_assumptions 0 (by omega)
    rw [h_subcircuit_sound]
    -- Now we need to show the RHS equals our spec
    -- First, simplify the evaluation of the vector
    simp only [eval_vector, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, circuit_norm]

  completeness := by
    simp only [circuit_norm, main]
    intros offset env input_var h_env input h_input h_s
    simp only [MultiMux3.circuit, circuit_norm]
    rw [← h_input] at h_s
    simp_all

end Mux3

end Circomlib
