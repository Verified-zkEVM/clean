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
https://github.com/iden3/circomlib/blob/master/circuits/mux2.circom
-/

namespace MultiMux2

structure Inputs (n : ℕ) (F : Type) where
  c : ProvableVector (fields 4) n F  -- n vectors of 4 constants each
  s : Vector F 2                      -- 2-bit selector

instance {n : ℕ} : ProvableStruct (Inputs n) where
  components := [ProvableVector (fields 4) n, fields 2]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template MultiMux2(n) {
    signal input c[n][4];  // Constants
    signal input s[2];   // Selector
    signal output out[n];

    signal a10[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    signal  s10;
    s10 <== s[1] * s[0];

    for (var i=0; i<n; i++) {
          a10[i] <==  ( c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s10;
           a1[i] <==  ( c[i][ 2]-c[i][ 0] ) * s[1];
           a0[i] <==  ( c[i][ 1]-c[i][ 0] ) * s[0];
            a[i] <==  ( c[i][ 0] );

          out[i] <==  (  a10[i] +  a1[i] +  a0[i] +  a[i] );
    }
}
-/
def main (n : ℕ) (input : Var (Inputs n) (F p)) := do
  let { c, s } := input

  let s10 <== s[1] * s[0]

  -- Witness and constrain output vector
  let out <== c.map fun ci =>
    let a10 := (ci[3] - ci[2] - ci[1] + ci[0]) * s10
    let a1 := (ci[2] - ci[0]) * s[1]
    let a0 := (ci[1] - ci[0]) * s[0]
    let a := ci[0]
    a10 + a1 + a0 + a

  return out

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n + 1
  localLength_eq := by sorry

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1]

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      let s0 := (if s[0] = 0 then 0 else 1)
      let s1 := (if s[1] = 0 then 0 else 1)
      let idx := 2 * s1 + s0
      have : idx < 4 := by
        simp only [idx, s0, s1]
        split <;> split <;> decide
      output[i] = (c[i])[idx]

  soundness := by sorry

  completeness := by sorry

end MultiMux2

namespace Mux2

structure Inputs (F : Type) where
  c : Vector F 4  -- 4 constants
  s : Vector F 2  -- 2-bit selector

instance : ProvableStruct Inputs where
  components := [fields 4, fields 2]
  toComponents := fun {c, s} => .cons c (.cons s .nil)
  fromComponents := fun (.cons c (.cons s .nil)) => ⟨c, s⟩
/-
template Mux2() {
    var i;
    signal input c[4];  // Constants
    signal input s[2];   // Selector
    signal output out;

    component mux = MultiMux2(1);

    for (i=0; i<4; i++) {
        mux.c[0][i] <== c[i];
    }

    for (i=0; i<2; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out[0] ==> out;
}
-/
def main (input : Var Inputs (F p)) := do
  let { c, s } := input

  -- Call MultiMux2 with n=1
  let mux_out ← MultiMux2.circuit 1 { c := #v[c], s }
  return mux_out[0]

def circuit : FormalCircuit (F p) Inputs field where
  main := main

  localLength _ := 2
  localLength_eq := by sorry

  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1]

  Spec input output :=
    let ⟨c, s⟩ := input
    let s0 := (if s[0] = 0 then 0 else 1)
    let s1 := (if s[1] = 0 then 0 else 1)
    let idx := 2 * s1 + s0
    have : idx < 4 := by
      simp only [idx, s0, s1]
      split <;> split <;> decide
    output = c[idx]

  soundness := by sorry

  completeness := by sorry

end Mux2

end Circomlib
