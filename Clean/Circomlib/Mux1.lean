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

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n
  localLength_eq := by sorry -- TODO: prove
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
    sorry -- TODO: prove soundness

  completeness := by
    simp only [circuit_norm, main]
    sorry -- TODO: prove completeness

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
  localLength_eq := by sorry -- TODO: prove
  subcircuitsConsistent := by sorry -- TODO: prove

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
