import Clean.Circuit
import Clean.Utils.Bits
import Clean-Circomlib.Bitify

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace IsZero
/-
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}
-/
def main (input : Expression (F p)) := do
  let inv ← witnessField fun env =>
    let in_val := input.eval env
    if in_val.val ≠ 0 then in_val⁻¹ else 0

  let out ← witnessField fun env => (-input * inv + 1).eval env
  out === -input * inv + 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 2

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end IsZero

namespace IsEqual
/-
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 - input.2
  let out ← subcircuit IsZero.circuit diff
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 2

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end IsEqual

namespace ForceEqualIfEnabled
/-
template ForceEqualIfEnabled() {
    signal input enabled;
    signal input in[2];

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    (1 - isz.out)*enabled === 0;
}
-/
structure Inputs (F : Type) where
  enabled : F
  inp : fieldPair F

instance : ProvableStruct Inputs where
  components := [field, fieldPair]
  toComponents := fun { enabled, inp } => .cons enabled (.cons inp .nil)
  fromComponents := fun (.cons enabled (.cons inp .nil)) => { enabled, inp }

def main (inputs : Var Inputs (F p)) := do
  let { enabled, inp } := inputs
  let isz_out ← subcircuit IsZero.circuit (inp.2 - inp.1)
  ((1 : Expression (F p)) - isz_out) * enabled === 0

def circuit : FormalAssertion (F p) Inputs where
  main
  localLength _ := 2

  Assumptions input := sorry
  Spec input := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end ForceEqualIfEnabled

namespace LessThan
/-
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1 << n) - in[1];

    out <== 1-n2b.out[n];
}
-/
def main (n : ℕ) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← subcircuitWithAssertion (Num2Bits.circuit (n+1)) diff
  let out ← witnessField fun env => (1 - bits[n]).eval env
  out === 1 - bits[n]
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) (fields 2) field where
  main := main n
  localLength _ := 1 + (n + 1)
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end LessThan

namespace LessEqThan
/-
template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;
    lt.out ==> out;
}
-/
def main (n : ℕ) (input : Vector (Expression (F p)) 2) := do
  let modified_input : Vector (Expression (F p)) 2 :=
    Vector.ofFn fun i => if i = 0 then input[0] else input[1] + 1
  let out ← LessThan.main n modified_input
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) (fields 2) field where
  main := main n
  localLength _ := 1 + (n + 1)
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end LessEqThan

namespace GreaterThan
/-
template GreaterThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}
-/
def main (n : ℕ) (input : Vector (Expression (F p)) 2) := do
  let swapped_input : Vector (Expression (F p)) 2 :=
    Vector.ofFn fun i => if i = 0 then input[1] else input[0]
  let out ← LessThan.main n swapped_input
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) (fields 2) field where
  main := main n
  localLength _ := 1 + (n + 1)
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end GreaterThan

namespace GreaterEqThan
/-
template GreaterEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0]+1;
    lt.out ==> out;
}
-/
def main (n : ℕ) (input : Vector (Expression (F p)) 2) := do
  let modified_input : Vector (Expression (F p)) 2 :=
    Vector.ofFn fun i => if i = 0 then input[1] else input[0] + 1
  let out ← LessThan.main n modified_input
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) (fields 2) field where
  main := main n
  localLength _ := 1 + (n + 1)
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end GreaterEqThan

end Circomlib
