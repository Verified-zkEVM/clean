import Clean.Circuit
import Clean.Utils.Bits
-- import Clean-Circomlib.Bitify

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
  main := main
  localLength _ := 2
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
def main (input : Vector (Expression (F p)) 2) := do
  let diff := input[1] - input[0]
  let out ← IsZero.main diff
  return out

def circuit : FormalCircuit (F p) (fields 2) field where
  main := main
  localLength _ := 2
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
def main (enabled : Expression (F p)) (input : Vector (Expression (F p)) 2) := do
  let diff := input[1] - input[0]
  let isz_out ← IsZero.main diff
  (1 - isz_out) * enabled === 0
  return ()

def circuit : FormalCircuit (F p) (fieldPair (fields 2)) unit where
  main := fun ⟨enabled, input⟩ => main enabled input
  localLength _ := 2
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
end ForceEqualIfEnabled

namespace LessThan
/-
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
}
-/
def main (n : ℕ) (input : Vector (Expression (F p)) 2) := do
  let diff := input[0] + (2^n : F p) - input[1]
  let bits ← Num2Bits.main (n+1) diff
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
