import Clean.Circuit
import Clean.Utils.Field

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
-/

namespace Circomlib
variable {p : ℕ} [Fact p.Prime]

namespace XOR
/-
template XOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - 2*a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - 2*a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input.1 = 0 ∨ input.1 = 1) ∧ (input.2 = 0 ∨ input.2 = 1)
  Spec input output :=
    output.val = input.1.val ^^^ input.2.val
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ (h_a | h_a), (h_b | h_b) ⟩ h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      rcases h_env with ⟨ _, _ ⟩
      simp_all only [h_a, h_b, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end XOR

namespace AND
/-
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input.1 = 0 ∨ input.1 = 1) ∧ (input.2 = 0 ∨ input.2 = 1)
  Spec input output :=
    output.val = input.1.val &&& input.2.val
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ (h_a | h_a), (h_b | h_b) ⟩ h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      rcases h_env with ⟨ _, _ ⟩
      simp_all only [h_a, h_b, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end AND

namespace OR
/-
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input.1 = 0 ∨ input.1 = 1) ∧ (input.2 = 0 ∨ input.2 = 1)
  Spec input output :=
    output.val = input.1.val ||| input.2.val
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ (h_a | h_a), (h_b | h_b) ⟩ h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      rcases h_env with ⟨ _, _ ⟩
      simp_all only [h_a, h_b, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end OR

namespace NOT
/-
template NOT() {
    signal input in;
    signal output out;

    out <== 1 + in - 2*in;
}
-/
def main (input : Expression (F p)) := do
  let in := input
  let out <== 1 + in - 2*in
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input = 0 ∨ input = 1)
  Spec input output :=
    output.val = ~~~input.val
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ _ _ h_env (h_in | h_in) h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      simp_all only [h_in, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end NOT

namespace NAND
/-
template NAND() {
    signal input a;
    signal input b;
    signal output out;

    out <== 1 - a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== 1 - a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input.1 = 0 ∨ input.1 = 1) ∧ (input.2 = 0 ∨ input.2 = 1)
  Spec input output :=
    output.val = ~~~(input.1.val &&& input.2.val)
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ (h_a | h_a), (h_b | h_b) ⟩ h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      rcases h_env with ⟨ _, _ ⟩
      simp_all only [h_a, h_b, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end NAND

namespace NOR
/-
template NOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b + 1 - a - b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a*b + 1 - a - b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := (input.1 = 0 ∨ input.1 = 1) ∧ (input.2 = 0 ∨ input.2 = 1)
  Spec input output :=
    output.val = ~~~(input.1.val ||| input.2.val)
    ∧ (output = 0 ∨ output = 1)

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ (h_a | h_a), (h_b | h_b) ⟩ h_hold
    all_goals {
      simp only [circuit_norm, main] at h_env h_hold ⊢
      rcases h_env with ⟨ _, _ ⟩
      simp_all only [h_a, h_b, h_hold]
      constructor
      · ring_nf; simp
      · ring_nf; simp
    }

  completeness := by
    simp_all only [circuit_norm, main]
end NOR

end Circomlib
