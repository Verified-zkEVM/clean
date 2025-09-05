import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/comparators.circom
-/

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
  let inv ← witness fun env =>
    let x := input.eval env
    if x ≠ 0 then x⁻¹ else 0

  let out <== -input * inv + 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 2

  Assumptions _ := True

  Spec input output :=
    output = (if input = 0 then 1 else 0)

  soundness := by
    circuit_proof_start
    simp only [id_eq, h_holds]
    split_ifs with h_ifs
    . simp only [h_ifs, zero_mul, neg_zero, zero_add]
    . rw [@neg_add_eq_zero]
      have h1 := h_holds.left
      have h2 := h_holds.right
      rw [h1] at h2
      simp only [id_eq, mul_eq_zero] at h2
      cases h2
      case neg.inl hl => contradiction
      case neg.inr hr =>
        rw [@neg_add_eq_zero] at hr
        exact hr

  completeness := by
    circuit_proof_start
    cases h_env with
    | intro left right =>
      simp only [left, ne_eq, id_eq, ite_not, mul_ite, mul_zero] at right
      simp only [id_eq, right, left, ne_eq, ite_not, mul_ite, mul_zero, mul_eq_zero, true_and]
      split_ifs with input
      case pos h_pos => left ; exact input
      case neg h_neg =>
        right
        rw [@neg_add_eq_zero]
        rw [propext (mul_inv_eq_one₀ input)]

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
  let out ← IsZero.circuit diff
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 2

  Assumptions _ := True
  Spec := fun (x, y) output =>
    output = (if x = y then 1 else 0)

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
  let isz ← IsZero.circuit (inp.2 - inp.1)
  enabled * (1 - isz) === 0

def circuit : FormalAssertion (F p) Inputs where
  main
  localLength _ := 2

  Assumptions := fun { enabled, inp } =>
    enabled = 0 ∨ enabled = 1

  Spec := fun { enabled, inp } =>
    enabled = 1 → inp.1 = inp.2

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
def main (n : ℕ) (hn : 2^(n+1) < p) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← Num2Bits.circuit (n + 1) hn diff
  let out <== 1 - bits[n]
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := main n hn
  localLength _ := n + 2
  localLength_eq := by simp [circuit_norm, main, Num2Bits.circuit]
  output _ i := var ⟨ i + n + 1 ⟩
  output_eq := by simp +arith [circuit_norm, main, Num2Bits.circuit]

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n

  Spec := fun (x, y) output =>
    output = (if x.val < y.val then 1 else 0)

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
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (x, y + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val <= y.val then 1 else 0)

  soundness := by
    intro i env input (x, y) h_input assumptions h_holds
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]
    have : 2^n < 2^(n+1) := by gcongr; repeat linarith
    have hy : y.val + (1 : F p).val < p := by
      simp only [ZMod.val_one]; linarith
    rw [ZMod.val_add_of_lt hy, ZMod.val_one] at h_holds
    by_cases hy : y.val + 1 = 2^n
    case neg =>
      specialize h_holds (by omega)
      simp_all [Nat.lt_add_one_iff]
    -- TODO the spec of LessThan is not strong enough to handle this case
    sorry

  completeness := by
    intro i env input h_env (x, y) h_input assumptions
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]
    -- TODO impossible to prove
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
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n

  Spec := fun (x, y) output =>
    output = (if x.val > y.val then 1 else 0)

  soundness := by
    simp_all [circuit_norm, LessThan.circuit]

  completeness := by
    simp_all [circuit_norm, LessThan.circuit]
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
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val >= y.val then 1 else 0)

  soundness := by
    simp only [circuit_norm]
    sorry

  completeness := by
    simp only [circuit_norm]
    sorry
end GreaterEqThan

end Circomlib
