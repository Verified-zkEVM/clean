import Clean.Circuit.Loops
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [prime: Fact p.Prime]

def to_bit (x : ZMod p) : Bool := x == 1

def to_bits (n : ℕ) (x : ZMod p) : Vector Bool n :=
  .ofFn fun i => x.val.testBit i

def from_bits {n : ℕ} (x : Vector Bool n) : ZMod p :=
  Nat.ofBits fun i => x[i.val]

def from_bits_expr {n: ℕ} (xs : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc i => acc + xs[i] * .const (2^i.val)) 0

@[reducible] def BitVector (n : ℕ) := ProvableVector field n

namespace ToBits
def main {n: ℕ} (x : Expression (F p)) := do
  let bits ← witness_vector n fun (eval : Environment (F p)) =>
    .ofFn fun i =>
      let bit : Bool := (eval x).val.testBit i
      (if bit then 1 else 0 : F p)

  Circuit.forEach bits fun bit => assertion Boolean.circuit bit

  let x' := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0
  x.assert_equals x'

  return bits

def circuit (n : ℕ) : FormalCircuit (F p) field (BitVector n) where
  main
  local_length _ := n
  output _ i := var_from_offset (ProvableVector field n) i

  initial_offset_eq _ _ := by simp only [main, circuit_norm]
  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl

  output_eq _ _ := by
    simp only [main, circuit_norm, Boolean.circuit, var_from_offset_vector]
    rfl

  assumptions (x : F p) := x.val < 2^n

  spec (x : F p) (xs : Vector (F p) n) :=
    ∀ (i : ℕ) (hi : i < n), xs[i] = if x.val.testBit i then 1 else 0

  soundness := by
    intro k env x_var x h_input h_assumptions h_holds
    simp only [main, circuit_norm, eval_vector, var_from_offset_vector] at *
    intro i hi
    sorry

  completeness := by
    intro k env x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, eval_vector, var_from_offset_vector] at *
    sorry

end Gadgets.ToBits
