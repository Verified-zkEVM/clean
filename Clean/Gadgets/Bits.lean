import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean
import Clean.Utils.Bits

namespace Gadgets.ToBits
open Utils.Bits
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def main (n: ℕ) (x : Expression (F p)) := do
  -- witness the bits of `x`
  let bits ← witnessVector n fun env => field_to_bits n (x.eval env)

  -- add boolean constraints on all bits
  Circuit.forEach bits (assertion Boolean.circuit)

  -- check that the bits correctly sum to `x`
  x === (field_from_bits_expr bits)
  return bits

-- formal circuit that implements `to_bits` like a function, assuming `x.val < 2^n`

def circuit (n : ℕ) (hn : 2^n < p) : FormalCircuit (F p) field (fields n) where
  main := main n
  local_length _ := n
  output _ i := varFromOffset (fields n) i

  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl
  subcircuits_consistent x i0 := by simp +arith only [main, circuit_norm]
    -- TODO arith is needed because forAll passes `local_length + offset` while bind passes `offset + local_length`

  assumptions (x : F p) := x.val < 2^n

  spec (x : F p) (bits : Vector (F p) n) :=
    bits = field_to_bits n x

  soundness := by
    intro k eval x_var x h_input _h_assumptions h_holds
    simp only [main, circuit_norm, Boolean.circuit] at *
    simp only [h_input, circuit_norm, subcircuit_norm] at h_holds
    clear h_input _h_assumptions

    obtain ⟨ h_bits, h_eq ⟩ := h_holds

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)
    let bits : Vector (F p) n := bit_vars.map eval

    replace h_bits (i : ℕ) (hi : i < n) : bits[i] = 0 ∨ bits[i] = 1 := by
      simp only [circuit_norm, bits, bit_vars]
      exact h_bits ⟨ i, hi ⟩

    change x = eval (field_from_bits_expr bit_vars) at h_eq
    rw [h_eq, field_from_bits_eval bit_vars, field_to_bits_field_from_bits hn bits h_bits]

  completeness := by
    intro k eval x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, Boolean.circuit] at *
    simp only [h_input, circuit_norm, subcircuit_norm] at h_env ⊢

    constructor
    · intro i
      rw [h_env i]
      simp [field_to_bits, to_bits]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)

    have h_bits_eq : bit_vars.map eval = field_to_bits n x := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_env ⟨ i, hi ⟩

    show x = eval (field_from_bits_expr bit_vars)
    rw [field_from_bits_eval bit_vars, h_bits_eq, field_from_bits_field_to_bits hn h_assumptions]

-- formal assertion that uses the same circuit to implement a range check. without input assumption

def range_check (n : ℕ) (hn : 2^n < p) : FormalAssertion (F p) field where
  main x := do _ ← main n x -- discard the output
  local_length _ := n

  subcircuits_consistent _ n := by simp +arith only [main, circuit_norm]
  local_length_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl

  assumptions _ := True
  spec (x : F p) := x.val < 2^n

  soundness := by
    simp only [circuit_norm, main, Boolean.circuit]
    simp only [circuit_norm, subcircuit_norm]
    intro k eval x_var x h_input ⟨ h_bits, h_eq ⟩
    rw [h_input] at h_eq
    change x = eval _ at h_eq
    rw [h_eq, field_from_bits_eval]
    apply field_from_bits_lt hn
    intro i hi
    simp only [circuit_norm, h_bits ⟨ i, hi ⟩]

  completeness := by
    simp only [circuit_norm, main, Boolean.circuit]
    simp only [circuit_norm, subcircuit_norm]
    intro k eval x_var h_env x h_input h_assumptions
    simp only [h_input] at h_env ⊢

    constructor
    · intro i
      rw [h_env i]
      simp [field_to_bits, to_bits]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)

    have h_bits_eq : bit_vars.map eval = field_to_bits n x := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_env ⟨ i, hi ⟩

    show _ = eval _
    rw [field_from_bits_eval, h_bits_eq, field_from_bits_field_to_bits hn h_assumptions]

end Gadgets.ToBits
