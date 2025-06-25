import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean
import Clean.Utils.Bits

namespace Gadgets.ToBits
open Utils.Bits
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def main (n: ℕ) (x : Expression (F p)) := do
  -- witness the bits of `x`
  let bits ← witnessVector n fun env => fieldToBits n (x.eval env)

  -- add boolean constraints on all bits
  Circuit.forEach bits (assertion Boolean.circuit)

  -- check that the bits correctly sum to `x`
  x === (fieldFromBitsExpr bits)
  return bits

-- formal circuit that implements `toBits` like a function, assuming `x.val < 2^n`

def circuit (n : ℕ) (hn : 2^n < p) : FormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := n
  output _ i := varFromOffset (fields n) i

  localLength_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl
  subcircuitsConsistent x i0 := by simp +arith only [main, circuit_norm]
    -- TODO arith is needed because forAll passes `localLength + offset` while bind passes `offset + localLength`

  Assumptions (x : F p) := x.val < 2^n

  Spec (x : F p) (bits : Vector (F p) n) :=
    bits = fieldToBits n x

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

    change x = eval (fieldFromBitsExpr bit_vars) at h_eq
    rw [h_eq, fieldFromBits_eval bit_vars, fieldToBits_fieldFromBits hn bits h_bits]

  completeness := by
    intro k eval x_var h_env x h_input h_assumptions
    simp only [main, circuit_norm, Boolean.circuit] at *
    simp only [h_input, circuit_norm, subcircuit_norm] at h_env ⊢

    constructor
    · intro i
      rw [h_env i]
      simp [fieldToBits, toBits]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)

    have h_bits_eq : bit_vars.map eval = fieldToBits n x := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_env ⟨ i, hi ⟩

    show x = eval (fieldFromBitsExpr bit_vars)
    rw [fieldFromBits_eval bit_vars, h_bits_eq, fieldFromBits_fieldToBits hn h_assumptions]

-- formal assertion that uses the same circuit to implement a range check. without input assumption

def rangeCheck (n : ℕ) (hn : 2^n < p) : FormalAssertion (F p) field where
  main x := do _ ← main n x -- discard the output
  localLength _ := n

  subcircuitsConsistent _ n := by simp +arith only [main, circuit_norm]
  localLength_eq _ _ := by simp only [main, circuit_norm, Boolean.circuit]; ac_rfl

  Assumptions _ := True
  Spec (x : F p) := x.val < 2^n

  soundness := by
    simp only [circuit_norm, main, Boolean.circuit]
    simp only [circuit_norm, subcircuit_norm]
    intro k eval x_var x h_input ⟨ h_bits, h_eq ⟩
    rw [h_input] at h_eq
    change x = eval _ at h_eq
    rw [h_eq, fieldFromBits_eval]
    apply fieldFromBits_lt hn
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
      simp [fieldToBits, toBits]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨k + ·⟩)

    have h_bits_eq : bit_vars.map eval = fieldToBits n x := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_env ⟨ i, hi ⟩

    show _ = eval _
    rw [fieldFromBits_eval, h_bits_eq, fieldFromBits_fieldToBits hn h_assumptions]

end Gadgets.ToBits
