import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean
import Clean.Utils.Bits
import Clean.Utils.Tactics

namespace Gadgets.ToBits
open Utils.Bits
variable {p : ℕ} [prime: Fact p.Prime] [p_large_enough: Fact (p > 2)]

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    (n : ℕ) (x : Expression (F p)) : Circuit sentences (Vector (Expression (F p)) n) := do
  -- witness the bits of `x`
  let bits ← witnessVector (sentences:=sentences) n (fun env => fieldToBits n (x.eval env))

  -- add boolean constraints on all bits
  Circuit.forEach bits (body := Boolean.assertBool (sentences:=sentences) order)

  -- check that the bits correctly sum to `x`
  Gadgets.Equality.circuit (sentences:=sentences) order field (x, fieldFromBitsExpr bits)
  return bits

-- formal circuit that implements `toBits` like a function, assuming `x.val < 2^n`

def toBits {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    (n : ℕ) (hn : 2^n < p) : GeneralFormalCircuit order field (fields n) where
  main := main (sentences:=sentences) order n
  localLength _ := n
  output _ i := varFromOffset (fields n) i

  localLength_eq _ _ := by simp only [main, circuit_norm]; ac_rfl
  subcircuitsConsistent x i0 := by simp +arith only [main, circuit_norm]
    -- TODO arith is needed because forAll passes `localLength + offset` while bind passes `offset + localLength`

  Assumptions _ (x : F p) := x.val < 2^n

  Spec (_checked : CheckedYields sentences) (x : F p) (bits : Vector (F p) n) :=
    x.val < 2^n ∧ bits = fieldToBits n x

  soundness := by
    circuit_proof_start
    obtain ⟨ h_bits_conj , ⟨ h_eq_yield, h_eq_conj ⟩ ⟩ := h_holds

    -- Extract the parts from the conjunctions
    have h_bits : ∀ (i : Fin n), IsBool (env.get (i₀ + i)) := fun i => (h_bits_conj i)
    have h_eq : input = env (fieldFromBitsExpr (.mapRange n (var ⟨i₀ + ·⟩))) := h_eq_conj

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨i₀ + ·⟩)
    let bits : Vector (F p) n := bit_vars.map env

    replace h_bits (i : ℕ) (hi : i < n) : IsBool bits[i] := by
      simp only [circuit_norm, bits, bit_vars]
      exact h_bits ⟨ i, hi ⟩

    change input = env (fieldFromBitsExpr bit_vars) at h_eq
    rw [h_eq, fieldFromBits_eval bit_vars, fieldToBits_fieldFromBits hn bits h_bits]

    constructor
    · -- Prove yielded sentences hold (should be empty)
      intro s
      simp [circuit_norm, Operations.localYields, Set.mem_union, Set.mem_empty_iff_false, or_false, FormalAssertion.toSubcircuit, Equality.main]
    · -- Prove the spec
      constructor
      · exact fieldFromBits_lt _ h_bits
      · rfl

  completeness := by
    circuit_proof_start

    constructor
    · intro i
      rw [h_env i]
      simp [fieldToBits, Utils.Bits.toBits, Vector.getElem_mapRange, IsBool]

    let bit_vars : Vector (Expression (F p)) n := .mapRange n (var ⟨i₀ + ·⟩)

    have h_bits_eq : bit_vars.map env = fieldToBits n input := by
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm, bit_vars]
      exact h_env ⟨ i, hi ⟩

    show input = env (fieldFromBitsExpr bit_vars)
    rw [fieldFromBits_eval bit_vars, h_bits_eq, fieldFromBits_fieldToBits h_assumptions]

-- formal assertion that uses the same circuit to implement a range check. without input assumption

def rangeCheck {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    (n : ℕ) (hn : 2^n < p) : FormalAssertion order field where
  main x := do
    -- we wrap the toBits circuit but ignore the output
    let _ ← toBits (sentences:=sentences) order n hn x

  localLength _ := n

  Assumptions _ := True
  Spec (_ : CheckedYields sentences) (x : F p) := x.val < 2^n

  soundness := by
    simp_all only [circuit_norm, toBits]
    intro offset env yields checked input_var input h_input h_holds s
    simp [circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalAssertion.toSubcircuit, main, Equality.main]
  completeness := by simp_all only [circuit_norm, toBits]

end ToBits
export ToBits (toBits)
end Gadgets
