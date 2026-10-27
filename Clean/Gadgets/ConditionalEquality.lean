module

public import Clean.Circuit
public import Clean.Gadgets.Equality
public import Clean.Utils.Tactics

@[expose] public section

/-!
# Conditional equality

Asserts that two values are equal where a gate is nonzero, by the constraints
`gate * (lhs[i] - rhs[i]) = 0`, one per cell: Plonky3's `when(gate).assert_zeros(lhs - rhs)`.
-/

namespace Gadgets.ConditionalEquality
variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

/-- A gate and the two values that must be equal where it is nonzero. -/
structure Input (M : TypeMap) (F : Type) where
  gate : F
  lhs : M F
  rhs : M F
deriving ProvableStruct

def main (input : Var (Input M) F) : Circuit F Unit :=
  let diffs := (toElements input.lhs).zip (toElements input.rhs) |>.map fun (x, y) => x - y
  .forEach diffs fun diff => assertZero (input.gate * diff)

@[reducible]
instance elaborated (M : TypeMap) [ProvableType M] : ElaboratedCircuit F (Input M) unit main := by
  elaborate_circuit

def circuit (M : TypeMap) [ProvableType M] : FormalAssertion F (Input M) where
  name := "conditionalEquality"
  main
  elaborated := elaborated M
  Spec input := input.gate ≠ 0 → input.lhs = input.rhs
  soundness := by
    circuit_proof_start
    obtain ⟨-, h_lhs, h_rhs⟩ := h_input
    intro h_nonzero
    rw [← h_lhs, ← h_rhs]
    rw [ProvableType.ext_iff]
    intro i hi
    have := h_holds ⟨i, hi⟩
    simp only [Vector.getElem_zip, ProvableType.getElem_eval_toElements] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h_nonzero)
  completeness := by
    circuit_proof_start
    obtain ⟨-, h_lhs, h_rhs⟩ := h_input
    intro i
    by_cases h_zero : input_gate = 0
    · rw [h_zero, zero_mul]
    · have h_eq := h_spec h_zero
      rw [← h_lhs, ← h_rhs, ProvableType.ext_iff] at h_eq
      simp only [Vector.getElem_zip, ProvableType.getElem_eval_toElements]
      rw [h_eq i.val i.isLt, sub_self, mul_zero]

@[circuit_norm]
lemma localLength_eq (input : Var (Input M) F) : (circuit M).localLength input = 0 := by
  simp only [circuit, FormalCircuitBase.localLength, elaborated]
  rfl

lemma interactions_eq (input : Var (Input M) F) (offset : ℕ) :
    (((circuit M).main input).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm]

end Gadgets.ConditionalEquality
