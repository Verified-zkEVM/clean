import Clean.Gadgets.ScalarMulU32
import Clean.Gadgets.Boolean
import Clean.Circuit.StructuralLemmas

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.BinaryMulU32

/--
Assumptions for binary multiplication of U32.
Requires the scalar to be binary (0 or 1) and the input U32 to be normalized.
-/
def Assumptions (input : ScalarMulU32.Inputs (F p)) : Prop :=
  IsBool input.scalar ∧ input.value.Normalized

/--
Specification for binary multiplication of U32.
Ensures each output limb equals scalar * input limb and the output is normalized.
-/
def Spec (input : ScalarMulU32.Inputs (F p)) (output : U32 (F p)) : Prop :=
  ScalarMulU32.Spec input output ∧ output.Normalized

/--
Key theorem: multiplying a normalized U32 by a binary scalar preserves normalization.
-/
theorem binary_mul_preserves_normalized {input : ScalarMulU32.Inputs (F p)} {output : U32 (F p)}
    (h_binary : IsBool input.scalar)
    (h_norm : input.value.Normalized)
    (h_spec : ScalarMulU32.Spec input output) :
    output.Normalized := by
  -- Unfold the spec to get the multiplication equations
  simp only [ScalarMulU32.Spec] at h_spec
  obtain ⟨h_x0, h_x1, h_x2, h_x3⟩ := h_spec
  -- Unfold normalization for input and output
  simp only [U32.Normalized] at h_norm ⊢
  obtain ⟨h_in0, h_in1, h_in2, h_in3⟩ := h_norm
  -- Case split on whether scalar is 0 or 1
  cases h_binary with
  | inl h_zero =>
    -- If scalar = 0, all outputs are 0
    simp [h_zero, zero_mul] at h_x0 h_x1 h_x2 h_x3
    simp [h_x0, h_x1, h_x2, h_x3, ZMod.val_zero]
  | inr h_one =>
    -- If scalar = 1, output = input
    simp [h_one, one_mul] at h_x0 h_x1 h_x2 h_x3
    simp [h_x0, h_x1, h_x2, h_x3]
    exact ⟨h_in0, h_in1, h_in2, h_in3⟩

/--
Binary multiplication circuit for U32.
Uses ScalarMulU32 with strengthened assumptions requiring binary scalar and normalized input.
-/
def circuit : FormalCircuit (F p) ScalarMulU32.Inputs U32 :=
  ScalarMulU32.circuit.strengthenAssumption
    Assumptions
    Spec
    (fun _ _ => trivial)  -- IsBool ∧ Normalized → True (original assumption)
    (fun _ _ ⟨h_bool, h_norm⟩ h_spec => 
      ⟨h_spec, binary_mul_preserves_normalized h_bool h_norm h_spec⟩)

end Gadgets.BinaryMulU32

end