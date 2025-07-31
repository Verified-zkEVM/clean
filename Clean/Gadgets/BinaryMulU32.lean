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

omit p_large_enough in
/--
Key theorem: multiplying a normalized U32 by a binary scalar preserves normalization.
-/
theorem binary_mul_preserves_normalized {input : ScalarMulU32.Inputs (F p)} {output : U32 (F p)}
    (h_binary : IsBool input.scalar)
    (h_norm : input.value.Normalized)
    (h_spec : ScalarMulU32.Spec input output) :
    output.Normalized := by
  simp only [ScalarMulU32.Spec] at h_spec
  simp only [U32.Normalized] at h_norm ⊢
  cases h_binary with
  | inl h_zero => aesop
  | inr h_one => aesop

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
