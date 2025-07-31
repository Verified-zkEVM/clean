import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Utils.Tactics

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.ScalarMulU32

/--
Inputs for scalar multiplication of U32.
Contains a field element scalar and a U32 value.
-/
structure Inputs (F : Type) where
  scalar : F
  value : U32 F

instance : ProvableStruct Inputs where
  components := [field, U32]
  toComponents := fun { scalar, value } => .cons scalar (.cons value .nil)
  fromComponents := fun (.cons scalar (.cons value .nil)) => { scalar, value }

/--
Main circuit that performs scalar multiplication on U32.
Multiplies each limb of the U32 by the scalar field element.
-/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let { scalar, value } := input
  let result : Var U32 (F p) := {
    x0 := scalar * value.x0
    x1 := scalar * value.x1
    x2 := scalar * value.x2
    x3 := scalar * value.x3
  }
  return result

/--
No assumptions needed for this gadget.
-/
def Assumptions (_ : Inputs (F p)) : Prop := True

/--
Specification: The output U32 has each limb equal to scalar * corresponding input limb.
-/
def Spec (input : Inputs (F p)) (output : U32 (F p)) : Prop :=
  output.x0 = input.scalar * input.value.x0 ∧
  output.x1 = input.scalar * input.value.x1 ∧
  output.x2 = input.scalar * input.value.x2 ∧
  output.x3 = input.scalar * input.value.x3

instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main
  localLength _ := 0
  output input_var _ := {
    x0 := input_var.scalar * input_var.value.x0
    x1 := input_var.scalar * input_var.value.x1
    x2 := input_var.scalar * input_var.value.x2
    x3 := input_var.scalar * input_var.value.x3
  }

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  -- manual steps follow because U32 is not a ProvableStruct
  rcases input_value
  simp only [explicit_provable_type, toVars] at ⊢ h_input
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil] at ⊢ h_input
  simp only [explicit_provable_type, U32.mk.injEq] at h_input
  simp [Expression.eval, h_input]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit (F p) Inputs U32 where
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Gadgets.ScalarMulU32

end
