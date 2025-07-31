import Clean.Circuit.StructuralLemmas

namespace ElementwiseAdd

section
variable {F : Type} [Field F]
variable {M : TypeMap} [ProvableType M]

open ProvableType

/--
Inputs for element-wise addition of two ProvableTypes.
-/
structure Inputs (M : TypeMap) (F : Type) where
  a : M F
  b : M F

instance : ProvableStruct (Inputs M) where
  components := [M, M]
  toComponents := fun { a, b } => .cons a (.cons b .nil)
  fromComponents := fun (.cons a (.cons b .nil)) => { a, b }

/--
Main circuit that performs element-wise addition.
Adds corresponding elements of two ProvableTypes.
-/
def main (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { a, b } := input
  let aVars := toVars a
  let bVars := toVars b
  let sumVars := Vector.ofFn fun i => aVars[i] + bVars[i]
  return fromVars sumVars

/--
No assumptions needed for basic element-wise addition.
-/
def Assumptions (_ : Inputs M F) : Prop := True

/--
Specification: Each element of the output equals the sum of corresponding input elements.
-/
def Spec (input : Inputs M F) (output : M F) : Prop :=
  toElements output = Vector.ofFn fun i => (toElements input.a)[i] + (toElements input.b)[i]

instance elaborated : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  intro i0 env input_var input h_input h_as h_holds
  simp only [Spec, elaborated, eval, explicit_provable_type]
  sorry

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  intro i0 env input_var h_uses_local h_env_extends
  simp only [elaborated, main, circuit_norm]

def circuit : FormalCircuit F (Inputs M) M where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end

end ElementwiseAdd