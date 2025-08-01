import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.StructuralLemmas
import Clean.Circuit.Theorems
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics

section
variable {F : Type} [Field F]
variable {M : TypeMap} [ProvableType M]

namespace Gadgets.ElementwiseScalarMul

/--
Inputs for element-wise scalar multiplication of a ProvableType.
Contains a scalar field element and a data value of type M.
-/
structure Inputs (M : TypeMap) (F : Type) where
  scalar : F
  data : M F

instance : ProvableStruct (Inputs M) where
  components := [field, M]
  toComponents := fun { scalar, data } => .cons scalar (.cons data .nil)
  fromComponents := fun (.cons scalar (.cons data .nil)) => { scalar, data }

/--
Main circuit that performs element-wise scalar multiplication.
Multiplies each element of the ProvableType by the scalar.
-/
def main (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { scalar, data } := input
  let dataVars := toVars data
  let scaledVars := dataVars.map (scalar * ·)
  return fromVars scaledVars

def Assumptions (_ : Inputs M F) : Prop := True

/--
Specification: Each element of the output equals scalar times the corresponding input element.
-/
def Spec (input : Inputs M F) (output : M F) : Prop :=
  output = input.scalar .* input.data

instance elaborated : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  circuit_proof_start
  simp only [ProvableType.elementwiseScalarMul]
  rcases input_var
  rcases input
  simp only [ProvableType.eval, toVars, toElements, toComponents, fromElements, fromComponents, components, ProvableStruct.componentsToElements] at h_input
  simp only [Inputs.mk.injEq] at h_input
  simp only [h_input.1.symm, h_input.2.symm]
  simp only [ProvableType.toElements_fromElements, ProvableType.eval]
  congr 1
  ext i h_i
  simp only [Vector.getElem_map]
  simp only [main, circuit_norm]
  simp only [Vector.instHAppendHAddNat, Vector.append, ProvableType.toElements_fromElements]
  aesop

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit F (Inputs M) M := {
  elaborated := elaborated (F := F) (M := M)
  Assumptions
  Spec
  soundness
  completeness
}

/--
Assumptions for binary scalar multiplication.
Requires the scalar to be boolean (0 or 1).
-/
def BinaryAssumptions (input : Inputs M F) : Prop :=
  IsBool input.scalar

/--
Alternative specification for binary scalar multiplication.
Guarantees that scalar 0 produces zero and scalar 1 preserves the data.
-/
def BinarySpec [DecidableEq F] (input : Inputs M F) (output : M F) : Prop :=
  output = if input.scalar = 1 then input.data else allZero

lemma binarySpec_holds [DecidableEq F] {input : Inputs M F} {output : M F}
      (h_bool : IsBool input.scalar)
      (h_spec : Spec input output) :
    BinarySpec input output := by
  simp only [BinarySpec, Spec] at *
  cases h_bool
  · rename_i h_zero
    simp [h_spec, h_zero, circuit_norm]
  · rename_i h_one
    simp [h_spec, h_one, circuit_norm]

/--
Binary scalar multiplication circuit with boolean assumptions.
Requires scalar to be 0 or 1, and guarantees clean if-then-else behavior.
-/
def binaryCircuit [DecidableEq F] : FormalCircuit F (Inputs M) M :=
  (circuit (F := F) (M := M)).strengthenAssumptions
    BinaryAssumptions
    BinarySpec
    (fun _ _ => True.intro)  -- BinaryAssumptions → Assumptions (which is True)
    (fun _ _ => binarySpec_holds)

end Gadgets.ElementwiseScalarMul

end
