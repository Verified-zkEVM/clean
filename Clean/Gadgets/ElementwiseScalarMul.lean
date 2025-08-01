import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.StructuralLemmas
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
  simp only [ProvableType.scalarMul]
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
Alternative specification for binary scalar multiplication.
Guarantees that scalar 0 produces zero and scalar 1 preserves the data.
-/
def BinarySpec (input : Inputs M F) (output : M F) : Prop :=
  (input.scalar = 0 → output = allZero) ∧
  (input.scalar = 1 → output = input.data)

lemma binarySpec_holds {input : Inputs M F} {output : M F}
    (h_spec : Spec input output) :
    BinarySpec input output := by
  simp only [BinarySpec, Spec] at *
  constructor
  · intro h_zero
    rw [h_zero, ProvableType.scalarMul] at h_spec
    rw [h_spec]
    rw [ProvableType.ext_iff]
    intro i hi
    simp only [ProvableType.toElements_fromElements, Vector.getElem_map, zero_mul, allZero]
    simp only [ProvableType.toElements_fromElements, Vector.getElem_fill]
  · intro h_one
    rw [h_one, ProvableType.scalarMul] at h_spec
    rw [h_spec]
    rw [ProvableType.ext_iff]
    intro i hi
    simp only [ProvableType.toElements_fromElements, Vector.getElem_map, one_mul]

/--
Binary scalar multiplication circuit with weaker specification.
Guarantees that scalar 0 produces zero and scalar 1 preserves the data.
-/
def binaryCircuit : FormalCircuit F (Inputs M) M :=
  (circuit (F := F) (M := M)).weakenSpec
    BinarySpec
    (fun _ _ _ h_spec => binarySpec_holds h_spec)

end Gadgets.ElementwiseScalarMul

end
