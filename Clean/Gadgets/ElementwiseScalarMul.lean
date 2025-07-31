import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.StructuralLemmas
import Clean.Gadgets.Boolean

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

/--
No assumptions needed for basic element-wise scalar multiplication.
-/
def Assumptions (_ : Inputs M F) : Prop := True

/--
Specification: Each element of the output equals scalar times the corresponding input element.
-/
def Spec (input : Inputs M F) (output : M F) : Prop :=
  toElements output = (toElements input.data).map (input.scalar * ·)

instance elaborated : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  intro i0 env input_var input h_input h_as h_holds
  simp only [Spec, elaborated, eval, explicit_provable_type]
  simp only [ProvableType.toElements_fromElements]
  rcases input_var
  rcases input
  simp only [ProvableType.eval, toVars, toElements, toComponents, fromElements, fromComponents, components, ProvableStruct.componentsToElements] at h_input
  simp only [Vector.cast_rfl, Vector.map_append, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil, Nat.add_zero, id_eq] at h_input
  simp only [ProvableStruct.componentsFromElements] at h_input
  simp only [Inputs.mk.injEq] at h_input
  simp only [main, circuit_norm]
  simp only [h_input.1.symm]
  simp only [h_input.2.symm]
  clear h_input
  ext i h_i
  simp only [Vector.getElem_map]
  simp only [main, circuit_norm]
  simp only [ProvableType.toElements_fromElements]
  simp only [Vector.getElem_map, Expression.eval]
  simp only [Vector.instHAppendHAddNat, Vector.append]
  aesop

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  intro i0 env input_var h_env input h_input h_as
  simp only [circuit_norm, main]

/--
Formal circuit for element-wise scalar multiplication.
-/
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
  (input.scalar = 0 → output = zero) ∧
  (input.scalar = 1 → output = input.data)

/--
Key theorem: binary scalar multiplication satisfies the stronger spec.
-/
theorem binary_spec_holds {input : Inputs M F} {output : M F}
    (h_spec : Spec input output) :
    BinarySpec input output := by
  simp only [BinarySpec, Spec] at *
  constructor
  · intro h_zero
    simp only [zero_mul, zero] at h_spec ⊢
    rw [ProvableType.ext_iff]
    intro i hi
    rw [ProvableType.toElements_fromElements]
    simp only [h_spec]
    simp only [Vector.getElem_map]
    simp only [h_zero]
    simp only [zero_mul]
    simp only [Vector.getElem_fill]
  · intro h_one
    rw [ProvableType.ext_iff]
    intro i hi
    simp only [h_spec]
    simp only [Vector.getElem_map]
    simp only [h_one]
    simp only [one_mul]

/--
Binary scalar multiplication circuit with stronger assumptions and guarantees.
-/
def binaryCircuit : FormalCircuit F (Inputs M) M :=
  (circuit (F := F) (M := M)).strengthenAssumption
    (fun _ => True)
    BinarySpec
    (fun _ _ => trivial)
    (fun _ _ _ h_spec => binary_spec_holds h_spec)

end Gadgets.ElementwiseScalarMul

end
