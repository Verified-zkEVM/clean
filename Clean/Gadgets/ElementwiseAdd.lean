import Clean.Circuit.StructuralLemmas
import Clean.Utils.Tactics

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
  circuit_proof_start
  rcases input
  rcases input_var
  simp only [Inputs.mk.injEq] at h_input
  ext i h_i
  simp only [Vector.getElem_ofFn, eval_fromElements, toElements_fromElements, Vector.getElem_map, Vector.getElem_ofFn,
    Expression.eval, getElem_eval_toElements, h_input.1, h_input.2]

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  circuit_proof_start

def circuit : FormalCircuit F (Inputs M) M where
  Assumptions
  Spec
  soundness
  completeness

/--
Weaker specification for ElementwiseAdd that handles zero inputs specially.
When either input is zero, the output equals the non-zero input.
-/
def WeakerSpec (input : Inputs M F) (output : M F) : Prop :=
  (input.a = zero → output = input.b) ∧
  (input.b = zero → output = input.a)

/--
Proof that the original spec implies the weaker spec.
-/
theorem spec_implies_weakerSpec : ∀ (input : Inputs M F) (output : M F),
    Assumptions input →
    Spec input output →
    WeakerSpec input output := by
  intro input output h_assumptions h_spec
  simp only [WeakerSpec, Spec] at *
  constructor
  · intro h_a_zero
    -- When a is zero, we need to show output = b
    simp only [ProvableType.ext_iff]
    intro i hi
    rw [h_spec]
    simp only [Vector.getElem_ofFn, h_a_zero, zero]
    simp only [toElements_fromElements, Vector.getElem_fill, zero_add, Fin.getElem_fin, add_eq_right]
  · intro h_b_zero
    -- When b is zero, we need to show output = a
    simp only [ProvableType.ext_iff]
    intro i hi
    rw [h_spec]
    simp only [Vector.getElem_ofFn, h_b_zero, zero]
    simp only [toElements_fromElements, Vector.getElem_fill, add_zero, Fin.getElem_fin, add_eq_left]

/--
ElementwiseAdd circuit with weaker specification for zero handling.
-/
def circuitWithZeroSpec : FormalCircuit F (Inputs M) M :=
  circuit.weakenSpec WeakerSpec spec_implies_weakerSpec

@[circuit_norm]
lemma circuitWithZeroSpec_assumptions : (circuitWithZeroSpec (F := F) (M := M)).Assumptions = Assumptions := by
  simp only [circuitWithZeroSpec, FormalCircuit.weakenSpec_assumptions]
  rfl

@[circuit_norm]
lemma circuitWithZeroSpec_spec : (circuitWithZeroSpec (F := F) (M := M)).Spec = WeakerSpec := by
  simp only [circuitWithZeroSpec, FormalCircuit.weakenSpec]

end

end ElementwiseAdd
