import Clean.Circuit.StructuralLemmas
import Clean.Circuit.Theorems
import Clean.Utils.Tactics

namespace ElementwiseAdd

section
variable {F : Type} [Field F]
variable {M : TypeMap} [ProvableType M]

open ProvableType

/--
Inputs for element-wise addition of two ProvableTypes. No carries for overflows and each element just wraps around.
-/
structure Inputs (M : TypeMap) (F : Type) where
  a : M F
  b : M F

instance : ProvableStruct (Inputs M) where
  components := [M, M]
  toComponents := fun { a, b } => .cons a (.cons b .nil)
  fromComponents := fun (.cons a (.cons b .nil)) => { a, b }

def main (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { a, b } := input
  let aVars := toVars a
  let bVars := toVars b
  let sumVars := Vector.ofFn fun i => aVars[i] + bVars[i]
  return fromVars sumVars

def Assumptions (_ : Inputs M F) : Prop := True

/--
Specification: Each element of the output equals the sum of corresponding input elements.
-/
def Spec (input : Inputs M F) (output : M F) : Prop :=
  output = input.a .+ input.b

instance elaborated : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  circuit_proof_start
  rcases input
  rcases input_var
  simp only [Inputs.mk.injEq] at h_input
  simp only [ProvableType.eval, ProvableType.elementwiseAdd]
  congr 1
  ext i h_i
  simp only [Vector.getElem_ofFn, eval_fromElements, toElements_fromElements, Vector.getElem_map, Vector.getElem_ofFn,
    Expression.eval, getElem_eval_toElements, h_input.1, h_input.2, toVars]
  simp only [Fin.getElem_fin]

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
  (input.a = allZero → output = input.b) ∧
  (input.b = allZero → output = input.a)

lemma spec_implies_weakerSpec : ∀ (input : Inputs M F) (output : M F),
    Assumptions input →
    Spec input output →
    WeakerSpec input output := by
  intro input output h_assumptions h_spec
  simp only [WeakerSpec, Spec] at *
  constructor
  · intro h_a_zero
    simp only [h_spec, h_a_zero, circuit_norm]
  · intro h_b_zero
    simp only [h_spec, h_b_zero, circuit_norm]

/--
When either input is zero, the output equals the non-zero input.
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
