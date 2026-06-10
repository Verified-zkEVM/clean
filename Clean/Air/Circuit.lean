/-
Shared circuit infrastructure for Clean.Air.
-/
import Clean.Circuit
import Clean.Circuit.Extensions

variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

abbrev Environment.fromInput (row : Input F) (data : ProverData F) : Environment F :=
  Environment.fromArray (toElements row).toArray data

@[circuit_norm]
lemma ProvableType.eval_fromInput_varFromOffset_zero (input : Input F) (data : ProverData F) :
    Eval.eval (Environment.fromInput input data) (varFromOffset (F:=F) Input 0) = input := by
  simp only [Environment.fromInput, Environment.fromArray]
  rw [eval_varFromOffset, ProvableType.fromElements_eq_iff, Vector.ext_iff]
  intro i hi
  simp only
  rw [Vector.getElem_mapRange, zero_add, Vector.getElem?_toArray,
    Vector.getElem?_eq_getElem hi, Option.getD_some]

@[circuit_norm]
lemma ProvableType.valueFromOffset_zero_fromInput_eq (input : Input F) (data : ProverData F) :
    valueFromOffset (F:=F) Input 0 (Environment.fromInput input data) = input := by
  simp only [valueFromOffset, zero_add]
  rw [fromElements_eq_iff, Vector.ext_iff]
  simp only [circuit_norm, Vector.getElem?_toArray]
  grind

namespace GeneralFormalCircuit
/--
Formal circuits are parametrized by their input, with the goal of being reusable in any parent circuit.
However, when using such a circuit to define AIR constraints, there is no longer any reusability concern,
and we have to get rid of the parametrization since there must be a unique set of constraints shared by every row.
`instantiate` accomplishes that by witnessing the inputs as fresh variables and plugging them into the circuit.

TODO instead of `witnessAny` which assumes the correct honest prover witness is part of the environment independently,
we could derive the witness information from `Environment.hint` to have a more obvious way of setting it up.
This is sort of blocked on having a string -> component identification.
-/
@[circuit_norm]
def instantiate (circuit : GeneralFormalCircuit F Input Output) : Circuit F Unit := do
  let input ← witnessAny Input
  let _ ← circuit input -- we don't care about the output in this context

@[circuit_norm]
def instantiateConst (circuit : GeneralFormalCircuit F Input unit) (input : Input F) : Circuit F Unit := do
  let _ ← circuit (const input)

def instantiateConst_toFormal (circuit : GeneralFormalCircuit F Input unit) (input : Input F) :
    GeneralFormalCircuit F unit unit where
  main _ := circuit.instantiateConst input
  Assumptions _ := circuit.Assumptions input
  ProverAssumptions _ := circuit.ProverAssumptions input
  Spec _ _ := circuit.Spec input ()
  soundness := by circuit_proof_all
  completeness := by circuit_proof_all

@[circuit_norm]
lemma instantiateConst_toFormal_operations {circuit : GeneralFormalCircuit F Input unit} {input : Input F} {n : ℕ} :
  ((circuit.instantiateConst_toFormal input).main ()).operations n =
    (circuit (const input)).operations n := rfl

def size (circuit : GeneralFormalCircuit F Input Output) : ℕ :=
  circuit.instantiate.localLength 0

lemma size_eq (circuit : GeneralFormalCircuit F Input Output) :
  circuit.size = (ProvableType.size Input) + circuit.localLength (varFromOffset Input 0) := rfl

def empty (F : Type) [FiniteField F] (Input : TypeMap) [ProvableType Input] :
    GeneralFormalCircuit F Input unit where
  main _ := return
  Assumptions | _, _ => True
  ProverAssumptions | _, _, _ => True
  Spec _ _ _ := True
  soundness := by circuit_proof_start
  completeness := by circuit_proof_start

@[circuit_norm] lemma empty_operations : ∀ input n,
    ((empty F Input).main input).operations n = [] := by
  simp only [circuit_norm, empty]

@[circuit_norm] lemma empty_assumptions : ∀ input env, (empty F Input).Assumptions input env := by
  simp only [circuit_norm, empty]

@[circuit_norm] lemma empty_channelsWithGuarantees :
  (empty F Input).channelsWithGuarantees = [] := rfl

@[circuit_norm] lemma empty_channelsWithRequirements :
  (empty F Input).channelsWithRequirements = [] := rfl
end GeneralFormalCircuit
