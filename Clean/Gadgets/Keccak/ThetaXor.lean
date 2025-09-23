import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaXor
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

structure Inputs (F : Type) where
  state : KeccakState F
  d : KeccakRow F

instance : ProvableStruct Inputs where
  components := [KeccakState, KeccakRow]
  toComponents := fun { state, d } => .cons state (.cons d .nil)
  fromComponents := fun (.cons state (.cons d .nil)) => { state, d }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Var Inputs (F p) → Circuit sentences (Var KeccakState (F p))
  | { state, d } => .mapFinRange 25 fun i =>
    Xor64.circuit order ⟨state[i.val], d[i.val / 5]⟩

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs KeccakState where
  main := main order
  localLength _ := 200
  yields _ _ _ := ∅
  yields_eq := by
    intro env input offset
    simp only [main, circuit_norm, Circuit.mapFinRange.localYields]
    simp only [Set.iUnion_eq_empty]
    intro i
    simp only [ElaboratedCircuit.yields_eq]
    simp only [Xor64.circuit, Xor64.elaborated, Set.union_empty]

  localLength_eq _ n := by simp only [main, circuit_norm, Xor64.circuit, Xor64.elaborated]
  subcircuitsConsistent _ i := by simp only [main, circuit_norm]

def Assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.Normalized ∧ d.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (inputs : Inputs (F p)) :=
  Assumptions inputs

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (inputs : Inputs (F p)) (out : KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaXor state.value d.value

-- rewrite thetaXor as a loop
lemma thetaXor_loop (state : Vector ℕ 25) (d : Vector ℕ 5) :
    Specs.Keccak256.thetaXor state d = .mapFinRange 25 fun i => state[i.val] ^^^ d[i.val / 5] := by
  simp [Specs.Keccak256.thetaXor, circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero]

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env yields checked ⟨state_var, d_var⟩ ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds

  -- rewrite goal
  constructor
  · -- Prove yielded sentences hold (vacuous - yields is empty)
    simp [elaborated]
  apply KeccakState.normalized_value_ext
  simp only [elaborated, main, circuit_norm, thetaXor_loop, Xor64.circuit, Xor64.elaborated, eval_vector,
    KeccakState.value, KeccakRow.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [circuit_norm, elaborated, main, h_input, Xor64.circuit, Xor64.elaborated, Xor64.Assumptions, Xor64.Spec] at h_holds

  -- use assumptions, prove goal
  intro i
  specialize h_holds i ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩
  have ⟨_, h_spec⟩ := h_holds
  exact ⟨ h_spec.right, h_spec.left ⟩

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  intro i0 env yields ⟨state_var, d_var⟩ h_env ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [h_input, elaborated, main, circuit_norm, Xor64.circuit, Xor64.elaborated]
  intro i
  exact ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs KeccakState :=
  { elaborated := elaborated order
    Assumptions
    CompletenessAssumptions
    Spec
    soundness := soundness order
    completeness := completeness order
    completenessAssumptions_implies_assumptions := fun _ _ h => h }

end Gadgets.Keccak256.ThetaXor
