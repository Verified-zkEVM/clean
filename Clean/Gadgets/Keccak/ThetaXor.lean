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

def main : Var Inputs (F p) → Circuit (F p) (Var KeccakState (F p))
  | { state, d } => .mapFinRange 25 fun i =>
    Xor64.circuit ⟨state[i.val], d[i.val / 5]⟩

instance elaborated : ElaboratedCircuit (F p) Inputs KeccakState where
  main
  localLength _ := 200

  localLength_eq _ n := by simp only [main, circuit_norm, Xor64.circuit]
  subcircuitsConsistent _ i := by simp only [main, circuit_norm]

def Assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.Normalized ∧ d.Normalized

def Spec (inputs : Inputs (F p)) (out: KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaXor state.value d.value

-- rewrite thetaXor as a loop
lemma thetaXor_loop (state : Vector ℕ 25) (d : Vector ℕ 5) :
    Specs.Keccak256.thetaXor state d = .mapFinRange 25 fun i => state[i.val] ^^^ d[i.val / 5] := by
  simp only [Specs.Keccak256.thetaXor, circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨state_var, d_var⟩ ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds

  -- rewrite goal
  apply KeccakState.normalized_value_ext
  simp only [main, circuit_norm, thetaXor_loop, Xor64.circuit, varFromOffset_vector, eval_vector,
    mul_comm, KeccakState.value, KeccakRow.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [circuit_norm, main, h_input, Xor64.circuit, Xor64.Assumptions, Xor64.Spec] at h_holds

  -- use assumptions, prove goal
  intro i
  specialize h_holds i ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩
  exact ⟨ h_holds.right, h_holds.left ⟩

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env ⟨state_var, d_var⟩ h_env ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [h_input, main, circuit_norm, Xor64.circuit, Xor64.Assumptions]
  intro i
  exact ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩

def circuit : FormalCircuit (F p) Inputs KeccakState :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Gadgets.Keccak256.ThetaXor
