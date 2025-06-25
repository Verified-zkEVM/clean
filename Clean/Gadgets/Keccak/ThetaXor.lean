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
  to_components := fun { state, d } => .cons state (.cons d .nil)
  from_components := fun (.cons state (.cons d .nil)) => { state, d }

def main : Var Inputs (F p) → Circuit (F p) (Var KeccakState (F p))
  | { state, d } => .mapFinRange 25 fun i =>
    subcircuit Xor64.circuit ⟨state[i.val], d[i.val / 5]⟩

instance elaborated : ElaboratedCircuit (F p) Inputs KeccakState where
  main
  localLength _ := 200

  localLength_eq _ n := by simp only [main, circuit_norm, Xor64.circuit]
  subcircuits_consistent _ i := by simp only [main, circuit_norm]

def assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.is_normalized ∧ d.is_normalized

def spec (inputs : Inputs (F p)) (out: KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.is_normalized
  ∧ out.value = Specs.Keccak256.theta_xor state.value d.value

-- rewrite theta_xor as a loop
lemma theta_xor_loop (state : Vector ℕ 25) (d : Vector ℕ 5) :
    Specs.Keccak256.theta_xor state d = .mapFinRange 25 fun i => state[i.val] ^^^ d[i.val / 5] := by
  simp only [Specs.Keccak256.theta_xor, circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero]

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro i0 env ⟨state_var, d_var⟩ ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds

  -- rewrite goal
  apply KeccakState.normalized_value_ext
  simp only [main, circuit_norm, theta_xor_loop, Xor64.circuit, varFromOffset_vector, eval_vector,
    mul_comm, KeccakState.value, KeccakRow.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [circuit_norm, subcircuit_norm, main, h_input, Xor64.circuit, Xor64.assumptions, Xor64.spec] at h_holds

  -- use assumptions, prove goal
  intro i
  specialize h_holds i ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩
  exact ⟨ h_holds.right, h_holds.left ⟩

theorem completeness : Completeness (F p) elaborated assumptions := by
  intro i0 env ⟨state_var, d_var⟩ h_env ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [h_input, main, circuit_norm, subcircuit_norm, Xor64.circuit, Xor64.assumptions]
  intro i
  exact ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩

def circuit : FormalCircuit (F p) Inputs KeccakState := {
  elaborated with assumptions, spec, soundness, completeness
}

end Gadgets.Keccak256.ThetaXor
