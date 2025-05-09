import Clean.Circuit.Loops
import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaXor
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
open Gadgets.Keccak256 (KeccakState KeccakRow)

structure Inputs (F : Type) where
  state : KeccakState F
  d : KeccakRow F

instance : ProvableStruct Inputs where
  components := [KeccakState, KeccakRow]
  to_components := fun { state, d } => .cons state (.cons d .nil)
  from_components := fun (.cons state (.cons d .nil)) => { state, d }

def theta_xor (inputs : Var Inputs (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  let { state, d } := inputs
  .mapFinRange 25 fun i =>
    subcircuit Gadgets.Xor.circuit ⟨state[i.val], d[i.val / 5]⟩

instance elaborated : ElaboratedCircuit (F p) Inputs (Var KeccakState (F p)) where
  main := theta_xor
  local_length _ := 200
  output _ i0 := var_from_offset KeccakState i0

  local_length_eq _ n := by simp only [theta_xor, circuit_norm]; ac_rfl
  initial_offset_eq _ i := by simp only [theta_xor, circuit_norm]
  output_eq _ i := by simp only [theta_xor, circuit_norm, Xor.circuit, var_from_offset_vector]

def assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.is_normalized ∧ d.is_normalized

def spec (inputs : Inputs (F p)) (out: KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.is_normalized
  ∧ out.value = Specs.Keccak256.theta_xor state.value d.value

-- rewrite theta_xor as a loop
lemma theta_xor_loop (state : Vector ℕ 25) (d : Vector ℕ 5) :
    Specs.Keccak256.theta_xor state d = .mapFinRange fun i => state[i.val] ^^^ d[i.val / 5] := by
  rw [Specs.Keccak256.theta_xor, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env ⟨state_var, d_var⟩ ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds
  -- rewrite goal
  apply KeccakState.normalized_value_ext
  simp only [elaborated, size, theta_xor_loop, var_from_offset_vector, eval_vector,
    Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_mapFinRange, mul_comm,
    KeccakState.value, KeccakRow.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Inputs.mk.injEq, Vector.ext_iff] at h_input
  simp only [circuit_norm, subcircuit_norm, theta_xor, h_input, Xor.circuit, Rotation64.circuit,
    Xor.assumptions, Xor.spec, Rotation64.assumptions, Rotation64.spec] at h_holds

  -- use assumptions, and prove goal
  intro i
  specialize h_holds i ⟨ state_norm i, d_norm ⟨i.val / 5, by omega⟩ ⟩
  exact ⟨ h_holds.right, h_holds.left ⟩

theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta_xor, Xor.circuit, Rotation64.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  sorry

def circuit : FormalCircuit (F p) Inputs KeccakState := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak256.ThetaXor
