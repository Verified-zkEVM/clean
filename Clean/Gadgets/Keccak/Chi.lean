import Clean.Types.U64
import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.And.And64
import Clean.Gadgets.Not.Not64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Chi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
open Not (not64_bytewise not64_bytewise_value)

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .mapFinRange 25 fun i => do
    let state_not ← Not.circuit (state[i + 5])
    let state_and ← And.And64.circuit ⟨state_not, state[i + 10]⟩
    Xor64.circuit ⟨state[i], state_and⟩

def Assumptions := KeccakState.Normalized (p:=p)

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit

-- rewrite the chi spec as a loop
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange 25 fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ Xor64.circuit, And.And64.circuit, And.And8.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec]

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, chi_loop, eval_vector, KeccakState.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [KeccakState.Normalized] at h_assumptions

  simp_all

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [Xor64.circuit, And.And64.circuit, And.And8.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec,
    KeccakState.Normalized]
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp_all

def circuit : FormalCircuit (F p) KeccakState KeccakState where
  main
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Keccak256.Chi
