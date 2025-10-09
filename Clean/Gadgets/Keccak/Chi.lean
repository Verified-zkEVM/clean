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

def Assumptions (state : KeccakState (F p)) (_ : Set (NamedList (F p))) := state.Normalized

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) (_ : Set (NamedList (F p))) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

-- #eval! main (p:=p_babybear) default |>.localLength
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  localLength _ := 400
  output _ i0 := Vector.mapRange 25 fun i => varFromOffset U64 (i0 + i*16 + 8)
  yields_eq := by intros; simp [circuit_norm, main, Xor64.circuit, Xor64.elaborated, And.And64.circuit, And.And64.elaborated, Not.circuit]

  localLength_eq state i0 := by simp only [main, circuit_norm, Xor64.circuit, And.And64.circuit, Not.circuit]
  subcircuitsConsistent state i0 := by
    simp only [main, circuit_norm]
    intro i
    and_intros <;> ac_rfl
  output_eq state i0 := by simp [main, circuit_norm, Xor64.circuit, And.And64.circuit, Not.circuit,
    Vector.mapRange, Vector.mapFinRange_succ, Vector.mapFinRange_zero]

-- rewrite the chi spec as a loop
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange 25 fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env yielded state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, chi_loop, eval_vector, KeccakState.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm
  simp only [main, circuit_norm, Xor64.circuit, And.And64.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec, Nat.reduceAdd] at h_holds

  simp_all

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env yielded state_var h_env state h_input state_norm

  -- simplify Assumptions
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm

  -- simplify constraints (goal + environment) and apply assumptions
  simp_all [main, circuit_norm, Xor64.circuit, And.And64.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec, Nat.reduceAdd]

def circuit : FormalCircuit (F p) KeccakState KeccakState :=
  { elaborated with Assumptions, Spec, soundness, completeness }
end Gadgets.Keccak256.Chi
