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

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (state : Var KeccakState (F p)) : Circuit sentences (Var KeccakState (F p)) :=
  .mapFinRange 25 fun i => do
    let state_not ← Not.circuit order (state[i + 5])
    let state_and ← And.And64.circuit order ⟨state_not, state[i + 10]⟩
    Xor64.circuit order ⟨state[i], state_and⟩

def Assumptions := KeccakState.Normalized (p:=p)

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

-- #eval! main (p:=p_babybear) default |>.localLength
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakState KeccakState where
  main := main order
  localLength _ := 400
  output _ i0 := Vector.mapRange 25 fun i => varFromOffset U64 (i0 + i*16 + 8)

  localLength_eq state i0 := by simp only [main, circuit_norm, Xor64.circuit, Xor64.elaborated, And.And64.circuit, And.And64.elaborated, Not.circuit]
  subcircuitsConsistent state i0 := by
    simp only [main, circuit_norm]
    intro i
    and_intros <;> ac_rfl
  output_eq state i0 := by simp only [main, circuit_norm, Xor64.circuit, Xor64.elaborated, And.And64.circuit, And.And64.elaborated, Not.circuit,
    Vector.mapRange, Vector.mapFinRange_succ, Vector.mapFinRange_zero]

-- rewrite the chi spec as a loop
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange 25 fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env yields checked state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, Spec, elaborated, chi_loop, eval_vector, KeccakState.value]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm
  simp only [main, circuit_norm, Xor64.circuit, Xor64.elaborated, And.And64.circuit, And.And64.elaborated, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec, Nat.reduceAdd] at h_holds

  simp_all

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) Assumptions := by
  intro i0 env yields state_var h_env state h_input state_norm

  -- simplify Assumptions
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm

  -- simplify constraints (goal + environment) and apply assumptions
  simp_all [state_norm, h_input, main, circuit_norm, Xor64.circuit, And.And64.circuit, Not.circuit,
    Xor64.Assumptions, Xor64.Spec, And.And64.Assumptions, And.And64.Spec, Nat.reduceAdd]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit (F p) sentences order KeccakState KeccakState :=
  { elaborated := elaborated order
    Assumptions
    Spec
    soundness := soundness order
    completeness := completeness order
    spec_monotonic := fun _ _ _ _ _ h => h }
end Gadgets.Keccak256.Chi
