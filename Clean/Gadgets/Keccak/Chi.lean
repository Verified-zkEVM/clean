import Clean.Types.U64
import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.And.And64
import Clean.Gadgets.Not.Not64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Chi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
open Gadgets.Keccak256 (KeccakState)
open Bitwise (not64)
open Not (not64_bytewise not64_bytewise_value)

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .mapFinRange 25 fun i => do
    let state_not ← subcircuit Not.circuit (state.get (i + 5))
    let state_and ← subcircuit And.And64.circuit ⟨state_not, state.get (i + 10)⟩
    subcircuit Xor.circuit ⟨state.get i, state_and⟩

def assumptions := KeccakState.is_normalized (p:=p)

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

-- #eval! main (p:=p_babybear) default |>.operations.local_length
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakState (F p)) where
  main
  local_length _ := 400
  local_length_eq state i0 := by simp only [main, circuit_norm, Xor.circuit, And.And64.circuit, Not.circuit]
  initial_offset_eq state i := by simp only [main, circuit_norm]

  output _ i0 := Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 8)
  output_eq state i := by
    simp only [main, circuit_norm, Xor.circuit, And.And64.circuit, Not.circuit]

-- rewrite the chi spec as a loop
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange 25 fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [spec, elaborated, chi_loop, eval_vector, KeccakState.value,
    Vector.getElem_map, Vector.getElem_mapRange, Fin.getElem_fin, Vector.getElem_mapFinRange]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [assumptions, KeccakState.is_normalized, Fin.getElem_fin] at state_norm
  simp only [main, circuit_norm, subcircuit_norm, Xor.circuit, And.And64.circuit, Not.circuit,
    Xor.assumptions, Xor.spec, And.And64.assumptions, And.And64.spec, Nat.reduceAdd] at h_holds

  simp_all

theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i0 env state_var h_env state h_input state_norm

  -- simplify constraints
  simp only [main, circuit_norm, subcircuit_norm, Xor.circuit, And.And64.circuit, Not.circuit,
    Xor.assumptions, Xor.spec, And.And64.assumptions, And.And64.spec, Nat.reduceAdd]
  intro i

  simp only [assumptions, KeccakState.is_normalized, Fin.getElem_fin] at state_norm

  -- TODO need theorem about `env.uses_local_witnesses_completeness (Vector.mapM ...)`
  dsimp only [circuit_norm, main, Vector.mapFinRangeM, Xor.circuit, And.And64.circuit, Not.circuit] at h_env
  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakState where
  assumptions
  spec
  soundness
  completeness
end Gadgets.Keccak256.Chi
