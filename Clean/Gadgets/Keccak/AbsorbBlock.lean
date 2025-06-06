import Clean.Gadgets.Keccak.Permutation
import Clean.Circuit.Explicit
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.AbsorbBlock
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

@[reducible] def KeccakBlock := ProvableVector U64 RATE

structure Input (F : Type) where
  state : KeccakState F
  block : KeccakBlock F

instance : ProvableStruct Input where
  components := [KeccakState, KeccakBlock]
  to_components := fun { state, block } => .cons state (.cons block .nil)
  from_components := fun (.cons state (.cons block .nil)) => { state, block }

def main (input : Var Input (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let { state, block } := input
  -- absorb the block into the state by XORing with the first RATE elements
  let state_rate ← Circuit.mapFinRange RATE fun i => subcircuit Xor.circuit ⟨state[i], block[i]⟩

  -- the remaining elements of the state are unchanged
  let state_capacity := Vector.mapFinRange (25 - RATE) fun i => state[RATE + i]
  let state' : Vector _ 25 := state_rate ++ state_capacity

  -- apply the permutation
  subcircuit Permutation.circuit state'

set_option linter.constructorNameAsVariable false

instance elaborated : ElaboratedCircuit (F p) Input KeccakState where
  main
  local_length _ := 36808
  output _ i0 := Permutation.state_var (i0 + 136) 23

  local_length_eq _ _ := by simp only [main, circuit_norm, Xor.circuit, Permutation.circuit, RATE]
  output_eq input i0 := by simp only [main, circuit_norm, Xor.circuit, Permutation.circuit, RATE]
  subcircuits_consistent _ _ := by simp +arith only [main, circuit_norm, Xor.circuit, Permutation.circuit, RATE]


end Gadgets.Keccak256.AbsorbBlock
