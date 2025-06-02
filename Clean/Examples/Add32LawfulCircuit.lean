import Clean.Utils.Primes
import Clean.Circuit.ExplicitCircuit
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Examples.AddOperations

open Gadgets.Addition8FullCarry (add8_full_carry)
open Gadgets.Addition32Full (add32_full Inputs)

-- `infer_explicit_circuit` seem to work for all circuits
instance explicit : ConstantExplicitCircuits (add32_full (p:=p)) := by
  apply ConstantExplicitCircuits.from_constant_length (by infer_explicit_circuit)
  try intros
  simp only [ExplicitCircuit.local_length]
  ac_rfl

@[reducible] def circuit32 input := add32_full (p:=p) input
#eval ExplicitCircuit.local_length (circuit32 default) 0
#eval ExplicitCircuit.output (circuit32 default) 0

example : ExplicitCircuit.final_offset (circuit32 default) 0 = 8 := by
  dsimp only [explicit_norm, explicit, Boolean.circuit]

example : ExplicitCircuit.output (circuit32 default) 0
    = { z := { x0 := var ⟨0⟩, x1 := var ⟨2⟩, x2 := var ⟨4⟩, x3 := var ⟨6⟩ }, carry_out := var ⟨7⟩ } := by
  dsimp only [explicit_norm, explicit, Boolean.circuit]

example (input : Var Inputs (F p)) (env) (i0 : ℕ) :
    Circuit.constraints_hold.soundness env ((circuit32 input).operations i0) := by
  let ⟨ x, y, carry_in ⟩ := input
  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y

  -- these are equivalent ways of rewriting the constraints
  -- the second one relies on prior inference of a `ExplicitCircuit` instance
  -- note that the second one only uses a handful of theorems (much fewer than `circuit_norm` + `subcircuit_norm`)
  -- for 90% of the unfolding; and doesn't even need to unfold names like `add32_full` and `add8_full_carry`

  -- TODO on the whole, which is better?

  -- first version: using `circuit_norm`
  -- dsimp only [circuit_norm, circuit32, add32_full, add8_full_carry, Boolean.circuit]
  -- simp only [subcircuit_norm, circuit_norm]

  -- second version: using `ExplicitCircuit`
  -- resolve explicit circuit operations
  dsimp only [lawful_norm, explicit, Boolean.circuit]
  -- simp constraints hold expression
  simp only [append_empty, empty_append, append_assoc, append_val, Circuit.constraints_hold.append_soundness, Circuit.constraints_hold.soundness]
  -- simp `eval` and boolean subcircuit soundness
  simp only [subcircuit_norm, circuit_norm]
  sorry
