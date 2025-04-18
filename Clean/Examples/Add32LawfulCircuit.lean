import Clean.Utils.Primes
import Clean.Gadgets.Addition32.Addition32Full

open Gadgets.Addition8FullCarry (add8_full_carry)
open Gadgets.Addition32Full (add32_full Inputs)

@[reducible] def p := p_babybear

-- `infer_lawful_circuit` / `infer_constant_lawful_circuits` seem to work for all circuits
instance : ConstantLawfulCircuits (add32_full (p:=p)) := by infer_constant_lawful_circuits

@[reducible] def circuit32 input := add32_full (p:=p) input
#eval LawfulCircuit.final_offset (circuit32 default) 0
#eval LawfulCircuit.output (circuit32 default) 0

example : LawfulCircuit.final_offset (circuit32 default) 0 = 8 := by
  dsimp only [LawfulCircuit.final_offset, ConstantLawfulCircuits.local_length, Boolean.circuit]

example : LawfulCircuit.output (circuit32 default) 0
    = { z := { x0 := var ⟨0⟩, x1 := var ⟨2⟩, x2 := var ⟨4⟩, x3 := var ⟨6⟩ }, carry_out := var ⟨7⟩ } := by
  dsimp only [LawfulCircuit.final_offset, ConstantLawfulCircuits.local_length, LawfulCircuit.output, ConstantLawfulCircuits.output, Boolean.circuit]

open OperationsFrom in
example (input : Var Inputs (F p)) (env) (i0 : ℕ) :
    Circuit.constraints_hold.soundness env ((circuit32 input).operations i0) := by
  let ⟨ x, y, carry_in ⟩ := input
  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y

  -- these are equivalent ways of rewriting the constraints
  -- the second one relies on prior inference of a `LawfulCircuit` instance
  -- note that the second one only uses a handful of theorems (much fewer than `circuit_norm` + `subcircuit_norm`)
  -- for 90% of the unfolding; and doesn't even need to unfold names like `add32_full` and `add8_full_carry`

  -- TODO on the whole, which is better?

  -- first version: using `circuit_norm`
  -- dsimp only [circuit_norm, circuit32, add32_full, add8_full_carry, Boolean.circuit]
  -- simp only [true_and, and_true, subcircuit_norm, circuit_norm]

  -- second version: using `LawfulCircuit`
  rw [LawfulCircuit.soundness_eq]
  -- resolve lawful circuit operations
  dsimp only [LawfulCircuit.operations, LawfulCircuit.final_offset, LawfulCircuit.output, Boolean.circuit,
    ConstantLawfulCircuits.local_length, ConstantLawfulCircuits.output, ConstantLawfulCircuits.operations]
  -- simp constraints hold expression
  simp only [append_empty, empty_append, append_assoc, append_val, Circuit.constraints_hold.append_soundness, Circuit.constraints_hold.soundness]
  -- simp `eval` and boolean subcircuit soundness
  simp only [true_and, and_true, subcircuit_norm, circuit_norm]
  sorry
