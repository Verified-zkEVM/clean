import Clean.Utils.Primes
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Addition32.Addition32Full

open Gadgets.Addition8FullCarry (add8_full_carry)
open Gadgets.Addition32Full (add32_full Inputs)
section
@[reducible] def p := p_babybear

def circuit := do
  let x ← witness (F := F p) (fun _ => 246)
  let y ← witness (fun _ => 20)
  let z ← Gadgets.Addition8.add8 { x, y }
  Gadgets.Addition8.add8 { x, y := z }

#eval circuit.operation_list

#eval circuit.witnesses

#eval Gadgets.Addition32Full.circuit (p:=p) |>.local_length default

#eval (do Gadgets.Addition32Full.add32_full (p:=p) (← default)).operation_list

-- lawful circuit experiments
instance (input : Var Inputs (F p)) : LawfulCircuit (add32_full input) := by infer_lawful_circuit

@[reducible] def circuit32 input := add32_full (p:=p_babybear) input
#eval LawfulCircuit.final_offset (circuit32 default) 0
#eval LawfulCircuit.output (circuit32 default) 0

example : LawfulCircuit.final_offset (circuit32 default) 0 = 8 := by
  dsimp only [LawfulCircuit.final_offset, Boolean.circuit]
example : LawfulCircuit.output (circuit32 default) 0
    = { z := { x0 := var ⟨0⟩, x1 := var ⟨2⟩, x2 := var ⟨4⟩, x3 := var ⟨6⟩ }, carry_out := var ⟨7⟩ } := by
  dsimp only [LawfulCircuit.final_offset, LawfulCircuit.output, Boolean.circuit]

open OperationsFrom in
example (input : Var Inputs (F p_babybear)) (i0 : ℕ) :
    (LawfulCircuit.operations (circuit:=circuit32 input) i0).val = .empty (F:=F p_babybear) (i0 + 8) := by
  dsimp only [LawfulCircuit.operations, LawfulCircuit.final_offset, LawfulCircuit.output]
  simp only [FormalAssertion.to_subcircuit]
  unfold Circuit.subassertion_soundness Circuit.subassertion_completeness
  simp only [Boolean.circuit]
  simp only [append_empty, empty_append, append_assoc, append_val]
  simp only [Nat.add_zero, id_eq, add_zero]
  let ⟨ x, y, carry_in ⟩ := input
  sorry

open OperationsFrom in
example (input : Var Inputs (F p_babybear)) (env) (i0 : ℕ) :
    Circuit.constraints_hold.soundness env ((circuit32 input).operations i0) ↔ True := by
  let ⟨ x, y, carry_in ⟩ := input
  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y

  -- dsimp only [circuit_norm, circuit32, add32_full, add8_full_carry, Boolean.circuit]
  -- simp only [circuit_norm, subcircuit_norm, true_and, and_true]

  simp only [LawfulCircuit.constraints_hold_eq.soundness]
  dsimp only [LawfulCircuit.operations, LawfulCircuit.final_offset, LawfulCircuit.output]
  simp only [append_empty, empty_append, append_assoc, append_val, Circuit.constraints_hold_append.soundness, Circuit.constraints_hold.soundness]
  simp only [true_and, and_true, subcircuit_norm, circuit_norm]
  sorry
end
