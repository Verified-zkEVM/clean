import Clean.Utils.Primes
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Addition32.Addition32Full

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

def circuit32 := do Gadgets.Addition32Full.add32_full (p:=p) (← default)
#eval circuit32.operation_list

-- lawful circuit experiments
open Gadgets.Addition32Full (add32_full Inputs)
instance (input : Var Inputs (F p)) : LawfulCircuit (add32_full input) := by infer_lawful_circuit

@[reducible] def c := add32_full (p:=p_babybear) default
#eval LawfulCircuit.final_offset c 0
#eval LawfulCircuit.output c 0

example : LawfulCircuit.final_offset c 0 = 8 := by
  dsimp only [LawfulCircuit.final_offset, Boolean.circuit]
example : LawfulCircuit.output c 0
    = { z := { x0 := var ⟨0⟩, x1 := var ⟨2⟩, x2 := var ⟨4⟩, x3 := var ⟨6⟩ }, carry_out := var ⟨7⟩ } := by
  dsimp only [LawfulCircuit.final_offset, LawfulCircuit.output, Boolean.circuit]

example (i0 : ℕ) : (LawfulCircuit.operations (circuit:=c) i0).val = .empty (F:=F p_babybear) (i0 + 8) := by
  dsimp only [LawfulCircuit.operations, LawfulCircuit.final_offset, LawfulCircuit.output, Boolean.circuit]
  open OperationsFrom in
  simp only [append_empty, empty_append, append_assoc, append_val]
  -- simp
  sorry
end
