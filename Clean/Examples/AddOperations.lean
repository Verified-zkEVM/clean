import Clean.Utils.Primes
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Addition32.Addition32Full

section
@[reducible] def p := p_babybear

def circuit := do
  let x ← witness (F := F p) (fun _ => 246)
  let y ← witness (fun _ => 20)
  let z ← Gadgets.Addition8.circuit.main { x, y }
  Gadgets.Addition8.circuit.main { x, y := z }

-- #eval circuit.operations

-- #eval circuit.witnesses

-- #eval Gadgets.Addition32Full.circuit (p:=p) |>.localLength default

-- #eval (do Gadgets.Addition32Full.add32_full (p:=p) (← default)).operations
end
