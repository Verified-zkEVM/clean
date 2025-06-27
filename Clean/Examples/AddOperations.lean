import Clean.Utils.Primes
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Addition32.Addition32Full

section
def circuit := do
  let x ← witness (F := F pBabybear) (fun _ => 246)
  let y ← witness (fun _ => 20)
  let z ← Gadgets.Addition8.circuit.main { x, y }
  Gadgets.Addition8.circuit.main { x, y := z }

-- #eval circuit.operations

-- #eval circuit.witnesses

-- #eval Gadgets.Addition32Full.circuit (p:=pBabybear) |>.localLength default

-- #eval (do Gadgets.Addition32Full.add32_full (p:=pBabybear) (← default)).operations
end
