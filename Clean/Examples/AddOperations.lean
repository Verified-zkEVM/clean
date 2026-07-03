import Clean.Utils.Primes
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Addition32.Addition32Full

section
def circuit := do
  let x ← witness (F := F pBabybear) 246
  let y ← witness 20
  let z ← Gadgets.Addition8.circuit { x, y }
  let _w : Expression _ ← witness (x + 1)
  Gadgets.Addition8.circuit { x, y := z }

-- #eval circuit.operations 0

/-- info: #[246, 20, 10, 1, 247, 0, 1] -/
#guard_msgs in
#eval (circuit.operations 0).localWitnesses (circuit.proverEnvironment default)|>.toArray
end
