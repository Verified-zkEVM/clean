module

public import Clean.Utils.Primes
public import Clean.Gadgets.Addition8.Addition8
public import Clean.Gadgets.Addition32.Addition32Full
public meta import Clean.Gadgets.Addition8.Addition8

-- `native_decide` runs compiled code from this module.
public meta import Clean.Utils.Primes

-- `circuit_norm`'s struct simprocs validate by `isDefEq` through `Array.ofFn`/`mapM`,
-- whose bodies core does not expose.
import all Init.Data.Array.Basic

@[expose] public section

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
