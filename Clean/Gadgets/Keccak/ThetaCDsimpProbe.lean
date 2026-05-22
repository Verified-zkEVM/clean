import Clean.Circuit.Loops
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState

namespace Gadgets.Keccak256.ThetaCDsimpProbe

set_option maxHeartbeats 20000

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakRow (F p)) :=
  .mapFinRange 5 fun i => do
    let c ← Xor64.circuit ⟨state[5*i.val], state[5*i.val + 1]⟩
    let c ← Xor64.circuit ⟨c, state[5*i.val + 2]⟩
    let c ← Xor64.circuit ⟨c, state[5*i.val + 3]⟩
    let c ← Xor64.circuit ⟨c, state[5*i.val + 4]⟩
    return c

/--
Copyable low-heartbeat repro for the current generated dsimp calls.

Run this file directly with debug output enabled:
```
lake env lean -Ddebug.explicitCircuitReduced=true Clean/Gadgets/Keccak/ThetaCDsimpProbe.lean
```

The reduced elaboration currently prints two dsimp passes for `localLength` and two for `output`:
```
dsimp only [explicit_circuit_norm, Gadgets.Keccak256.ThetaCDsimpProbe.main,
  Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit]
dsimp only [explicit_circuit_norm, Gadgets.Keccak256.ThetaCDsimpProbe.main,
  Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit, Gadgets.Xor64.main,
  Witnessable.witness]
```

The corresponding command is:
```
example : ElaboratedCircuit (F p) KeccakState KeccakRow main := by
  infer_elaborated_circuit_reduced
```
It times out with `maxHeartbeats 20000` after those normalization passes, while building/checking
record proof fields.
-/
example : True := by trivial

end Gadgets.Keccak256.ThetaCDsimpProbe
