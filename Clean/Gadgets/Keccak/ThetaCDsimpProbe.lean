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

instance explicit : ExplicitCircuits (F:=F p) main := by
  apply ExplicitCircuits.fromSingle
  intro state
  unfold main
  infer_explicit_circuit

/-- Manual approximation of the current reduced-elaboration tactic's localLength normalization.
This is intentionally left as an `example : True`: uncomment the body below to reproduce the fast
low-heartbeat timeout seen in `ThetaC` reduced elaboration.

```
example (state : Var KeccakState (F p)) :
    ExplicitCircuits.localLength main state 0 = 160 := by
  dsimp only [explicit_circuit_norm, explicit, main, Xor64.circuit]
```
-/
example : True := by trivial

/-- Manual approximation of output normalization.  The analogous command is:

```
example (state : Var KeccakState (F p)) (i0 : ℕ) :
    ExplicitCircuits.output main state i0 =
      Vector.mapFinRange 5 fun i => varFromOffset U64 (i0 + i * 32 + 24) := by
  dsimp only [explicit_circuit_norm, explicit, main, Xor64.circuit]
```
-/
example : True := by trivial

end Gadgets.Keccak256.ThetaCDsimpProbe
