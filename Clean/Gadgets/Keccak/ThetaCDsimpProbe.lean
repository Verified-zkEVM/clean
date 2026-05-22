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

/-- This is the explicit proof term inferred by `infer_elaborated_circuit_reduced`. -/
def explicitManual : ExplicitCircuits (F:=F p) main :=
  ExplicitCircuits.fromSingle fun _ => Circuit.ExplicitCircuit.from_mapFinRange

/-- Written-out replay of the generated `localLength` normalization steps.

This intentionally stops after replaying the generated dsimp calls: the remaining goal shows what the
current reduced elaboration tactic is still leaving to the elaborator/kernel.
-/
example (state : Var KeccakState (F p)) :
    @ExplicitCircuits.localLength (F p) _ _ _ main explicitManual state 0 = 160 := by
  dsimp only [explicit_circuit_norm, explicitManual, Gadgets.Keccak256.ThetaCDsimpProbe.main,
    Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit]
  try dsimp only [explicit_circuit_norm, explicitManual, Gadgets.Keccak256.ThetaCDsimpProbe.main,
    Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit, Gadgets.Xor64.main,
    Witnessable.witness]
  admit

/-- Written-out replay of the generated `output` normalization steps.

This intentionally stops after replaying the generated dsimp calls: the remaining goal shows what the
current reduced elaboration tactic is still leaving to the elaborator/kernel.
-/
example (state : Var KeccakState (F p)) (i0 : ℕ) :
    @ExplicitCircuits.output (F p) _ _ _ main explicitManual state i0 =
      Vector.mapFinRange 5 fun i => varFromOffset U64 (i0 + i * 32 + 24) := by
  dsimp only [explicit_circuit_norm, explicitManual, Gadgets.Keccak256.ThetaCDsimpProbe.main,
    Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit]
  try dsimp only [explicit_circuit_norm, explicitManual, Gadgets.Keccak256.ThetaCDsimpProbe.main,
    Gadgets.Xor64.circuit, instExplicitCircuitVarSubcircuit, Gadgets.Xor64.main,
    Witnessable.witness]
  admit

end Gadgets.Keccak256.ThetaCDsimpProbe
