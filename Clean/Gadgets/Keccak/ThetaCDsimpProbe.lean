import Clean.Circuit
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

def explicit : ExplicitCircuits (F:=F p) main := by infer_explicit_circuits

def trueLength : ℕ := 160

example (state : Var KeccakState (F p)) :
    @ExplicitCircuits.localLength (F p) _ _ _ main explicit state 0 = trueLength := by
  dsimp only [explicit_circuit_norm, main, Gadgets.Xor64.circuit, explicit]
  -- this is nice!
  simp only [seval]
  dsimp only [trueLength]

def trueOutput (i0 : ℕ) : Vector (Var U64 (F p)) 5 := .mapFinRange 5 fun i => varFromOffset U64 (i0 + i * 32 + 24)

example (state : Var KeccakState (F p)) (i0 : ℕ) :
    @ExplicitCircuits.output (F p) _ _ _ main explicit state i0 = trueOutput i0 := by
  dsimp only [explicit_circuit_norm, main, Gadgets.Xor64.circuit, explicit]
  simp +arith only
  simp +arith only [trueOutput]

end Gadgets.Keccak256.ThetaCDsimpProbe
