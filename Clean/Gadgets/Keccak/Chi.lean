import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.And.And64
import Clean.Gadgets.Not.Not64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Chi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
open Gadgets.Keccak256 (KeccakState)

def xor (x y : Var U64 (F p)) := subcircuit Xor.circuit ⟨x, y⟩
def and (x y : Var U64 (F p)) := subcircuit And.And64.circuit ⟨x, y⟩
def not (x : Var U64 (F p)) := subcircuit Not.circuit x

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do return #v[
  ←xor state[0] (←and (←not state[5]) state[10]),
  ←xor state[1] (←and (←not state[6]) state[11]),
  ←xor state[2] (←and (←not state[7]) state[12]),
  ←xor state[3] (←and (←not state[8]) state[13]),
  ←xor state[4] (←and (←not state[9]) state[14]),
  ←xor state[5] (←and (←not state[10]) state[15]),
  ←xor state[6] (←and (←not state[11]) state[16]),
  ←xor state[7] (←and (←not state[12]) state[17]),
  ←xor state[8] (←and (←not state[13]) state[18]),
  ←xor state[9] (←and (←not state[14]) state[19]),
  ←xor state[10] (←and (←not state[15]) state[20]),
  ←xor state[11] (←and (←not state[16]) state[21]),
  ←xor state[12] (←and (←not state[17]) state[22]),
  ←xor state[13] (←and (←not state[18]) state[23]),
  ←xor state[14] (←and (←not state[19]) state[24]),
  ←xor state[15] (←and (←not state[20]) state[0]),
  ←xor state[16] (←and (←not state[21]) state[1]),
  ←xor state[17] (←and (←not state[22]) state[2]),
  ←xor state[18] (←and (←not state[23]) state[3]),
  ←xor state[19] (←and (←not state[24]) state[4]),
  ←xor state[20] (←and (←not state[0]) state[5]),
  ←xor state[21] (←and (←not state[1]) state[6]),
  ←xor state[22] (←and (←not state[2]) state[7]),
  ←xor state[23] (←and (←not state[3]) state[8]),
  ←xor state[24] (←and (←not state[4]) state[9])
]

def assumptions := KeccakState.is_normalized (p:=p)

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

-- #eval! main (p:=p_babybear) default |>.operations.local_length
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakState (F p)) where
  main
  local_length _ := 400
  local_length_eq state i := by
    dsimp only [circuit_norm, main, not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit]

  output _ i0 := #v[
    var_from_offset U64 (i0 + 8),
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 40),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 72),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 104),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 136),
    var_from_offset U64 (i0 + 152),
    var_from_offset U64 (i0 + 168),
    var_from_offset U64 (i0 + 184),
    var_from_offset U64 (i0 + 200),
    var_from_offset U64 (i0 + 216),
    var_from_offset U64 (i0 + 232),
    var_from_offset U64 (i0 + 248),
    var_from_offset U64 (i0 + 264),
    var_from_offset U64 (i0 + 280),
    var_from_offset U64 (i0 + 296),
    var_from_offset U64 (i0 + 312),
    var_from_offset U64 (i0 + 328),
    var_from_offset U64 (i0 + 344),
    var_from_offset U64 (i0 + 360),
    var_from_offset U64 (i0 + 376),
    var_from_offset U64 (i0 + 392)
  ]
  output_eq state i := by
    dsimp only [circuit_norm, main, not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit]

theorem soundness : Soundness (F p) assumptions spec := by
  sorry

theorem completeness : Completeness (F p) KeccakState assumptions := by
  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakState where
  assumptions
  spec
  soundness
  completeness
end Gadgets.Keccak256.Chi
