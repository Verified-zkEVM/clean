import Clean.Gadgets.SHA256.Add32
import Clean.Gadgets.SHA256.Ch32
import Clean.Gadgets.SHA256.Maj32
import Clean.Gadgets.SHA256.UpperSigma0
import Clean.Gadgets.SHA256.UpperSigma1
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# SHA-256 Round Function

Implements one round of the SHA-256 compression function at the bit level,
using only R1CS constraints (no lookup tables).

State convention: `Vector (Var (fields 32) (F p)) 8` holds [a, b, c, d, e, f, g, h],
where each word is a 32-bit vector with LSB at index 0.

Witness count per round:
  upperSigma1 = 64, ch32 = 32, 4×add32 = 4×33 = 132 for t1 chain
  upperSigma0 = 64, maj32 = 64, add32 = 33 for t2
  2×add32 = 2×33 = 66 for new_a, new_e
  Total: 64 + 32 + 132 + 64 + 64 + 33 + 66 = 455
-/

/-- One round of SHA-256 compression.

    state = [a, b, c, d, e, f, g, h], each a 32-bit word (fields 32).
    k: round constant as a 32-bit word.
    w: message schedule word as a 32-bit word.
-/
def sha256Round
    (state : Vector (Var (fields 32) (F p)) 8)
    (k w : Var (fields 32) (F p))
    : Circuit (F p) (Vector (Var (fields 32) (F p)) 8) := do
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  -- t1 = h + Σ₁(e) + Ch(e,f,g) + k + w
  let sig1  ← upperSigma1 e
  let ch    ← ch32 e f g
  let t1_0  ← add32 h sig1
  let t1_1  ← add32 t1_0 ch
  let t1_2  ← add32 t1_1 k
  let t1    ← add32 t1_2 w
  -- t2 = Σ₀(a) + Maj(a,b,c)
  let sig0  ← upperSigma0 a
  let maj   ← maj32 a b c
  let t2    ← add32 sig0 maj
  -- new state
  let new_a ← add32 t1 t2
  let new_e ← add32 d t1
  return #v[new_a, a, b, c, new_e, e, f, g]

namespace SHA256Round

structure Inputs (F : Type) where
  state : SHA256State F
  k : fields 32 F
  w : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  sha256Round input.state input.k input.w

set_option maxHeartbeats 0 in
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 455
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.k ∧ Normalized input.w

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  let state_val : Vector ℕ 8 := input.state.map valueBits
  let k_val := valueBits input.k
  let w_val := valueBits input.w
  let expected := Specs.SHA256.sha256Round state_val k_val w_val
  ∀ i : Fin 8, valueBits out[i] = expected[i] ∧ Normalized out[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs SHA256State where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SHA256Round
end Gadgets.SHA256
end
