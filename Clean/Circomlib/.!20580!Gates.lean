import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Boolean
import Clean.Utils.Bitwise
import Clean.Utils.Vector
import Clean.Utils.BinaryOps
import Clean.Circuit.Theorems
import Mathlib.Data.Nat.Bitwise

open IsBool

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
-/

namespace Circomlib
variable {p : ℕ} [Fact p.Prime]

open Circuit (bind_output_eq bind_localLength_eq bind_forAll)
open Operations (append_localLength)
open BinaryOps (List.foldl_and_IsBool List.and_foldl_eq_foldl)

namespace XOR
/-
template XOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - 2*a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - 2*a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
