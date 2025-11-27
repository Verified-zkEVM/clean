import Clean.Circuit
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Circomlib
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/sha256/rotate.circom
-/

namespace RotR

/-
template RotR(n, r) {
    signal input inp[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== inp[ (i+r)%n ];
    }
}
-/
def main (n r : ℕ) [NeZero n] (inp : Vector (Expression (F p)) n) := do
  let out <== Vector.mapFinRange n fun i => inp.get (i + Fin.ofNat n r)
  return out

def circuit (n r : ℕ) [NeZero n] : FormalCircuit (F p) (fields n) (fields n) where
  main := main n r

  localLength _ := n
-- Note: here rotate goes to the "left" from the array notation perspective, which
-- is the "right" from the bit notation perspective (Circom)
  Spec input output := output = input.rotate r

  soundness := by
    circuit_proof_start
    -- Use h_holds: circuit constraints hold, so output = circuit computation
    rw [h_holds]
    ext i hi
    -- Simplify LHS: circuit computation at index i
    simp only [Vector.getElem_map, Vector.getElem_mapFinRange]
    -- Simplify RHS: (input.rotate r)[i] = input[(i + r) % n]
    rw [Vector.getElem_rotate]
    simp only [Vector.get]
    -- Use h_input: eval input_var = input
    simp only [← h_input, Vector.getElem_map]
    congr 1
    -- Normalize array/vector indexing
    simp only [Vector.getElem_toArray]
    congr 1
    -- Prove index equality via Fin arithmetic
    simp [Fin.coe_cast, Fin.val_add]

  completeness := by
    circuit_proof_start
    -- element-wise equality
    ext i hi
    -- simplify output to witness value
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    -- witness = eval of rotated input
    rw [h_env ⟨i, hi⟩]
    -- simplify RHS to match
    rw [Vector.getElem_mapFinRange i hi]

end RotR
end Circomlib
