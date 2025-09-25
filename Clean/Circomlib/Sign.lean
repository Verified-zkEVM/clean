import Clean.Circuit
import Clean.Utils.Field
import Clean.Utils.Bits
import Clean.Circomlib.CompConstant

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/sign.circom

The original Sign circuit uses a specific constant for the BN128 curve.
We generalize this to work with any prime field by using (p-1)/2.
-/

namespace Circomlib
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace Sign
/-
template Sign() {
    signal input in[254];
    signal output sign;

    component comp = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);

    var i;

    for (i=0; i<254; i++) {
        comp.in[i] <== in[i];
    }

    sign <== comp.out;
}
-/

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Vector (Expression (F p)) 254) : Circuit sentences (Expression (F p)) :=
  -- Use (p-1)/2 as the constant for comparison
  CompConstant.circuit order ((p - 1) / 2) input

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order (fields 254) field where
  main := main order
  localLength input := (CompConstant.circuit order ((p - 1) / 2)).localLength input
  yields _ _ _ := ∅

  yields_eq := by
    intros _ _ _
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [CompConstant.circuit]

  Assumptions input :=
    -- Input should be binary representation of a field element
    ∀ i (_ : i < 254), IsBool input[i]

  CompletenessAssumptions _ input :=
    -- Input should be binary representation of a field element
    ∀ i (_ : i < 254), IsBool input[i]

  completenessAssumptions_implies_assumptions _ _ h := h

  Spec _ input output :=
    -- The output is 1 if the input (as a number) is greater than (p-1)/2
    -- This effectively checks if the field element is in the "upper half" of the field
    output = if Utils.Bits.fromBits (input.map ZMod.val) > (p - 1) / 2 then 1 else 0

  soundness := by
    circuit_proof_start
    -- Proof follows easily from the fact that Sign is a
    -- specialization of CompConstant
    exact (h_holds h_assumptions).2

  completeness := by
    circuit_proof_start
    -- We're just left to prove CompConstant's assumptions are met
    -- which is trivial by h_assumptions
    exact h_assumptions

end Sign
end Circomlib
