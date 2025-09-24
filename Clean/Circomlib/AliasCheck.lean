import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.CompConstant

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/aliascheck.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]
instance hp135 : Fact (p > 2^135) := .mk (by linarith [‹Fact (p > 2^253)›.elim])

namespace AliasCheck
/-
template AliasCheck() {

    signal input in[254];

    component  compConstant = CompConstant(-1);

    for (var i=0; i<254; i++) in[i] ==> compConstant.in[i];

    compConstant.out === 0;
}
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Vector (Expression (F p)) 254) : Circuit sentences Unit := do
  -- CompConstant(-1) means we're comparing against p-1 (since -1 ≡ p-1 mod p)
  let comp_out ← CompConstant.circuit order (p - 1) input
  comp_out ===[order] 0

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalAssertion order (fields 254) where
  main := main order
  localLength _ := 127 + 1 + 135 + 1

  Assumptions input := ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

  Spec _ bits := fromBits (bits.map ZMod.val) < p

  soundness := by
    simp only [circuit_norm, main, CompConstant.circuit]
    intros offset env yields checked input_var input h_input h_assumption h_holds
    constructor
    · -- Prove yielded sentences hold (vacuous - no yields)
      intro s hs _
      simp only [CompConstant.main, Gadgets.Equality.circuit, Gadgets.Equality.elaborated, HasAssignEq.assignEq, FormalCircuit.toSubcircuit, circuit_norm, FormalAssertion.toSubcircuit, Gadgets.Equality.main, Num2Bits.circuit, GeneralFormalCircuit.toSubcircuit, Num2Bits.arbitraryBitLengthCircuit] at hs
      simp only [Num2Bits.main, circuit_norm, FormalAssertion.toSubcircuit, Gadgets.Equality.main] at hs
      simp only [Gadgets.allZero, circuit_norm] at hs
      rw [Circuit.foldlRange.localYields_empty] at hs
      · simp only [Set.empty_union] at hs
        exact absurd hs (Set.notMem_empty s)
      · intro acc i n
        sorry -- Need: Operations.localYields of subcircuit with forEach/assertZero is empty
    have : p > 2^135 := hp135.elim
    rcases h_holds with ⟨ h_holds1, h_holds3 ⟩
    simp only [h_holds3, h_input] at h_holds1
    specialize h_holds1 (by
      intros i x
      specialize h_assumption i x
      simp only [← h_input] at h_assumption
      aesop)
    rcases h_holds1 with ⟨ h_holds11, h_holds12 ⟩
    split at h_holds12
    · aesop
    · omega

  completeness := by
    simp only [circuit_norm, main, CompConstant.circuit, CompConstant.CompletenessAssumptions]
    simp_all
    omega

end AliasCheck

end Circomlib
