import Clean.Circuit.Basic
import Clean.Types.U32
import Clean.Utils.Tactics

namespace Examples.YieldExample.U32NormalizedAssertion

variable {p : ℕ} [Fact p.Prime]

/--
Main circuit that uses yielded byte values to check U32 normalization
-/
def main (input : Var U32 (F p)) : Circuit (F p) Unit := do
  -- Use the yielded byte values for each limb
  use ⟨"byte", [input.x0]⟩
  use ⟨"byte", [input.x1]⟩
  use ⟨"byte", [input.x2]⟩
  use ⟨"byte", [input.x3]⟩
  return ()

def elaborated : ElaboratedCircuit (F p) U32 unit where
  main
  localLength _ := 0
  localLength_eq := by simp [circuit_norm, main]
  yields _ _ _ := ∅
  yields_eq := by intros; simp [circuit_norm, main]
  subcircuitsConsistent := by simp [circuit_norm, main]

/--
Assumptions:
1. All yielded "byte" NamedLists with single element must have value < 256 (for soundness)
2. All bytes [0..255] are in the yielded set (for completeness)
-/
def Assumptions (_ : U32 (F p)) (yielded : Set (NamedList (F p))) : Prop :=
  ∀ (v : F p), ⟨"byte", [v]⟩ ∈ yielded ↔ v.val < 256

/--
Spec: The U32 input is normalized
-/
def Spec (input : U32 (F p)) : Prop :=
  input.Normalized

theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [NamedList.eval, U32.Normalized]
  obtain ⟨ x0, x1, x2, x3 ⟩ := input
  simp only [ne_eq, one_ne_zero, not_false_eq_true, forall_const] at h_holds
  simp_all only [explicit_provable_type, circuit_norm, U32.mk.injEq]

theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [NamedList.eval, U32.Normalized]
  obtain ⟨ x0, x1, x2, x3 ⟩ := input
  simp_all only [explicit_provable_type, circuit_norm, U32.mk.injEq]

def circuit : FormalAssertion (F p) U32 where
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Examples.YieldExample.U32NormalizedAssertion
