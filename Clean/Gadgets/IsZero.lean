import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Loops
import Clean.Gadgets.IsZeroField
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZero

variable {p : ℕ} [Fact p.Prime]
variable {M : TypeMap} [ProvableType M]

/--
Main circuit that checks if all components of a ProvableType are zero.
Returns 1 if all components are 0, otherwise returns 0.
-/
def main (input : Var M (F p)) : Circuit (F p) (Var field (F p)) := do
  let elemVars := toVars input
  -- Use foldlRange to multiply all IsZero results together
  -- Start with 1, and for each element, multiply by its IsZero result
  let result ← Circuit.foldlRange (size M) (1 : Expression (F p)) fun acc i => do
    let isZeroElem ← IsZeroField.circuit elemVars[i]
    return acc * isZeroElem
  return result

instance elaborated : ElaboratedCircuit (F p) M field where
  main := main
  localLength _ := 2 * size M  -- Each IsZeroField uses 2 witnesses
  localLength_eq := by
    simp only [main, circuit_norm]
    sorry
  subcircuitsConsistent := by
    intros
    sorry

def Assumptions (_ : M (F p)) : Prop := True

def Spec (input : M (F p)) (output : F p) : Prop :=
  output = if (∀ i : Fin (size M), (toElements input)[i] = 0) then 1 else 0

theorem soundness : Soundness (F p) (elaborated (M := M)) Assumptions Spec := by
  circuit_proof_start
  sorry

theorem completeness : Completeness (F p) (elaborated (M := M)) Assumptions := by
  circuit_proof_start
  sorry

def circuit : FormalCircuit (F p) M field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZero
