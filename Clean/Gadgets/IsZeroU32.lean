import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.IsZero
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Types.U32

namespace Gadgets.IsZeroU32

variable {p : ℕ} [Fact p.Prime]

/--
Main circuit that checks if a U32 (32-bit unsigned integer) is zero.
Returns 1 if all limbs are 0, otherwise returns 0.
-/
def main (x : Var U32 (F p)) : Circuit (F p) (Var field (F p)) := do
  -- x is zero iff all limbs are zero
  -- We'll use the IsZero gadget for each limb

  -- For each limb, check if it's zero using the IsZero gadget
  let isZero0 ← IsZero.circuit x.x0
  let isZero1 ← IsZero.circuit x.x1
  let isZero2 ← IsZero.circuit x.x2
  let isZero3 ← IsZero.circuit x.x3

  -- The U32 is zero iff all limbs are zero
  let result := isZero0 * isZero1 * isZero2 * isZero3
  return result

instance elaborated : ElaboratedCircuit (F p) U32 field where
  main := main
  localLength _ := 8  -- 4 calls to IsZero.main, each uses 2 witnesses
  localLength_eq := by
    simp [main, circuit_norm, IsZero.circuit, IsZero.elaborated]

def Assumptions (_ : U32 (F p)) : Prop := True

def Spec (x : U32 (F p)) (output : F p) : Prop :=
  output = if x.value = 0 then 1 else 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro offset env x_var x h_eval h_assumptions h_holds
  simp only [main, circuit_norm] at h_holds
  simp only [Spec]
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  simp [IsZero.circuit, IsZero.Assumptions]

def circuit : FormalCircuit (F p) U32 field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZeroU32
