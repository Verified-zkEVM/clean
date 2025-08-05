import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZeroField

variable {p : ℕ} [Fact p.Prime]

/--
Main circuit that checks if a field element is zero.
Returns 1 if the input is 0, otherwise returns 0.
-/
def main (x : Var field (F p)) : Circuit (F p) (Var field (F p)) := do
  let isZero ← witness fun env => if x.eval env = 0 then (1 : F p) else 0

  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let x_inv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F p)⁻¹

  isZero * x === 0  -- If isZero = 1, then x must be 0
  isZero * (isZero - 1) === 0  -- isZero must be boolean (0 or 1)

  -- If isZero = 0 (i.e., x ≠ 0), then x * x_inv = 1, so x is non-zero
  (1 - isZero) * x * x_inv === (1 - isZero)

  return isZero

instance elaborated : ElaboratedCircuit (F p) field field where
  main := main
  localLength _ := 2  -- 2 witnesses: isZero and x_inv

def Assumptions (_ : F p) : Prop := True

def Spec (x : F p) (output : F p) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  split
  · rename_i h_input
    simp only [h_input] at *
    norm_num at *
    rcases h_holds with ⟨ _, h_one ⟩
    symm
    apply sub_eq_zero.mp
    simp only [h_one]
    ring_nf
  · aesop

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  aesop

def circuit : FormalCircuit (F p) field field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZeroField
