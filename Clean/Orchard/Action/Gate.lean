import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard action checks

Clean port of the Orchard action-level arithmetic gate.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Orchard circuit checks`

This assertion models the four arithmetic constraints enabled by the Halo2
`q_orchard` selector, not the selector, column layout, or region assignment machinery.
-/

namespace Orchard.Action.Gate

variable {F : Type} [FiniteField F]

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

structure Input (F : Type) where
  vOld : F
  vNew : F
  magnitude : F
  sign : F
  root : F
  anchor : F
  enableSpends : F
  enableOutputs : F
deriving ProvableStruct

def Spec (row : Input Fp) : Prop :=
  row.vOld = row.vNew + row.magnitude * row.sign ∧
    (row.vOld = 0 ∨ row.root = row.anchor) ∧
    (row.vOld = 0 ∨ row.enableSpends = 1) ∧
    (row.vNew = 0 ∨ row.enableOutputs = 1)

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (row.vOld - row.vNew - row.magnitude * row.sign)
  assertZero (row.vOld * (row.root - row.anchor))
  assertZero (row.vOld * (1 - row.enableSpends))
  assertZero (row.vNew * (1 - row.enableOutputs))

def circuit : FormalAssertion Fp Input where
  name := "GATE Orchard circuit checks"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hValue, hRoot, hSpend, hOutput⟩
    constructor
    · apply sub_eq_zero.mp
      ring_nf at hValue ⊢
      exact hValue
    constructor
    · exact (mul_eq_zero.mp hRoot).imp_right fun h => sub_eq_zero.mp h
    constructor
    · exact (mul_eq_zero.mp hSpend).imp_right fun h => (sub_eq_zero.mp h).symm
    exact (mul_eq_zero.mp hOutput).imp_right fun h => (sub_eq_zero.mp h).symm
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hValue, hRoot, hSpend, hOutput⟩
    constructor
    · rw [hValue]
      ring
    constructor
    · exact mul_eq_zero_of_or (hRoot.imp_right fun h => by rw [h]; ring)
    constructor
    · exact mul_eq_zero_of_or (hSpend.imp_right fun h => by rw [h]; ring)
    exact mul_eq_zero_of_or (hOutput.imp_right fun h => by rw [h]; ring)

end Orchard.Action.Gate
