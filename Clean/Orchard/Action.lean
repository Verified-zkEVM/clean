import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard action checks

Clean approximations of Orchard action-level arithmetic gates.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Orchard circuit checks`

This assertion models the four arithmetic constraints enabled by the Halo2
`q_orchard` selector, not the selector, column layout, or region assignment machinery.
-/

namespace Orchard
namespace ActionChecks

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

structure Row (F : Type) where
  vOld : F
  vNew : F
  magnitude : F
  sign : F
  root : F
  anchor : F
  enableSpends : F
  enableOutputs : F
deriving ProvableStruct

def valueNet (row : Row R) : R :=
  row.vOld - row.vNew - row.magnitude * row.sign

def merklePathValidity (row : Row R) : R :=
  row.vOld * (row.root - row.anchor)

def spendEnabled (row : Row R) : R :=
  row.vOld * (1 - row.enableSpends)

def outputEnabled (row : Row R) : R :=
  row.vNew * (1 - row.enableOutputs)

def constraints (row : Row R) : Prop :=
  valueNet row = 0 ∧
    merklePathValidity row = 0 ∧
    spendEnabled row = 0 ∧
    outputEnabled row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (valueNet row)
  assertZero (merklePathValidity row)
  assertZero (spendEnabled row)
  assertZero (outputEnabled row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, valueNet, merklePathValidity,
      spendEnabled, outputEnabled]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, valueNet, merklePathValidity,
      spendEnabled, outputEnabled]
    simp_all [sub_eq_add_neg]

end ActionChecks
end Orchard
