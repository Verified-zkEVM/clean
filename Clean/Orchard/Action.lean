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

/-!
Reference:
`orchard@0.14.0/src/circuit.rs`
- `Circuit::synthesize`

This assertion models the source-level action wiring that connects computed gadget
outputs to public inputs or explicitly witnessed values:
- `cv_net`, `nf_old`, `rk`, and `cmx` are constrained to public instance columns.
- derived `pk_d_old` and `cm_old` are constrained equal to the corresponding witnesses.
- `rho_new` is assigned from `nf_old`.
- the final `Orchard circuit checks` gate is enabled over the shared row values.

It does not model the internal Merkle, note-commitment, value-commitment, nullifier,
or spend-authority sub-gadgets; those are represented by the row's explicit computed
values and by the lower-level assertions in other Orchard modules.
-/

namespace ActionWiring

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
  cvNetX : F
  cvNetY : F
  publicCvNetX : F
  publicCvNetY : F
  nfOld : F
  publicNfOld : F
  rhoNew : F
  rkX : F
  rkY : F
  publicRkX : F
  publicRkY : F
  derivedPkDOldX : F
  derivedPkDOldY : F
  pkDOldX : F
  pkDOldY : F
  derivedCmOldX : F
  derivedCmOldY : F
  cmOldX : F
  cmOldY : F
  cmxNew : F
  publicCmx : F
deriving ProvableStruct

def checksRow (row : Row R) : ActionChecks.Row R where
  vOld := row.vOld
  vNew := row.vNew
  magnitude := row.magnitude
  sign := row.sign
  root := row.root
  anchor := row.anchor
  enableSpends := row.enableSpends
  enableOutputs := row.enableOutputs

def cvNetXCheck (row : Row R) : R := row.cvNetX - row.publicCvNetX
def cvNetYCheck (row : Row R) : R := row.cvNetY - row.publicCvNetY
def nfOldCheck (row : Row R) : R := row.nfOld - row.publicNfOld
def rhoNewCheck (row : Row R) : R := row.rhoNew - row.nfOld
def rkXCheck (row : Row R) : R := row.rkX - row.publicRkX
def rkYCheck (row : Row R) : R := row.rkY - row.publicRkY
def pkDOldXCheck (row : Row R) : R := row.derivedPkDOldX - row.pkDOldX
def pkDOldYCheck (row : Row R) : R := row.derivedPkDOldY - row.pkDOldY
def cmOldXCheck (row : Row R) : R := row.derivedCmOldX - row.cmOldX
def cmOldYCheck (row : Row R) : R := row.derivedCmOldY - row.cmOldY
def cmxCheck (row : Row R) : R := row.cmxNew - row.publicCmx

def constraints (row : Row R) : Prop :=
  ActionChecks.constraints (checksRow row) ∧
    cvNetXCheck row = 0 ∧
    cvNetYCheck row = 0 ∧
    nfOldCheck row = 0 ∧
    rhoNewCheck row = 0 ∧
    rkXCheck row = 0 ∧
    rkYCheck row = 0 ∧
    pkDOldXCheck row = 0 ∧
    pkDOldYCheck row = 0 ∧
    cmOldXCheck row = 0 ∧
    cmOldYCheck row = 0 ∧
    cmxCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  ActionChecks.main (checksRow row)
  assertZero (cvNetXCheck row)
  assertZero (cvNetYCheck row)
  assertZero (nfOldCheck row)
  assertZero (rhoNewCheck row)
  assertZero (rkXCheck row)
  assertZero (rkYCheck row)
  assertZero (pkDOldXCheck row)
  assertZero (pkDOldYCheck row)
  assertZero (cmOldXCheck row)
  assertZero (cmOldYCheck row)
  assertZero (cmxCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, checksRow, ActionChecks.main,
      ActionChecks.constraints, ActionChecks.valueNet, ActionChecks.merklePathValidity,
      ActionChecks.spendEnabled, ActionChecks.outputEnabled, cvNetXCheck, cvNetYCheck,
      nfOldCheck, rhoNewCheck, rkXCheck, rkYCheck, pkDOldXCheck, pkDOldYCheck,
      cmOldXCheck, cmOldYCheck, cmxCheck]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, checksRow, ActionChecks.main,
      ActionChecks.constraints, ActionChecks.valueNet, ActionChecks.merklePathValidity,
      ActionChecks.spendEnabled, ActionChecks.outputEnabled, cvNetXCheck, cvNetYCheck,
      nfOldCheck, rhoNewCheck, rkXCheck, rkYCheck, pkDOldXCheck, pkDOldYCheck,
      cmOldXCheck, cmOldYCheck, cmxCheck]
    simp_all [sub_eq_add_neg]

end ActionWiring
end Orchard
