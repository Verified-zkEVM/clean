import Clean.Circuit
import Clean.Orchard.Sinsemilla
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard action checks

Clean ports of Orchard action-level arithmetic gates and copy constraints.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Orchard circuit checks`

This assertion models the four arithmetic constraints enabled by the Halo2
`q_orchard` selector, not the selector, column layout, or region assignment machinery.
-/

namespace Orchard
namespace ActionChecks

variable {F : Type} [Field F]

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

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

def valueNet {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.vOld - row.vNew - row.magnitude * row.sign

def merklePathValidity {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.vOld * (row.root - row.anchor)

def spendEnabled {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  row.vOld * (1 - row.enableSpends)

def outputEnabled {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  row.vNew * (1 - row.enableOutputs)

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.vOld = row.vNew + row.magnitude * row.sign ∧
    (row.vOld = 0 ∨ row.root = row.anchor) ∧
    (row.vOld = 0 ∨ row.enableSpends = 1) ∧
    (row.vNew = 0 ∨ row.enableOutputs = 1)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (valueNet row)
  assertZero (merklePathValidity row)
  assertZero (spendEnabled row)
  assertZero (outputEnabled row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  name := "GATE Orchard circuit checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, valueNet, merklePathValidity, spendEnabled, outputEnabled]
    rcases h_holds with ⟨hValue, hRoot, hSpend, hOutput⟩
    constructor
    · apply sub_eq_zero.mp
      ring_nf at hValue ⊢
      exact hValue
    constructor
    · exact (mul_eq_zero.mp hRoot).imp_right fun h => left_eq_of_add_neg_eq_zero h
    constructor
    · exact (mul_eq_zero.mp hSpend).imp_right fun h =>
        (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm
    exact (mul_eq_zero.mp hOutput).imp_right fun h =>
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm
  completeness := by
    circuit_proof_start [main, Spec, valueNet, merklePathValidity, spendEnabled, outputEnabled]
    rcases h_spec with ⟨hValue, hRoot, hSpend, hOutput⟩
    constructor
    · rw [hValue]
      ring
    constructor
    · exact mul_eq_zero_of_or (hRoot.imp_right fun h => by rw [h]; ring)
    constructor
    · exact mul_eq_zero_of_or (hSpend.imp_right fun h => by rw [h]; ring)
    exact mul_eq_zero_of_or (hOutput.imp_right fun h => by rw [h]; ring)

end ActionChecks

/-!
Reference:
`orchard@0.14.0/src/circuit.rs`
- `Circuit::synthesize`

This assertion records the action-row copy and public-input constraints from
`Circuit::synthesize`:
- `cv_net`, `nf_old`, `rk`, and `cmx` are constrained to public instance columns.
- derived `pk_d_old` and `cm_old` are constrained equal to the corresponding witnesses.
- `rho_new` is assigned from `nf_old`.
- the final `Orchard circuit checks` gate is enabled over the shared row values.

TODO(source-conformance): implement the full action synthesis entry circuit that composes
Merkle, note-commitment, value-commitment, nullifier, spend-authority, and address
integrity sub-gadgets internally.
-/

namespace ActionWiring

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

def checksRow {K : Type} (row : Row K) : ActionChecks.Row K where
  vOld := row.vOld
  vNew := row.vNew
  magnitude := row.magnitude
  sign := row.sign
  root := row.root
  anchor := row.anchor
  enableSpends := row.enableSpends
  enableOutputs := row.enableOutputs

def cvNetXCheck {K : Type} [Sub K] (row : Row K) : K := row.cvNetX - row.publicCvNetX
def cvNetYCheck {K : Type} [Sub K] (row : Row K) : K := row.cvNetY - row.publicCvNetY
def nfOldCheck {K : Type} [Sub K] (row : Row K) : K := row.nfOld - row.publicNfOld
def rhoNewCheck {K : Type} [Sub K] (row : Row K) : K := row.rhoNew - row.nfOld
def rkXCheck {K : Type} [Sub K] (row : Row K) : K := row.rkX - row.publicRkX
def rkYCheck {K : Type} [Sub K] (row : Row K) : K := row.rkY - row.publicRkY
def pkDOldXCheck {K : Type} [Sub K] (row : Row K) : K := row.derivedPkDOldX - row.pkDOldX
def pkDOldYCheck {K : Type} [Sub K] (row : Row K) : K := row.derivedPkDOldY - row.pkDOldY
def cmOldXCheck {K : Type} [Sub K] (row : Row K) : K := row.derivedCmOldX - row.cmOldX
def cmOldYCheck {K : Type} [Sub K] (row : Row K) : K := row.derivedCmOldY - row.cmOldY
def cmxCheck {K : Type} [Sub K] (row : Row K) : K := row.cmxNew - row.publicCmx

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  ActionChecks.Spec (checksRow row) ∧
    row.cvNetX = row.publicCvNetX ∧
    row.cvNetY = row.publicCvNetY ∧
    row.nfOld = row.publicNfOld ∧
    row.rhoNew = row.nfOld ∧
    row.rkX = row.publicRkX ∧
    row.rkY = row.publicRkY ∧
    row.derivedPkDOldX = row.pkDOldX ∧
    row.derivedPkDOldY = row.pkDOldY ∧
    row.derivedCmOldX = row.cmOldX ∧
    row.derivedCmOldY = row.cmOldY ∧
    row.cmxNew = row.publicCmx

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  ActionChecks.circuit (checksRow row)
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

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, checksRow, ActionChecks.circuit, ActionChecks.Spec,
      cvNetXCheck, cvNetYCheck, nfOldCheck, rhoNewCheck, rkXCheck, rkYCheck,
      pkDOldXCheck, pkDOldYCheck, cmOldXCheck, cmOldYCheck, cmxCheck]
    rcases h_holds with
      ⟨hChecks, hCvX, hCvY, hNf, hRho, hRkX, hRkY, hPkDX, hPkDY, hCmX, hCmY, hCmx⟩
    change ActionChecks.Spec
      { vOld := input_vOld, vNew := input_vNew, magnitude := input_magnitude,
        sign := input_sign, root := input_root, anchor := input_anchor,
        enableSpends := input_enableSpends, enableOutputs := input_enableOutputs } at hChecks
    exact ⟨hChecks,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNf),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRho),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hPkDX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hPkDY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCmX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCmY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCmx)⟩
  completeness := by
    circuit_proof_start [main, Spec, checksRow, ActionChecks.circuit, ActionChecks.Spec,
      cvNetXCheck, cvNetYCheck, nfOldCheck, rhoNewCheck, rkXCheck, rkYCheck,
      pkDOldXCheck, pkDOldYCheck, cmOldXCheck, cmOldYCheck, cmxCheck]
    rcases h_spec with
      ⟨hChecks, hCvX, hCvY, hNf, hRho, hRkX, hRkY, hPkDX, hPkDY, hCmX, hCmY, hCmx⟩
    change ActionChecks.Spec
      { vOld := input_vOld, vNew := input_vNew, magnitude := input_magnitude,
        sign := input_sign, root := input_root, anchor := input_anchor,
        enableSpends := input_enableSpends, enableOutputs := input_enableOutputs } at hChecks
    exact ⟨hChecks,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hNf,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRho,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hPkDX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hPkDY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCmX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCmY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCmx⟩

end ActionWiring

/-!
TODO(source-conformance): action computed-output wiring is not implemented.

The deleted wrapper composed non-conformant value-commitment, nullifier, and
spend-authority wrappers that exposed internally computed fixed-base products and hash
outputs as row inputs.
-/

/-!
TODO(source-conformance): old/new note-commitment action wiring is not implemented.

The deleted wrapper depended on `gadgets::note_commit` being modeled as an entry circuit
that computes the Sinsemilla commitment and blinding scalar multiplication internally.
-/

/-!
Action wiring with the Merkle path root.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Merkle path validity check`
- final `Orchard circuit checks`

`MerklePath::calculate_root` repeats the Merkle path-step gadget and returns the final
node as `root`. This assertion connects one final `PathStep` output to the action row's
`root`; repeating `Sinsemilla.Merkle.PathStep.circuit` outside this assertion models the
whole path.
-/
namespace ActionMerkleWiring

structure Row (F : Type) where
  action : ActionWiring.Row F
  finalStep : Sinsemilla.Merkle.PathStep.Row F
deriving ProvableStruct

def rootCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.finalStep.nextNode - row.action.root

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  ActionWiring.Spec row.action ∧
    Sinsemilla.Merkle.PathStep.Spec row.finalStep ∧
    row.finalStep.nextNode = row.action.root

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  ActionWiring.circuit row.action
  Sinsemilla.Merkle.PathStep.circuit row.finalStep
  assertZero (rootCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, rootCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Sinsemilla.Merkle.PathStep.circuit, Sinsemilla.Merkle.PathStep.Spec]
    rcases h_holds with ⟨hAction, hStep, hRoot⟩
    exact ⟨hAction, hStep,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRoot)⟩
  completeness := by
    circuit_proof_start [main, Spec, rootCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Sinsemilla.Merkle.PathStep.circuit, Sinsemilla.Merkle.PathStep.Spec]
    rcases h_spec with ⟨hAction, hStep, hRoot⟩
    exact ⟨hAction, hStep,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRoot⟩

end ActionMerkleWiring

/-!
TODO(source-conformance): diversified-address integrity wiring is not implemented.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Diversified address integrity`
- final public-input/action wiring in `Circuit::synthesize`

The replacement should compute `ivk = CommitIvk(ak, nk, rivk)`, convert it to the
variable-base scalar, compute `[ivk] g_d_old`, and constrain the result to `pk_d_old`
inside the entry circuit. The deleted wrapper exposed the derived point as row inputs.
-/
end Orchard
