import Clean.Circuit
import Clean.Orchard.CommitIvk
import Clean.Orchard.Gadget
import Clean.Orchard.NoteCommit
import Clean.Orchard.Sinsemilla
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

def valueNet (row : Row R) : R :=
  row.vOld - row.vNew - row.magnitude * row.sign

def merklePathValidity (row : Row R) : R :=
  row.vOld * (row.root - row.anchor)

def spendEnabled (row : Row R) : R :=
  row.vOld * (1 - row.enableSpends)

def outputEnabled (row : Row R) : R :=
  row.vNew * (1 - row.enableOutputs)

def Spec (row : Row R) : Prop :=
  row.vOld = row.vNew + row.magnitude * row.sign ∧
    (row.vOld = 0 ∨ row.root = row.anchor) ∧
    (row.vOld = 0 ∨ row.enableSpends = 1) ∧
    (row.vNew = 0 ∨ row.enableOutputs = 1)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (valueNet row)
  assertZero (merklePathValidity row)
  assertZero (spendEnabled row)
  assertZero (outputEnabled row)

def circuit : FormalAssertion F Row where
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

def Spec (row : Row R) : Prop :=
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

def main (row : Var Row F) : Circuit F Unit := do
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

def circuit : FormalAssertion F Row where
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
Action wiring with selected computed gadget outputs.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Value commitment integrity`
- `Spend authority`
- final public-input/action wiring in `Circuit::synthesize`

This assertion connects source-level gadget outputs into `ActionWiring.circuit`:
`value_commit_orchard` supplies `cv_net`, the nullifier gadget supplies `nf_old`, and
spend authority supplies `rk`. Other action sub-gadgets remain represented by the
explicit fields of `ActionWiring.Row` and their lower-level assertions.
-/
namespace ActionComputedWiring

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  action : ActionWiring.Row F
  valueCommitment : Gadget.ValueCommitment.Row F
  nullifier : Gadget.Nullifier.Row F
  spendAuth : Gadget.SpendAuth.Row F
deriving ProvableStruct

def cvXCheck (row : Row R) : R :=
  row.valueCommitment.cvX - row.action.cvNetX

def cvYCheck (row : Row R) : R :=
  row.valueCommitment.cvY - row.action.cvNetY

def nfCheck (row : Row R) : R :=
  row.nullifier.nf - row.action.nfOld

def rkXCheck (row : Row R) : R :=
  row.spendAuth.rkX - row.action.rkX

def rkYCheck (row : Row R) : R :=
  row.spendAuth.rkY - row.action.rkY

def Spec (row : Row R) : Prop :=
  ActionWiring.Spec row.action ∧
    Gadget.ValueCommitment.Spec row.valueCommitment ∧
    Gadget.Nullifier.Spec row.nullifier ∧
    Gadget.SpendAuth.Spec row.spendAuth ∧
    row.valueCommitment.cvX = row.action.cvNetX ∧
    row.valueCommitment.cvY = row.action.cvNetY ∧
    row.nullifier.nf = row.action.nfOld ∧
    row.spendAuth.rkX = row.action.rkX ∧
    row.spendAuth.rkY = row.action.rkY

def main (row : Var Row F) : Circuit F Unit := do
  ActionWiring.circuit row.action
  Gadget.ValueCommitment.circuit row.valueCommitment
  Gadget.Nullifier.circuit row.nullifier
  Gadget.SpendAuth.circuit row.spendAuth
  assertZero (cvXCheck row)
  assertZero (cvYCheck row)
  assertZero (nfCheck row)
  assertZero (rkXCheck row)
  assertZero (rkYCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, cvXCheck, cvYCheck, nfCheck, rkXCheck, rkYCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Gadget.ValueCommitment.circuit, Gadget.ValueCommitment.Spec,
      Gadget.Nullifier.circuit, Gadget.Nullifier.Spec,
      Gadget.SpendAuth.circuit, Gadget.SpendAuth.Spec]
    rcases h_holds with ⟨hAction, hValue, hNullifier, hSpendAuth, hCvX, hCvY, hNf, hRkX, hRkY⟩
    exact ⟨hAction, hValue, hNullifier, hSpendAuth,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNf),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkY)⟩
  completeness := by
    circuit_proof_start [main, Spec, cvXCheck, cvYCheck, nfCheck, rkXCheck, rkYCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Gadget.ValueCommitment.circuit, Gadget.ValueCommitment.Spec,
      Gadget.Nullifier.circuit, Gadget.Nullifier.Spec,
      Gadget.SpendAuth.circuit, Gadget.SpendAuth.Spec]
    rcases h_spec with ⟨hAction, hValue, hNullifier, hSpendAuth, hCvX, hCvY, hNf, hRkX, hRkY⟩
    exact ⟨hAction, hValue, hNullifier, hSpendAuth,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hNf,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkY⟩

namespace Entry

structure Row (F : Type) where
  action : ActionWiring.Row F
  valueCommitment : Gadget.ValueCommitment.Entry.Row F
  nullifier : Gadget.NullifierWithPoseidonBoundary.Entry.Row F
  spendAuth : Gadget.SpendAuth.Entry.Row F
deriving ProvableStruct

def cvXCheck (row : Row R) : R :=
  row.valueCommitment.cvX - row.action.cvNetX

def cvYCheck (row : Row R) : R :=
  row.valueCommitment.cvY - row.action.cvNetY

def nfCheck (row : Row R) : R :=
  row.nullifier.nullifier.nf - row.action.nfOld

def rkXCheck (row : Row R) : R :=
  row.spendAuth.rkX - row.action.rkX

def rkYCheck (row : Row R) : R :=
  row.spendAuth.rkY - row.action.rkY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  ActionWiring.Spec row.action ∧
    Gadget.ValueCommitment.Entry.Spec row.valueCommitment ∧
    Gadget.NullifierWithPoseidonBoundary.Entry.Spec row.nullifier ∧
    Gadget.SpendAuth.Entry.Spec row.spendAuth ∧
    row.valueCommitment.cvX = row.action.cvNetX ∧
    row.valueCommitment.cvY = row.action.cvNetY ∧
    row.nullifier.nullifier.nf = row.action.nfOld ∧
    row.spendAuth.rkX = row.action.rkX ∧
    row.spendAuth.rkY = row.action.rkY

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Gadget.ValueCommitment.Entry.Assumptions row.valueCommitment ∧
    Gadget.NullifierWithPoseidonBoundary.Entry.Assumptions row.nullifier ∧
    Gadget.SpendAuth.Entry.Assumptions row.spendAuth

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  ActionWiring.circuit row.action
  Gadget.ValueCommitment.Entry.circuit row.valueCommitment
  Gadget.NullifierWithPoseidonBoundary.Entry.circuit row.nullifier
  Gadget.SpendAuth.Entry.circuit row.spendAuth
  assertZero (cvXCheck row)
  assertZero (cvYCheck row)
  assertZero (nfCheck row)
  assertZero (rkXCheck row)
  assertZero (rkYCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, Assumptions, cvXCheck, cvYCheck, nfCheck, rkXCheck, rkYCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Gadget.ValueCommitment.Entry.circuit, Gadget.ValueCommitment.Entry.Spec,
      Gadget.NullifierWithPoseidonBoundary.Entry.circuit,
      Gadget.NullifierWithPoseidonBoundary.Entry.Spec,
      Gadget.SpendAuth.Entry.circuit, Gadget.SpendAuth.Entry.Spec]
    rcases h_assumptions with ⟨hValueAssumptions, hNullifierAssumptions, hSpendAssumptions⟩
    rcases h_holds with
      ⟨hAction, hValue, hNullifier, hSpendAuth, hCvX, hCvY, hNf, hRkX, hRkY⟩
    exact ⟨hAction, hValue hValueAssumptions, hNullifier hNullifierAssumptions,
      hSpendAuth hSpendAssumptions,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hCvY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNf),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hRkY)⟩
  completeness := by
    circuit_proof_start [main, Spec, Assumptions, cvXCheck, cvYCheck, nfCheck, rkXCheck, rkYCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Gadget.ValueCommitment.Entry.circuit, Gadget.ValueCommitment.Entry.Spec,
      Gadget.ValueCommitment.Entry.Assumptions,
      Gadget.NullifierWithPoseidonBoundary.Entry.circuit,
      Gadget.NullifierWithPoseidonBoundary.Entry.Spec,
      Gadget.NullifierWithPoseidonBoundary.Entry.Assumptions,
      Gadget.SpendAuth.Entry.circuit, Gadget.SpendAuth.Entry.Spec,
      Gadget.SpendAuth.Entry.Assumptions]
    rcases h_assumptions with ⟨hValueAssumptions, hNullifierAssumptions, hSpendAssumptions⟩
    rcases h_spec with
      ⟨hAction, hValue, hNullifier, hSpendAuth, hCvX, hCvY, hNf, hRkX, hRkY⟩
    exact ⟨hAction, ⟨hValueAssumptions, hValue⟩, ⟨hNullifierAssumptions, hNullifier⟩,
      ⟨hSpendAssumptions, hSpendAuth⟩,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hCvY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hNf,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hRkY⟩

end Entry

end ActionComputedWiring

/-!
Action wiring with old and new note commitment outputs.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Old note commitment integrity`
- `New note commitment integrity`
- final public-input/action wiring in `Circuit::synthesize`

This assertion connects `gadgets::note_commit` output cells to the action row: the old
derived commitment is constrained to the witnessed `cm_old`, and the new commitment's
extracted x-coordinate supplies the public `cmx`. The internal note-commitment gates are
kept in `NoteCommit.Wiring.circuit`, so this assertion only records the action-level copy
constraints.
-/
namespace ActionNoteCommitWiring

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

structure Row (F : Type) where
  action : ActionWiring.Row F
  oldNoteCommit : NoteCommit.Wiring.Row F
  newNoteCommit : NoteCommit.Wiring.Row F
deriving ProvableStruct

def oldCmXCheck (row : Row R) : R :=
  row.oldNoteCommit.cmX - row.action.derivedCmOldX

def oldCmYCheck (row : Row R) : R :=
  row.oldNoteCommit.cmY - row.action.derivedCmOldY

def newCmxCheck (row : Row R) : R :=
  row.newNoteCommit.cmX - row.action.cmxNew

def Spec (row : Row R) : Prop :=
  ActionWiring.Spec row.action ∧
    row.oldNoteCommit.cmX = row.action.derivedCmOldX ∧
    row.oldNoteCommit.cmY = row.action.derivedCmOldY ∧
    row.newNoteCommit.cmX = row.action.cmxNew

def main (row : Var Row F) : Circuit F Unit := do
  ActionWiring.circuit row.action
  assertZero (oldCmXCheck row)
  assertZero (oldCmYCheck row)
  assertZero (newCmxCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, oldCmXCheck, oldCmYCheck, newCmxCheck,
      ActionWiring.circuit, ActionWiring.Spec]
    rcases h_holds with ⟨hAction, hOldX, hOldY, hNewCmx⟩
    exact ⟨hAction,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hOldX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hOldY),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNewCmx)⟩
  completeness := by
    circuit_proof_start [main, Spec, oldCmXCheck, oldCmYCheck, newCmxCheck,
      ActionWiring.circuit, ActionWiring.Spec]
    rcases h_spec with ⟨hAction, hOldX, hOldY, hNewCmx⟩
    exact ⟨hAction,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hOldX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hOldY,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hNewCmx⟩

end ActionNoteCommitWiring

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

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]
  [OfNat R (2 ^ 5)] [OfNat R (2 ^ 10)] [OfNat R (2 ^ 240)]

structure Row (F : Type) where
  action : ActionWiring.Row F
  finalStep : Sinsemilla.Merkle.PathStep.Row F
deriving ProvableStruct

def rootCheck (row : Row R) : R :=
  row.finalStep.nextNode - row.action.root

def Spec (row : Row R) : Prop :=
  ActionWiring.Spec row.action ∧
    Sinsemilla.Merkle.PathStep.Spec row.finalStep ∧
    rootCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  ActionWiring.circuit row.action
  Sinsemilla.Merkle.PathStep.circuit row.finalStep
  assertZero (rootCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, rootCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Sinsemilla.Merkle.PathStep.circuit, Sinsemilla.Merkle.PathStep.Spec]
    rcases h_holds with ⟨hAction, hStep, hRoot⟩
    exact ⟨hAction, hStep,
      by simpa [sub_eq_add_neg] using hRoot⟩
  completeness := by
    circuit_proof_start [main, Spec, rootCheck,
      ActionWiring.circuit, ActionWiring.Spec,
      Sinsemilla.Merkle.PathStep.circuit, Sinsemilla.Merkle.PathStep.Spec]
    rcases h_spec with ⟨hAction, hStep, hRoot⟩
    exact ⟨hAction, hStep,
      by simpa [sub_eq_add_neg] using hRoot⟩

end ActionMerkleWiring

/-!
Action wiring with diversified-address integrity outputs.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Diversified address integrity`
- final public-input/action wiring in `Circuit::synthesize`

The source computes `ivk = CommitIvk(ak, nk, rivk)`, converts it to the scalar used by
`[ivk] g_d_old`, and constrains the resulting `derived_pk_d_old` to the witnessed
`pk_d_old`. This assertion records those action-level copy edges. The internals of
`CommitIvk`, fixed-base multiplication, and variable-base multiplication are represented
by their own lower-level assertions and explicit row values.
-/
namespace ActionAddressWiring

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

structure Row (F : Type) where
  action : ActionWiring.Row F
  spendAuth : Gadget.SpendAuth.Row F
  commitIvk : CommitIvk.Wiring.Row F
  ivkScalar : F
  derivedPkDX : F
  derivedPkDY : F
deriving ProvableStruct

def akCheck (row : Row R) : R :=
  row.commitIvk.gate.ak - row.spendAuth.akX

def ivkScalarCheck (row : Row R) : R :=
  row.commitIvk.ivk - row.ivkScalar

def pkDXCheck (row : Row R) : R :=
  row.derivedPkDX - row.action.derivedPkDOldX

def pkDYCheck (row : Row R) : R :=
  row.derivedPkDY - row.action.derivedPkDOldY

def Spec (row : Row R) : Prop :=
  ActionWiring.Spec row.action ∧
    row.commitIvk.gate.ak = row.spendAuth.akX ∧
    row.commitIvk.ivk = row.ivkScalar ∧
    row.derivedPkDX = row.action.derivedPkDOldX ∧
    row.derivedPkDY = row.action.derivedPkDOldY

def main (row : Var Row F) : Circuit F Unit := do
  ActionWiring.circuit row.action
  assertZero (akCheck row)
  assertZero (ivkScalarCheck row)
  assertZero (pkDXCheck row)
  assertZero (pkDYCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, akCheck, ivkScalarCheck, pkDXCheck, pkDYCheck,
      ActionWiring.circuit, ActionWiring.Spec]
    rcases h_holds with ⟨hAction, hAk, hIvk, hPkDX, hPkDY⟩
    exact ⟨hAction,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hAk),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hIvk),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hPkDX),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hPkDY)⟩
  completeness := by
    circuit_proof_start [main, Spec, akCheck, ivkScalarCheck, pkDXCheck, pkDYCheck,
      ActionWiring.circuit, ActionWiring.Spec]
    rcases h_spec with ⟨hAction, hAk, hIvk, hPkDX, hPkDY⟩
    exact ⟨hAction,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hAk,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hIvk,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hPkDX,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hPkDY⟩

end ActionAddressWiring
end Orchard
