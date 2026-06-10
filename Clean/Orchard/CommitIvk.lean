import Clean.Circuit
import Clean.Orchard.NoteCommit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard incoming viewing key commitment gate

Clean approximation of the Orchard `CommitIvk` custom gate.

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `CommitIvk canonicity check`
- `gadgets::commit_ivk`

The top-level `circuit` models the arithmetic constraints enabled by the Halo2
`q_commit_ivk` selector, not the selector, row layout, Sinsemilla hash, lookup range
checks, or assignment machinery around the gate. `Wiring.circuit` additionally models
the source-level connection between that gate row and the explicit `short_commit` output.
-/

namespace Orchard
namespace CommitIvk

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]
  [OfNat R 16] [OfNat R 32] [OfNat R 512]
  [OfNat R (2 ^ 130)] [OfNat R (2 ^ 140)] [OfNat R (2 ^ 245)]
  [OfNat R (2 ^ 250)] [OfNat R (2 ^ 254)]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  ak : F
  nk : F
  a : F
  bWhole : F
  c : F
  dWhole : F
  b0 : F
  b1 : F
  b2 : F
  d0 : F
  d1 : F
  z13A : F
  z13C : F
  aPrime : F
  b2CPrime : F
  z13APrime : F
  z14B2CPrime : F
deriving ProvableStruct

def bDecomposition (row : Row R) : R :=
  row.bWhole - (row.b0 + row.b1 * 16 + row.b2 * 32)

def dDecomposition (row : Row R) : R :=
  row.dWhole - (row.d0 + row.d1 * 512)

def akDecomposition (row : Row R) : R :=
  row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) - row.ak

def nkDecomposition (row : Row R) : R :=
  row.b2 + row.c * 32 + row.d0 * OfNat.ofNat (2 ^ 245) +
    row.d1 * OfNat.ofNat (2 ^ 254) - row.nk

def aPrimeCheck (row : Row R) : R :=
  row.a + OfNat.ofNat (2 ^ 130) - NoteCommit.tP - row.aPrime

def b2CPrimeCheck (row : Row R) : R :=
  row.b2 + row.c * 32 + OfNat.ofNat (2 ^ 140) - NoteCommit.tP - row.b2CPrime

def constraints (row : Row R) : Prop :=
  NoteCommit.boolPoly row.b1 = 0 ∧
    NoteCommit.boolPoly row.d1 = 0 ∧
    bDecomposition row = 0 ∧
    dDecomposition row = 0 ∧
    akDecomposition row = 0 ∧
    nkDecomposition row = 0 ∧
    row.b1 * row.b0 = 0 ∧
    row.b1 * row.z13A = 0 ∧
    aPrimeCheck row = 0 ∧
    row.b1 * row.z13APrime = 0 ∧
    row.d1 * row.d0 = 0 ∧
    row.d1 * row.z13C = 0 ∧
    b2CPrimeCheck row = 0 ∧
    row.d1 * row.z14B2CPrime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly row.b1)
  assertZero (NoteCommit.boolPoly row.d1)
  assertZero (bDecomposition row)
  assertZero (dDecomposition row)
  assertZero (akDecomposition row)
  assertZero (nkDecomposition row)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (aPrimeCheck row)
  assertZero (row.b1 * row.z13APrime)
  assertZero (row.d1 * row.d0)
  assertZero (row.d1 * row.z13C)
  assertZero (b2CPrimeCheck row)
  assertZero (row.d1 * row.z14B2CPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bDecomposition,
      dDecomposition, akDecomposition, nkDecomposition, aPrimeCheck, b2CPrimeCheck,
      NoteCommit.tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bDecomposition,
      dDecomposition, akDecomposition, nkDecomposition, aPrimeCheck, b2CPrimeCheck,
      NoteCommit.tP]
    simp_all [sub_eq_add_neg]

/-!
`commit_ivk` source-level wiring.

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `gadgets::commit_ivk`

The Rust gadget constructs four Sinsemilla message pieces, obtains running-sum endpoints
from `CommitDomain::short_commit`, feeds those cells into `GateCells`, assigns the
canonicity gate, and returns `ivk`. The short commitment itself is represented here by an
explicit `computedIvk` row value; this assertion only records the wiring around the
already ported canonicity gate.
-/
namespace Wiring

structure Row (F : Type) where
  gate : CommitIvk.Row F
  computedIvk : F
  ivk : F
deriving ProvableStruct

def ivkCheck (row : Row R) : R :=
  row.computedIvk - row.ivk

def constraints (row : Row R) : Prop :=
  CommitIvk.constraints row.gate ∧ ivkCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly row.gate.b1)
  assertZero (NoteCommit.boolPoly row.gate.d1)
  assertZero (CommitIvk.bDecomposition row.gate)
  assertZero (CommitIvk.dDecomposition row.gate)
  assertZero (CommitIvk.akDecomposition row.gate)
  assertZero (CommitIvk.nkDecomposition row.gate)
  assertZero (row.gate.b1 * row.gate.b0)
  assertZero (row.gate.b1 * row.gate.z13A)
  assertZero (CommitIvk.aPrimeCheck row.gate)
  assertZero (row.gate.b1 * row.gate.z13APrime)
  assertZero (row.gate.d1 * row.gate.d0)
  assertZero (row.gate.d1 * row.gate.z13C)
  assertZero (CommitIvk.b2CPrimeCheck row.gate)
  assertZero (row.gate.d1 * row.gate.z14B2CPrime)
  assertZero (ivkCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, ivkCheck, CommitIvk.constraints,
      CommitIvk.bDecomposition, CommitIvk.dDecomposition, CommitIvk.akDecomposition,
      CommitIvk.nkDecomposition, CommitIvk.aPrimeCheck, CommitIvk.b2CPrimeCheck,
      NoteCommit.boolPoly, NoteCommit.tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, ivkCheck, CommitIvk.constraints,
      CommitIvk.bDecomposition, CommitIvk.dDecomposition, CommitIvk.akDecomposition,
      CommitIvk.nkDecomposition, CommitIvk.aPrimeCheck, CommitIvk.b2CPrimeCheck,
      NoteCommit.boolPoly, NoteCommit.tP]
    simp_all [sub_eq_add_neg]

end Wiring

end CommitIvk
end Orchard
