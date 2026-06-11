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

def IsBool {K : Type} [Zero K] [One K] (x : K) : Prop :=
  x = 0 ∨ x = 1

private theorem isBool_of_bool_factor_eq_zero {x : F} (h : x * (x + -1) = 0) :
    IsBool x := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h1))

private theorem bool_factor_eq_zero_of_isBool {x : F} (h : IsBool x) :
    x * (x + -1) = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

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

def bDecomposition {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 16] [OfNat K 32]
    (row : Row K) : K :=
  row.bWhole - (row.b0 + row.b1 * 16 + row.b2 * 32)

def dDecomposition {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 512] (row : Row K) : K :=
  row.dWhole - (row.d0 + row.d1 * 512)

def akDecomposition {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 250)]
    [OfNat K (2 ^ 254)] (row : Row K) : K :=
  row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) - row.ak

def nkDecomposition {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 32] [OfNat K (2 ^ 245)]
    [OfNat K (2 ^ 254)] (row : Row K) : K :=
  row.b2 + row.c * 32 + row.d0 * OfNat.ofNat (2 ^ 245) +
    row.d1 * OfNat.ofNat (2 ^ 254) - row.nk

def aPrimeCheck {K : Type} [Add K] [Sub K] [OfNat K (2 ^ 130)]
    [OfNat K 45560315531419706090280762371685220353] (row : Row K) : K :=
  row.a + OfNat.ofNat (2 ^ 130) - NoteCommit.tP - row.aPrime

def b2CPrimeCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 32] [OfNat K (2 ^ 140)]
    [OfNat K 45560315531419706090280762371685220353] (row : Row K) : K :=
  row.b2 + row.c * 32 + OfNat.ofNat (2 ^ 140) - NoteCommit.tP - row.b2CPrime

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsBool row.b1 ∧
    IsBool row.d1 ∧
    row.bWhole = row.b0 + row.b1 * 16 + row.b2 * 32 ∧
    row.dWhole = row.d0 + row.d1 * 512 ∧
    row.ak = row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) ∧
    row.nk = row.b2 + row.c * 32 + row.d0 * OfNat.ofNat (2 ^ 245) +
      row.d1 * OfNat.ofNat (2 ^ 254) ∧
    (row.b1 = 0 ∨ row.b0 = 0) ∧
    (row.b1 = 0 ∨ row.z13A = 0) ∧
    row.aPrime = row.a + OfNat.ofNat (2 ^ 130) - NoteCommit.tP ∧
    (row.b1 = 0 ∨ row.z13APrime = 0) ∧
    (row.d1 = 0 ∨ row.d0 = 0) ∧
    (row.d1 = 0 ∨ row.z13C = 0) ∧
    row.b2CPrime = row.b2 + row.c * 32 + OfNat.ofNat (2 ^ 140) - NoteCommit.tP ∧
    (row.d1 = 0 ∨ row.z14B2CPrime = 0)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
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

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bDecomposition,
      dDecomposition, akDecomposition, nkDecomposition, aPrimeCheck, b2CPrimeCheck,
      NoteCommit.tP]
    rcases h_holds with
      ⟨hb1, hd1, hb, hd, hak, hnk, hb0, hz13A, haPrime, hz13APrime, hd0, hz13C,
        hb2CPrime, hz14B2CPrime⟩
    exact ⟨isBool_of_bool_factor_eq_zero hb1, isBool_of_bool_factor_eq_zero hd1,
      left_eq_of_add_neg_eq_zero hb, left_eq_of_add_neg_eq_zero hd,
      (left_eq_of_add_neg_eq_zero hak).symm, (left_eq_of_add_neg_eq_zero hnk).symm,
      mul_eq_zero.mp hb0, mul_eq_zero.mp hz13A,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero haPrime).symm,
      mul_eq_zero.mp hz13APrime, mul_eq_zero.mp hd0, mul_eq_zero.mp hz13C,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hb2CPrime).symm,
      mul_eq_zero.mp hz14B2CPrime⟩
  completeness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bDecomposition,
      dDecomposition, akDecomposition, nkDecomposition, aPrimeCheck, b2CPrimeCheck,
      NoteCommit.tP]
    rcases h_spec with
      ⟨hb1, hd1, hb, hd, hak, hnk, hb0, hz13A, haPrime, hz13APrime, hd0, hz13C,
        hb2CPrime, hz14B2CPrime⟩
    constructor
    · exact bool_factor_eq_zero_of_isBool hb1
    constructor
    · exact bool_factor_eq_zero_of_isBool hd1
    constructor
    · rw [hb]
      ring
    constructor
    · rw [hd]
      ring
    constructor
    · rw [hak]
      ring
    constructor
    · rw [hnk]
      ring
    constructor
    · exact mul_eq_zero_of_or hb0
    constructor
    · exact mul_eq_zero_of_or hz13A
    constructor
    · rw [haPrime]
      ring
    constructor
    · exact mul_eq_zero_of_or hz13APrime
    constructor
    · exact mul_eq_zero_of_or hd0
    constructor
    · exact mul_eq_zero_of_or hz13C
    constructor
    · rw [hb2CPrime]
      ring
    exact mul_eq_zero_of_or hz14B2CPrime

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

def ivkCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.computedIvk - row.ivk

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  CommitIvk.Spec row.gate ∧ row.computedIvk = row.ivk

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  CommitIvk.circuit row.gate
  assertZero (ivkCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, ivkCheck, CommitIvk.circuit, CommitIvk.Spec]
    exact ⟨h_holds.1, left_eq_of_add_neg_eq_zero h_holds.2⟩
  completeness := by
    circuit_proof_start [main, Spec, ivkCheck, CommitIvk.circuit, CommitIvk.Spec]
    constructor
    · exact h_spec.1
    simpa [sub_eq_add_neg] using sub_eq_zero.mpr h_spec.2

end Wiring

/-!
Incoming-viewing-key commitment output connected to Sinsemilla short-commit arithmetic.

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `gadgets::commit_ivk`

The Rust gadget constructs the `CommitIvk` message/canonicity gate, calls
`CommitDomain::short_commit`, and returns the extracted x-coordinate as `ivk`.
`Wiring.circuit` records the canonicity-gate wiring. This assertion connects its
explicit `computedIvk` output to the `Sinsemilla.ShortCommit.Entry.circuit` extracted
value, while its spec records the source-level fixed-base blinding product
`[rivk] CommitIvkR`.
-/
namespace WiringWithShortCommit

structure Row (F : Type) where
  wiring : Wiring.Row F
  shortCommit : Sinsemilla.ShortCommit.Entry.Row F
deriving ProvableStruct

def ivkCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.shortCommit.extracted - row.wiring.computedIvk

def blindProduct (row : Row Ecc.PallasBaseField) : Ecc.Point Ecc.PallasBaseField where
  x := row.shortCommit.commit.blindX
  y := row.shortCommit.commit.blindY

def OrchardSpec (rivkScalar : ℕ) (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.IsOrchardFixedBaseMul .commitIvkR rivkScalar (blindProduct row) ∧
  Wiring.Spec row.wiring ∧
    Sinsemilla.ShortCommit.Entry.Spec row.shortCommit ∧
    row.shortCommit.extracted = row.wiring.computedIvk

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Wiring.Spec row.wiring ∧
    Sinsemilla.ShortCommit.Entry.Spec row.shortCommit ∧
    row.shortCommit.extracted = row.wiring.computedIvk

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Sinsemilla.ShortCommit.Entry.Assumptions row.shortCommit

theorem spec_of_orchardSpec {rivkScalar : ℕ} {row : Row Ecc.PallasBaseField}
    (h : OrchardSpec rivkScalar row) :
    Spec row :=
  h.2

theorem blindProduct_groupAction_of_orchardSpec
    {rivkScalar : ℕ} {row : Row Ecc.PallasBaseField}
    (h : OrchardSpec rivkScalar row) :
    Ecc.pointCoords (blindProduct row) =
      Ecc.orchardFixedBaseMulGroupActionCoords .commitIvkR rivkScalar :=
  (Ecc.isOrchardFixedBaseMul_iff_groupAction).1 h.1

theorem assumptions_of_orchardSpec {rivkScalar : ℕ} {row : Row Ecc.PallasBaseField}
    (hHash : Ecc.isPointOrIdentity (Sinsemilla.Commit.Entry.addInput row.shortCommit.commit).p)
    (h : OrchardSpec rivkScalar row) :
    Assumptions row :=
  ⟨hHash, Ecc.isOrchardFixedBaseMul_isPointOrIdentity h.1⟩

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Wiring.circuit row.wiring
  Sinsemilla.ShortCommit.Entry.circuit row.shortCommit
  assertZero (ivkCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, Assumptions, ivkCheck, Wiring.circuit,
      Wiring.Spec, Sinsemilla.ShortCommit.Entry.circuit, Sinsemilla.ShortCommit.Entry.Spec]
    rcases h_holds with ⟨hWiring, hShort, hIvk⟩
    exact ⟨hWiring, hShort h_assumptions,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hIvk)⟩
  completeness := by
    circuit_proof_start [main, Spec, Assumptions, ivkCheck, Wiring.circuit,
      Wiring.Spec, Sinsemilla.ShortCommit.Entry.circuit, Sinsemilla.ShortCommit.Entry.Spec,
      Sinsemilla.ShortCommit.Entry.Assumptions]
    rcases h_spec with ⟨hWiring, hShort, hIvk⟩
    exact ⟨hWiring, ⟨h_assumptions, hShort⟩,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hIvk⟩

end WiringWithShortCommit

end CommitIvk
end Orchard
