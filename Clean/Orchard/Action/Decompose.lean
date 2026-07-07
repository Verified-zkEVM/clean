import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# NoteCommit message-piece decomposition gates

Custom-gate `FormalAssertion`s that constrain each Sinsemilla message piece to equal the
weighted sum of its sub-pieces (`orchard note_commit.rs` `Decompose*`).
-/

namespace Orchard.Action.NoteCommit

namespace DecomposeB.Gate

structure Row (F : Type) where
  b : F
  b0 : F
  b1 : F
  b2 : F
  b3 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  IsBool row.b1 ∧
  IsBool row.b2 ∧
  row.b = row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.b1
  assertBool row.b2
  assertZero (row.b - (row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64))

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit MessagePiece b"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hb1, hb2, hdec⟩
    exact ⟨hb1, hb2, sub_eq_zero.mp hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hb1, hb2, hdec⟩
    exact ⟨hb1, hb2, by rw [hdec]; ring⟩

end DecomposeB.Gate

namespace DecomposeD.Gate

structure Row (F : Type) where
  d : F
  d0 : F
  d1 : F
  d2 : F
  d3 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  IsBool row.d0 ∧
  IsBool row.d1 ∧
  row.d = row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.d0
  assertBool row.d1
  assertZero (row.d - (row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024))

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit MessagePiece d"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hd0, hd1, hdec⟩
    exact ⟨hd0, hd1, sub_eq_zero.mp hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hd0, hd1, hdec⟩
    exact ⟨hd0, hd1, by rw [hdec]; ring⟩

end DecomposeD.Gate

namespace DecomposeE.Gate

structure Row (F : Type) where
  e : F
  e0 : F
  e1 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.e = row.e0 + row.e1 * 64

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.e - (row.e0 + row.e1 * 64))

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit MessagePiece e"
  main
  Spec
  soundness := by
    circuit_proof_start
    exact sub_eq_zero.mp h_holds
  completeness := by
    circuit_proof_start
    rw [h_spec]
    ring

end DecomposeE.Gate

namespace DecomposeG.Gate

structure Row (F : Type) where
  g : F
  g0 : F
  g1 : F
  g2 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  IsBool row.g0 ∧
  row.g = row.g0 + row.g1 * 2 + row.g2 * 1024

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.g0
  assertZero (row.g - (row.g0 + row.g1 * 2 + row.g2 * 1024))

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit MessagePiece g"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hg0, hdec⟩
    exact ⟨hg0, sub_eq_zero.mp hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hg0, hdec⟩
    exact ⟨hg0, by rw [hdec]; ring⟩

end DecomposeG.Gate

namespace DecomposeH.Gate

structure Row (F : Type) where
  h : F
  h0 : F
  h1 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  IsBool row.h1 ∧
  row.h = row.h0 + row.h1 * 32

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.h1
  assertZero (row.h - (row.h0 + row.h1 * 32))

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit MessagePiece h"
  main
  Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hh1, hdec⟩
    exact ⟨hh1, sub_eq_zero.mp hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hh1, hdec⟩
    exact ⟨hh1, by rw [hdec]; ring⟩

end DecomposeH.Gate

end Orchard.Action.NoteCommit
