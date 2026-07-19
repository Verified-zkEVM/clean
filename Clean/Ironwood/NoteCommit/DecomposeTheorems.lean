import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Ironwood.NoteCommit.CanonicityTheorems
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# NoteCommit message-piece decomposition gates

Custom-gate `FormalAssertion`s that constrain each Sinsemilla message piece to equal the
weighted sum of its sub-pieces (`orchard note_commit.rs` `Decompose*`).
-/

namespace Halo2.Ironwood.NoteCommit

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

end DecomposeD.Gate

namespace DecomposeE.Gate

structure Row (F : Type) where
  e : F
  e0 : F
  e1 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.e = row.e0 + row.e1 * 64

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

end DecomposeH.Gate

end Halo2.Ironwood.NoteCommit
