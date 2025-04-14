import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64
import Clean.Gadgets.Not.ByteNotTable

section
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]


namespace Gadgets.Not
@[reducible]
def Inputs (F : Type) := U64 F

@[reducible]
def Outputs (F : Type) := U64 F

def not_u64 (x : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p))  := do
  let y ← ProvableType.witness (fun env =>
    let y0 := 255 - (env x.x0).val
    let y1 := 255 - (env x.x1).val
    let y2 := 255 - (env x.x2).val
    let y3 := 255 - (env x.x3).val
    let y4 := 255 - (env x.x4).val
    let y5 := 255 - (env x.x5).val
    let y6 := 255 - (env x.x6).val
    let y7 := 255 - (env x.x7).val
    U64.mk y0 y1 y2 y3 y4 y5 y6 y7)

  byte_not_lookup x.x0 y.x0
  byte_not_lookup x.x1 y.x1
  byte_not_lookup x.x2 y.x2
  byte_not_lookup x.x3 y.x3
  byte_not_lookup x.x4 y.x4
  byte_not_lookup x.x5 y.x5
  byte_not_lookup x.x6 y.x6
  byte_not_lookup x.x7 y.x7
  return y

def assumptions (x: Inputs (F p)) := x.is_normalized

def spec (x: Inputs (F p)) (y : Outputs (F p)) :=
  y.x0.val = 255 - x.x0.val ∧
  y.x1.val = 255 - x.x1.val ∧
  y.x2.val = 255 - x.x2.val ∧
  y.x3.val = 255 - x.x3.val ∧
  y.x4.val = 255 - x.x4.val ∧
  y.x5.val = 255 - x.x5.val ∧
  y.x6.val = 255 - x.x6.val ∧
  y.x7.val = 255 - x.x7.val

def circuit : FormalCircuit (F p) Inputs Outputs where
  main := not_u64
  assumptions := assumptions
  spec := spec
  local_length _ := 8
  output _ i0 := { y := ⟨var ⟨i0⟩, var ⟨i0 + 1⟩, var ⟨i0 + 2⟩, var ⟨i0 + 3⟩, var ⟨i0 + 4⟩, var ⟨i0 + 5⟩, var ⟨i0 + 6⟩, var ⟨i0 + 7⟩ ⟩ }

  soundness := by
    sorry

  completeness := by
    sorry

end Gadgets.Not
