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
structure Inputs (F : Type) where
  x: U64 F

structure Outputs (F : Type) where
  y: U64 F

instance : ProvableType Inputs where
  size := 8
  to_elements s := #v[s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.x.x4, s.x.x5, s.x.x6, s.x.x7]
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ ⟩

instance : ProvableType Outputs where
  size := 8
  to_elements s := #v[s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.y.x4, s.y.x5, s.y.x6, s.y.x7]
  from_elements v :=
    let ⟨ .mk [y0, y1, y2, y3, y4, y5, y6, y7], _ ⟩ := v
    ⟨ ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ⟩

def not_u64 (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p))  := do
  let ⟨x⟩ := input
  let y ← Provable.witness (fun env =>
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
  return { y }

def assumptions (input: Inputs (F p)) :=
  let ⟨x⟩ := input
  x.is_normalized

def bitwise_not_u64 (x : ℕ) : ℕ :=
  Nat.xor x 0xffffffffffffffff

def spec (input: Inputs (F p)) (outputs : Outputs (F p)) :=
  let ⟨x⟩ := input
  outputs.y.value = bitwise_not_u64 x.value

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
