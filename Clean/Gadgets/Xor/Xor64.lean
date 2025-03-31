import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable

section
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]


namespace Gadgets.Xor
structure Inputs (F : Type) where
  x: U64 F
  y: U64 F

structure Outputs (F : Type) where
  z: U64 F

instance : ProvableType Inputs where
  size := 16
  to_elements s := #v[s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.x.x4, s.x.x5, s.x.x6, s.x.x7, s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.y.x4, s.y.x5, s.y.x6, s.y.x7]
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7], _ ⟩ := v
    ⟨ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ⟩

instance : ProvableType Outputs where
  size := 8
  to_elements s := #v[s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.z.x4, s.z.x5, s.z.x6, s.z.x7]
  from_elements v :=
    let ⟨ .mk [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ ⟩

def xor_u64 (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p))  := do
  let ⟨x, y⟩ := input
  let z ← Provable.witness (fun env =>
    let z0 := Nat.xor (env x.x0).val (env y.x0).val
    let z1 := Nat.xor (env x.x1).val (env y.x1).val
    let z2 := Nat.xor (env x.x2).val (env y.x2).val
    let z3 := Nat.xor (env x.x3).val (env y.x3).val
    let z4 := Nat.xor (env x.x4).val (env y.x4).val
    let z5 := Nat.xor (env x.x5).val (env y.x5).val
    let z6 := Nat.xor (env x.x6).val (env y.x6).val
    let z7 := Nat.xor (env x.x7).val (env y.x7).val
    U64.mk z0 z1 z2 z3 z4 z5 z6 z7)

  byte_xor_lookup x.x0 y.x0 z.x0
  byte_xor_lookup x.x1 y.x1 z.x1
  byte_xor_lookup x.x2 y.x2 z.x2
  byte_xor_lookup x.x3 y.x3 z.x3
  byte_xor_lookup x.x4 y.x4 z.x4
  byte_xor_lookup x.x5 y.x5 z.x5
  byte_xor_lookup x.x6 y.x6 z.x6
  byte_xor_lookup x.x7 y.x7 z.x7
  return { z }

def assumptions (input: Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.is_normalized ∧ y.is_normalized

def spec (input: Inputs (F p)) (outputs : Outputs (F p)) :=
  let ⟨x, y⟩ := input
  outputs.z.value = Nat.xor x.value y.value


def circuit : FormalCircuit (F p) Inputs Outputs where
  main := xor_u64
  assumptions := assumptions
  spec := spec
  local_length _ := 8
  output _ i0 := { z := ⟨var ⟨i0⟩, var ⟨i0 + 1⟩, var ⟨i0 + 2⟩, var ⟨i0 + 3⟩, var ⟨i0 + 4⟩, var ⟨i0 + 5⟩, var ⟨i0 + 6⟩, var ⟨i0 + 7⟩ ⟩ }

  soundness := by
    sorry

  completeness := by
    sorry

end Gadgets.Xor
