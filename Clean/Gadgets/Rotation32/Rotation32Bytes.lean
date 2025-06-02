import Clean.Types.U32
import Clean.Gadgets.Rotation32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation32Bytes
variable {p : ℕ} [Fact p.Prime]

open Bitwise (rot_right32)
-- TODO: Create necessary soundness theorems for Rotation32Bytes
-- open Rotation32.Theorems (soundnessCase1 soundnessCase2 soundnessCase3 soundnessCase4 soundnessCase5 soundnessCase6 soundnessCase7)

@[reducible]
def Inputs (F : Type) := U32 F

@[reducible]
def Outputs (F : Type) := U32 F

-- q Is this indeed a right rotation?
/--
  Rotate the 32-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot32_bytes (offset : Fin 4) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3⟩ := input

  if offset = 0 then
    return ⟨ x0, x1, x2, x3 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x0, x1 ⟩
  else
    return ⟨ x3, x0, x1, x2 ⟩
