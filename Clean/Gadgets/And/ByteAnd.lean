import Clean.Circuit.Basic
import Clean.Gadgets.ByteLookup

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableType Inputs where
  size := 2
  to_elements x := #v[x.x, x.y]
  from_elements v :=
    let ⟨ .mk [x, y], _ ⟩ := v
    ⟨ x, y ⟩

structure Outputs (F : Type) where
  z: F

instance : ProvableType Outputs where
  size := 1
  to_elements x := #v[x.z]
  from_elements v :=
    let ⟨ .mk [z], _ ⟩ := v
    ⟨ z ⟩

end Gadgets.And
