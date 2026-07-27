import Clean.Halo2.TopLevel
import Clean.Halo2.Keygen

/-!
# Additional keygen facts for a top-level circuit

`TopLevelCircuit` already owns the V1 placement, fitting domain, fixed rows, and canonical
semantic environment. This module adds the pinned-CS identity for backend key-generation code.
-/

namespace Halo2

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- The pinned constraint system derived solely from the closed circuit: the
projection of its synthesis-closed constraint system through its circuit-owned
selector map. -/
def pinnedCS (self : TopLevelCircuit F Config PublicInput) :
    PinnedConstraintSystem F :=
  PinnedConstraintSystem.derive self.constraintSystem self.selectorMap

/--
The circuit-owned pinned constraint system is exactly the projection using its
circuit-owned selector map.
-/
theorem pinnedCS_eq_derive
    (self : TopLevelCircuit F Config PublicInput) :
    self.pinnedCS =
      PinnedConstraintSystem.derive self.constraintSystem self.selectorMap :=
  rfl

end TopLevelCircuit

end Halo2
