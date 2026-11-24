import CompPoly.Fields.BLS12_381
import Clean.Halo2.Basic

namespace Midnight

/-- Midnight's `midnight_curves::Fq`: the BLS12-381 scalar field. -/
abbrev F := BLS12_381.ScalarField

/-- The canonical representative, as the fixed matrix holds it; never Montgomery form. -/
def scalarNat (x : F) : Nat := x.val

end Midnight
