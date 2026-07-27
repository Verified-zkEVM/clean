import Clean.Halo2.TopLevel
import Clean.Halo2.Keygen

/-!
# Additional keygen facts for a top-level circuit

`TopLevelCircuit` already owns the V1 placement, fitting domain, fixed rows, and canonical
semantic environment. This module adds the pinned-CS identity and reusable arithmetic
facts for backend key-generation code.
-/

namespace Halo2

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- The pinned constraint system derived solely from the closed circuit. -/
def pinnedCS (self : TopLevelCircuit F Config PublicInput) :
    PinnedConstraintSystem F :=
  self.formalCircuit.toPinnedCS () ()

/--
The circuit-owned pinned constraint system is exactly the projection using its
circuit-owned selector map.
-/
theorem pinnedCS_eq_derive
    (self : TopLevelCircuit F Config PublicInput) :
    self.pinnedCS =
      PinnedConstraintSystem.derive self.constraintSystem self.selectorMap := by
  rfl

/-- The keygen fit assertion for a proposed domain exponent. -/
def FitsAt (self : TopLevelCircuit F Config PublicInput) (k : ℕ) : Prop :=
  self.usedRows + self.blindingFactors + 1 ≤ 2 ^ k

/-- The total circuit-derived domain exponent satisfies the keygen fit inequality. -/
theorem fitsAt_domainExponent
    (self : TopLevelCircuit F Config PublicInput) :
    self.FitsAt self.domainExponent := by
  unfold FitsAt
  exact (Nat.le_max_left _ _).trans
    (Halo2.minimalK_fits self.constraintSystem self.operations)

/-- A fitting keygen domain has strictly more rows than its blinding count. -/
theorem blindingFactors_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput)
    (k : ℕ) (hfit : self.FitsAt k) :
    self.blindingFactors < 2 ^ k := by
  unfold FitsAt at hfit
  omega

/--
A nonempty operation footprint leaves at least one non-blinding usable row
before the final usable row.
-/
theorem blindingFactors_succ_lt_domainSize
    (self : TopLevelCircuit F Config PublicInput)
    (k : ℕ) (hfit : self.FitsAt k)
    (hused : 0 < self.usedRows) :
    self.blindingFactors + 1 < 2 ^ k := by
  unfold FitsAt at hfit
  omega

theorem usedRows_le_usableRowsAt
    (self : TopLevelCircuit F Config PublicInput) (k : ℕ)
    (hfit : self.FitsAt k) :
    self.usedRows ≤ self.usableRowsAt k := by
  unfold FitsAt at hfit
  unfold usableRowsAt
  omega

end TopLevelCircuit

end Halo2
