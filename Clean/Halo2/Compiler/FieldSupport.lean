import Clean.Halo2.TopLevel
import Clean.Utils.FieldDomainParams

/-!
# Field support for a compiled circuit

These are numerical compatibility conditions between a circuit and certified field
parameters, not additional circuit lawfulness.
-/

namespace Halo2

/-- The circuit fits the evaluation domains, characteristic, and permutation cosets
provided by the field. All algebraic consequences follow from `FieldDomainParams`. -/
class CircuitFieldSupport
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    [params : FieldDomainParams F] : Prop where
  domainExponent_le : top.domainExponent ≤ params.twoAdicity
  constraintDegree_lt_ringChar : top.constraintDegree < ringChar F
  permutationColumnCount_le : top.permutationColumnCount ≤ params.oddPart

namespace TopLevelCircuit

variable {F : Type} [FiniteField F] [params : FieldDomainParams F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- The circuit's evaluation root, using the field's chosen domain convention. -/
def omega : F := FieldDomainParams.omega top.domainExponent

/-- Field support bounds the circuit's domain exponent by the chosen two-adicity. -/
theorem domainExponent_lt [CircuitFieldSupport top] :
    top.domainExponent < params.twoAdicity + 1 :=
  Nat.lt_succ_of_le (CircuitFieldSupport.domainExponent_le (top := top))

end TopLevelCircuit

namespace CircuitFieldSupport

variable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    [params : FieldDomainParams F]

variable [CircuitFieldSupport top]

/-- Numerical domain support gives the circuit root its exact order. -/
theorem omega_isPrimitiveRoot : IsPrimitiveRoot top.omega top.n := by
  simpa only [TopLevelCircuit.omega, TopLevelCircuit.n] using
    FieldDomainParams.omega_isPrimitiveRoot (F := F) (domainExponent_le (top := top))

theorem omega_ne_zero : top.omega ≠ 0 :=
  (omega_isPrimitiveRoot top).isUnit (by
    simp only [TopLevelCircuit.n]; positivity) |>.ne_zero

/-- Circuit columns occupy distinct cosets of the evaluation subgroup. -/
theorem eq_of_delta_pow_eq_omega_pow_mul
    (j j' : Fin top.permutationColumnCount) (row : ℕ)
    (h : FieldDomainParams.delta ^ (j : ℕ) =
      top.omega ^ row * FieldDomainParams.delta ^ (j' : ℕ)) :
    j = j' :=
  FieldDomainParams.eq_of_delta_pow_eq_omega_pow_mul
    (domainExponent_le (top := top))
    (permutationColumnCount_le (top := top)) j j' row h

include params in
/-- Clean's constraint-system degree is the same bounded circuit degree. -/
theorem csDegree_lt_ringChar : csDegree top.constraintSystem < ringChar F := by
  rw [top.constraintSystem_csDegree]
  exact constraintDegree_lt_ringChar (top := top)

end CircuitFieldSupport

namespace TopLevelCircuit

variable {F : Type} [FiniteField F] [FieldDomainParams F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    [CircuitFieldSupport top]

theorem omega_pow_n : top.omega ^ top.n = 1 :=
  (CircuitFieldSupport.omega_isPrimitiveRoot top).pow_eq_one

/-- The circuit's domain enumerates distinct evaluation points. -/
theorem domainRowsInjective :
    Function.Injective (fun row : Fin top.n => top.omega ^ (row : ℕ)) := by
  intro i j h
  exact Fin.ext ((CircuitFieldSupport.omega_isPrimitiveRoot top).pow_inj i.isLt j.isLt h)

theorem n_cast_ne_zero : (top.n : F) ≠ 0 := by
  letI : NeZero top.n := ⟨top.n_pos.ne'⟩
  exact (CircuitFieldSupport.omega_isPrimitiveRoot top).neZero'.out

/-- Transport row injectivity when another domain has the same exponent. -/
theorem domainRowsInjective_of_domainExponent_eq {k : ℕ}
    (hk : top.domainExponent = k) :
    Function.Injective (fun row : Fin (2 ^ k) => top.omega ^ (row : ℕ)) := by
  rw [← hk, ← top.n_eq_two_pow_domainExponent]
  exact top.domainRowsInjective

end TopLevelCircuit

end Halo2
