import Midnight.SHA256.Semantics.GatesSource
import Midnight.SHA256.Semantics.GatesParity
import Midnight.SHA256.Semantics.Rotations

namespace Midnight.SHA256.Semantics.Gates
open Halo2 Midnight.Keygen
open Midnight.SHA256.Semantics Decomposition

-- Keep proof composition from unfolding the complete configured source or table.
attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

set_option linter.constructorNameAsVariable false in
/-- The real Maj selector forces this equation at its actual rotated advice cells. -/
theorem maj_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 5 row)) :
    read env (place self + row : Nat) 5 (-1) + read env (place self + row : Nat) 6 (-1) +
      read env (place self + row : Nat) 5 0 =
      parityPlane env (place self + row : Nat) 3 +
        2 * parityPlane env (place self + row : Nat) 1 := by
  rw [activation_maj] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, majGate, majSpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [read, parityPlane, Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- The actual 11/11/10 gate binds its returned plain cell to the lookup limbs. -/
theorem parity_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 11 row)) :
    (parityWord env (place self + row : Nat) 0 : F) =
      read env (place self + row : Nat) 4 (-1) := by
  rw [activation_parity] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, parityGate, paritySpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  rw [parityWord_cast]
  norm_num [read, Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- A returned cell is the canonical bounded value fixed by its actual gate and
lookup tuples, with no claim about honest witness generation in the premise. -/
theorem parity_output {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 11 row))
    (lookups : ParityLookups env (place self + row : Nat) 0 1) :
    (read env (place self + row : Nat) 4 (-1)).val =
      parityWord env (place self + row : Nat) 0 := by
  have equal := congrArg ZMod.val
    (parity_equation (place := place) (self := self) (env := env) (row := row) satisfied)
  clear satisfied
  have small : parityWord env (place self + row : Nat) 0 < BLS12_381.scalarFieldSize :=
    (parityLookups_sound (env := env) (absolute := (place self + row : Nat)) (plain := 0) (expanded := 1) lookups).1.trans (by decide +kernel)
  rw [ZMod.val_natCast_of_lt small] at equal
  exact equal.symm

set_option linter.constructorNameAsVariable false in
/-- Soundness at the real Maj row: copied input spreads, both native output
lookup planes, and the actual selected gates force the returned cell to SHA Maj. -/
theorem majority_row_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row a b c : Nat}
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32)
    (aRead : read env (place self + row : Nat) 5 (-1) = (spread a : F))
    (bRead : read env (place self + row : Nat) 6 (-1) = (spread b : F))
    (cRead : read env (place self + row : Nat) 5 0 = (spread c : F))
    (gate : RegionOperations.Constraints place self env (activation 5 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (oddLookups : ParityLookups env (place self + row : Nat) 0 1)
    (evenLookups : ParityLookups env (place self + row : Nat) 2 3) :
    (read env (place self + row : Nat) 4 (-1)).val = Specs.SHA256.Maj a b c := by
  obtain ⟨oddBound, oddPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) oddLookups
  obtain ⟨evenBound, evenPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) evenLookups
  have equation := maj_equation (place := place) (self := self) (env := env) (row := row) gate
  rw [aRead, bRead, cRead, evenPlane, oddPlane] at equation
  have semantic := spread_triple_field_sound ha hb hc evenBound oddBound
    sha256_parity_capacity equation
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate oddLookups]
  exact semantic.2

/-- Field-valued counterpart of the source witness recipe, used only to state
what the real polynomial reads at a gate row. -/
def weightedField {n : Nat} (recipe : Witness.Recipe n) (values : Vector F n) : F :=
  recipe.foldr (fun (exponent, index) acc => (4 : F) ^ exponent * values[index] + acc) 0

theorem weightedField_cast {n : Nat} (recipe : Witness.Recipe n) (values : Vector Nat n) :
    weightedField recipe (values.map (fun n : Nat => (n : F))) =
      (Witness.weighted recipe values : F) := by
  induction recipe with
  | nil => simp [weightedField, Witness.weighted]
  | cons term rest ih =>
    simp [weightedField, Witness.weighted] at ih
    simpa [weightedField, Witness.weighted, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using ih

def bigSigma0Inputs (env : Environment F) (absolute : Int) : Vector F 4 :=
  #v[read env absolute 5 (-1), read env absolute 6 (-1), read env absolute 5 (0), read env absolute 6 (0)]

set_option linter.constructorNameAsVariable false in
/-- Exact source selector 7, evaluated at its real query cells and rotations. -/
theorem bigSigma0_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 7 row)) :
    weightedField Witness.bigSigma0Recipe (bigSigma0Inputs env (place self + row : Nat)) =
      parityPlane env (place self + row : Nat) 1 +
        2 * parityPlane env (place self + row : Nat) 3 := by
  rw [activation_bigSigma0] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, bigSigma0Gate, bigSigma0Spec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [weightedField, Witness.bigSigma0Recipe, bigSigma0Inputs, read, parityPlane,
    Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- Any bounded source-limb assignment satisfying the actual selected gate and
output lookup/decomposition gates has the specified SHA sigma output. -/
theorem bigSigma0_row_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (a b c d : Nat)
    (bounded : Bounded (aLimbs a b c d))
    (inputs : bigSigma0Inputs env (place self + row : Nat) =
      (#v[spread a, spread b, spread c, spread d].map (fun n : Nat => (n : F))))
    (gate : RegionOperations.Constraints place self env (activation 7 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (evenLookups : ParityLookups env (place self + row : Nat) 0 1)
    (oddLookups : ParityLookups env (place self + row : Nat) 2 3) :
    (read env (place self + row : Nat) 4 (-1)).val =
      Specs.SHA256.upperSigma0 (pack (aLimbs a b c d)) := by
  obtain ⟨evenBound, evenPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) evenLookups
  obtain ⟨oddBound, oddPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) oddLookups
  have equation := bigSigma0_equation (place := place) (self := self) (env := env) (row := row) gate
  rw [inputs, weightedField_cast, evenPlane, oddPlane] at equation
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate evenLookups]
  exact Rotations.bigSigma0_field_sound a b c d bounded evenBound oddBound equation

def bigSigma1Inputs (env : Environment F) (absolute : Int) : Vector F 5 :=
  #v[read env absolute 5 (-1), read env absolute 6 (-1), read env absolute 5 (0), read env absolute 6 (0), read env absolute 5 (1)]

set_option linter.constructorNameAsVariable false in
/-- Exact source selector 8, evaluated at its real query cells and rotations. -/
theorem bigSigma1_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 8 row)) :
    weightedField Witness.bigSigma1Recipe (bigSigma1Inputs env (place self + row : Nat)) =
      parityPlane env (place self + row : Nat) 1 +
        2 * parityPlane env (place self + row : Nat) 3 := by
  rw [activation_bigSigma1] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, bigSigma1Gate, bigSigma1Spec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [weightedField, Witness.bigSigma1Recipe, bigSigma1Inputs, read, parityPlane,
    Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- Any bounded source-limb assignment satisfying the actual selected gate and
output lookup/decomposition gates has the specified SHA sigma output. -/
theorem bigSigma1_row_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (a b c d e : Nat)
    (bounded : Bounded (eLimbs a b c d e))
    (inputs : bigSigma1Inputs env (place self + row : Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e].map (fun n : Nat => (n : F))))
    (gate : RegionOperations.Constraints place self env (activation 8 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (evenLookups : ParityLookups env (place self + row : Nat) 0 1)
    (oddLookups : ParityLookups env (place self + row : Nat) 2 3) :
    (read env (place self + row : Nat) 4 (-1)).val =
      Specs.SHA256.upperSigma1 (pack (eLimbs a b c d e)) := by
  obtain ⟨evenBound, evenPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) evenLookups
  obtain ⟨oddBound, oddPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) oddLookups
  have equation := bigSigma1_equation (place := place) (self := self) (env := env) (row := row) gate
  rw [inputs, weightedField_cast, evenPlane, oddPlane] at equation
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate evenLookups]
  exact Rotations.bigSigma1_field_sound a b c d e bounded evenBound oddBound equation

def sigma0Inputs (env : Environment F) (absolute : Int) : Vector F 8 :=
  #v[read env absolute 5 (-1), read env absolute 6 (-1), read env absolute 4 (0), read env absolute 5 (0), read env absolute 6 (0), read env absolute 4 (1), read env absolute 5 (1), read env absolute 6 (1)]

set_option linter.constructorNameAsVariable false in
/-- Exact source selector 9, evaluated at its real query cells and rotations. -/
theorem sigma0_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 9 row)) :
    weightedField Witness.sigma0Recipe (sigma0Inputs env (place self + row : Nat)) =
      parityPlane env (place self + row : Nat) 1 +
        2 * parityPlane env (place self + row : Nat) 3 := by
  rw [activation_sigma0] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, sigma0Gate, sigma0Spec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [weightedField, Witness.sigma0Recipe, sigma0Inputs, read, parityPlane,
    Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- Any bounded source-limb assignment satisfying the actual selected gate and
output lookup/decomposition gates has the specified SHA sigma output. -/
theorem sigma0_row_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (a b c d e f g h : Nat)
    (bounded : Bounded (messageLimbs a b c d e f g h))
    (inputs : sigma0Inputs env (place self + row : Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h].map (fun n : Nat => (n : F))))
    (gate : RegionOperations.Constraints place self env (activation 9 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (evenLookups : ParityLookups env (place self + row : Nat) 0 1)
    (oddLookups : ParityLookups env (place self + row : Nat) 2 3) :
    (read env (place self + row : Nat) 4 (-1)).val =
      Specs.SHA256.lowerSigma0 (pack (messageLimbs a b c d e f g h)) := by
  obtain ⟨evenBound, evenPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) evenLookups
  obtain ⟨oddBound, oddPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) oddLookups
  have equation := sigma0_equation (place := place) (self := self) (env := env) (row := row) gate
  rw [inputs, weightedField_cast, evenPlane, oddPlane] at equation
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate evenLookups]
  exact Rotations.sigma0_field_sound a b c d e f g h bounded evenBound oddBound equation

def sigma1Inputs (env : Environment F) (absolute : Int) : Vector F 8 :=
  #v[read env absolute 5 (-1), read env absolute 6 (-1), read env absolute 4 (0), read env absolute 5 (0), read env absolute 6 (0), read env absolute 4 (1), read env absolute 5 (1), read env absolute 6 (1)]

set_option linter.constructorNameAsVariable false in
/-- Exact source selector 10, evaluated at its real query cells and rotations. -/
theorem sigma1_equation {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (satisfied : RegionOperations.Constraints place self env (activation 10 row)) :
    weightedField Witness.sigma1Recipe (sigma1Inputs env (place self + row : Nat)) =
      parityPlane env (place self + row : Nat) 1 +
        2 * parityPlane env (place self + row : Nat) 3 := by
  rw [activation_sigma1] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, sigma1Gate, sigma1Spec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [weightedField, Witness.sigma1Recipe, sigma1Inputs, read, parityPlane,
    Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

set_option linter.constructorNameAsVariable false in
/-- Any bounded source-limb assignment satisfying the actual selected gate and
output lookup/decomposition gates has the specified SHA sigma output. -/
theorem sigma1_row_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (a b c d e f g h : Nat)
    (bounded : Bounded (messageLimbs a b c d e f g h))
    (inputs : sigma1Inputs env (place self + row : Nat) =
      (#v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h].map (fun n : Nat => (n : F))))
    (gate : RegionOperations.Constraints place self env (activation 10 row))
    (outputGate : RegionOperations.Constraints place self env (activation 11 row))
    (evenLookups : ParityLookups env (place self + row : Nat) 0 1)
    (oddLookups : ParityLookups env (place self + row : Nat) 2 3) :
    (read env (place self + row : Nat) 4 (-1)).val =
      Specs.SHA256.lowerSigma1 (pack (messageLimbs a b c d e f g h)) := by
  obtain ⟨evenBound, evenPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) evenLookups
  obtain ⟨oddBound, oddPlane⟩ := parityLookups_sound (env := env) (absolute := (place self + row : Nat)) oddLookups
  have equation := sigma1_equation (place := place) (self := self) (env := env) (row := row) gate
  rw [inputs, weightedField_cast, evenPlane, oddPlane] at equation
  rw [parity_output (place := place) (self := self) (env := env) (row := row) outputGate evenLookups]
  exact Rotations.sigma1_field_sound a b c d e f g h bounded evenBound oddBound equation

end Midnight.SHA256.Semantics.Gates
