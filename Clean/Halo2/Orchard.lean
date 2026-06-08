import Clean.Halo2.Pinned

/-!
# Orchard Halo2 circuit construction in Lean

This is the beginning of a direct Lean implementation of the Halo2-side Orchard
circuit configuration.  It uses the builder from `Clean.Halo2.Pinned` rather
than copying the Rust pinned-CS dump.

The immediate target is to grow this until `orchardValueCommitCS` exactly matches
`Clean/Halo2/Fixtures/orchard_value_commit_rust_pinned_cs.txt`, and then to
extend the same style to the full Orchard action circuit.
-/

namespace Halo2.Orchard

open Halo2.Pinned

namespace FieldConst

def zero := "0x0000000000000000000000000000000000000000000000000000000000000000"
def one := "0x0000000000000000000000000000000000000000000000000000000000000001"
def two := "0x0000000000000000000000000000000000000000000000000000000000000002"
def three := "0x0000000000000000000000000000000000000000000000000000000000000003"
def four := "0x0000000000000000000000000000000000000000000000000000000000000004"
def five := "0x0000000000000000000000000000000000000000000000000000000000000005"
def eight := "0x0000000000000000000000000000000000000000000000000000000000000008"

def pallasB := "0x0000000000000000000000000000000000000000000000000000000000000005"

end FieldConst

structure EccColumns where
  advices : Array Pinned.Column
  lagrangeCoeffs : Array Pinned.Column
  constants : Pinned.Column
  tableIdx : Pinned.Column
  selectors : Array Nat

private def allocManyAdvice : Nat → Builder → Array Pinned.Column × Builder
  | 0, b => (#[], b)
  | n+1, b =>
      let (c, b) := b.adviceColumn
      let (cs, b) := allocManyAdvice n b
      (#[c] ++ cs, b)

private def allocManyFixed : Nat → Builder → Array Pinned.Column × Builder
  | 0, b => (#[], b)
  | n+1, b =>
      let (c, b) := b.fixedColumn
      let (cs, b) := allocManyFixed n b
      (#[c] ++ cs, b)

private def allocManySelectors : Nat → Builder → Array Nat × Builder
  | 0, b => (#[], b)
  | n+1, b =>
      let (c, b) := b.selector
      let (cs, b) := allocManySelectors n b
      (#[c] ++ cs, b)

private def arrayGetD (xs : Array Pinned.Column) (i : Nat) : Pinned.Column := xs[i]!

private def queryA (b : Builder) (cols : EccColumns) (i : Nat) (rot : Int := 0) : Expression × Builder :=
  b.queryAdvice (arrayGetD cols.advices i) (.rot rot)

private def queryF (b : Builder) (cols : EccColumns) (i : Nat) (rot : Int := 0) : Expression × Builder :=
  b.queryFixed (arrayGetD cols.lagrangeCoeffs i) (.rot rot)

private def querySelector (b : Builder) (cols : EccColumns) (i : Nat) : Expression × Builder :=
  (.selector cols.selectors[i]!, b)

private def selected (q : Expression) (e : Expression) : Expression := q * e

/-- Configure the columns used by the Orchard value-commitment Halo2 test. -/
def configureColumns (b : Builder) : EccColumns × Builder :=
  let (advices, b) := allocManyAdvice 10 b
  let b := advices.foldl (fun b col => b.enableEquality col) b
  let (lagrangeCoeffs, b) := allocManyFixed 8 b
  let (constants, b) := b.fixedColumn
  let b := b.enableConstant constants
  let (tableIdx, b) := b.fixedColumn
  let (selectors, b) := allocManySelectors 56 b
  ({ advices, lagrangeCoeffs, constants, tableIdx, selectors }, b)

/-- First range-check table gate created by `LookupRangeCheckConfig::configure`.
This matches the first polynomial in the Rust dump: q · (2-q)(3-q)... . -/
def configureRangeCheck (cols : EccColumns) (b : Builder) : Builder :=
  let (q, b) := b.queryFixed cols.tableIdx (.rot 0)
  let poly := q * (.constant FieldConst.two - q) * (.constant FieldConst.three - q) *
    (.constant FieldConst.four - q) * (.constant FieldConst.five - q)
  b.createGate [poly]

/-- A first direct transcription of `EccChip::configure`'s custom gates.  This is
incomplete, but unlike the previous scaffold it is generated from circuit-style
configuration code and uses Halo2 query allocation. -/
def configureEccChipAt (selectorOffset : Nat) (cols : EccColumns) (b : Builder) : Builder :=
  let (qWitness, b) := querySelector b cols selectorOffset
  let (x, b) := queryA b cols 0
  let (y, b) := queryA b cols 1
  let b := b.createGate [selected qWitness (y*y - x*x*x - .constant FieldConst.pallasB)]
  let (qAdd, b) := querySelector b cols (selectorOffset + 1)
  let (x0, b) := queryA b cols 0
  let (y0, b) := queryA b cols 1
  let (x1, b) := queryA b cols 2
  let (y1, b) := queryA b cols 3
  let (lambda, b) := queryA b cols 4
  let polySlope := (y1 - y0) - lambda * (x1 - x0)
  b.createGate [selected qAdd polySlope]

def configureEccChip (cols : EccColumns) (b : Builder) : Builder :=
  configureEccChipAt 0 cols b

/-- Construct the pinned constraint-system portion for the Orchard value-commitment
VK test from idiomatic Halo2 configuration steps. -/
def orchardValueCommitCS : ConstraintSystem :=
  let b : Builder := {}
  let (cols, b) := configureColumns b
  let b := configureRangeCheck cols b
  let b := configureEccChip cols b
  b.cs

end Halo2.Orchard

namespace Halo2.Orchard.LookupRangeCheck

open Halo2.Pinned

private def twoPow10 := "0x0000000000000000000000000000000000000000000000000000000000000400"

/-- Port of `LookupRangeCheckConfig::<_, 10>::configure`. -/
def configure (cols : Orchard.EccColumns) (b : Builder) : Builder :=
  let runningSum := cols.advices[9]!
  let tableIdx := cols.tableIdx
  let b := b.enableEquality runningSum
  let (qLookup, b) := b.complexSelector
  let (qRunning, b) := b.complexSelector
  let (qBitshift, b) := b.selector
  let (qLookupE, b) := (.selector qLookup, b)
  let (qRunningE, b) := (.selector qRunning, b)
  let (zCur, b) := b.queryAdvice runningSum (.rot 0)
  let (zNext, b) := b.queryAdvice runningSum (.rot 1)
  let tableExpr := (b.queryFixed tableIdx (.rot 0)).1
  let b := (b.queryFixed tableIdx (.rot 0)).2
  let one := Expression.constant FieldConst.one
  let runningSumWord := zCur - zNext * Expression.constant twoPow10
  let runningSumLookup := qRunningE * runningSumWord
  let shortLookup := (one - qRunningE) * zCur
  let b := b.lookup { inputExpressions := [qLookupE * (runningSumLookup + shortLookup)], tableExpressions := [tableExpr] }
  let qBitshiftE := Expression.selector qBitshift
  let (word, b) := b.queryAdvice runningSum (.rot (-1))
  let (shiftedWord, b) := b.queryAdvice runningSum (.rot 0)
  let (invTwoPowS, b) := b.queryAdvice runningSum (.rot 1)
  b.createGate [qBitshiftE * (word * Expression.constant twoPow10 * invTwoPowS - shiftedWord)]

end Halo2.Orchard.LookupRangeCheck


namespace Halo2.Orchard.EccAllocated

open Halo2.Pinned

private def a (b : Builder) (cols : Orchard.EccColumns) (i : Nat) (r : Int := 0) :=
  Orchard.queryA b cols i r

/-- Allocate selectors in the same order as `EccChip::configure` and create the
first ECC gates. Later gates in this namespace are being filled out following
`halo2_gadgets/src/ecc/chip`. -/
def configure (cols : Orchard.EccColumns) (b : Builder) : Builder :=
  -- witness_point::Config::configure
  let (qPoint, b) := b.selector
  let (qPointNonId, b) := b.selector
  let (x0, b) := a b cols 0
  let (y0, b) := a b cols 1
  let curve := y0*y0 - x0*x0*x0 - Expression.constant FieldConst.pallasB
  let b := b.createGate [Expression.selector qPoint * x0 * curve, Expression.selector qPoint * y0 * curve]
  let b := b.createGate [Expression.selector qPointNonId * curve]
  -- add_incomplete::Config::configure
  let (qAddIncomplete, b) := b.selector
  let (xp, b) := a b cols 0
  let (yp, b) := a b cols 1
  let (xq, b) := a b cols 2
  let (yq, b) := a b cols 3
  let (xr, b) := a b cols 2 1
  let (yr, b) := a b cols 3 1
  let poly1 := (xr + xq + xp) * (xp - xq) * (xp - xq) - (yp - yq) * (yp - yq)
  let poly2 := (yr + yq) * (xp - xq) - (yp - yq) * (xq - xr)
  let b := b.createGate [Expression.selector qAddIncomplete * poly1, Expression.selector qAddIncomplete * poly2]
  -- add::Config::configure
  let (qAdd, b) := b.selector
  let (lambda, b) := a b cols 4
  let (alpha, b) := a b cols 5
  let (beta, b) := a b cols 6
  let (gamma, b) := a b cols 7
  let (delta, b) := a b cols 8
  let one := Expression.constant FieldConst.one
  let two := Expression.constant FieldConst.two
  let three := Expression.constant FieldConst.three
  let xqMinusXp := xq - xp
  let xpMinusXr := xp - xr
  let yqPlusYp := yq + yp
  let ifAlpha := xqMinusXp * alpha
  let ifBeta := xp * beta
  let ifGamma := xq * gamma
  let ifDelta := yqPlusYp * delta
  let polyAdd1 := xqMinusXp * (xqMinusXp * lambda - (yq - yp))
  let polyAdd2 := (one - ifAlpha) * (two * yp * lambda - three * xp * xp)
  let polyAdd3 := lambda * lambda - xp - xq - xr
  let polyAdd4 := lambda * xpMinusXr - yp - yr
  let b := b.createGate [
    Expression.selector qAdd * polyAdd1,
    Expression.selector qAdd * polyAdd2,
    Expression.selector qAdd * polyAdd3,
    Expression.selector qAdd * polyAdd4,
    Expression.selector qAdd * (ifAlpha * (one - ifAlpha)),
    Expression.selector qAdd * (ifBeta * (one - ifBeta)),
    Expression.selector qAdd * (ifGamma * (one - ifGamma)),
    Expression.selector qAdd * (ifDelta * (one - ifDelta))]
  -- variable-base scalar mul selectors: hi(3), lo(3), complete, overflow, lsb
  let (_, b) := b.selector; let (_, b) := b.selector; let (_, b) := b.selector
  let (_, b) := b.selector; let (_, b) := b.selector; let (_, b) := b.selector
  let (_, b) := b.selector
  let (_, b) := b.selector
  let (_, b) := b.selector
  -- fixed-base shared running sum, full-width, short, base-field selectors
  let (_, b) := b.selector
  let (_, b) := b.selector
  let (_, b) := b.selector
  let (_, b) := b.selector
  b

end Halo2.Orchard.EccAllocated


namespace Halo2.Orchard.Action

open Halo2.Pinned

private def a (b : Builder) (cols : Orchard.EccColumns) (i : Nat) (r : Int := 0) :=
  Orchard.queryA b cols i r

private def sel (b : Builder) (cols : Orchard.EccColumns) (i : Nat) :=
  Orchard.querySelector b cols i

/-- The top-level Orchard action gate from `orchard/src/circuit.rs`. -/
def configureOrchardGate (cols : Orchard.EccColumns) (b : Builder) : Builder :=
  let (q, b) := sel b cols 0
  let (vOld, b) := a b cols 0
  let (vNew, b) := a b cols 1
  let (magnitude, b) := a b cols 2
  let (sign, b) := a b cols 3
  let (root, b) := a b cols 4
  let (anchor, b) := a b cols 5
  let (enableSpends, b) := a b cols 6
  let (enableOutputs, b) := a b cols 7
  let one := Expression.constant FieldConst.one
  b.createGate [
    q * (vOld - vNew - magnitude * sign),
    q * (vOld * (root - anchor)),
    q * (vOld * (one - enableSpends)),
    q * (vNew * (one - enableOutputs))
  ]

/-- The tiny field-addition chip used by Orchard. -/
def configureAddChip (cols : Orchard.EccColumns) (b : Builder) : Builder :=
  let (q, b) := sel b cols 1
  let (aa, b) := a b cols 7
  let (bb, b) := a b cols 8
  let (cc, b) := a b cols 6
  b.createGate [q * (aa + bb - cc)]

/-- Allocate the public input column and top-level Orchard columns in the same
order as the Rust circuit. -/
def configureActionColumns (b : Builder) : Orchard.EccColumns × Builder :=
  let (advices, b) := Orchard.allocManyAdvice 10 b
  let (_, b) := b.selector
  let (_, b) := b.selector
  let (tableIdx, b) := b.fixedColumn
  let (_lookupX, b) := b.fixedColumn
  let (_lookupY, b) := b.fixedColumn
  let (_primary, b) := b.instanceColumn
  let b := b.enableEquality (Pinned.Column.instanceCol 0)
  let b := advices.foldl (fun b col => b.enableEquality col) b
  let (lagrangeCoeffs, b) := Orchard.allocManyFixed 8 b
  let b := b.enableConstant lagrangeCoeffs[0]!
  let selectors := (List.range 56).toArray
  ({ advices, lagrangeCoeffs, constants := lagrangeCoeffs[0]!, tableIdx, selectors }, b)

/-- Current Lean-side full Orchard action CS builder. This function is meant to
mirror `Circuit::configure`; subchip ports are filled in incrementally. -/
def orchardActionCS : ConstraintSystem :=
  let b : Builder := {}
  let (cols, b) := configureActionColumns b
  let b := configureOrchardGate cols b
  let b := configureAddChip cols b
  let b := Halo2.Orchard.LookupRangeCheck.configure cols b
  let b := Halo2.Orchard.EccAllocated.configure cols b
  let b := b.ensureNumSelectors 56
  b.cs

end Halo2.Orchard.Action
