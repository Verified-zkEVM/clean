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
def configureEccChip (cols : EccColumns) (b : Builder) : Builder :=
  let (qWitness, b) := querySelector b cols 0
  let (x, b) := queryA b cols 0
  let (y, b) := queryA b cols 1
  let b := b.createGate [selected qWitness (y*y - x*x*x - .constant FieldConst.pallasB)]
  let (qAdd, b) := querySelector b cols 1
  let (x0, b) := queryA b cols 0
  let (y0, b) := queryA b cols 1
  let (x1, b) := queryA b cols 2
  let (y1, b) := queryA b cols 3
  let (lambda, b) := queryA b cols 4
  let polySlope := (y1 - y0) - lambda * (x1 - x0)
  b.createGate [selected qAdd polySlope]

/-- Construct the pinned constraint-system portion for the Orchard value-commitment
VK test from idiomatic Halo2 configuration steps. -/
def orchardValueCommitCS : ConstraintSystem :=
  let b : Builder := {}
  let (cols, b) := configureColumns b
  let b := configureRangeCheck cols b
  let b := configureEccChip cols b
  b.cs

end Halo2.Orchard

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
  let (cols, b) := Orchard.configureColumns b
  -- Rust allocates the instance column after lookup table columns and before
  -- enabling advice equality. Our column counts are independent, but the
  -- permutation order is important; ensure instance equality is first.
  let cs := { b.cs with
    numInstanceColumns := 1
    instanceQueries := [(Pinned.Column.instanceCol 0, Rotation.rot 0)] }
  (cols, { b with cs := cs })

/-- Current Lean-side full Orchard action CS builder. This function is meant to
mirror `Circuit::configure`; subchip ports are filled in incrementally. -/
def orchardActionCS : ConstraintSystem :=
  let b : Builder := {}
  let (cols, b) := configureActionColumns b
  let b := configureOrchardGate cols b
  let b := configureAddChip cols b
  let b := Orchard.configureRangeCheck cols b
  let b := Orchard.configureEccChip cols b
  b.cs

end Halo2.Orchard.Action
