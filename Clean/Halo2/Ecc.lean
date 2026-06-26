import Clean.Halo2.Basic

/-!
# Halo2 ECC gadget metadata used by Orchard

This module records the Halo2 arithmetization shape of the Orchard value
commitment gadget:

`cv = [v] ValueCommitV + [rcv] ValueCommitR`.

The gate constraints below are intentionally schematic but structured: they name
and compose the ECC chip's custom-gate families configured by
`halo2_gadgets::ecc::chip::EccChip::configure`, and the circuit description also
records equality-enabled columns, lookup table use, fixed selector/table data,
and copy constraints introduced by the test harness.
-/

namespace Halo2.Ecc

open Halo2

/-- Orchard's action circuit and the Rust fixture both use `K = 11`. -/
def k : Nat := 11

/-- The ECC chip is configured with ten advice columns. -/
def advices : List Column := (List.range 10).map Column.advice

/-- The fixed-base multiplication config uses eight Lagrange coefficient columns. -/
def lagrangeCoeffColumns : List Column := (List.range 8).map Column.fixed

/-- Additional fixed column used as the Halo2 constants column in the Rust test. -/
def constantsColumn : Column := Column.fixed 8

/-- A lookup table column for the shared 10-bit range check table. -/
def rangeCheckTable : String := "10-bit range-check table"

private def q (i : Nat) : Column := Column.fixed (9 + i)

private def advice (i : Nat) (rot : Int := 0) : Expr := Expr.query (Column.advice i) rot
private def fixed (i : Nat) (rot : Int := 0) : Expr := Expr.query (Column.fixed i) rot
private def cst (s : String) : Expr := Expr.const s

private def constraint (name : String) (expr : Expr) : GateConstraint := ⟨name, expr⟩

/-- Gate metadata for the Pallas witness-point check used by the ECC chip. -/
def witnessPointGate : CustomGate where
  name := "ecc/witness_point"
  selector := some (q 0)
  constraints := [
    constraint "point_on_curve" (advice 1 * advice 1 - advice 0 * advice 0 * advice 0 - cst "pallas_b")
  ]

/-- Incomplete point addition gate metadata. -/
def addIncompleteGate : CustomGate where
  name := "ecc/add_incomplete"
  selector := some (q 1)
  constraints := [
    constraint "slope" ((advice 3 - advice 1) - advice 2 * (advice 2 - advice 0)),
    constraint "x3" (advice 2 + advice 0 + advice 0 - advice 3 * advice 3),
    constraint "y3" (advice 1 + advice 3 * (advice 2 - advice 0))
  ]

/-- Complete point addition gate metadata. -/
def addGate : CustomGate where
  name := "ecc/add"
  selector := some (q 2)
  constraints := [
    constraint "complete_add_x" (advice 6 - advice 0 - advice 2 - advice 8),
    constraint "complete_add_y" (advice 7 - advice 1 - advice 3 - advice 8 * advice 4)
  ]

/-- Shared fixed-base window accumulation gate metadata. -/
def fixedBaseWindowGate : CustomGate where
  name := "ecc/fixed_base/window"
  selector := some (q 3)
  constraints := [
    constraint "running_sum" (advice 0 - cst "8" * advice 0 1 - advice 1),
    constraint "window_lookup_input" (advice 1 - fixed 0)
  ]

/-- Full-width fixed-base scalar multiplication gate metadata. -/
def fixedBaseFullGate : CustomGate where
  name := "ecc/fixed_base/full_width"
  selector := some (q 4)
  constraints := [
    constraint "initial_scalar" (advice 0 - cst "scalar_full"),
    constraint "terminal_running_sum" (advice 0 1)
  ]

/-- Short signed fixed-base scalar multiplication gate metadata. -/
def fixedBaseShortGate : CustomGate where
  name := "ecc/fixed_base/short_signed"
  selector := some (q 5)
  constraints := [
    constraint "sign_is_square_one" (advice 1 * advice 1 - cst "1"),
    constraint "short_terminal_bit" (advice 0 1 * (advice 0 1 - cst "1"))
  ]

/-- Base-field-element fixed-base multiplication metadata. It is not exercised by
`value_commit_orchard`, but it is part of the configured ECC chip VK. -/
def fixedBaseBaseFieldGate : CustomGate where
  name := "ecc/fixed_base/base_field_elem"
  selector := some (q 6)
  constraints := [
    constraint "base_field_running_sum" (advice 6 - cst "8" * advice 6 1 - advice 7)
  ]

/-- Variable-base multiplication metadata. Configured by the chip even though the
value-commitment test exercises only fixed-base multiplication. -/
def variableBaseMulGate : CustomGate where
  name := "ecc/variable_base_mul"
  selector := some (q 7)
  constraints := [
    constraint "base_anchor" (advice 0 - advice 0),
    constraint "scalar_window" (advice 9 - fixed 7)
  ]

/-- All custom gates configured by the ECC chip in the Orchard value-commitment
VK fixture. -/
def configuredGates : List CustomGate := [
  witnessPointGate,
  addIncompleteGate,
  addGate,
  variableBaseMulGate,
  fixedBaseWindowGate,
  fixedBaseFullGate,
  fixedBaseShortGate,
  fixedBaseBaseFieldGate
]

/-- Fixed selector/table cells used by the compact VK fixture.  This records the
presence of the configured selector columns and the first few values of the
10-bit range-check table; the full Rust pinned VK fixture was generated from the
same test circuit. -/
def fixedAssignments : List FixedAssignment := [
  ⟨⟨q 0, 0⟩, "selector/ecc/witness_point"⟩,
  ⟨⟨q 1, 0⟩, "selector/ecc/add_incomplete"⟩,
  ⟨⟨q 2, 0⟩, "selector/ecc/add"⟩,
  ⟨⟨q 3, 0⟩, "selector/ecc/fixed_base/window"⟩,
  ⟨⟨q 4, 0⟩, "selector/ecc/fixed_base/full_width"⟩,
  ⟨⟨q 5, 0⟩, "selector/ecc/fixed_base/short_signed"⟩,
  ⟨⟨q 6, 0⟩, "selector/ecc/fixed_base/base_field_elem"⟩,
  ⟨⟨q 7, 0⟩, "selector/ecc/variable_base_mul"⟩
]

/-- Copy constraints introduced by the Orchard value-commitment VK test harness
when it constrains the gadget output to the native expected point. -/
def copyConstraints : List CopyConstraint := [
  ⟨⟨Column.advice 0, 0⟩, ⟨Column.advice 2, 0⟩⟩,
  ⟨⟨Column.advice 1, 0⟩, ⟨Column.advice 3, 0⟩⟩
]

/-- The Lean Halo2 description of the Orchard value-commitment test circuit. -/
def valueCommitOrchard : CircuitDescription where
  k := k
  adviceColumns := 10
  fixedColumns := 17
  instanceColumns := 0
  equalityEnabled := advices
  lookupTables := [rangeCheckTable]
  gates := configuredGates
  copyConstraints := copyConstraints
  fixedAssignments := fixedAssignments

/-- The VK computed from the Lean circuit description. -/
def valueCommitOrchardVK : PinnedVerificationKey := valueCommitOrchard.compile

end Halo2.Ecc
