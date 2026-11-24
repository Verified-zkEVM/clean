import LoweringFixtures.VanillaPlonk.Fixture
import LoweringFixtures.SelectorlessGate.Fixture
import LoweringFixtures.ForeignMultiSelect.Fixture
import LoweringFixtures.ScannerSubstring.Fixture
import Midnight.Backend.Checks
import Midnight.Backend.Meaning
import Midnight.Backend.Rows.ForeignMultiSelect

/-! The rows fixtures as Clean configure programs: each compiles to the fixture's `ConfigM`
source, and `Agrees` holds, so at any one valuation `ConfigurationHoldsAt` on it is the source's
`RowGatesHoldAt ∧ RowLookupsHoldAt` (`configurationHoldsAt_iff`). With every owned lookup's tables
loaded, holding at Rust's valuation for every blinding is `RowGatesHold ∧ RowLookupsHold`
(`compiled_configurationHolds_iff`, as `foreignMultiSelect_meaning` uses). The rows-gate canary is the SHA-256 program followed by a selector-free gate.
Programs that end with an equality or a lookup are compared without the builder scratch
`currentQueries`. Rust has no such field: it is the closure recorder's scratch, read only while a
`ConfigM` gate or lookup is built (Configuration.lean), never by layout or key derivation, and the
replay keeps it exact only for programs ending with a gate. `run.sh OUT` (the default Simple run)
replays each program here in place of its fixture's source, so Rust keys the compiled CS too. -/

namespace LoweringFixtures.Compiled
open Halo2 (Column)
open Midnight
open Midnight.Keygen (E CS GateSpec)
open Midnight.Keygen.Rust (sub mul neg)
open Midnight.Backend (Agrees)

def scrub (s : CS) : CS := { s with currentQueries := #[] }

def vanillaPlonk : Frontend.Configure Unit := do
  let a ← Frontend.adviceColumn
  let b ← Frontend.adviceColumn
  let c ← Frontend.adviceColumn
  let d ← Frontend.adviceColumn
  let e ← Frontend.adviceColumn
  let sf ← Frontend.fixedColumn
  let sa ← Frontend.fixedColumn
  let sb ← Frontend.fixedColumn
  let sc ← Frontend.fixedColumn
  let sm ← Frontend.fixedColumn
  let sp ← Frontend.fixedColumn
  let p ← Frontend.instanceColumn
  Frontend.gateWithoutSelector "Combined add-mult" do
    let dn ← Frontend.advice d 1
    let x ← Frontend.advice a
    let f ← Frontend.fixed sf
    let ep ← Frontend.advice e (-1)
    let y ← Frontend.advice b
    let z ← Frontend.advice c
    let fa ← Frontend.fixed sa
    let fb ← Frontend.fixed sb
    let fc ← Frontend.fixed sc
    let fm ← Frontend.fixed sm
    return #[("", .add (sub (.add (.add (mul x fa) (mul y fb)) (mul (mul x y) fm))
      (mul z fc)) (mul f (mul dn ep)))]
  Frontend.gateWithoutSelector "Public input" do
    let x ← Frontend.advice a
    let pi ← Frontend.inst p
    let fp ← Frontend.fixed sp
    return #[("", mul fp (sub x pi))]
  Frontend.enableEquality sf
  Frontend.enableEquality e
  Frontend.enableEquality d
  Frontend.enableEquality p
  Frontend.enableEquality sm
  Frontend.enableEquality sa

def selectorless : Frontend.Configure Unit := do
  let f ← Frontend.fixedColumn
  let a ← Frontend.adviceColumn
  let b ← Frontend.adviceColumn
  let c ← Frontend.adviceColumn
  let sa ← Frontend.fixedColumn
  let sb ← Frontend.fixedColumn
  let sc ← Frontend.fixedColumn
  let sm ← Frontend.fixedColumn
  Frontend.gateWithoutSelector "fixed column at two rotations" do
    let cur ← Frontend.fixed f
    let next ← Frontend.fixed f 1
    return #[("", mul cur next)]
  Frontend.gateWithoutSelector "Combined add-mult" do
    let x ← Frontend.advice a
    let y ← Frontend.advice b
    let z ← Frontend.advice c
    let fa ← Frontend.fixed sa
    let fb ← Frontend.fixed sb
    let fc ← Frontend.fixed sc
    let fm ← Frontend.fixed sm
    return #[("", sub (.add (.add (mul x fa) (mul y fb)) (mul (mul x y) fm)) (mul z fc))]

def scanner : Frontend.Configure Unit := do
  let cols ← (List.range 6).mapM fun _ => Frontend.adviceColumn
  let indexCol ← Frontend.fixedColumn
  let tagCol ← Frontend.fixedColumn
  let q ← Frontend.complexSelector
  for batch in [0:3] do
    Frontend.lookupAny s!"substring lookup (batch {batch})" none do
      let sel ← Frontend.querySelector q
      let notSel := sub (.const 1) sel
      let index ← Frontend.fixed indexCol
      let tag ← Frontend.fixed tagCol
      let shift : E := .const 257
      let table ← Frontend.advice (cols.getD (2 * batch) ⟨0⟩)
      let packed ← Frontend.advice (cols.getD (2 * batch + 1) ⟨0⟩)
      return #[(tag, mul sel tag),
        (packed, .add (mul sel (.add (mul index shift) table)) (mul notSel packed))]

/-- The rows-gate canary: SHA-256 plus `f(next) - f(next)` on the byte table column. -/
def rowsCanary : Frontend.Configure Unit := do
  Frontend.SHA256.configure
  Frontend.gateWithoutSelector "rows" do
    let next ← Frontend.fixed ⟨11⟩ 1
    return #[("z", sub next next)]

def canaryGate : GateSpec :=
  { name := "rows", selector := ⟨0, false⟩, queries := #[.fixed ⟨11⟩ 1],
    constraints := #[("z", .add (.var (.fixed ⟨11⟩ 1)) (neg (.var (.fixed ⟨11⟩ 1))))],
    raw := true, rows := true }

/-- The canary's source: the SHA-256 baseline with the gate, its fixed query and its closure. -/
def canarySource : CS :=
  { Backend.Fixtures.sha256 with
    gates := Backend.Fixtures.sha256.gates.push canaryGate
    fixedQueries := Backend.Fixtures.sha256.fixedQueries.push (11, 1)
    gateClosures := Backend.Fixtures.sha256.gateClosures.push
      ("rows", #[.fixed ⟨11⟩ 1], #[.fixed ⟨11⟩ 1], true)
    currentQueries := #[.fixed ⟨11⟩ 1] }

theorem vanillaPlonk_cs : scrub (Frontend.compile vanillaPlonk) = scrub VanillaPlonk.source := by
  native_decide

theorem selectorless_cs : Frontend.compile selectorless = SelectorlessGate.source := by
  native_decide

theorem foreignMultiSelect_cs :
    scrub (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) =
      scrub ForeignMultiSelect.source := by
  native_decide

theorem scanner_cs : scrub (Frontend.compile scanner) = scrub ScannerSubstring.source := by
  native_decide

theorem rowsCanary_cs : Frontend.compile rowsCanary = canarySource := by
  native_decide

theorem vanillaPlonk_agrees : Agrees (vanillaPlonk.run {}).2 (Frontend.compile vanillaPlonk) := by
  native_decide

theorem selectorless_agrees :
    Agrees (selectorless.run {}).2 (Frontend.compile selectorless) := by
  native_decide

theorem foreignMultiSelect_agrees :
    Agrees (Backend.Rows.ForeignMultiSelect.configure.run {}).2
      (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) := by
  native_decide

theorem scanner_agrees : Agrees (scanner.run {}).2 (Frontend.compile scanner) := by
  native_decide

theorem rowsCanary_agrees : Agrees (rowsCanary.run {}).2 (Frontend.compile rowsCanary) := by
  native_decide

/-- ForeignMultiSelect's `ConfigurationHolds`, at Rust's valuation for every blinding, is its
compiled source's reference meaning. -/
theorem foreignMultiSelect_meaning (ops : Halo2.Operations F) (k : ℕ)
    (env : Halo2.Environment F) :
    (∀ blind, Halo2.ConfigurationHoldsAt (Backend.Rows.ForeignMultiSelect.configure.run {}).2
        (2 ^ k) (Chips.CertifiedCircuit.layoutConfig
          (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) k).usableRows
        (Chips.CertifiedCircuit.rowValuation
          (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) ops k env blind)) ↔
      Chips.CertifiedCircuit.RowGatesHold
          (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) ops k env ∧
        Chips.CertifiedCircuit.RowLookupsHold
          (Frontend.compile Backend.Rows.ForeignMultiSelect.configure) ops k env :=
  Backend.compiled_configurationHolds_iff foreignMultiSelect_agrees
    (Backend.loaded_of_unowned (by native_decide)) k env

end LoweringFixtures.Compiled
