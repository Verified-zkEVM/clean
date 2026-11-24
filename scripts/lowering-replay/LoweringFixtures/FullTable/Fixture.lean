import LoweringFixtures.Common

/-! A table filling every usable row. Rust's `fill_from_row` at row `usable` fails; Lean's
`OperationsLawful.TableValid` rejects it too (`values.length < usable`). -/
namespace LoweringFixtures.FullTable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "full" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def full : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def usable : Nat := (Chips.CertifiedCircuit.layoutConfig source 4).usableRows

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ ((List.range usable).map fun i => (i : F)),
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableLookup (cleanLookup full) [⟨0, false⟩] 0]]

end LoweringFixtures.FullTable
