import LoweringFixtures.Common

/-! Six advice queries on one column, five registered only by a lookup closure that does not
use them: they set the blinding factors, so the usable rows. The table fills all but one usable
row, a region reaches the last usable row and the next is placed after the first on the other column. -/
namespace LoweringFixtures.LookupBlinding
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩
  batchedLookup "wide" ql do
    let _ ← advice b (-3)
    let _ ← advice b 4
    let x ← advice a
    let _ ← advice b 1
    let _ ← advice b (-1)
    let _ ← advice b 2
    let y ← advice b
    return #[(#[x + y], t)]

def source : CS := (configure.run {}).2

def wide : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def usable : Nat := (Chips.CertifiedCircuit.layoutConfig source 5).usableRows

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ ((List.range (usable - 1)).map fun i => (i + 3 : F)),
    .region "l" [.assignAdvice ⟨1⟩ 3 witness, .enableLookup (cleanLookup wide) [⟨0, false⟩] 3],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ (usable - 1) witness],
    .region "s" [.assignAdvice ⟨1⟩ 0 witness,
      .constrainEqual (cell 2 0 .advice 1) (cell 1 (usable - 1) .advice 0)]]

end LoweringFixtures.LookupBlinding
