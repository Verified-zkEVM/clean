import LoweringFixtures.Common

/-! A selector-free trash argument on complex `q` beside an owned lookup on `q`. Row 0 enables both;
row 1 enables only the lookup. Rust's `q.enable` there switches the trash identity on as well, and
`Canonical.ops` enables the trash gate there (SharedSelector's class). -/
namespace LoweringFixtures.AdditiveLookupUncovered
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  batchedLookup "own" q do
    let x ← advice a
    return #[(#[x], t)]
  additiveGate "bool" q do
    let x ← advice a
    let y ← advice a 1
    return #[("bool", Rust.mul x x - x), ("next", y - x)]

def source : CS := (configure.run {}).2

def trash : GateSpec := source.trashcans[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def own : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
      .enableGate (cleanGate trash) 0, .enableLookup (cleanLookup own) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup own) [⟨0, false⟩] 1]]

#guard source.validate.isOk && (source.trashcans.map (·.rows)) == #[false]

end LoweringFixtures.AdditiveLookupUncovered
