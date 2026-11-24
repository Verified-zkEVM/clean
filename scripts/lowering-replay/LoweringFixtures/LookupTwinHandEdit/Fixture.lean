import LoweringFixtures.Common

/-! Two lookups equal as values whose closures differ: the second also queries `b(2)`, which
nothing else does. Dropping the first by hand leaves a Rust-producible CS (gate, then the second
lookup); the export must give the kept lookup its own closure, not the first equal record's. -/
namespace LoweringFixtures.LookupTwinHandEdit
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  gate "g" q do
    let x ← advice a
    return #[("g", x)]
  batchedLookup "l" ql do
    let x ← advice a
    return #[(#[x], t)]
  batchedLookup "l" ql do
    let _ ← advice b 2
    let x ← advice a
    return #[(#[x], t)]

def configured : CS := (configure.run {}).2

def empty : BatchedLookup := ⟨"", .const 0, #[], #[]⟩

def source : CS := { configured with lookups := #[configured.lookups[1]?.getD empty] }

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 2 witness, .enableGate (cleanGate g) 0,
      .enableLookup (cleanLookup (source.lookups[0]?.getD empty)) [⟨1, false⟩] 0]]

end LoweringFixtures.LookupTwinHandEdit
