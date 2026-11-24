import LoweringFixtures.Common

/-! Lookups edited by hand after configuration: the first is dropped and a renamed copy of the
second appended. The second's closure registers `b(2)`, which nothing else queries, so the export
must give it its own closure (keyed by the lookup, not by position) for Rust to register Lean's
query list; the hand-built copy has no closure. -/
namespace LoweringFixtures.LookupHandEdit
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  gate "g" q do
    let x ← advice a
    let y ← advice b 1
    return #[("g", x - y)]
  batchedLookup "first" ql do
    let x ← advice a
    let _ ← advice b 1
    return #[(#[x], t)]
  batchedLookup "second" ql do
    let _ ← advice b 2
    let x ← advice a
    return #[(#[x], t)]

def configured : CS := (configure.run {}).2

def empty : BatchedLookup := ⟨"", .const 0, #[], #[]⟩

def source : CS :=
  let second := configured.lookups[1]?.getD empty
  { configured with lookups := #[second, { second with name := "by hand" }] }

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness, .enableGate (cleanGate g) 0,
      .enableLookup (cleanLookup (source.lookups[0]?.getD empty)) [⟨1, false⟩] 0,
      .enableLookup (cleanLookup (source.lookups[1]?.getD empty)) [⟨1, false⟩] 0]]

#guard (Export.Replay.lookupClosures source).map (·.1) =
  #[#[.advice ⟨1⟩ 2, .advice ⟨0⟩ 0], #[]]

end LoweringFixtures.LookupHandEdit
