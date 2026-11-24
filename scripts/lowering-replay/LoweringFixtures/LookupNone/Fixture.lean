import LoweringFixtures.Common

/-! `batched_lookup(None)`: every usable row's tuples are looked up, with selector degree 0 in
the LogUp degree. Two table columns, two parallel tuples, an input at rotation 1; no enable. -/
namespace LoweringFixtures.LookupNone
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let q ← selector
  gate "bool" q do
    let x ← advice a
    return #[("", Rust.sub (Rust.mul x x) x)]
  batchedLookup "every row" none do
    let x ← advice a
    let y ← advice b 1
    return #[(#[x, y], t0), (#[Rust.mul x y, x], t1)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩
def bool : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2], .loadTable ⟨⟨1⟩⟩ [0, 5, 6],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness, .enableGate (cleanGate bool) 0,
      .assignAdvice ⟨0⟩ 1 witness]]

#guard source.validate.isOk && !lk.owned && lk.handles.isEmpty
#guard lk.degree source.degree == 3

end LoweringFixtures.LookupNone
