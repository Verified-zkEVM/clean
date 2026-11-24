import LoweringFixtures.Common

/-! Batches of no tuples: `batched_lookup(Some(q), [(vec![], t)])` and
`batched_lookup_any(None, ..)` with two empty input columns. Rust's input degree is then 1
(`unwrap_or(1)`, logup.rs:231) and the batch has no chunks; a third, ordinary lookup shares `q`.
Lean states nothing for an empty batch; `q` is enabled through its handle and the ordinary tuple. -/
namespace LoweringFixtures.LookupZeroParallel
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  batchedLookup "empty" q do return #[(#[], t)]
  batchedLookupAny "empty any" none do
    let x ← advice a
    let y ← advice a 1
    return #[(#[], x), (#[], Rust.mul x y)]
  batchedLookup "one" q do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lookup (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (lookupHandle (lookup 0) 0) 0,
      .enableLookup (cleanLookup (lookup 2)) [⟨0, false⟩] 0]]

#guard source.validate.isOk && (source.lookups.map (·.inputs.size)) == #[0, 0, 1]
#guard (source.lookups.map (·.inputDegree)) == #[1, 1, 1] &&
  (source.lookups.map (·.numChunks source.degree)) == #[0, 0, 1]

end LoweringFixtures.LookupZeroParallel
