import LoweringFixtures.Common

/-! `set_minimum_degree(9)` over degree-3 gates and a degree-2 LogUp batch of three: the CS degree
(9, else 5), the chunking that reads it (one chunk, else two) and the pinned
`minimum_degree: Some(9)`. `MinimumDegreeLow` sets 2, below the rest. -/
namespace LoweringFixtures.MinimumDegree
open Halo2 Midnight Midnight.Keygen

def configure (minimum : Nat) : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  setMinimumDegree minimum
  gate "square" q do
    let x ← advice a
    return #[("square", Rust.mul x x)]
  batchedLookup "range" ql do
    let x ← advice a
    let y ← advice a 1
    return #[(#[x, y, Rust.mul x y], t)]

def source (minimum : Nat) : CS := ((configure minimum).run {}).2

def fixtureOf (minimum : Nat) : Export.Replay.Fixture where
  source := source minimum
  k := 6
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2, 3],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .enableGate (cleanGate ((source minimum).gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩)) 0] ++
      (List.range 3).map fun i => .enableLookup
        (cleanLookup ((source minimum).lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩) i) [⟨1, false⟩] 0)]

def fixture : Export.Replay.Fixture := fixtureOf 9

#guard (source 9).degree == 9 && (source 2).degree == 5 && (source 9).validate.isOk
#guard ((source 9).lookups.map (·.numChunks 9)) == #[1] && ((source 2).lookups.map (·.numChunks 5)) == #[2]
#guard ((source 9).pinnedDebug.splitOn "minimum_degree: Some(9) }").length == 2

end LoweringFixtures.MinimumDegree
