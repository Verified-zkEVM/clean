import LoweringFixtures.Common

/-! V1 placement (v1/strategy.rs): regions sorted by advice area, ties in reverse stream order
(stable sort, then reverse), first fit over each region's columns in `Column` order with slack.
Region 4 leaves a gap on a0 that regions 11 (pushed down to row 3 by s1, within the gap's slack),
9 and 1 later fill; regions 6 and 7 share selector 0 and stack in reverse order; an empty region
and selector-only and fixed-only regions. Starts from an independent model of strategy.rs. -/
namespace LoweringFixtures.V1Placement
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a0 ← adviceColumn
  let _ ← adviceColumn
  let a2 ← adviceColumn
  let f0 ← fixedColumn
  let _ ← fixedColumn
  let q0 ← selector
  let q1 ← selector
  gate "g0" q0 do
    let x ← advice a0
    return #[("x", x)]
  gate "g1" q1 do
    let y ← advice a2
    let k ← fixed f0
    return #[("y", y * k)]

def source : CS := (configure.run {}).2

def g0 : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def g1 : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def advice (column rows : Nat) : RegionOperations F :=
  (List.range rows).map fun row => .assignAdvice ⟨column⟩ row witness

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "a01x2" (advice 0 2 ++ advice 1 2),
    .region "a0x2" (advice 0 2),
    .region "a1x5" (advice 1 5),
    .region "a2x2" (advice 2 2),
    .region "a01x2b" (advice 1 2 ++ advice 0 2),
    .region "f0x3" [.assignFixed ⟨0⟩ 0 1, .assignFixed ⟨0⟩ 2 3],
    .region "s0" [.enableGate (cleanGate g0) 0],
    .region "s0b" [.enableGate (cleanGate g0) 0],
    .region "empty" [],
    .region "a0f0x2" (advice 0 1 ++ [.assignFixed ⟨0⟩ 1 7]),
    .region "a2s1x3" (advice 2 3 ++ [.enableGate (cleanGate g1) 1]),
    .region "a0s1x2" (advice 0 2 ++ [.enableGate (cleanGate g1) 0])]

def layout : Chips.Layout.DerivedLayout :=
  Export.layout source fixture.ops fixture.k (Export.v1 source)

#guard layout.regionStarts == [7, 9, 0, 3, 5, 2, 1, 0, 0, 0, 0, 3]
#guard (Export.layout source fixture.ops fixture.k).regionStarts != layout.regionStarts

end LoweringFixtures.V1Placement
