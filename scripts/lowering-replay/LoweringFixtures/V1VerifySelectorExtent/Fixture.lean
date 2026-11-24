import LoweringFixtures.Common

/-! V1's `first_unassigned_row` from a selector column: three selector-only regions stack on `q` to
row 9, and no region touches the constants column f0, so it has exactly nine positions for the nine
constants. Constants name a later region, a fixed cell (f1 has equality) and the same cell twice,
and an empty-shape region queues three of them. Simple rejects the forward constant. -/
namespace LoweringFixtures.V1VerifySelectorExtent
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f0 ← fixedColumn
  let f1 ← fixedColumn
  let q ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, f1⟩
  enableConstant f0
  gate "g" q do
    let x ← advice a
    return #[("g", x)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩

def selectors : RegionOperations F := [0, 1, 2].map (.enableGate (cleanGate g) ·)

def ops : Operations F := [
  .region "sel0" (selectors ++ [.constrainConstant (cell 3 0 .advice 0) 1]),
  .region "sel1" (selectors ++ [.constrainConstant (cell 3 1 .advice 0) 2]),
  .region "sel2" selectors,
  .region "adv" ((List.range 4).map (.assignAdvice ⟨0⟩ · witness) ++
    [.constrainConstant (cell 3 2 .advice 0) 3, .constrainConstant (cell 3 3 .advice 0) 4,
     .constrainConstant (cell 3 0 .advice 0) 5]),
  .region "fx" [.assignFixed ⟨1⟩ 0 7, .constrainConstant (cell 4 0 .fixed 1) 7],
  .region "empty" [.constrainConstant (cell 3 1 .advice 0) 8,
    .constrainEqual (cell 3 0 .advice 0) (cell 4 0 .fixed 1),
    .constrainConstant (cell 3 2 .advice 0) 9, .constrainConstant (cell 3 3 .advice 0) 10]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := ops

#guard Chips.Layout.v1Positions [0] (Chips.Canonical.rustOps source ops) == (List.range 9).map (0, ·)

end LoweringFixtures.V1VerifySelectorExtent
