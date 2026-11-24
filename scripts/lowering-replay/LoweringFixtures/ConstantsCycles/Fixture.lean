import LoweringFixtures.Common

/-! Deferred constants building permutation cycles: one cell constrained twice in its region and
again from later regions, a constant on a cell of the constants column itself, a region of only a
constant (empty shape), equality and instance copies on constrained cells, a gapped `assign_fixed`
on the constants column pushed below the constants, a second constants column that is only
region-written, equality on the constants column enabled before `enableConstant`, and the values 0,
-1 and 2^200. -/
namespace LoweringFixtures.ConstantsCycles
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← fixedColumn
  let g ← fixedColumn
  let inst ← instanceColumn
  let q ← selector
  enableEquality ⟨.fixed, c⟩
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩
  enableConstant c
  enableConstant g
  enableEquality ⟨.advice, b⟩
  gate "id" q do
    let x ← advice a
    let y ← advice b
    return #[("id", Rust.sub x y)]

def source : CS := (configure.run {}).2

def idGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def big : F := ((2 ^ 200 : ℕ) : F)

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "g" [.assignFixed ⟨1⟩ 2 1],
    .region "r1" ([.assignAdvice ⟨0⟩ 0 witness] ++ (assignAdviceFromConstant ⟨0⟩ 1 big).operations 1 ++
      [.constrainConstant (cell 1 1 .advice 0) big, .assignFixed ⟨0⟩ 0 (-1),
       .constrainConstant (cell 1 0 .fixed 0) (-1), .enableGate (cleanGate idGate) 1,
       .assignAdvice ⟨1⟩ 1 witness, .constrainEqual (cell 1 1 .advice 1) (cell 1 1 .advice 0)]),
    .region "only" [.constrainConstant (cell 1 1 .advice 1) 0],
    .constrainInstance (cell 1 1 .advice 0) ⟨0⟩ 0,
    .region "r3" [.assignFixed ⟨0⟩ 3 7, .assignAdvice ⟨0⟩ 0 witness,
      .constrainConstant (cell 3 0 .advice 0) 9, .assignFixed ⟨1⟩ 0 4],
    .region "r4" [.assignAdvice ⟨1⟩ 0 witness, .constrainConstant (cell 4 0 .advice 1) 1,
      .constrainConstant (cell 1 0 .advice 0) 3, .constrainConstant (cell 1 1 .advice 0) big,
      .constrainInstance (cell 4 0 .advice 1) ⟨0⟩ 0]]

def layout : Chips.Layout.DerivedLayout := Export.layout source fixture.ops fixture.k

-- r1 at 0 (c rows 2..4), "only" at 0 (c row 5), r3 at c's next row 6 (its c row 9 = 7, its
-- constant at c row 10), r4 at b's next row 2 (c rows 11..13).
#guard layout.regionStarts == [0, 0, 0, 6, 2]
#guard (layout.fixed[0]!).toList.take 14 ==
  [scalarNat (-1 : F), 0, scalarNat big, scalarNat big, scalarNat (-1 : F), 0, 0, 0, 0, 7, 9, 1, 3, scalarNat big]

end LoweringFixtures.ConstantsCycles
