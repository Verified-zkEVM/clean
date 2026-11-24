import LoweringFixtures.Common

/-! Copies, a constant and a layouter instance copy naming regions not yet synthesized. V1 places
every region before its assignment pass (v1.rs:79-81), so it keys them; Simple's `regions` does not
hold them yet and panics (single_pass.rs:231/299/469). Region 2 is placed first (largest advice
area). -/
namespace LoweringFixtures.V1ForwardCopies
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a0 ← adviceColumn
  let a1 ← adviceColumn
  let f ← fixedColumn
  let i ← instanceColumn
  enableEquality ⟨.advice, a0⟩
  enableEquality ⟨.advice, a1⟩
  enableEquality ⟨.instance, i⟩
  enableConstant f

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 0 0 .advice 0) (cell 2 1 .advice 1),
      .constrainConstant (cell 1 0 .advice 0) 3],
    .constrainInstance (cell 2 0 .advice 1) ⟨0⟩ 0,
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainInstance (cell 1 0 .advice 0) ⟨0⟩ 1,
      .constrainEqual (cell 1 0 .advice 0) (cell 2 0 .advice 1)],
    .region "r2" [.assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨0⟩ 0 witness,
      .assignAdvice ⟨0⟩ 1 witness]]

def layout : Chips.Layout.DerivedLayout :=
  Export.layout source fixture.ops fixture.k (Export.v1 source)

#guard layout.regionStarts == [3, 2, 0]

end LoweringFixtures.V1ForwardCopies
