import LoweringFixtures.Common

/-! Two instance columns queried at rotations -1 and 2, equality enables interleaved with the
gate, an advice rotation -2, in-region instance copies to both instance columns, a region of
one cell at offset 4 and a later region placed inside it on another column, copy chains and
layouter instance copies. Starts [0, 3, 3]. -/
namespace LoweringFixtures.InstanceRotations
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let i0 ← instanceColumn
  let i1 ← instanceColumn
  let q ← selector
  enableEquality ⟨.instance, i1⟩
  gate "rot" q do
    let x ← advice a (-2)
    let y ← advice b
    let p ← query (.instance ⟨i1⟩ (-1))
    let r ← query (.instance ⟨i0⟩ 2)
    return #[("rot", x * p - y * r), ("lin", x - y + p)]
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.instance, i0⟩
  enableEquality ⟨.advice, a⟩

def source : CS := (configure.run {}).2

def rot : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .assignAdvice ⟨1⟩ 2 witness, .enableGate (cleanGate rot) 2,
      .constrainInstance (cell 0 2 .advice 1) ⟨1⟩ 4],
    .region "r1" [.assignAdvice ⟨1⟩ 4 witness,
      .constrainEqual (cell 1 4 .advice 1) (cell 0 0 .advice 0),
      .constrainInstance (cell 1 4 .advice 1) ⟨0⟩ 0],
    .constrainInstance (cell 0 1 .advice 0) ⟨1⟩ 0,
    .region "r2" [.assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 2 0 .advice 0) (cell 1 4 .advice 1),
      .constrainEqual (cell 0 1 .advice 0) (cell 2 0 .advice 0)],
    .constrainInstance (cell 2 0 .advice 0) ⟨0⟩ 3]

end LoweringFixtures.InstanceRotations
