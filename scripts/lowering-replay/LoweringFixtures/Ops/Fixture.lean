import LoweringFixtures.Common

/-! Every operation kind the checked fragment admits, small: a table load, a gate with a
rotation and a fixed coefficient, a batched lookup enabled in two regions, an in-region
instance copy, cross-region and fixed-cell equalities and a layouter-level instance copy. -/
namespace LoweringFixtures.Ops
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let inst ← instanceColumn
  let q ← selector
  let ql ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.fixed, f⟩
  gate "mul" q do
    let x ← advice a
    let y ← advice b
    let z ← advice a 1
    let c ← fixed f
    return #[("mul", c * x * y - z)]
  batchedLookup "range" ql do
    let x ← advice b
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def mulGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def range : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def ops : Operations F := [
  .loadTable ⟨⟨1⟩⟩ [0, 1, 2, 3],
  .region "mul" [
    .assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignFixed ⟨0⟩ 0 3,
    .assignAdvice ⟨0⟩ 1 witness, .enableGate (cleanGate mulGate) 0,
    .enableLookup (cleanLookup range) [⟨1, false⟩] 0,
    .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 0],
  .region "copy" [
    .assignAdvice ⟨1⟩ 0 witness,
    .constrainEqual (cell 1 0 .advice 1) (cell 0 1 .advice 0),
    .enableLookup (cleanLookup range) [⟨1, false⟩] 0,
    .constrainEqual (cell 1 0 .advice 1) (cell 0 0 .fixed 0)],
  .constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 1]

def fixture : Export.Replay.Fixture := { source, ops, k := 5 }

end LoweringFixtures.Ops
