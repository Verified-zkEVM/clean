import LoweringFixtures.Common

/-! Instance copies and table loads interleaved with regions: two tables of different lengths loaded
before and between regions, an in-region instance copy, layouter copies before and after a later
region, two cells copied to the same instance row, one cell copied in-region and again by the
layouter, an equality across regions, and a two-table two-parallel lookup whose closure queries `b`
before `a`. -/
namespace LoweringFixtures.InstanceTableMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let inst ← instanceColumn
  let q ← selector
  let ql ← selector false
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.advice, a⟩
  gate "mul" q do
    let x ← advice a
    let y ← advice b
    let z ← advice a 1
    return #[("mul", Rust.sub (Rust.mul x y) z)]
  batchedLookup "two" ql do
    let y ← advice b
    let x ← advice a
    return #[(#[x, y], t0), (#[y, Rust.scale x 3], t1)]

def source : CS := (configure.run {}).2

def mulGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lookup : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [
    .loadTable ⟨⟨0⟩⟩ [0, 1, 2, 3],
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .enableGate (cleanGate mulGate) 0,
      .constrainInstance (cell 0 0 .advice 1) ⟨0⟩ 0,
      .enableLookup (cleanLookup lookup 1) [⟨1, false⟩] 0,
      .enableLookup (cleanLookup lookup 0) [⟨1, false⟩] 0],
    .loadTable ⟨⟨1⟩⟩ [0, 1, 2, 3, 4, 5],
    .constrainInstance (cell 0 1 .advice 0) ⟨0⟩ 1,
    .region "r1" [.assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 1 0 .advice 1) (cell 0 1 .advice 0),
      .constrainInstance (cell 1 0 .advice 0) ⟨0⟩ 1],
    .constrainInstance (cell 0 0 .advice 1) ⟨0⟩ 2,
    .constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 3]

end LoweringFixtures.InstanceTableMix
