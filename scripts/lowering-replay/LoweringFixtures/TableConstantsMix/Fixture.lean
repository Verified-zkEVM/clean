import LoweringFixtures.Common

/-! Last writer across a two-column lookup table whose second column is the constants column:
constants before and after its load, a region write under the load, a region write after the
table fill, a trash argument and a simple gate. Simple: constants at c rows 0, 4, 5, the load
overwrites rows 0, 1 and fills from 2, the last constant lands on the fill. V1 places r2, r1, r0
and puts all three constants on c rows 3-5 after synthesis, over the fill. -/
namespace LoweringFixtures.TableConstantsMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let c ← fixedColumn
  let f ← fixedColumn
  let qc ← selector false
  let qs ← selector
  let qa ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩
  enableConstant c
  batchedLookup "lt" qc do
    let x ← advice a
    let y ← advice b
    return #[(#[x], t), (#[y], c)]
  gate "g" qs do
    let x ← advice a
    let y ← fixed f
    return #[("g", Rust.sub x y)]
  additiveGate "tr" qa do
    let x ← advice b
    return #[("b", x)]

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def g : GateSpec := source.gates[0]?.getD empty
def tr : GateSpec := source.trashcans[0]?.getD empty
def lt : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignFixed ⟨2⟩ 1 4,
      .enableGate (cleanGate g) 1, .constrainConstant (cell 0 0 .advice 0) 3],
    .loadTable ⟨⟨0⟩⟩ [1, 2],
    .region "r1" [.assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨1⟩ 2 witness,
      .assignFixed ⟨1⟩ 1 6, .enableGate (cleanGate tr) 0, .enableLookup (cleanLookup lt) [⟨0, false⟩] 2,
      .constrainConstant (cell 1 1 .advice 1) 5],
    .loadTable ⟨⟨1⟩⟩ [6, 7],
    .region "r2" [.assignFixed ⟨0⟩ 3 9, .assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 2 0 .advice 0) 8]]

#guard source.validate.isOk && lt.owned
#guard (Export.layout source fixture.ops fixture.k).regionStarts = [0, 1, 2]

end LoweringFixtures.TableConstantsMix
