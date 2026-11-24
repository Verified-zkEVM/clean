import LoweringFixtures.Common

/-! Selector sharing with every owner enabled: two gates on one simple selector, a gate, an
additive gate and a two-deep lookup on one complex selector, unused simple and complex
selectors, an enabled constants column with no constants, a lookup table written by region
fixed cells and never loaded, and a loaded column no lookup reads but a gate queries. -/
namespace LoweringFixtures.MixedSelectors
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let f ← fixedColumn
  let u ← fixedColumn
  let _ ← selector
  let qg ← selector
  let qc ← selector false
  let _ ← selector false
  enableEquality ⟨.fixed, f⟩
  gate "g1" qg do
    let x ← advice a
    let y ← advice b (-1)
    return #[("g1", x * y - x)]
  gate "g2" qg do
    let y ← advice b
    let k ← fixed u
    return #[("g2", y - k), ("g2b", y * y)]
  batchedLookup "tab" qc do
    let x ← advice a
    let y ← advice b 1
    return #[(#[x, y], t)]
  gate "g3" qc do
    let x ← advice a
    return #[("g3", x * x * x - x)]
  enableEquality ⟨.advice, b⟩

def trash : GateSpec :=
  let a : E := .var (.advice ⟨0⟩ 0)
  ⟨"trash", ⟨2, false⟩, #[.advice ⟨0⟩ 0], #[("boolean", .add (.mul a a) (.mul (.const (-1)) a))], false, false⟩

def source : CS :=
  let s := (configure.run {}).2
  { s with constantColumns := #[1], trashcans := #[trash] }

def g1 : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def g2 : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def g3 : GateSpec := source.gates[2]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def tab : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "table" [.assignFixed ⟨0⟩ 0 3, .assignFixed ⟨0⟩ 1 5, .assignFixed ⟨0⟩ 2 0],
    .loadTable ⟨⟨2⟩⟩ [4, 0, 6],
    .region "use" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨0⟩ 1 witness,
      .enableGate (cleanGate g1) 1, .enableGate (cleanGate g2) 1,
      .enableLookup (cleanLookup tab 0) [⟨2, false⟩] 0, .enableLookup (cleanLookup tab 1) [⟨2, false⟩] 0,
      .enableGate (cleanGate g3) 0, .enableGate (cleanGate trash) 0],
    .region "eq" [.assignFixed ⟨1⟩ 0 9, .assignAdvice ⟨1⟩ 2 witness,
      .constrainEqual (cell 2 2 .advice 1) (cell 1 1 .advice 1),
      .constrainEqual (cell 2 0 .fixed 1) (cell 2 2 .advice 1)]]

end LoweringFixtures.MixedSelectors
