import LoweringFixtures.Common

/-! Rust's folding where it changes degrees and lookups: a gate constraint `0 * x⁵`, degree 6 as
written and `Constant(0)` in Rust (so the lookup sets the degree), lookup inputs `0 + x` and
`1 * y`, and an additive body `x * 1`. -/
namespace LoweringFixtures.Normalization
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  let _ ← selector false
  gate "zero" q do
    let x ← advice a
    let y ← advice b
    return #[("vanishes", .mul (.const 0) (x * x * x * x * x)), ("linear", x - y)]
  batchedLookup "fold" ql do
    let x ← advice a
    let y ← advice b
    return #[(#[.add (.const 0) x, .mul (.const 1) y], t)]

def raw : GateSpec := ((configure.run {}).2).gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fold : BatchedLookup := ((configure.run {}).2).lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def additive : GateSpec :=
  ⟨"additive", ⟨2, false⟩, #[.advice ⟨0⟩ 0], #[("times one", Rust.mul (.var (.advice ⟨0⟩ 0)) (.const 1))], false, false⟩

def fixture : Export.Replay.Fixture where
  source := { (configure.run {}).2 with trashcans := #[additive] }
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .enableGate (cleanGate raw) 0,
      .enableLookup (cleanLookup fold 0) [⟨1, false⟩] 0, .enableLookup (cleanLookup fold 1) [⟨1, false⟩] 0,
      .enableGate (cleanGate additive) 0]]

#guard raw.constraints.toList.map (fun (_, p) => raw.polyDegree p) == [0, 2]

end LoweringFixtures.Normalization
