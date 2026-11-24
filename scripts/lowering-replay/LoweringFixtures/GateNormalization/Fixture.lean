import LoweringFixtures.Common

/-! Gate bodies `0 + x`, `1 * x` and a constant, and an additive body `0 + x`. A Rust chip builds
them with operators, which fold, and so does Lean's pinned serializer. -/
namespace LoweringFixtures.GateNormalization
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  let _ ← selector false
  gate "raw" q do
    let x ← advice a
    return #[("zero plus", .add (.const 0) x), ("one times", .mul (.const 1) x), ("constant", .const 5)]

def raw : GateSpec := ((configure.run {}).2).gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- The trash argument `additiveGate` records for `0 + x` on the complex selector, written out. -/
def additive : GateSpec :=
  ⟨"additive", ⟨1, false⟩, #[.advice ⟨0⟩ 0], #[("zero plus", .add (.const 0) (.var (.advice ⟨0⟩ 0)))], false, false⟩

def fixture : Export.Replay.Fixture where
  source := { (configure.run {}).2 with trashcans := #[additive] }
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate raw) 0,
    .enableGate (cleanGate additive) 0]]

end LoweringFixtures.GateNormalization
