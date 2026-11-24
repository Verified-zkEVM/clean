import LoweringFixtures.Common

/-! A selector-free trash argument on complex `q`, enabled at row 0 through its Clean gate and at
row 1 only through the empty `gates` entry `additiveGate` registers (Rust's trash closure leaves a
gate with no polynomials). Both are `q.enable` in Rust, which enforces the trash identity on both
rows; `Canonical.ops` enables the trash gate at row 1. -/
namespace LoweringFixtures.AdditivePlaceholderOnly
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  additiveGate "bool" q do
    let x ← advice a
    return #[("bool", Rust.mul x x - x)]

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def placeholder : GateSpec := source.gates[0]?.getD empty
def trash : GateSpec := source.trashcans[0]?.getD empty

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .enableGate (cleanGate trash) 0, .enableGate (cleanGate placeholder) 1]]

#guard source.validate.isOk && placeholder.constraints.isEmpty && placeholder.selector.index == 0
#guard (source.trashcans.map (·.rows)) == #[false]

end LoweringFixtures.AdditivePlaceholderOnly
