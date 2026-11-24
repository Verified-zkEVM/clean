import LoweringFixtures.Common

/-! The SHA-256 baseline plus an additive gate (`Constraints::with_additive_selector`) on a new
complex selector, built by `additiveGate` and enabled in a new last region. -/
namespace LoweringFixtures.Trashcan
open Halo2 Midnight Midnight.Keygen

def addTrash : ConfigM Unit := do
  let q ← selector false
  additiveGate "trash" q do
    let a ← advice 0
    return #[("boolean", a * a - a)]

def source : CS := (addTrash.run sha.source).2

def trash : GateSpec := source.trashcans[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture :=
  { sha with
    source := source
    ops := sha.ops ++ [.region "trash" ((List.range 4).map (RegionOperation.enableGate (cleanGate trash)))] }

#guard source.adviceQueries == sha.source.adviceQueries && source.gates.size == sha.source.gates.size + 1

end LoweringFixtures.Trashcan
