import LoweringFixtures.Common

/-! The SHA-256 baseline plus a gate on a new simple selector, enabled in a new last region. -/
namespace LoweringFixtures.ExtraGate
open Halo2 Midnight Midnight.Keygen

def extra : GateSpec :=
  let a : E := .var (.advice ⟨0⟩ 0)
  ⟨"extra", ⟨sha.source.numSelectors, true⟩, #[.advice ⟨0⟩ 0],
    #[("boolean", .add (.mul a a) (.mul (.const (-1)) a))], false, false⟩

def fixture : Export.Replay.Fixture :=
  { sha with
    source := { sha.source with
      numSelectors := sha.source.numSelectors + 1, gates := sha.source.gates.push extra }
    ops := sha.ops ++ [.region "extra" ((List.range 4).map (RegionOperation.enableGate (cleanGate extra)))] }

end LoweringFixtures.ExtraGate
