import LoweringFixtures.Common

/-! `assign_advice_from_instance` into an advice cell past the usable rows that nothing else
assigns (k = 4: 9 usable). The assignment is keyed, the copy fails. -/
namespace LoweringFixtures.InstanceCopyPastUsable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainInstance (cell 0 12 .advice 0) ⟨0⟩ 0]]

end LoweringFixtures.InstanceCopyPastUsable
