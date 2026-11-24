import LoweringFixtures.Common

/-! A lookup input multiplied by another complex selector, queried first in the closure;
that selector owns a gate enabled on two rows, the lookup's on one through its handle (the
lookup is not `owned`, its meaning is `RowLookupsHold`). -/
namespace LoweringFixtures.LookupSelectorInput
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  let qs ← selector false
  gate "mark" qs do
    let x ← advice a
    return #[("mark", x * x - x)]
  batchedLookup "sel-input" ql do
    let s ← query (.selector qs)
    let x ← advice a
    return #[(#[s * x], t)]

def source : CS := (configure.run {}).2

def mark : GateSpec := source.gates[0]?.getD ⟨"", ⟨1, false⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .enableGate (cleanGate mark) 0, .enableGate (cleanGate mark) 1,
      .enableGate (lookupHandle lk 0) 0]]

#guard source.validate.isOk && !lk.owned
#guard lk.handles.map (·.selector.index) == [0, 1]

end LoweringFixtures.LookupSelectorInput
