import LoweringFixtures.Common

/-! A simple selector that folds out of a lookup input: `(qs * 0) + x` is `x` before Rust's
`contains_simple_selector` assertion (circuit.rs:1760), so Rust keys it. -/
namespace LoweringFixtures.LookupFoldedSimple
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  let ql ← selector false
  gate "s" qs do
    let x ← advice a
    return #[("", Rust.mul x x)]
  batchedLookup "folded" ql do
    let x ← advice a
    return #[(#[.add (Rust.mul (querySelector qs) (.const 0)) x], t)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩
def s : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (lookupHandle lk 1) 0, .enableGate (cleanGate s) 0]]

#guard source.validate.isOk && !lk.owned

end LoweringFixtures.LookupFoldedSimple
