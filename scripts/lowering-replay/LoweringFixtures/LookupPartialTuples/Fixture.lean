import LoweringFixtures.Common

/-! An owned two-tuple batch whose stream states tuple 0 at row 0 and tuple 1 at row 1 only. Rust's
`q` enables both tuples on both rows, as `Canonical.ops` does. A `None` lookup and a simple gate sit
beside it. -/
namespace LoweringFixtures.LookupPartialTuples
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  let qs ← selector
  gate "bool" qs do
    let x ← advice a
    return #[("", Rust.sub (Rust.mul x x) x)]
  batchedLookup "owned" q do
    let x ← advice a
    let y ← advice a 1
    return #[(#[x, y], t)]
  batchedLookup "none" none do
    let x ← advice a (-1)
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def bool : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
      .enableLookup (cleanLookup (lk 0) 0) [⟨0, false⟩] 0, .enableGate (cleanGate bool) 0,
      .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] 1]]

#guard source.validate.isOk && (lk 0).owned && !(lk 1).owned

end LoweringFixtures.LookupPartialTuples
