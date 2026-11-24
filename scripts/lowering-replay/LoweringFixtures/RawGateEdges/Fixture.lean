import LoweringFixtures.Common

/-! `without_selector` edge cases: a simple selector in products only (Rust's `+` and `-`
panic on simple selectors), on the right of a nested product, under `Mul<F>` and `Neg`, sharing
its selector with a `with_selector` gate; a complex selector in a difference of two selected terms,
shared with a lookup, at a negative rotation enabled at region row 0. -/
namespace LoweringFixtures.RawGateEdges
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  let qc ← selector false
  gateWithoutSelector "simple" do
    let x ← advice a
    let y ← advice b
    let q := querySelector qs
    return #[("left", Rust.mul q x), ("right", Rust.mul x (Rust.mul q y)),
      ("scaled", Rust.scale (Rust.mul q x) 3), ("negated", Rust.neg (Rust.mul q y))]
  gate "plain" qs do
    let x ← advice a
    let y ← advice b
    return #[("plain", Rust.sub x y)]
  batchedLookup "range" qc do
    let x ← advice a
    return #[(#[x], t)]
  gateWithoutSelector "complex" do
    let prev ← advice b (-1)
    let x ← advice a
    let q := querySelector qc
    return #[("difference", Rust.sub (Rust.mul q prev) (Rust.mul (Rust.mul q x) x))]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def range : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2, 3],
    .region "complex" [.enableGate (cleanGate (spec 2)) 0, .assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup range) [⟨1, false⟩] 0],
    .region "simple" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableGate (cleanGate (spec 1)) 0, .enableGate (cleanGate (spec 0)) 0,
      .assignAdvice ⟨1⟩ 1 witness, .enableGate (cleanGate (spec 2)) 1,
      .enableLookup (cleanLookup range) [⟨1, false⟩] 1, .assignAdvice ⟨0⟩ 1 witness]]

end LoweringFixtures.RawGateEdges
