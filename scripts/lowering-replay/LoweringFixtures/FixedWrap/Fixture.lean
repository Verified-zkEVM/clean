import LoweringFixtures.Common

/-! The fixed-write form of Rust's `usize` wrap (release build, no overflow checks): r1 starts at 2
and writes `f` at offset `2^64 - 1`, which keygen's `assign_fixed` receives as row 1; the shape's
`offset + 1` wraps to 0, so r1 keeps row count 1 and r2 writes `f` at row 3. Rust keys it under
both planners, and Lean lowers in `usize` too (`Usize`). -/
namespace LoweringFixtures.FixedWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let q ← selector
  gate "g" q do
    let x ← advice a
    let y ← fixed f
    return #[("g", Rust.sub x y)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ (2 ^ 64 - 1) 7],
    .region "r2" [.assignFixed ⟨0⟩ 0 5]]

end LoweringFixtures.FixedWrap
