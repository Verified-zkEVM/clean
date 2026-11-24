import LoweringFixtures.Common

/-! The copy form of Rust's `usize` wrap (release build, no overflow checks): r1 starts at 2, and an
equality, a constant and a layouter instance copy name its cells at offsets `2^64 - 1` and
`2^64 - 2`, which `regions[1] + row_offset` resolves to rows 1 and 0 (single_pass.rs:231, 299, 469;
v1.rs:136, 336, 481). Copy endpoints do not enter the shape, so placement is unchanged and Rust keys
the stream under both planners, with the key of CopiesWrapNormal. Lean lowers in
`usize` too (`Usize`). -/
namespace LoweringFixtures.CopiesWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  let i ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, i⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 1 0 .advice 0) (cell 1 (2 ^ 64 - 1) .advice 0),
      .constrainConstant (cell 1 (2 ^ 64 - 2) .advice 0) 9],
    .constrainInstance (cell 1 (2 ^ 64 - 2) .advice 0) ⟨0⟩ 0]

end LoweringFixtures.CopiesWrap
