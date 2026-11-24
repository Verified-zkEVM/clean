import LoweringFixtures.Common

/-! `qs * F::ZERO` is `Scaled(qs, 0)`, not folded, so `x + qs * F::ZERO` in a lookup input
panics in Rust's `+` (circuit.rs:1197); `validate` rejects it. -/
namespace LoweringFixtures.LookupScaledSimple
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  let q ← selector false
  gate "s" qs do
    let x ← advice a
    return #[("", Rust.mul x x)]
  batchedLookup "scaled" q do
    let x ← advice a
    return #[(#[.add x (Rust.scale (querySelector qs) 0)], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1], .region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard !source.validate.isOk

end LoweringFixtures.LookupScaledSimple
