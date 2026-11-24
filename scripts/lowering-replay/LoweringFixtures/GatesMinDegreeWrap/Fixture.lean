import LoweringFixtures.Common

/-! `set_minimum_degree(2^32 + 3)`: Rust's `EvaluationDomain::new(cs.degree() as u32, k)`
(keygen.rs:44, poly/domain.rs:54) truncates the degree to 3, so keygen succeeds with
`extended_k = k + 1` and the pinned `minimum_degree: Some(4294967299)`. Lean's `extendedK` truncates
as Rust does and keeps the pinned minimum degree whole. -/
namespace LoweringFixtures.GatesMinDegreeWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q ← selector
  gate "plain" q do
    let x ← advice a
    let y ← advice b
    return #[("", Rust.sub x y)]
  setMinimumDegree (2 ^ 32 + 3)

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
    .enableGate (cleanGate (source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩)) 0]]

#guard source.validate.isOk && source.degree == 2 ^ 32 + 3

end LoweringFixtures.GatesMinDegreeWrap
