import LoweringFixtures.Common

/-! `x + 0 * (qs + a.rot(5))` with simple `qs` and `a.rot(5)` from no closure, spelled: Rust's `+`
panics on `qs + a.rot(5)` before `0 *` folds it (circuit.rs:1198). `pruneFolded` keeps `qs` beside
the erased query, so `validate` still sees the panic. -/
namespace LoweringFixtures.FoldedSimpleSum
open Halo2 Midnight Midnight.Keygen Export.Replay

def body : Spelling :=
  .add (.atom (.var (.advice ⟨0⟩ 0))) (.mul (.const 0) (.add (.atom (querySelector ⟨1, true⟩)) (.atom (.var (.advice ⟨0⟩ 5)))))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  let _ ← selector
  gate "folded simple sum" q do
    let _ ← advice a
    return #[("", body.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]
  spellings := [body]

#guard source.adviceQueries == #[(0, 0)]
#guard !source.validate.isOk

end LoweringFixtures.FoldedSimpleSum
