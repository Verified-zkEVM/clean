import LoweringFixtures.Common
import LoweringFixtures.CopiesWrap.Fixture

/-! CopiesWrap with each wrapped endpoint written as the cell Rust resolves it to. -/
namespace LoweringFixtures.CopiesWrapNormal
open Halo2 Midnight Midnight.Keygen

def fixture : Export.Replay.Fixture where
  source := CopiesWrap.source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 1 0 .advice 0) (cell 0 1 .advice 0),
      .constrainConstant (cell 0 0 .advice 0) 9],
    .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 0]

end LoweringFixtures.CopiesWrapNormal
