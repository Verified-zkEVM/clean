import LoweringFixtures.Common

/-! A simple selector only inside factors Rust folds away, their queries from no closure:
`x + 0 * (qs * a.rot(5))` under a simple gate selector, in a `batched_lookup` input and in a trash
body. Rust's `*` allows one simple side, and `0 *` folds the factor before `q *`, the lookup's
simple-selector assertion (circuit.rs:1760) and trash finalization (circuit.rs:1993) see it, so Rust
keys all three. -/
namespace LoweringFixtures.FoldedSimpleFactors
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))
def qs : Spelling := .atom (querySelector ⟨1, true⟩)
def x : Spelling := adv 0 0

def gateBody : Spelling := .add x (.mul (.const 0) (.mul qs (adv 0 5)))
def input : Spelling := .add x (.mul (.const 0) (.mul qs (adv 1 4)))
def trashBody : Spelling := .add x (.mul (.mul qs (adv 0 7)) (.const 0))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← adviceColumn
  let t ← fixedColumn
  let qg ← selector
  let _ ← selector
  let ql ← selector false
  let q3 ← selector false
  gate "simple outer" qg do
    let _ ← advice a
    return #[("", gateBody.toE)]
  batchedLookup "folded simple input" ql do
    let _ ← advice a
    return #[(#[input.toE], t)]
  additiveGate "folded simple trash" q3 do
    let _ ← advice a
    return #[("", trashBody.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" ((List.range 4).flatMap (fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness]) ++
      [.enableGate (cleanGate (source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩)) 0,
       .enableLookup (cleanLookup (source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩)) [⟨2, false⟩] 1,
       .enableGate (cleanGate (source.trashcans[0]?.getD ⟨"", ⟨3, false⟩, #[], #[], false, false⟩)) 2])]
  spellings := [gateBody, input, trashBody]

#guard source.adviceQueries == #[(0, 0)]

end LoweringFixtures.FoldedSimpleFactors
