import LoweringFixtures.Common

/-! Selectors used only inside factors Rust folds away, and enabled: a complex `q2` only in
`0 * (q2 * a.rot(5))` in a gate and a lookup input, a raw gate `b + 0 * (q4 * a.rot(6))` whose only
selector is folded (Rust's gate is `b`, on every row), a simple `qs` only in `0 * (qs * b.rot(2))`.
Rust still gives every selector a fixed column (circuit.rs:1951), so enabling them changes the key
only through their columns. -/
namespace LoweringFixtures.FoldedOnlySelectors
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))
def sel (i : Nat) (simple : Bool := false) : Spelling := .atom (querySelector ⟨i, simple⟩)
def x : Spelling := adv 0 0

def gateBody : Spelling := .add x (.mul (.const 0) (.mul (sel 1) (adv 0 5)))
def rawBody : Spelling := .add (adv 1 0) (.mul (.const 0) (.mul (sel 2) (adv 0 6)))
def simpleBody : Spelling := .add x (.mul (.const 0) (.mul (sel 3 true) (adv 1 2)))
def input : Spelling := .add (adv 1 0) (.mul (.const 0) (.mul (sel 1) (adv 0 3)))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let q ← selector false
  let _ ← selector false
  let _ ← selector false
  let _ ← selector
  gate "folded q2" q do
    let _ ← advice a
    return #[("", gateBody.toE)]
  gateWithoutSelector "raw folded q4" do
    let _ ← advice b
    return #[("", rawBody.toE)]
  gate "folded qs" q do
    let _ ← advice a
    return #[("", simpleBody.toE)]
  lookupAny "folded q2 input" q do
    let _ ← advice b
    let t ← fixed f
    return #[(input.toE, t)]

def source : CS := (configure.run {}).2

def gateAt (i : Nat) : Gate F := cleanGate (source.gates[i]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩)

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 4).flatMap (fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness]) ++
    [.enableGate (gateAt 0) 0, .enableGate (gateAt 1) 1, .enableGate (gateAt 2) 2])]
  spellings := [gateBody, rawBody, simpleBody, input]

#guard source.adviceQueries == #[(0, 0), (1, 0)]

end LoweringFixtures.FoldedOnlySelectors
