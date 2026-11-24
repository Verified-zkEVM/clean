import LoweringFixtures.Common

/-! Selector-carrying factors Rust folds away, their queries from no closure: `0 * (q2 * a.rot(5))`
in a gate, `(q2 * b.rot(3)) * 0` in a raw gate, `0 * (q2 * -b.rot(7) * F::from(3))` in a lookup
input and `0 * (q2 * a.rot(6))` in a trash body (an index-free `query_cell`). `pruneFolded` erases
the queries and keeps `q2`, whose uses (raw gate owners, `rows`) are Rust's tree's. -/
namespace LoweringFixtures.FoldedSelectorContexts
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))
def sel (q : Selector) : Spelling := .atom (querySelector q)

def x : Spelling := .atom (.var (.advice ⟨0⟩ 0))
def q2 : Spelling := sel ⟨1, false⟩

def gateBody : Spelling := .add x (.mul (.const 0) (.mul q2 (adv 0 5)))
def rawBody : Spelling :=
  .add (.mul (sel ⟨0, false⟩) (.atom (.var (.advice ⟨1⟩ 0)))) (.mul (.mul q2 (adv 1 3)) (.const 0))
def input : Spelling := .add x (.mul (.const 0) (.scale (.mul q2 (.neg (adv 1 7))) 3))
def trashBody : Spelling := .add x (.mul (.const 0) (.mul q2 (adv 0 6)))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let q ← selector false
  let _ ← selector false
  let q3 ← selector false
  gate "gate" q do
    let _ ← advice a
    return #[("", gateBody.toE)]
  gateWithoutSelector "raw" do
    let _ ← advice b
    return #[("", rawBody.toE)]
  lookupAny "lookup" q do
    let _ ← advice a
    let t ← fixed f
    return #[(input.toE, t)]
  additiveGate "trash" q3 do
    let _ ← advice a
    return #[("", trashBody.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 4).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]
  spellings := [gateBody, rawBody, input, trashBody]

#guard source.adviceQueries == #[(0, 0), (1, 0)]
#guard source.gates.any fun g => g.raw && g.rows

end LoweringFixtures.FoldedSelectorContexts
