import LoweringFixtures.Common

/-! Factors that reach `Constant(0)` only through Rust's own folding, next to near misses that do
not, around queries no closure made: `(0 * a.rot(9)) * (q2 * b.rot(5))`, `(1 * 0) * a.rot(8)` and
`(0 + 0 * a.rot(13)) * b.rot(14)` fold away; `-(0 * a.rot(11)) * b.rot(12)` (`Negated` does not
fold) and `(q2 * a.rot(15)) * F::ZERO` (`Scaled` does not fold) are walked, so `b.rot(12)` and
`a.rot(15)` are registered. In a gate, a raw gate and a lookup. -/
namespace LoweringFixtures.FoldedZeroChains
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))
def q2 : Spelling := .atom (querySelector ⟨1, false⟩)
def qc : Spelling := .atom (querySelector ⟨0, false⟩)
def x : Spelling := adv 0 0

def bodies : List (String × Spelling) := [
  ("chain", .add x (.mul (.mul (.const 0) (adv 0 9)) (.mul q2 (adv 1 5)))),
  ("one times zero", .add x (.mul (.mul (.const 1) (.const 0)) (adv 0 8))),
  ("negated zero", .add x (.mul (.neg (.mul (.const 0) (adv 0 11))) (adv 1 12))),
  ("zero sum", .add x (.mul (.add (.const 0) (.mul (.const 0) (adv 0 13))) (adv 1 14))),
  ("scaled selector", .add x (.scale (.mul q2 (adv 0 15)) 0))]

def raw : Spelling :=
  .mul qc (.add (adv 1 0) (.mul (.mul (.const 0) (adv 0 18)) (.mul q2 (adv 1 19))))
def input : Spelling := .add x (.mul (.add (.const 0) (.mul (.const 0) (adv 0 20))) (adv 1 21))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let q ← selector false
  let _ ← selector false
  gate "chains" q do
    let _ ← advice a
    return (bodies.map fun (name, s) => (name, s.toE)).toArray
  gateWithoutSelector "raw chain" do
    let _ ← advice b
    return #[("", raw.toE)]
  lookupAny "chain" q do
    let _ ← advice a
    let t ← fixed f
    return #[(input.toE, t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.region "r" ((List.range 8).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]
  spellings := bodies.map (·.2) ++ [raw, input]

#guard !source.adviceQueries.contains (0, 9) && !source.adviceQueries.contains (1, 5) &&
  !source.adviceQueries.contains (0, 8) && !source.adviceQueries.contains (0, 13) &&
  !source.adviceQueries.contains (1, 14) && !source.adviceQueries.contains (0, 11)
#guard source.adviceQueries.contains (1, 12) && source.adviceQueries.contains (0, 15)

end LoweringFixtures.FoldedZeroChains
