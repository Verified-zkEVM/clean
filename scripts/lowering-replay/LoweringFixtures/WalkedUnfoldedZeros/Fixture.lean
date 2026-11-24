import LoweringFixtures.Common

/-! Zeros Rust's operators do not fold, around queries no closure made: `-Constant(0) * a.rot(5)`,
`a.rot(4) * F::ZERO`, `(Constant(0) * F) * a.rot(3)`, `0 - a.rot(2)` and `(a - a) * b.rot(1)`, sent
as spellings, in a gate, a raw gate and a lookup. Rust's walk visits every one of these atoms, so
each is registered, in walk order. -/
namespace LoweringFixtures.WalkedUnfoldedZeros
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))
def qc : Spelling := .atom (querySelector ⟨0, false⟩)

def bodies : List (String × Spelling) := [
  ("negated zero", .mul (.neg (.const 0)) (adv 0 5)),
  ("scaled by zero", .scale (adv 0 4) 0),
  ("scaled zero", .add (adv 0 0) (.mul (.scale (.const 0) 3) (adv 0 3))),
  ("zero minus", .sub (.const 0) (adv 0 2)),
  ("difference", .mul (.sub (adv 0 0) (adv 0 0)) (adv 1 1))]

def raw : Spelling := .mul qc (.add (.neg (.const 0)) (.scale (adv 1 (-1)) 0))
def input : Spelling := .add (adv 1 0) (.mul (.neg (.const 0)) (adv 1 3))
def table : Spelling := .scale (.atom (.var (.fixed ⟨0⟩ 2))) 0

def configure : ConfigM Unit := do
  let ca ← adviceColumn
  let _ ← adviceColumn
  let _ ← fixedColumn
  let q ← selector false
  gate "zeros" q do
    let _ ← advice ca
    return (bodies.map fun (name, s) => (name, s.toE)).toArray
  gateWithoutSelector "raw zeros" do
    return #[("", raw.toE)]
  lookupAny "zeros" q do
    return #[(input.toE, table.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 8).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]
  spellings := bodies.map (·.2) ++ [raw, input, table]

#guard source.adviceQueries == #[(0, 0), (0, 5), (0, 4), (0, 3), (0, 2), (1, 1), (1, -1), (1, 0), (1, 3)]
#guard source.fixedQueries == #[(0, 2)]

end LoweringFixtures.WalkedUnfoldedZeros
