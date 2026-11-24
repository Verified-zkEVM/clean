import LoweringFixtures.Common

/-! Folded-away factors under nodes Rust does not fold, from no closure: `-(0 * a.rot(7))` is
`Negated(Constant(0))`, `(0 * a.rot(8)) * F::from(3)` is `Scaled`, `a.rot(9) + 0 * a.rot(10)` is
`a.rot(9)`, `a.rot(5) * F::ZERO + a.rot(6) * (0 * b.rot(2))` keeps `Scaled(a.rot(5), 0)`, and
`(b.rot(4) + 0) * -(b.rot(5) * 0)` keeps `Product(b.rot(4), Negated(Constant(0)))`; a lookup input
`x + -(0 * b.rot(6))` and table `(a.rot(3) * 0) * F::from(2)`; `a.rot(11) - 0 * a.rot(12)` is
`a.rot(11)`, whose `Rust.sub` drops `a.rot(12)` from `E`. Rust registers only the atoms its built
trees keep, in walk order; `pruneFolded` must erase exactly the others. -/
namespace LoweringFixtures.PrunedContexts
open Halo2 Midnight Midnight.Keygen Export.Replay

def adv (c : Nat) (r : Int) : Spelling := .atom (.var (.advice ⟨c⟩ r))

def bodies : List (String × Spelling) := [
  ("negated", .neg (.mul (.const 0) (adv 0 7))),
  ("scaled", .scale (.mul (.const 0) (adv 0 8)) 3),
  ("plus zero", .add (adv 0 9) (.mul (.const 0) (adv 0 10))),
  ("scaled by zero", .add (.scale (adv 0 5) 0) (.mul (adv 0 6) (.mul (.const 0) (adv 1 2)))),
  ("negated factor", .mul (.add (adv 1 4) (.const 0)) (.neg (.mul (adv 1 5) (.const 0)))),
  ("minus zero", .sub (adv 0 11) (.mul (.const 0) (adv 0 12)))]

def input : Spelling := .add (.atom (.var (.advice ⟨0⟩ 0))) (.neg (.mul (.const 0) (adv 1 6)))
def table : Spelling := .scale (.mul (adv 0 3) (.const 0)) 2

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← adviceColumn
  let q ← selector false
  gate "contexts" q do
    let _ ← advice a
    return (bodies.map fun (name, s) => (name, s.toE)).toArray
  lookupAny "contexts" q do
    let _ ← advice a
    return #[(input.toE, table.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 12).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]
  spellings := bodies.map (·.2) ++ [input, table]

#guard source.adviceQueries == #[(0, 0), (0, 9), (0, 5), (1, 4), (0, 11)]
#guard source.fixedQueries == #[]

end LoweringFixtures.PrunedContexts
