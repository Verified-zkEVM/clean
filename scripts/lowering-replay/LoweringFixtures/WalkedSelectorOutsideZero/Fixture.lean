import LoweringFixtures.Common

/-! A selector outside a factor Rust folds away, `x + q2 * (0 * a.rot(5))`, in a gate, a raw gate
and a lookup input, the queries from no closure. Rust folds `0 * a.rot(5)`
to `Constant(0)`, then `q2 * 0` too, so `q2` and the query vanish and Rust keys it.
`pruneFolded` erases the selector-free inner factor and keeps `q2`, so Lean keys it as well,
unlike `0 * (q2 * a.rot(5))` (WalkedFoldedSelector). -/
namespace LoweringFixtures.WalkedSelectorOutsideZero
open Halo2 Midnight Midnight.Keygen

def adv (c : Nat) (r : Int) : E := .var (.advice ⟨c⟩ r)

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let q ← selector false
  let q2 ← selector false
  gate "outside" q do
    let x ← advice a
    return #[("", .add x (Rust.mul (querySelector q2) (Rust.mul (.const 0) (adv a 5))))]
  gateWithoutSelector "raw outside" do
    let y ← advice b
    return #[("", .add (Rust.mul (querySelector q) y)
      (Rust.mul (Rust.mul (.const 0) (adv b 3)) (querySelector q2)))]
  lookupAny "outside" q do
    let x ← advice a
    let t ← fixed f
    return #[(.add x (Rust.mul (querySelector q2) (Rust.mul (.const 0) (adv b 7))), t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 4).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]

#guard source.adviceQueries == #[(0, 0), (1, 0)]
#guard source.fixedQueries == #[(0, 0)]

end LoweringFixtures.WalkedSelectorOutsideZero
