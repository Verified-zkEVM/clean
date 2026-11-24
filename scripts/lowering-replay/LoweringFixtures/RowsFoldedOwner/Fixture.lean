import LoweringFixtures.Common

/-! `(q2 * 0) + q1 * x(-1)`: Rust's tree is `q1 * x(-1)`, Lean's owner is the folded-away `q2`, so the
gate is `rows` with a handle on `q1`; `q2` also owns a `with_selector` gate on `f(-1)`. Beside it a
selector-free `f(1) * (x(-1) - x - p(-1))` enabled nowhere, wrapping at row 0, and an owned
`-(3 * (qs * x(2)))` on a simple selector; a layouter instance copy. -/
namespace LoweringFixtures.RowsFoldedOwner
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let p ← instanceColumn
  let q1 ← selector false
  let q2 ← selector false
  let qs ← selector
  gateWithoutSelector "folded owner" do
    let x ← advice a (-1)
    return #[("", .add (Rust.mul (querySelector q2) (.const 0)) (Rust.mul (querySelector q1) x))]
  gate "on q2" q2 do
    let w ← fixed f (-1)
    let x ← advice a
    return #[("", Rust.sub (Rust.mul w x) w)]
  gateWithoutSelector "wrap" do
    let n ← fixed f 1
    let x ← advice a (-1)
    let y ← advice a
    let i ← query (.instance ⟨p⟩ (-1))
    return #[("", Rust.mul n (Rust.sub (Rust.sub x y) i))]
  gateWithoutSelector "neg scale" do
    let x ← advice a 2
    return #[("", Rust.neg (Rust.scale (Rust.mul (querySelector qs) x) 3))]
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, p⟩

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- Gate 0's handle on `q1`. -/
def handle : Gate F :=
  if h : (spec 0).valid then ((spec 0).rowsHandles h).find? (·.selector.index == 0) |>.getD (cleanGate (spec 0))
  else cleanGate (spec 0)

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "first" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate (spec 3)) 0,
      .assignFixed ⟨0⟩ 0 3, .assignAdvice ⟨0⟩ 1 witness, .enableGate handle 1, .assignFixed ⟨0⟩ 1 1,
      .assignAdvice ⟨0⟩ 2 witness, .enableGate (cleanGate (spec 0)) 2, .enableGate (cleanGate (spec 1)) 2],
    .constrainInstance (cell 0 2 .advice 0) ⟨0⟩ 1,
    .region "second" [.enableGate handle 0, .assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate (spec 1)) 0]]

#guard source.gates.map (·.rows) == #[true, false, true, false]
#guard (spec 0).selector.index == 1
#guard (if h : (spec 0).valid then ((spec 0).rowsHandles h).map (·.selector.index) else []) == [0]
#guard source.fixedQueries == #[(0, -1), (0, 1)]

end LoweringFixtures.RowsFoldedOwner
