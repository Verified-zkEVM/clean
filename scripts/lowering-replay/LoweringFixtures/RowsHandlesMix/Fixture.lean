import LoweringFixtures.Common

/-! Rows-gate handles beside owned gates: `q1 * x + q2 * y(-1) - q3 * z(1)` over complex
selectors, where `q1` is the owner, `q2` owns another gate and `q3` owns none. `q3` is enabled
through its `rowsHandles` handle, twice on one row and on a second region's last row; selector-free
`Rust.sub` still folds a zero operand. -/
namespace LoweringFixtures.RowsHandlesMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q1 ← selector false
  let q2 ← selector false
  let q3 ← selector false
  gateWithoutSelector "three" do
    let x ← advice a
    let y ← advice b (-1)
    let z ← advice a 1
    return #[("", Rust.sub (.add (Rust.mul (querySelector q1) x) (Rust.mul (querySelector q2) y))
      (Rust.mul (querySelector q3) z))]
  gate "own" q2 do
    let x ← advice a
    let y ← advice b
    return #[("", Rust.sub (Rust.sub x y) (.const 0)), ("left", Rust.sub (.const 0) (Rust.mul x y))]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- The handle of gate 0 on selector `q`. -/
def handle (q : Nat) : Gate F :=
  if h : (spec 0).valid then ((spec 0).rowsHandles h).find? (·.selector.index == q) |>.getD (cleanGate (spec 0))
  else cleanGate (spec 0)

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
      .enableGate (cleanGate (spec 0)) 1, .enableGate (handle 2) 1, .enableGate (handle 2) 1,
      .enableGate (cleanGate (spec 1)) 1, .enableGate (cleanGate (spec 1)) 0],
    .region "s" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness, .enableGate (handle 2) 1]]

#guard source.gates.map (·.rows) == #[true, false]
#guard (if h : (spec 0).valid then ((spec 0).rowsHandles h).map (·.selector.index) else []) == [1, 2]

end LoweringFixtures.RowsHandlesMix
