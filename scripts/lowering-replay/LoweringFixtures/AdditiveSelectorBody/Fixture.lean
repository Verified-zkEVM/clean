import LoweringFixtures.Common

/-! Complex selectors inside additive bodies: `x - q2 * y`, a body reading its own
selector `q1 * (x * x - x)`, and an additive gate on `q2` whose body only reads `q1`, beside an
ordinary trash argument on `q2`. Such a trash argument means `RowGatesHold` of `q * c`; `q2` is
also enabled through the first gate's handle, with the ordinary one, as Rust's `q2.enable`. -/
namespace LoweringFixtures.AdditiveSelectorBody
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q1 ← selector false
  let q2 ← selector false
  additiveGate "selected body" q1 do
    let x ← advice a
    let y ← advice b 1
    return #[("difference", x - Rust.mul (querySelector q2) y),
      ("own", Rust.mul (querySelector q1) (Rust.mul x x - x))]
  additiveGate "plain" q2 do
    let y ← advice b
    return #[("square", Rust.mul y y - y)]
  additiveGate "reads q1" q2 do
    let x ← advice a (-1)
    return #[("q1 x", Rust.mul x (querySelector q1))]

def source : CS := (configure.run {}).2

def trash (i : Nat) : GateSpec := source.trashcans[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- Handles of a `rows` trash argument's other selectors. -/
def handles (g : GateSpec) : List (Gate F) := if h : g.valid = true then g.rowsHandles h else []

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
    .enableGate (cleanGate (trash 0)) 0, .assignAdvice ⟨0⟩ 1 witness,
    .enableGate (cleanGate (trash 1)) 1, .enableGate (cleanGate (trash 2)) 1,
    .enableGate (cleanGate (trash 0)) 2, .assignAdvice ⟨1⟩ 2 witness, .assignAdvice ⟨1⟩ 3 witness] ++
    (handles (trash 0)).map (RegionOperation.enableGate · 2) ++
    [.enableGate (cleanGate (trash 1)) 2])]

#guard source.validate.isOk && (source.trashcans.map (·.rows)) == #[true, false, true]
#guard ((handles (trash 0)).map (·.selector.index)) == [1] &&
  ((handles (trash 2)).map (·.selector.index)) == [0]

end LoweringFixtures.AdditiveSelectorBody
