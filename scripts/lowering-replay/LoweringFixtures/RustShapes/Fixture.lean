import LoweringFixtures.Common

/-! Rust shapes that plain `E` arithmetic does not spell, through the `Rust` operator spellings:
`Constant(-1) * x`, `Constant(3) * F(7)`, `x * Constant(5)`, `-Constant(0)`, `x + -Constant(0)`,
`x - 0`, `0 - y`, `x - y`, `Constant(2) * Constant(3)`, `x * F(9)`, `x * -Constant(1)` and
`x * Constant(-1)`. Sent as spellings, so Rust's operators build them. -/
namespace LoweringFixtures.RustShapes
open Halo2 Midnight Midnight.Keygen Export.Replay

def xs : Spelling := .atom (.var (.advice ⟨0⟩ 0))
def ys : Spelling := .atom (.var (.advice ⟨0⟩ 1))

def shapes : List (String × Spelling) := [
  ("minus one times", .mul (.const (-1)) xs),
  ("scaled constant", .scale (.const 3) 7),
  ("times constant", .mul xs (.const 5)),
  ("negated zero", .neg (.const 0)),
  ("plus negated zero", .add xs (.neg (.const 0))),
  ("minus zero", .sub xs (.const 0)),
  ("zero minus", .sub (.const 0) ys),
  ("minus", .sub xs ys),
  ("constant product", .mul (.const 2) (.const 3)),
  ("scaled", .scale xs 9),
  ("times negated one", .mul xs (.neg (.const 1))),
  ("times minus one", .mul xs (.const (-1)))]

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gate "shapes" q do
    let _ ← advice a
    let _ ← advice a 1
    return (shapes.map fun (name, s) => (name, s.toE)).toArray

def source : CS := (configure.run {}).2

def shapesGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .enableGate (cleanGate shapesGate) 0]]
  spellings := shapes.map (·.2)

private def pinned : String := source.finalize.pinnedDebug
private def count (part : String) : Nat := (pinned.splitOn part).length - 1
private def x : String := "Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }"
private def y : String := "Advice { query_index: 1, column_index: 0, rotation: Rotation(1) }"
private def c (v : F) : String := "Constant(" ++ scalarDebug v ++ ")"

#guard count ("Product(" ++ c (-1) ++ ", " ++ x ++ ")") == 1
#guard count ("Scaled(" ++ c 3 ++ ", " ++ scalarDebug 7 ++ ")") == 1
#guard count ("Product(" ++ x ++ ", " ++ c 5 ++ ")") == 1
#guard count ("Negated(" ++ c 0 ++ ")") == 2
#guard count ("Sum(" ++ x ++ ", Negated(" ++ y ++ "))") == 1
#guard count ("Product(" ++ c 2 ++ ", " ++ c 3 ++ ")") == 1
#guard count ("Scaled(" ++ x ++ ", " ++ scalarDebug 9 ++ ")") == 1
#guard count ("Product(" ++ x ++ ", Negated(" ++ c 1 ++ "))") == 1
#guard count ("Product(" ++ x ++ ", " ++ c (-1) ++ ")") == 1

end LoweringFixtures.RustShapes
