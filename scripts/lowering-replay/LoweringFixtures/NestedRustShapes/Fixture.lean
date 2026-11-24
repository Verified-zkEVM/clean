import LoweringFixtures.Common

/-! Nested `Rust` spellings in a gate, a lookup input and a trashcan: `Negated(Constant(1))` and
`Scaled(Constant(1), -1)` as either factor of a product, double negation, `x - -Constant(0)`,
`-Constant(0) - x`, `x * F(1) * Constant(1)`, a constant product as a right factor and
`y * (1 * Constant(-1))`. The harness rebuilds Lean's erased tree with Rust's operators, so the
`#guard`s pin the shapes erasure must produce. -/
namespace LoweringFixtures.NestedRustShapes
open Halo2 Midnight Midnight.Keygen

private def one : E := .const 1

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  let _ ← selector false
  gate "nested" q do
    let x ← advice a
    let y ← advice b
    return #[
      ("neg one left", Rust.mul (Rust.neg one) x),
      ("double neg", Rust.neg (Rust.neg x)),
      ("neg zero minus", Rust.sub (Rust.neg (.const 0)) x),
      ("scaled one folded", Rust.mul (Rust.scale x 1) one),
      ("constant", Rust.mul (.const (-1)) one),
      ("constant product right", Rust.mul x (Rust.mul (.const 2) (.const 3))),
      ("scaled neg one", Rust.scale (Rust.neg one) 4),
      ("scaled one left", Rust.mul (Rust.scale one (-1)) x),
      ("scaled one right", Rust.mul x (Rust.scale one (-1))),
      ("neg times neg one", Rust.mul (Rust.neg x) (Rust.neg one)),
      ("neg one plus", .add (Rust.neg one) (Rust.mul (.const (-1)) x)),
      ("minus neg zero", Rust.sub x (Rust.neg (.const 0))),
      ("folded minus one", Rust.mul y (Rust.mul one (.const (-1))))]
  batchedLookup "nested" ql do
    let x ← advice a
    return #[(#[Rust.sub (Rust.scale x 2) (Rust.neg one)], t)]

def source0 : CS := (configure.run {}).2

def trash : GateSpec :=
  let y : E := .var (.advice ⟨1⟩ 0)
  ⟨"trash", ⟨2, false⟩, #[.advice ⟨1⟩ 0], #[("neg one neg", Rust.mul (Rust.neg one) (Rust.neg y))], false, false⟩

def source : CS := { source0 with trashcans := #[trash] }

def nested : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lookup : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableGate (cleanGate nested) 0, .enableLookup (cleanLookup lookup) [⟨1, false⟩] 0,
      .enableGate (cleanGate trash) 0]]

private def pinned : String := source.finalize.pinnedDebug
private def count (part : String) : Nat := (pinned.splitOn part).length - 1
private def x : String := "Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }"
private def y : String := "Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }"
private def c (v : F) : String := "Constant(" ++ scalarDebug v ++ ")"
private def n1 : String := "Negated(" ++ c 1 ++ ")"
private def s1 : String := "Scaled(" ++ c 1 ++ ", " ++ scalarDebug (-1) ++ ")"

#guard count ("Product(" ++ n1 ++ ", " ++ x ++ ")") == 1
#guard count ("Negated(Negated(" ++ x ++ "))") == 1
#guard count ("Sum(Negated(" ++ c 0 ++ "), Negated(" ++ x ++ "))") == 1
#guard count ("Scaled(" ++ x ++ ", " ++ scalarDebug 1 ++ ")") == 1
#guard count ("Product(" ++ x ++ ", Product(" ++ c 2 ++ ", " ++ c 3 ++ "))") == 1
#guard count ("Scaled(" ++ n1 ++ ", " ++ scalarDebug 4 ++ ")") == 1
#guard count ("Product(" ++ s1 ++ ", " ++ x ++ ")") == 1
#guard count ("Product(" ++ x ++ ", " ++ s1 ++ ")") == 1
#guard count ("Product(Negated(" ++ x ++ "), " ++ n1 ++ ")") == 1
#guard count ("Sum(" ++ n1 ++ ", Product(" ++ c (-1) ++ ", " ++ x ++ "))") == 1
#guard count ("Sum(" ++ x ++ ", Negated(Negated(" ++ c 0 ++ ")))") == 1
#guard count ("Product(" ++ y ++ ", " ++ c (-1) ++ ")") == 1
#guard count ("Sum(Scaled(" ++ x ++ ", " ++ scalarDebug 2 ++ "), Negated(" ++ n1 ++ "))") == 1
#guard count ("Product(" ++ n1 ++ ", Negated(" ++ y ++ "))") == 1
#guard count ("Product(" ++ x ++ ", " ++ c (-1) ++ ")") == 0
#guard count ("Product(Negated(" ++ x ++ "), " ++ c (-1) ++ ")") == 0

end LoweringFixtures.NestedRustShapes
