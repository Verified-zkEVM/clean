import LoweringFixtures.Common

/-! Folding inside lookups mixed with ordinal-prefixed names: a three-wide parallel batch whose
inputs are degree 3 as written and degree 1 in Rust (`xxx * 0 + y`, `1 * x`,
`Constant(0) * F(5) + x`, the last unfolded), a two-column lookup with a `x * Constant(0)` column,
empty and spaced names, gate constraints folding to `q` and `q * -Constant(0)`, and a trashcan of
`x * 1` and `y - 0`. -/
namespace LoweringFixtures.FoldedLookupMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let t2 ← fixedColumn
  let q ← selector
  let ql ← selector false
  let _ ← selector false
  gate "units" q do
    let x ← advice a
    let y ← advice b
    return #[("one", Rust.mul (.const 1) (.const 1)), ("zero minus zero", Rust.sub (.const 0) (.const 0)),
      ("quad", x * y)]
  batchedLookup "" ql do
    let x ← advice a
    let y ← advice b
    return #[(#[.add (Rust.mul (x * x * x) (.const 0)) y, .mul (.const 1) x, .add (Rust.scale (.const 0) 5) x], t)]
  batchedLookup " spaced  ~name " ql do
    let x ← advice a
    let y ← advice b 1
    return #[(#[y], t), (#[Rust.mul x (.const 0)], t2)]

def source0 : CS := (configure.run {}).2

def trash : GateSpec :=
  let x : E := .var (.advice ⟨0⟩ 0)
  let y : E := .var (.advice ⟨1⟩ 0)
  ⟨"trash", ⟨2, false⟩, #[.advice ⟨0⟩ 0, .advice ⟨1⟩ 0],
    #[("times one", Rust.mul x (.const 1)), ("minus zero", Rust.sub y (.const 0))], false, false⟩

def source : CS := { source0 with trashcans := #[trash] }

def units : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lookup (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2], .loadTable ⟨⟨1⟩⟩ [0, 5],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableGate (cleanGate units) 0,
      .enableLookup (cleanLookup (lookup 0) 0) [⟨1, false⟩] 0,
      .enableLookup (cleanLookup (lookup 0) 1) [⟨1, false⟩] 0,
      .enableLookup (cleanLookup (lookup 0) 2) [⟨1, false⟩] 0,
      .enableLookup (cleanLookup (lookup 1) 0) [⟨1, false⟩] 0,
      .enableGate (cleanGate trash) 0]]

#guard (lookup 0).inputDegree == 1 && (lookup 1).inputDegree == 1
#guard (source.pinnedDebug.splitOn "name: \"lookup #1: \"").length == 2
#guard (source.pinnedDebug.splitOn "name: \"lookup #2:  spaced  ~name \"").length == 2

end LoweringFixtures.FoldedLookupMix
