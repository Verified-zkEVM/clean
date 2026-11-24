import LoweringFixtures.Common

/-! Additive gates setting the degree: a `rows` trash body `q2 * x^3 - y` (degree 4), one folding to
`Constant(0)` (trash degree 2) and a negated product on `q2`; `set_minimum_degree(6)` between them
lifts the batch degree of a four-tuple degree-2 `None` batch (rotated table expression) to 9 in one
chunk (without it: degree 5, two chunks); a zero-tuple batch on `q2` over a column loaded only
empty. -/
namespace LoweringFixtures.AdditiveDegreeChunks
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let t2 ← fixedColumn
  let q1 ← selector false
  let q2 ← selector false
  additiveGate "cube" q1 do
    let x ← advice a
    let y ← advice b
    return #[("cube", Rust.sub (Rust.mul (Rust.mul (Rust.mul (querySelector q2) x) x) x) y)]
  setMinimumDegree 6
  additiveGate "const" q1 do
    let x ← advice a 1
    return #[("zero", Rust.mul x (.const 0))]
  additiveGate "neg" q2 do
    let x ← advice a
    let y ← advice b (-1)
    return #[("neg", Rust.neg (Rust.mul x y)), ("lin", x + y)]
  batchedLookupAny "wide" none do
    let x ← advice a
    let y ← advice b
    let y1 ← advice b 1
    let tt ← fixed t
    let t21 ← fixed t2 1
    return #[(#[Rust.mul x y, Rust.mul x x, Rust.mul y y, Rust.mul x y1], tt),
      (#[x, y, y1, x], t21)]
  batchedLookup "empty" q2 do return #[(#[], t2)]

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def trash (i : Nat) : GateSpec := source.trashcans[i]?.getD empty
def handles (g : GateSpec) : List (Gate F) := if h : g.valid = true then g.rowsHandles h else []

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.loadTable ⟨⟨1⟩⟩ [], .loadTable ⟨⟨0⟩⟩ [0, 1, 2, 3],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness, .assignAdvice ⟨1⟩ 2 witness,
      .enableGate (cleanGate (trash 0)) 1, .enableGate (cleanGate (trash 1)) 1,
      .enableGate (cleanGate (trash 2)) 2] ++
      (handles (trash 0)).map (RegionOperation.enableGate · 2) ++
      [.enableGate (cleanGate (trash 1)) 0, .enableGate (cleanGate (trash 0)) 0])]

#guard source.validate.isOk && source.degree == 9
#guard (source.trashcans.map (·.rows)) == #[true, false, false]
#guard (source.lookups.map (·.numChunks source.degree)) == #[1, 0]

end LoweringFixtures.AdditiveDegreeChunks
