import LoweringFixtures.Common

/-! Rust's minimum rows where folding sets the LogUp chunk count: eight parallel inputs
`y * y * 0 + y` (degree 2 as written, 1 in Rust) make two chunks, so seven advice rotations, one
trashcan and two chunks give 13 blinding factors and `2^4 = 16` rows is exactly the minimum.
Unfolded degrees would give four chunks. -/
namespace LoweringFixtures.FoldedRows
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  let _ ← selector false
  gate "wide" q do
    let xs ← (List.range 7).mapM fun r => advice a r
    return #[("sum", (xs.drop 2).foldl (· + ·) (xs.getD 0 (.const 0) * xs.getD 1 (.const 0)))]
  batchedLookup "folded" ql do
    let y ← advice b
    let input : E := .add (Rust.mul (y * y) (.const 0)) y
    return #[((Array.range 8).map (fun _ => input), t)]

def trash (selector : Nat) : GateSpec :=
  let y : E := .var (.advice ⟨1⟩ 0)
  ⟨s!"trash {selector}", ⟨selector, false⟩, #[.advice ⟨1⟩ 0], #[("y", Rust.mul y (.const 1))], false, false⟩

def source : CS := { (configure.run {}).2 with trashcans := #[trash 2] }

def wide : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def folded : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def ops (trashcans : List GateSpec) : Operations F :=
  [.loadTable ⟨⟨0⟩⟩ [0],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .enableGate (cleanGate wide) 0] ++
      (List.range 8).map (fun i => .enableLookup (cleanLookup folded i) [⟨1, false⟩] 0) ++
      trashcans.map (fun g => .enableGate (cleanGate g) 0))]

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := ops [trash 2]

#guard source.degree == 5 && folded.numChunks source.degree == 2
#guard source.blindingFactors + 3 == 16

end LoweringFixtures.FoldedRows
