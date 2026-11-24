import LoweringFixtures.Common

/-! BitPair, a small zk.golf-style circuit: two advice bits, their sum and product on the instance
column, one additive gate with both equations and a two-tuple LogUp batch on the same complex
selector, k = 4. `split` registers the equations as two additive gates on that selector, the second
with its query order reversed. -/
namespace LoweringFixtures.AdditiveBitPair
open Halo2 Midnight Midnight.Keygen

def configure (split : Bool) : ConfigM Unit := do
  let x ← adviceColumn
  let y ← adviceColumn
  let sum ← adviceColumn
  let product ← adviceColumn
  let table ← fixedColumn
  let publicCol ← instanceColumn
  enableEquality ⟨.advice, sum⟩
  enableEquality ⟨.advice, product⟩
  enableEquality ⟨.instance, publicCol⟩
  let q ← selector false
  if split then
    additiveGate "sum" q do
      let x ← advice x
      let y ← advice y
      let sum ← advice sum
      return #[("sum", sum - x - y)]
    additiveGate "product" q do
      let product ← advice product
      let y ← advice y
      let x ← advice x
      return #[("product", product - x * y)]
  else
    additiveGate "sum and product" q do
      let x ← advice x
      let y ← advice y
      let sum ← advice sum
      let product ← advice product
      return #[("sum", sum - x - y), ("product", product - x * y)]
  batchedLookup "bits" q do
    let x ← advice x
    let y ← advice y
    return #[(#[x, y], table)]

def source (split : Bool) : CS := ((configure split).run {}).2

def trashGates (split : Bool) : List (Gate F) := (source split).trashcans.toList.map cleanGate

def bits (split : Bool) : BatchedLookup := (source split).lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixtureOf (split : Bool) : Export.Replay.Fixture where
  source := source split
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "bit pair" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨2⟩ 0 witness, .assignAdvice ⟨3⟩ 0 witness] ++
      (trashGates split).map (.enableGate · 0) ++
      [.enableLookup (cleanLookup (bits split) 0) [⟨0, false⟩] 0,
       .enableLookup (cleanLookup (bits split) 1) [⟨0, false⟩] 0]),
    .constrainInstance (cell 0 0 .advice 2) ⟨0⟩ 0,
    .constrainInstance (cell 0 0 .advice 3) ⟨0⟩ 1]

def fixture : Export.Replay.Fixture := fixtureOf false

#guard (source false).validate.isOk && (source true).validate.isOk
#guard (source true).adviceQueries == #[(2, 0), (3, 0), (0, 0), (1, 0)] &&
  (source true).gates.size == 2 && (source true).trashcans.size == 2

end LoweringFixtures.AdditiveBitPair
