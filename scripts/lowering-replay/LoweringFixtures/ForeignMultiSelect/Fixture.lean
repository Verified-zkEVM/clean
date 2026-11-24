import LoweringFixtures.Common

/-! Foreign ECC's self-referential `multi_select` lookup (circuits/src/ecc/foreign/common.rs:189-256):
`lookup_any(None)` of `(v, (1 - q) * v)` over the index, x and y limbs and the fixed tag, rows filled
as `fill_dynamic_lookup_row` does: copied limbs on table rows, `q.enable` and free limbs on a
lookup row. -/
namespace LoweringFixtures.ForeignMultiSelect
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let x0 ← adviceColumn
  let x1 ← adviceColumn
  let y0 ← adviceColumn
  let y1 ← adviceColumn
  let idx ← adviceColumn
  for c in [x0, x1, y0, y1] do enableEquality ⟨.advice, c⟩
  let q ← selector false
  enableEquality ⟨.advice, idx⟩
  let tag ← fixedColumn
  lookupAny "multi_select lookup" none do
    let sel ← query (.selector q)
    let notSel := Rust.sub (.const 1) sel
    let mut identities : Array (E × E) := #[]
    for c in [idx, x0, x1, y0, y1] do
      let v ← advice c
      identities := identities.push (v, Rust.mul notSel v)
    let t ← fixed tag
    return identities.push (t, Rust.mul notSel t)

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

/-- A source region holding limbs and an index. -/
def limbs : RegionOperations F :=
  [0, 1, 2, 3, 4].map fun c => .assignAdvice ⟨c⟩ 0 witness

/-- `fill_dynamic_lookup_row` for region `r`, copying from region `src` unless `lookup`. -/
def row (r src : Nat) (tagValue : F) (lookup : Bool) : RegionOperations F :=
  (if lookup then [.enableGate (lookupHandle lk 0) 0] else []) ++
  ([0, 2, 1, 3].flatMap fun c => .assignAdvice ⟨c⟩ 0 witness ::
    if lookup then [] else [.constrainEqual (cell r 0 .advice c) (cell src 0 .advice c)]) ++
  [.assignAdvice ⟨4⟩ 0 witness, .constrainEqual (cell r 0 .advice 4) (cell src 0 .advice 4),
    .assignFixed ⟨0⟩ 0 tagValue]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "limbs" limbs, .region "limbs" limbs,
    .region "multi_select table" (row 2 0 7 false), .region "multi_select table" (row 3 1 7 false),
    .region "multi_select table" (row 4 0 7 true)]

#guard source.validate.isOk && !lk.owned
#guard lk.selector = .const 1
#guard lk.handles.map (·.selector.index) == [0]
#guard (source.pinnedDebug.splitOn
  "selector: Constant(Fq(0x0000000000000000000000000000000000000000000000000000000000000001))").length == 2

end LoweringFixtures.ForeignMultiSelect
