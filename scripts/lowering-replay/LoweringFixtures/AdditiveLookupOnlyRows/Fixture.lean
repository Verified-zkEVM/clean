import LoweringFixtures.Common
import Midnight.Additive

/-! A `rows` trash argument on complex `q` (body reads `q2` and `q` itself) whose selector is
enabled only through an owned lookup on `q`, in two regions; `q2` only through the trash argument's
handle. Rust enforces the trash identity wherever `q.enable` ran; Lean admits (the trash argument's
Clean gate is a constraint-free handle) and `selectorRows` must hold those lookup rows, so
`additive_selector_clean`'s `rows` clause covers them. -/
namespace LoweringFixtures.AdditiveLookupOnlyRows
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  let q2 ← selector false
  batchedLookup "own" q do
    let x ← advice a
    return #[(#[x], t)]
  additiveGate "rows" q do
    let x ← advice a
    let y ← advice b (-1)
    return #[("q2 y", Rust.mul (querySelector q2) y),
      ("own q", Rust.mul (querySelector q) (Rust.sub x (.const 1)))]

def source : CS := (configure.run {}).2

def trash : GateSpec := source.trashcans[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def handles (g : GateSpec) : List (Gate F) := if h : g.valid = true then g.rowsHandles h else []
def own : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def ops : Operations F :=
  [.loadTable ⟨⟨0⟩⟩ [1, 2],
   .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
     .enableLookup (cleanLookup own) [⟨0, false⟩] 0, .assignAdvice ⟨0⟩ 2 witness,
     .enableLookup (cleanLookup own) [⟨0, false⟩] 2] ++
     (handles trash).map (RegionOperation.enableGate · 1)),
   .region "s" [.assignAdvice ⟨0⟩ 0 witness, .enableLookup (cleanLookup own) [⟨0, false⟩] 0]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := ops

def starts : List Nat := Chips.Layout.Planner.simple.starts source.constantColumn ops

#guard source.validate.isOk && (source.trashcans.map (·.rows)) == #[true]
#guard ((handles trash).map (·.selector.index)) == [1]
#guard starts == [0, 3]
#guard decide (selectorRows 0 starts ops = {0, 2, 3})
#guard decide (selectorRows 1 starts ops = {1})
#guard decide (selectorColumn 0 starts ops 3 = 1 ∧ selectorColumn 0 starts ops 1 = 0)

end LoweringFixtures.AdditiveLookupOnlyRows
