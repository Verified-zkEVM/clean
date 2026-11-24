import LoweringFixtures.Common
import Midnight.Additive

/-! Simple and complex selectors interleaved (s0 simple, q1 complex, s2 simple, q3 complex, s4
simple), so Rust compresses the simple ones and converts q1, q3 to their own fixed columns. Trash
bodies read the other complex selector in both index orders (`q3` reads `q1`, `q1` reads `q3`), a
fixed column at -1 and 2, advice at -1 from row 0 (wraps to the blinding rows); two trash arguments
on `q1`, one `rows`, one plain. `selectorRows` must be Rust's selector columns. -/
namespace LoweringFixtures.AdditiveSelectorColumns
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let s0 ← selector
  let q1 ← selector false
  let s2 ← selector
  let q3 ← selector false
  let s4 ← selector
  gate "s0" s0 do
    let x ← advice a
    return #[("bool", Rust.mul x x - x)]
  additiveGate "t3" q3 do
    let x ← advice a 1
    let fm ← fixed f (-1)
    let y ← advice b
    return #[("q1 x", Rust.mul (querySelector q1) x), ("lin", fm - y)]
  gate "s2" s2 do
    let y ← advice b
    return #[("bool", Rust.mul y y - y)]
  additiveGate "t1" q1 do
    let x ← advice a (-1)
    let y ← advice b
    return #[("diff", x - y)]
  additiveGate "t1b" q1 do
    let f2 ← fixed f 2
    let y ← advice b 1
    return #[("q3 f", Rust.mul (querySelector q3) f2 + y)]
  gate "s4" s4 do
    let x ← advice a
    let y ← advice b
    return #[("eq", x - y)]

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def gateNamed (n : String) : GateSpec := (source.gates.find? (·.name == n)).getD empty
def trashNamed (n : String) : GateSpec := (source.trashcans.find? (·.name == n)).getD empty

def ops : Operations F :=
  [.region "a" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
     .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness, .assignAdvice ⟨1⟩ 2 witness,
     .assignFixed ⟨0⟩ 0 3, .assignFixed ⟨0⟩ 3 4,
     .enableGate (cleanGate (gateNamed "s0")) 0, .enableGate (cleanGate (trashNamed "t1")) 0,
     .enableGate (cleanGate (trashNamed "t1b")) 0, .enableGate (cleanGate (gateNamed "s2")) 1,
     .enableGate (cleanGate (trashNamed "t1")) 1, .enableGate (cleanGate (trashNamed "t1b")) 1,
     .enableGate (cleanGate (trashNamed "t3")) 1, .enableGate (cleanGate (trashNamed "t3")) 2,
     .enableGate (cleanGate (gateNamed "s4")) 2],
   .region "b" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
     .enableGate (cleanGate (gateNamed "s0")) 0, .enableGate (cleanGate (trashNamed "t3")) 0]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := ops

def starts : List Nat := Chips.Layout.Planner.simple.starts source.constantColumn ops

#guard (source.trashcans.map (·.rows)) == #[true, false, true]
#guard (source.trashcans.map (·.selector.index)) == #[3, 1, 1]
#guard starts == [0, 4]
#guard decide (selectorRows 1 starts ops = {0, 1})
#guard decide (selectorRows 3 starts ops = {1, 2, 4})
#guard decide (selectorRows 0 starts ops = {0, 4} ∧ selectorRows 2 starts ops = {1} ∧
  selectorRows 4 starts ops = {2})

end LoweringFixtures.AdditiveSelectorColumns
