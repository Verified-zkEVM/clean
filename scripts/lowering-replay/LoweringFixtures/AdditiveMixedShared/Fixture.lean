import LoweringFixtures.Common

/-! One complex selector `q` owning a multiplicative gate, a selector-free additive gate (fixed at
-1, instance, a duplicate and a backward advice query, `x * 0` folding), a `rows` additive gate
reading `q` itself, `q3` and a simple `qs` folded away by `* 0`, and an owned lookup (`qs` enabled
through its handle, beside its own gate); a zero-tuple `None` batch whose table reads `q3`;
`set_minimum_degree` called twice (7, then 4: last wins); empty table loads before and after the
real one; deferred constants and an instance copy. -/
namespace LoweringFixtures.AdditiveMixedShared
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let c ← fixedColumn
  let inst ← instanceColumn
  let q ← selector false
  let q3 ← selector false
  let qs ← selector
  setMinimumDegree 7
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩
  enableConstant c
  gate "mul" q do
    let x ← advice a
    let y ← advice b
    let z ← advice a 1
    return #[("mul", Rust.mul x y - z)]
  additiveGate "free" q do
    let x1 ← advice a 1
    let fm ← fixed f (-1)
    let y ← advice b (-2)
    let i ← query (.instance ⟨inst⟩ 0)
    let x1' ← advice a 1
    return #[("lin", x1 - Rust.mul fm y + i), ("zero", Rust.mul x1' (.const 0)),
      ("dup", Rust.sub x1 x1')]
  batchedLookup "own" q do
    let x ← advice a
    return #[(#[x], t)]
  additiveGate "rows" q do
    let x ← advice a
    let y ← advice b 1
    return #[("self", Rust.mul (querySelector q) (Rust.sub x (.const 1))),
      ("other", Rust.mul (querySelector q3) y),
      ("simple folded", Rust.mul (querySelector qs) (.const 0) + y)]
  gate "simple" qs do
    let y ← advice b
    return #[("bool", Rust.mul y y - y)]
  batchedLookupAny "nil" none do
    let x ← advice b 1
    return #[(#[], Rust.mul (querySelector q3) x)]
  setMinimumDegree 4

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def mulGate : GateSpec := source.gates[0]?.getD empty
def simpleGate : GateSpec := (source.gates.find? (·.name == "simple")).getD empty
def trash (i : Nat) : GateSpec := source.trashcans[i]?.getD empty
def handles (g : GateSpec) : List (Gate F) := if h : g.valid = true then g.rowsHandles h else []
def own : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def enableQ (row : Nat) : RegionOperations F :=
  [.enableGate (cleanGate mulGate) row, .enableGate (cleanGate (trash 0)) row,
   .enableLookup (cleanLookup own) [⟨0, false⟩] row, .enableGate (cleanGate (trash 1)) row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.loadTable ⟨⟨1⟩⟩ [],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .assignAdvice ⟨0⟩ 2 witness, .assignAdvice ⟨0⟩ 3 witness, .assignAdvice ⟨1⟩ 3 witness,
      .assignFixed ⟨0⟩ 1 5] ++ enableQ 2 ++
      (handles (trash 1)).map (RegionOperation.enableGate · 1) ++
      [.enableGate (cleanGate simpleGate) 1, .enableGate (cleanGate simpleGate) 3, .constrainConstant (cell 0 0 .advice 0) 9] ++
      (assignAdviceFromConstant ⟨0⟩ 4 (-2)).operations 0 ++ enableQ 3),
    .loadTable ⟨⟨1⟩⟩ [3, 4, 5],
    .constrainInstance (cell 0 2 .advice 0) ⟨0⟩ 1,
    .loadTable ⟨⟨1⟩⟩ []]

#guard source.validate.isOk && source.minimumDegree == some 4
#guard (source.trashcans.map (·.rows)) == #[false, true] && source.gates.size == 4
#guard ((handles (trash 1)).map (·.selector.index)) == [1, 2]

end LoweringFixtures.AdditiveMixedShared
