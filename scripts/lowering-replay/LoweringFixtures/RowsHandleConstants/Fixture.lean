import LoweringFixtures.Common

/-! `rows` gates and nonzero rotations mixed with constants and lookups: a selector-free `rows` gate
whose handle (default selector index 0) is enabled beside the simple selector 0's own gate, querying
a fixed column at the i32 extremes, with literal bodies `Constant(0)` and `0 - 0`; an owned raw gate
whose two constraints have q-degrees 2 and 1 (`(q * q) * ..`, `(-q) * x`) reading the constants
column at -1 and +1 before `enable_constant` registers its rotation 0; `with_selector(qc, [qc * x])`
and `with_selector(qc, [qs * y])` rows gates; a lookup on `qc` reading the constants column at 3;
deferred constants. -/
namespace LoweringFixtures.RowsHandleConstants
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← fixedColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let qs ← selector
  let qc ← selector false
  gateWithoutSelector "free" do
    let x ← advice a
    let up ← fixed f 2147483647
    let down ← fixed f (-2147483648)
    return #[("extreme", Rust.mul (Rust.mul up down) x), ("zero", .const 0),
      ("lit", Rust.sub (.const 0) (.const 0))]
  gate "plain" qs do
    let y ← advice b
    return #[("bool", Rust.mul y (Rust.sub y (.const 1))), ("zero", .const 0)]
  gateWithoutSelector "owned" do
    let up ← fixed c (-1)
    let x ← advice a
    let next ← fixed c 1
    let q := querySelector qc
    return #[("sq", Rust.mul (Rust.mul q q) (Rust.sub up next)), ("neg", Rust.mul (Rust.neg q) x)]
  enableConstant c
  enableEquality ⟨.advice, a⟩
  gate "self" qc do
    let x ← advice a
    return #[("", Rust.mul (querySelector qc) x)]
  gate "cross" qc do
    let y ← advice b
    return #[("", Rust.mul (querySelector qs) y)]
  batchedLookup "lk" qc do
    let x ← advice a
    let cc ← fixed c 3
    return #[(#[Rust.mul x cc], t)]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def complexAt (row : Nat) : RegionOperations F :=
  [.enableGate (cleanGate (spec 2)) row, .enableLookup (cleanLookup lk) [⟨1, false⟩] row,
   .enableGate (cleanGate (spec 3)) row, .enableGate (cleanGate (spec 4)) row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨2⟩⟩ [0, 3],
    .region "r" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableGate (cleanGate (spec 0)) 0, .enableGate (cleanGate (spec 1)) 0,
      .assignAdvice ⟨0⟩ 1 witness, .enableGate (cleanGate (spec 1)) 1,
      .constrainConstant (cell 0 1 .advice 0) 5] ++ complexAt 1 ++
      [.assignFixed ⟨1⟩ 2 7, .constrainConstant (cell 0 0 .advice 0) (-1)]),
    .region "s" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 3 witness] ++ complexAt 3 ++
      [.enableGate (cleanGate (spec 0)) 3, .enableGate (cleanGate (spec 1)) 3,
       .constrainEqual (cell 1 0 .advice 0) (cell 0 1 .advice 0)])]

#guard source.gates.map (·.rows) == #[true, false, false, true, true]
#guard source.fixedQueries == #[(1, 2147483647), (1, -2147483648), (0, -1), (0, 1), (0, 0), (0, 3), (2, 0)]

end LoweringFixtures.RowsHandleConstants
