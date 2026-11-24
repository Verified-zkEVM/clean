import LoweringFixtures.Common

/-! A `rows` gate `qs * (x(1) + qc * (f(3) * (f(-2) - y(-1))))` owned by the simple `qs`, whose
complex `qc` also owns a `with_selector` gate on `f(-1)` and a lookup on `x * f(1)`: Rust's one
`qc.enable` is Lean's gate, lookup and `rows` handle enables. `qs` is enabled at a region's last row
(x(1) in the next region) and at row 0 of the second region (rotations into the first). -/
namespace LoweringFixtures.RowsSimpleOwnerMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let qs ← selector
  let qc ← selector false
  gate "own" qc do
    let z ← advice b
    let fm ← fixed f (-1)
    return #[("", Rust.sub fm z)]
  gateWithoutSelector "mixed" do
    let up ← fixed f 3
    let x ← advice a 1
    let dn ← fixed f (-2)
    let y ← advice b (-1)
    return #[("", Rust.mul (querySelector qs)
      (.add x (Rust.mul (querySelector qc) (Rust.mul up (Rust.sub dn y)))))]
  batchedLookup "range" qc do
    let x ← advice a
    let g ← fixed f 1
    return #[(#[Rust.mul x g], t)]
  enableEquality ⟨.fixed, f⟩

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def range : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

/-- The `rows` gate's handle on `qc`. -/
def handle : Gate F :=
  if h : (spec 1).valid then ((spec 1).rowsHandles h).head?.getD (cleanGate (spec 1))
  else cleanGate (spec 1)

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨1⟩⟩ [0, 1, 2],
    .region "a" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignFixed ⟨0⟩ 0 4,
      .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness, .enableGate (cleanGate (spec 1)) 1,
      .assignAdvice ⟨0⟩ 2 witness, .enableGate handle 2, .enableLookup (cleanLookup range) [⟨1, false⟩] 2,
      .enableGate (cleanGate (spec 0)) 2, .assignFixed ⟨0⟩ 3 9, .enableGate (cleanGate (spec 1)) 3],
    .region "b" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 0 5, .enableGate (cleanGate (spec 1)) 0,
      .enableGate (cleanGate (spec 0)) 0, .enableGate handle 0, .enableLookup (cleanLookup range) [⟨1, false⟩] 0]]

#guard source.gates.map (·.rows) == #[false, true]
#guard (spec 1).selector.index == 0 && (spec 1).selector.simple
#guard (if h : (spec 1).valid then ((spec 1).rowsHandles h).map (·.selector.index) else []) == [1]
#guard source.fixedQueries == #[(0, -1), (0, 3), (0, -2), (0, 1), (1, 0), (0, 0)]

end LoweringFixtures.RowsSimpleOwnerMix
