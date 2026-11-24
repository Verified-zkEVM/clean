import LoweringFixtures.Common

/-! LogUp degree from the table side: `lookup_any(Some(q1))` of `(x, i(-1))` in `(q2 * (t * t), 7)`
has accumulator degree 2 + 1 + 3 = 6, so the CS degree is 9 although every gate has degree 3;
a constant table expression has degree 0. A `batched_lookup_any(None)` of three degree-2 and
degree-1 inputs against `b(-1)` shares `q3` with an owned gate. -/
namespace LoweringFixtures.LookupAnyHighDegree
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let inst ← instanceColumn
  let q1 ← selector false
  let q2 ← selector false
  let q3 ← selector false
  gate "bool" q3 do
    let x ← advice a
    return #[("", Rust.mul x (Rust.sub x (.const 1)))]
  lookupAny "cubic table" q1 do
    let s2 ← query (.selector q2)
    let tv ← fixed t
    let x ← advice a
    let i ← query (.instance ⟨inst⟩ (-1))
    return #[(x, Rust.mul s2 (Rust.mul tv tv)), (i, .const 7)]
  batchedLookupAny "every row" none do
    let s3 ← query (.selector q3)
    let x ← advice a
    let y ← advice b 1
    let tb ← advice b (-1)
    return #[(#[Rust.mul s3 x, y, Rust.mul x y], tb)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def bool : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.region "table" ((List.range 5).flatMap fun r =>
      [.assignFixed ⟨0⟩ r (r + 2), .enableGate (lookupHandle (lk 0) 1) r, .assignAdvice ⟨1⟩ r witness]),
    .region "use" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .enableGate (lookupHandle (lk 0) 0) 0,
      .enableGate (cleanGate bool) 1, .enableGate (lookupHandle (lk 0) 0) 1, .assignAdvice ⟨1⟩ 2 witness]]

#guard source.validate.isOk && !(lk 0).owned && !(lk 1).owned
#guard (lk 0).degree 3 == 9 && (lk 1).degree 3 == 3 && source.degree == 9
#guard (lk 1).numChunks source.degree == 1

end LoweringFixtures.LookupAnyHighDegree
