import LoweringFixtures.Common

/-! A `Some(qc)` batch of three degree-3 tuples has no chunk capacity at the degree without
lookups (3), so its helper term is 1, but its own accumulator lifts the CS degree to 5, where it
chunks one tuple per helper. A `None` batch of five degree-2 tuples against `f(1)` chunks two per
helper at the final degree, and an empty `Some(qc)` batch has none: 6 helpers in the blinding. -/
namespace LoweringFixtures.LookupLift
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let t ← fixedColumn
  let f ← fixedColumn
  let qc ← selector false
  let qs ← selector
  gate "mul" qs do
    let x ← advice a
    let y ← advice b
    let z ← advice c
    return #[("", Rust.sub (Rust.mul x y) z)]
  batchedLookup "lift" qc do
    let x ← advice a
    let y ← advice b
    let z ← advice c
    return #[(#[Rust.mul (Rust.mul x y) z, Rust.mul (Rust.mul y y) x, Rust.mul (Rust.mul z z) z], t)]
  batchedLookupAny "none five" none do
    let x ← advice a
    let y ← advice b
    let tf ← fixed f 1
    return #[(#[Rust.mul x y, Rust.mul x x, Rust.mul y y, Rust.mul y x, Rust.mul x (.const 2)], tf)]
  batchedLookup "zero" qc do return #[(#[], t)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def mul : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨2⟩ 0 witness,
      .enableGate (cleanGate mul) 0,
      .enableLookup (cleanLookup (lk 0) 0) [⟨0, false⟩] 1, .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] 1,
      .enableLookup (cleanLookup (lk 0) 2) [⟨0, false⟩] 1, .assignAdvice ⟨0⟩ 1 witness,
      .assignFixed ⟨1⟩ 2 7]]

#guard source.validate.isOk && (lk 0).owned && !(lk 2).owned
#guard source.degree == 5 && (source.lookups.map (·.numChunks source.degree)) == #[3, 3, 0] &&
  (lk 0).chunkCapacity 3 == 0 && source.blindingFactors == 12

end LoweringFixtures.LookupLift
