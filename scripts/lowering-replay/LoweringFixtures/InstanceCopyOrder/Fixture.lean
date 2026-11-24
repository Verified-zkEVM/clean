import LoweringFixtures.Common

/-! In-region instance copies Rust's `assign_advice_from_instance` produces: a copy after the gate's
enable, one cell copied to two instance rows, an equality from that cell back into the first region,
then a layouter-level copy; the gate folds `1 * (a * b) - a[1]`. `first` puts the first region's
copy before its assignments. -/
namespace LoweringFixtures.InstanceCopyOrder
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let inst ← instanceColumn
  let q ← selector
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, b⟩
  gate "mul" q do
    let x ← advice a
    let y ← advice b
    let z ← advice a 1
    return #[("mul", Rust.sub (Rust.mul (.const 1) (x * y)) z)]

def source : CS := (configure.run {}).2

def mulGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def late (first : Bool) : RegionOperations F :=
  let copy : RegionOperation F := .constrainInstance (cell 0 2 .advice 0) ⟨0⟩ 0
  let body := [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .enableGate (cleanGate mulGate) 0, .assignAdvice ⟨0⟩ 2 witness]
  if first then copy :: body else body ++ [copy]

def ops (first : Bool := false) : Operations F := [
  .region "late" (late first),
  .region "twice" [
    .assignAdvice ⟨1⟩ 0 witness,
    .constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 1,
    .constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 2,
    .constrainEqual (cell 1 0 .advice 1) (cell 0 2 .advice 0)],
  .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 3]

def fixture : Export.Replay.Fixture := { source, ops := ops, k := 5 }

end LoweringFixtures.InstanceCopyOrder
