import LoweringFixtures.Common

/-! Selectors that fold out of lookups before Rust sees them: `batched_lookup(Some(q))` of
`x + qc * 0` (Rust's lookup is selector-free, Lean's is not owned), `(qs * 0) * x(1)`, a constant
input next to an advice one, and a `lookup_any(None)` whose table is `(qs scaled by 0) * 0 + t`,
which folds to `t` (`Mul<F>` does not fold, `*` by `Constant(0)` does). `qc` is never enabled. -/
namespace LoweringFixtures.LookupFoldedSelectors
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let u ← fixedColumn
  let qs ← selector
  let q ← selector false
  let qc ← selector false
  gate "s" qs do
    let x ← advice a
    return #[("", Rust.sub (Rust.mul x x) x)]
  batchedLookup "folded" q do
    let x ← advice a
    let y ← advice a 1
    return #[(#[.add x (Rust.mul (querySelector qc) (.const 0)), .const 3], t),
      (#[Rust.mul (Rust.mul (querySelector qs) (.const 0)) y, x], u)]
  lookupAny "scaled" none do
    let x ← advice a
    let tv ← fixed t
    return #[(x, .add (Rust.mul (Rust.scale (querySelector qs) 0) (.const 0)) tv)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def s : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 3], .loadTable ⟨⟨1⟩⟩ [0, 3],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .enableGate (lookupHandle (lk 0) 1) 0,
      .enableGate (cleanGate s) 1, .enableGate (lookupHandle (lk 0) 1) 1]]

#guard source.validate.isOk && !(lk 0).owned && !(lk 1).owned
#guard (lk 0).handles.map (·.selector.index) == [1, 2, 0] && (lk 0).inputDegree == 1

end LoweringFixtures.LookupFoldedSelectors
