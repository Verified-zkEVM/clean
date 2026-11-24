import LoweringFixtures.Common

/-! `without_selector` bodies on a simple selector that Rust's operators fold: `(q * x) * 0`
pins `Constant(0)`, `q * 1` pins the bare selector, `1 * (f * q)`, a doubly negated product and a
zero-scaled product; fixed rotations -3, 16 = n and -17, the 16 shared with a `with_selector`
gate on a complex selector that queries advice at -1, both enabled in two regions. -/
namespace LoweringFixtures.RawGateFolds
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let qs ← selector
  let qc ← selector false
  gateWithoutSelector "folds" do
    let x ← advice a
    let up ← fixed f (-3)
    let wrap ← fixed f 16
    let under ← fixed f (-17)
    let q := querySelector qs
    return #[("zero", Rust.mul (Rust.mul q x) (.const 0)),
      ("one", Rust.mul q (.const 1)),
      ("left one", Rust.mul (.const 1) (Rust.mul up q)),
      ("double neg", Rust.neg (Rust.neg (Rust.mul wrap q))),
      ("scaled", Rust.scale (Rust.mul q under) 0),
      ("deep", Rust.mul x (Rust.mul up (Rust.mul wrap (Rust.mul q under))))]
  gate "plain" qc do
    let w ← fixed f 16
    let x ← advice a (-1)
    return #[("w", Rust.sub w x)]

def source : CS := (configure.run {}).2

def folds : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def plain : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "first" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate folds) 0,
      .enableGate (cleanGate plain) 0, .assignFixed ⟨0⟩ 0 7],
    .region "pad" [.assignFixed ⟨0⟩ 0 1, .assignFixed ⟨0⟩ 3 2],
    .region "last" [.enableGate (cleanGate plain) 2, .enableGate (cleanGate folds) 2,
      .assignAdvice ⟨0⟩ 2 witness]]

private def pinned : String := source.finalize.pinnedDebug
private def count (part : String) : Nat := (pinned.splitOn part).length - 1

#guard source.gates.map (·.raw) == #[true, false]
#guard source.fixedQueries == #[(0, -3), (0, 16), (0, -17)]
#guard count ("Constant(" ++ scalarDebug 0 ++ ")") ≥ 1

end LoweringFixtures.RawGateFolds
