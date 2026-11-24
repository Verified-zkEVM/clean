import LoweringFixtures.Common

/-! Bodies using queries their closure did not make: an expression kept from an earlier closure
(`a`, `b(1)`) and `Column::cur()`-style queries with no index (`c(-1)`, `b(2)`, the instance, `a(3)`,
`c(1)`, `f(1)`, `a(-2)`). `create_gate` and `batched_lookup_any` register the new ones by walking
the folded trees (circuit.rs:1913-1919, 1757-1771), so `a` under `0 *` is not visited and a bare
table column is queried before the inputs. A trash body is not walked; its kept `b(1)` has its index.
The replay builds every walked atom without an index, so Rust's walk does the registering. -/
namespace LoweringFixtures.WalkedQueries
open Halo2 Midnight Midnight.Keygen

def adv (c : Nat) (r : Int) : E := .var (.advice ⟨c⟩ r)

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let i ← instanceColumn
  let qs ← selector
  let q ← selector false
  gate "first" q do
    let x ← advice a
    let y ← advice b 1
    return #[("", .add x (Rust.neg y))]
  gate "walk" q do
    let z ← advice b
    return #[("one", Rust.mul (adv c (-1)) z), ("two", .add (adv a 0) (adv b 2)),
      ("instance", .add (Rust.mul (.const 0) (adv a 0)) (.var (.instance ⟨i⟩ 0)))]
  gateWithoutSelector "raw" do
    return #[("", Rust.mul (querySelector qs) (adv a 3))]
  lookupAny "any" none do
    return #[(adv c 1, .var (.fixed ⟨f⟩ 1))]
  batchedLookup "bare" q do
    return #[(#[adv a (-2)], t)]
  additiveGate "trash" q do
    let x ← advice a
    return #[("", Rust.sub x (adv b 1))]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" ((List.range 6).flatMap (fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness,
      .assignAdvice ⟨2⟩ r witness]) ++ [.enableGate (cleanGate (spec 0)) 2, .enableGate (cleanGate (spec 2)) 2]),
    .loadTable ⟨⟨1⟩⟩ [1, 2, 3]]

#guard source.adviceQueries == #[(0, 0), (1, 1), (1, 0), (2, -1), (1, 2), (0, 3), (2, 1), (0, -2)]
#guard source.fixedQueries == #[(0, 1), (1, 0)]
#guard source.instanceQueries == #[(0, 0)]
#guard source.gateClosures.map (·.1) == #["first", "walk", "raw", "trash"]

end LoweringFixtures.WalkedQueries
