import LoweringFixtures.Common

/-! Enables `Canonical.ops` must read as Rust does: a lookup enable with no selectors past the
usable rows (Rust enables nothing), an unused simple selector enabled through a lookup op, one
lookup op naming `q` twice and a simple selector, `q2` used only as a rows gate's non-owner atom,
the rows gate's owner handle, an unused complex selector through an unconfigured gate, and `q`
enabled both through its gate and its lookup on one row. -/
namespace LoweringFixtures.CanonicalEnableEdges
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  let q1 ← selector false
  let q2 ← selector false
  let qs ← selector
  let _qus ← selector
  let _quc ← selector false
  gate "g" q do
    let x ← advice a
    return #[("g", Rust.mul x x)]
  batchedLookup "own" q do
    let x ← advice a
    return #[(#[x], t)]
  gateWithoutSelector "rows" do
    let x ← advice a
    let y ← advice b
    return #[("", .add (Rust.mul (querySelector q1) x) (Rust.mul (querySelector q2) y))]
  gate "s" qs do
    let y ← advice b
    return #[("s", Rust.mul y y)]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def rowsHandle (q : Nat) : Gate F :=
  if h : (spec 1).valid then ((spec 1).rowsHandles h).find? (·.selector.index == q) |>.getD (cleanGate (spec 1))
  else cleanGate (spec 1)

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" ([0, 1, 2, 3, 4, 5].map (.assignAdvice ⟨0⟩ · witness) ++
      [0, 1, 2, 3, 4, 5].map (.assignAdvice ⟨1⟩ · witness) ++
      [.enableLookup (cleanLookup lk) [] 40,
       .enableLookup (cleanLookup lk) [⟨4, true⟩] 0,
       .enableLookup (cleanLookup lk) [⟨0, false⟩, ⟨0, false⟩, ⟨3, true⟩] 1,
       .enableGate (rowsHandle 2) 2,
       .enableGate (cleanGate (spec 1)) 3,
       .enableGate (cleanGate ⟨"u", ⟨5, false⟩, #[], #[], false, false⟩) 4,
       .enableGate (cleanGate (spec 0)) 5, .enableLookup (cleanLookup lk) [⟨0, false⟩] 5])]

#guard source.validate.isOk && source.unusedSelectors == [4, 5]
#guard source.gates.map (·.rows) == #[false, true, false] && lk.owned
-- Unused selectors keep their kind in the export (`selectorKinds`).
#guard (List.range 6).map source.selectorSimple == [false, false, false, true, true, false]

end LoweringFixtures.CanonicalEnableEdges
