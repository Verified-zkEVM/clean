import LoweringFixtures.Common

/-! One complex selector owning a `without_selector` gate (selector left, right and nested, a
difference of selected terms, `Negated(Scaled(..))`), a `with_selector` gate, an additive gate and
a two-wide lookup whose inputs query a fixed column at rotations 2 and -1; a simple
selector owning a raw gate and a plain gate; instance at -1 in the raw body; enables interleaved
with assignments, the complex one at region rows 0 and 2. -/
namespace LoweringFixtures.RawGateComplexMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let i ← instanceColumn
  let qc ← selector false
  let qs ← selector
  batchedLookup "shared" qc do
    let x ← advice a
    let fr ← fixed f 2
    return #[(#[x, fr], t)]
  gateWithoutSelector "mixed" do
    let fm ← fixed f (-1)
    let x ← advice a
    let y ← advice b 1
    let p ← query (.instance ⟨i⟩ (-1))
    let q := querySelector qc
    return #[("difference", Rust.sub (Rust.mul q x) (Rust.mul (Rust.mul x q) y)),
      ("negscale", .add (Rust.neg (Rust.scale (Rust.mul fm q) 3)) (Rust.mul y (Rust.mul q fm))),
      ("instance", Rust.mul (Rust.mul p y) q)]
  gate "with" qc do
    let x ← advice a
    let fr ← fixed f 2
    return #[("with", Rust.sub x fr)]
  gateWithoutSelector "simple raw" do
    let g ← fixed f 5
    let y ← advice b 1
    return #[("s", Rust.mul g (Rust.mul (querySelector qs) y))]
  gate "simple plain" qs do
    let y ← advice b
    return #[("y", y)]
  enableEquality ⟨.instance, i⟩

def trash : GateSpec :=
  let x : E := .var (.advice ⟨0⟩ 0)
  ⟨"trash", ⟨0, false⟩, #[.advice ⟨0⟩ 0], #[("boolean", .add (.mul x x) (.mul (.const (-1)) x))], false, false⟩

def source : CS :=
  let s := (configure.run {}).2
  { s with trashcans := #[trash] }

def spec (n : Nat) : GateSpec := source.gates[n]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def shared : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def complexAt (row : Nat) : RegionOperations F :=
  [.enableGate (cleanGate (spec 0)) row, .enableLookup (cleanLookup shared 0) [⟨0, false⟩] row,
   .enableGate (cleanGate trash) row, .enableLookup (cleanLookup shared 1) [⟨0, false⟩] row,
   .enableGate (cleanGate (spec 1)) row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨1⟩⟩ [0, 1, 2],
    .region "main" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness] ++ complexAt 0 ++
      [.assignFixed ⟨0⟩ 2 4, .enableGate (cleanGate (spec 3)) 1, .enableGate (cleanGate (spec 2)) 1,
       .assignAdvice ⟨0⟩ 2 witness] ++ complexAt 2 ++ [.assignAdvice ⟨1⟩ 3 witness])]

#guard source.fixedQueries == #[(0, 2), (1, 0), (0, -1), (0, 5)]

end LoweringFixtures.RawGateComplexMix
