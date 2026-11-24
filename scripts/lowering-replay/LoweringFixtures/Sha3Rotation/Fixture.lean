import LoweringFixtures.Common

/-! sha3 packed_chip decomposition (sha3-circuit@1a3ef7d decomposition/gates.rs:16-110) with
three limbs: the spread lookup, the linear-combination gate querying each coefficient column at
`cur` and the rotation gate querying the same columns at `next`, each interleaved with its
limb queries and folded from `Constant(0)` as the closures do. -/
namespace LoweringFixtures.Sha3Rotation
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let f0 ← fixedColumn
  let f1 ← fixedColumn
  let f2 ← fixedColumn
  let a0 ← adviceColumn
  let a1 ← adviceColumn
  let a2 ← adviceColumn
  let res ← adviceColumn
  let tSpread ← fixedColumn
  let qDc ← selector
  let qRotate ← selector
  let qSpread ← selector false
  let pairs := [(a0, f0), (a1, f1), (a2, f2)]
  batchedLookup "decomposition lookup" qSpread do
    let x ← advice a0
    let y ← advice a1
    let z ← advice a2
    return #[(#[x, y, z], tSpread)]
  gate "linear combination constraint" qDc do
    let mut acc : E := .const 0
    for (l, f) in pairs do
      let coef ← fixed f
      let limb ← advice l
      acc := .add acc (Rust.mul coef limb)
    let r ← advice res
    return #[("", Rust.sub r acc)]
  gate "rotation constraint" qRotate do
    let mut acc : E := .const 0
    for (l, f) in pairs do
      let coef ← fixed f 1
      let limb ← advice l
      acc := .add acc (Rust.mul coef limb)
    let r ← advice res 1
    return #[("", Rust.sub r acc)]

def source : CS := (configure.run {}).2

def lc : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def rot : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def spread : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def limbRow (row : Nat) : RegionOperations F :=
  [.assignAdvice ⟨0⟩ row witness, .assignAdvice ⟨1⟩ row witness, .assignAdvice ⟨2⟩ row witness,
   .assignAdvice ⟨3⟩ row witness] ++
  (List.range 3).map fun i => .enableLookup (cleanLookup spread i) [⟨2, false⟩] row

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨3⟩⟩ [0, 1, 4, 5, 16, 17, 20, 21],
    .region "decompose" (limbRow 0 ++ [.assignFixed ⟨0⟩ 0 1, .assignFixed ⟨1⟩ 0 256,
      .assignFixed ⟨2⟩ 0 65536, .enableGate (cleanGate lc) 0, .assignFixed ⟨0⟩ 1 65536,
      .assignFixed ⟨1⟩ 1 1, .assignFixed ⟨2⟩ 1 256, .enableGate (cleanGate rot) 0,
      .assignAdvice ⟨3⟩ 1 witness]),
    .region "rotate" (limbRow 0 ++ limbRow 1 ++ [.enableGate (cleanGate rot) 0, .enableGate (cleanGate rot) 1,
      .assignFixed ⟨2⟩ 2 3, .enableGate (cleanGate lc) 1, .assignFixed ⟨0⟩ 1 2])]

-- Fixed queries in closure call order: the three `cur` coefficients, then the three `next`.
#guard source.fixedQueries == #[(3, 0), (0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)]

end LoweringFixtures.Sha3Rotation
