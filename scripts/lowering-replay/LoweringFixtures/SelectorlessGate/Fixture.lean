import LoweringFixtures.Common

/-! Gates with no selector at all, which Rust's vanishing argument enforces on every row of the
domain: midnight-zk's verifier-gadget test gate `cur * next` on one fixed column
(circuits/src/verifier/verifier_gadget.rs:917-922) and the fixed-coefficient PLONK gate of
proofs/benches/plonk.rs:216, as `rows` gates. -/
namespace LoweringFixtures.SelectorlessGate
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let f ← fixedColumn
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let sa ← fixedColumn
  let sb ← fixedColumn
  let sc ← fixedColumn
  let sm ← fixedColumn
  gateWithoutSelector "fixed column at two rotations" do
    let cur ← fixed f
    let next ← fixed f 1
    return #[("", Rust.mul cur next)]
  gateWithoutSelector "Combined add-mult" do
    let x ← advice a
    let y ← advice b
    let z ← advice c
    let fa ← fixed sa
    let fb ← fixed sb
    let fc ← fixed sc
    let fm ← fixed sm
    return #[("", Rust.sub (.add (.add (Rust.mul x fa) (Rust.mul y fb)) (Rust.mul (Rust.mul x y) fm))
      (Rust.mul z fc))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
    .assignAdvice ⟨2⟩ 0 witness, .assignFixed ⟨1⟩ 0 1, .assignFixed ⟨3⟩ 0 1]]

end LoweringFixtures.SelectorlessGate
