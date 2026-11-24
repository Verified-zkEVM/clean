import LoweringFixtures.Common

/-! midnight-zk's vanilla PLONK gates (proofs/tests/plonk_api.rs:320-343): selector-free
`without_selector` polynomials on fixed coefficients at rotations next and prev, which Rust
enforces on every row (`RowGatesHold`), with equality on fixed, advice and instance columns
and an instance copy. -/
namespace LoweringFixtures.VanillaPlonk
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let d ← adviceColumn
  let e ← adviceColumn
  let sf ← fixedColumn
  let sa ← fixedColumn
  let sb ← fixedColumn
  let sc ← fixedColumn
  let sm ← fixedColumn
  let sp ← fixedColumn
  let p ← instanceColumn
  gateWithoutSelector "Combined add-mult" do
    let dn ← advice d 1
    let x ← advice a
    let f ← fixed sf
    let ep ← advice e (-1)
    let y ← advice b
    let z ← advice c
    let fa ← fixed sa
    let fb ← fixed sb
    let fc ← fixed sc
    let fm ← fixed sm
    return #[("", .add (Rust.sub (.add (.add (Rust.mul x fa) (Rust.mul y fb)) (Rust.mul (Rust.mul x y) fm))
      (Rust.mul z fc)) (Rust.mul f (Rust.mul dn ep)))]
  gateWithoutSelector "Public input" do
    let x ← advice a
    let pi ← query (.instance ⟨p⟩ 0)
    let fp ← fixed sp
    return #[("", Rust.mul fp (Rust.sub x pi))]
  enableEquality ⟨.fixed, sf⟩
  enableEquality ⟨.advice, e⟩
  enableEquality ⟨.advice, d⟩
  enableEquality ⟨.instance, p⟩
  enableEquality ⟨.fixed, sm⟩
  enableEquality ⟨.fixed, sa⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "public" [.assignAdvice ⟨4⟩ 0 witness, .assignFixed ⟨5⟩ 0 1],
    .constrainInstance (cell 0 0 .advice 4) ⟨0⟩ 0,
    .region "mul" [.assignAdvice ⟨4⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨2⟩ 1 witness, .assignAdvice ⟨3⟩ 2 witness,
      .assignFixed ⟨1⟩ 1 0, .assignFixed ⟨4⟩ 1 1, .assignFixed ⟨3⟩ 1 1, .assignFixed ⟨0⟩ 1 5,
      .constrainEqual (cell 1 0 .advice 4) (cell 1 2 .advice 3)]]

#guard source.errors.isEmpty && source.validate.isOk && source.gates.all (·.rows)

end LoweringFixtures.VanillaPlonk
