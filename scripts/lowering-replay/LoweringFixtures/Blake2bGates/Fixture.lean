import LoweringFixtures.Common

/-! blake2b_halo2@257ae18's `Blake2bChip::configure` without XOR: constants and equality columns,
the limb decomposition, rotate-63, negate and addition-mod-2^64 gates as
`Constraints::without_selector` polynomials with the complex selector inside, and the limb
range lookup; a stream modelled on `generate_addition_rows_from_cells` followed by a rotation and
a negation, after an IV word assigned from a constant. -/
namespace LoweringFixtures.Blake2bGates
open Halo2 Midnight Midnight.Keygen

def two64 : F := ((2 ^ 64 : ℕ) : F)

def configure : ConfigM Unit := do
  let constants ← fixedColumn
  let full ← adviceColumn
  let limbs ← (List.range 8).mapM fun _ => adviceColumn
  enableConstant constants
  enableEquality ⟨.advice, full⟩
  for l in limbs do enableEquality ⟨.advice, l⟩
  let qDecompose ← selector false
  gateWithoutSelector "decompose in 8 bit words" do
    let q := querySelector qDecompose
    let n ← advice full
    let ls ← limbs.mapM fun l => advice l
    let body := (ls.zip (List.range 8)).drop 1 |>.foldl
      (fun acc (l, i) => Rust.sub acc (Rust.mul l (.const ((2 ^ (8 * i) : ℕ) : F))))
      (Rust.sub n (ls.headD (.const 0)))
    return #[("", Rust.mul q body)]
  let qRange ← selector false
  let tRange ← fixedColumn
  batchedLookup "lookup limbs" qRange do
    let ls ← limbs.mapM fun l => advice l
    return #[(ls.toArray, tRange)]
  let qRot ← selector false
  gateWithoutSelector "rotate right 63" do
    let q := querySelector qRot
    let input ← advice full (-1)
    let output ← advice full
    let a := Rust.sub (Rust.mul (.const 2) input) output
    let b := Rust.sub (Rust.sub (Rust.mul (.const 2) input) output) (.const (two64 - 1))
    return #[("", Rust.mul (Rust.mul q a) b)]
  let qNeg ← selector false
  gateWithoutSelector "negate" do
    let q := querySelector qNeg
    let value ← advice full
    let notValue ← advice full 1
    return #[("", Rust.mul q (Rust.sub (Rust.sub (.const (two64 - 1)) value) notValue))]
  let qAdd ← selector false
  gateWithoutSelector "sum mod 2 ^ 64" do
    let q := querySelector qAdd
    let x ← advice full
    let y ← advice full 1
    let r ← advice full 2
    let carry ← advice (limbs.headD 0) 1
    return #[("", Rust.mul q (.add (Rust.sub (Rust.sub r x) y) (Rust.mul carry (.const two64)))),
      ("", Rust.mul (Rust.mul q carry) (Rust.sub (.const 1) carry))]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

/-- `generate_row_from_word_value` with the decomposition and range enables. -/
def wordRow (row : Nat) : RegionOperations F :=
  (List.range 9).map (fun c => .assignAdvice ⟨c⟩ row witness) ++
  [.enableGate (cleanGate (spec 0)) row] ++
  (List.range 8).map fun i => .enableLookup (cleanLookup lk i) [⟨1, false⟩] row

def fixture : Export.Replay.Fixture where
  source := source
  k := 9
  ops := [.loadTable ⟨⟨1⟩⟩ ((List.range 256).map fun i => (i : F)),
    .region "iv" ((assignAdviceFromConstant ⟨0⟩ 0 0x6a09e667f3bcc908).operations 0),
    .region "add" ([.enableGate (cleanGate (spec 3)) 0, .assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 0 0 .advice 0) (cell 1 0 .advice 0),
      .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness] ++ wordRow 2 ++
      [.enableGate (cleanGate (spec 1)) 3] ++ wordRow 3 ++
      [.enableGate (cleanGate (spec 2)) 4, .assignAdvice ⟨0⟩ 4 witness, .assignAdvice ⟨0⟩ 5 witness])]

private def pinned : String := source.finalize.pinnedDebug
private def count (part : String) : Nat := (pinned.splitOn part).length - 1

-- rotate-63 and the carry check are `(q * a) * b`; the other three are `q * a`.
#guard count "Product(Product(Fixed { query_index: " == 2
#guard source.gates.map (·.raw) == #[true, true, true, true]

end LoweringFixtures.Blake2bGates
