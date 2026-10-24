/-
`fast_witness_test`: fast witness generation, interpreted and compiled, against generation and
against Plonky3. Runs natively, since the packed-word accessors are C.
-/
module

public import Clean.Examples.FastWitness.Component
public import Clean.Examples.KeccakAir.FastKernel
public import Clean.Examples.KeccakAir.Test
public import CompPoly.Fields.Montgomery.Native32Bytes
meta import Clean.Examples.FastWitness.Component
meta import CompPoly.Fields.KoalaBear.Fast

@[expose] public section

namespace FastWitnessTest
open Air.Flat Air.Flat.FastWitness Montgomery.Native32 KeccakAir

abbrev p := KoalaBear.fieldSize
abbrev F := _root_.F p

fast_witness_kernel exampleKernel for KoalaBear.fieldSize :=
  compileSegments (FastWitnessExample.component (p := KoalaBear.fieldSize)) #[("seed", 1)]

/-- Rows of field elements as CompStark's chunks of packed rows: `2 ^ logChunks` chunks of
consecutive rows, each the `encode` of its values in Montgomery form (`rowChunks`). -/
def rowChunks (rows : Array (Array F)) (logChunks : ℕ) : Array ByteArray :=
  let size := rows.size / 2 ^ logChunks
  (Array.range (2 ^ logChunks)).map fun c =>
    CompPoly.PackedRepr.encode ((rows.extract (c * size) (c * size + size)).flatMap
      (·.map FastField.ofField))

def sameChunks (expected actual : Array ByteArray) : Bool :=
  expected.size == actual.size && (expected.zip actual).all fun (a, b) => a.data == b.data

/-- The trace of the generated table: each row's cells but the fixed and the window cells. -/
def generatedTrace {PublicIO : TypeMap} [ProvableType PublicIO] (ens : Ensemble F PublicIO)
    (publicInput : PublicIO F) (proverInput : ens.ProverInput F) :
    Except String (Array (Array F)) :=
  match WitnessGeneration.generate ens 1000 publicInput proverInput with
  | .error error => .error (toString error)
  | .ok witness => match witness.tables with
    | [table] =>
      let component := table.component
      let own := component.ownInputWidth
      .ok (table.table.toArray.map fun row => row.extract component.fixedWidth own ++
        row.extract (own + component.windowWidth) component.width)
    | _ => .error "expected one table"

/-- Packed words of field elements. -/
def wordsOf (values : Array F) : ByteArray :=
  CompPoly.PackedRepr.encode (values.map FastField.ofField)

/-! ### The example component -/

def seeds : Vector F 6 := #v[0, 1, 5, 12345, 2 ^ 30, 7]

def exampleChecks : Except String (List (String × Bool)) := do
  let expected ← generatedTrace (FastWitnessExample.ensemble (p := p)) () seeds
  let hints := #[("seed", 1, wordsOf seeds.toArray)]
  let changed := expected.modify 5 (·.modify 9 (· + 1))
  let detected := match segmentTrace (FastWitnessExample.component (p := p)) hints 0 with
    | .ok chunks => !sameChunks (rowChunks changed 0) chunks
    | .error _ => false
  return ("a changed cell is detected", detected) :: (List.range 3).flatMap fun logChunks =>
    [(s!"example interpreted, 2^{logChunks} chunks", match segmentTrace
        (FastWitnessExample.component (p := p)) hints logChunks with
      | .ok chunks => sameChunks (rowChunks expected logChunks) chunks
      | .error _ => false),
    (s!"example compiled, 2^{logChunks} chunks", match exampleKernel.trace #[wordsOf seeds.toArray]
        16 logChunks with
      | .ok chunks => sameChunks (rowChunks expected logChunks) chunks
      | .error _ => false)]

/-! ### Plonky3's Keccak AIR -/

/-- The prover input of the ensemble of `height` rows for `inputs`, padded with zero inputs. -/
def keccakProverInput (height : UInt64) (inputs : Array Trace.State) :
    (ensemble (p := p) height).ProverInput F :=
  let limbs := inputs.toList.flatMap preimageLimbs
  Vector.ofFn fun i => (limbs[i.val]?.getD 0 : F)

def keccakChecks : Except String (List (String × Bool)) := do
  -- one permutation and its padding
  let inputs := #[Test.input]
  let expected ← generatedTrace (ensemble (p := p) 32) () (keccakProverInput 32 inputs)
  let reference := Test.traceRows
  let checks := [("keccak generation is the transcribed trace", expected == reference)] ++
    (List.range 4).flatMap fun logChunks =>
      [(s!"keccak interpreted, 2^{logChunks} chunks", match fastTrace (p := p) inputs logChunks with
        | .ok chunks => sameChunks (rowChunks reference logChunks) chunks
        | .error _ => false),
      (s!"keccak compiled, 2^{logChunks} chunks", match koalaBearTrace inputs logChunks with
        | .ok chunks => sameChunks (rowChunks reference logChunks) chunks
        | .error _ => false)]
  -- 42 permutations: compiled and interpreted agree, in any number of chunks
  let many := (Array.range 42).map fun k =>
    Vector.ofFn fun i => Test.splitMix (k * 25 + i.val).toUInt64
  let some one := (fastTrace (p := p) many 0).toOption | throw "fastTrace failed"
  let joined := one.foldl (· ++ ·) ByteArray.empty
  let checks := checks ++ [0, 3, 6].map fun logChunks =>
    (s!"keccak 2^10 rows, compiled in 2^{logChunks} chunks",
      match koalaBearTrace many logChunks with
      | .ok chunks => (chunks.foldl (· ++ ·) ByteArray.empty).data == joined.data
      | .error _ => false)
  -- Plonky3's trace of three permutations
  return checks ++ [
    ("keccak compiled is Plonky3's", Test.rowHashes (koalaBearTrace Test.katInputs 2) ==
      Test.plonky3RowHashes),
    ("keccak interpreted is Plonky3's", Test.rowHashes (fastTrace (p := p) Test.katInputs 2) ==
      Test.plonky3RowHashes)]

end FastWitnessTest

open FastWitnessTest in
public def main : IO UInt32 := do
  let mut failed := false
  for checks in [exampleChecks, keccakChecks] do
    match checks with
    | .error message => IO.println s!"error: {message}"; failed := true
    | .ok checks =>
      for (name, ok) in checks do
        IO.println s!"{if ok then "ok" else "FAILED"}: {name}"
        failed := failed || !ok
  return if failed then 1 else 0
