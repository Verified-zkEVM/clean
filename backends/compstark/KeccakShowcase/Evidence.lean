module

public import KeccakShowcase.Air
public import KeccakShowcase.Kernel
public import KeccakShowcase.Json
public import Clean.Examples.KeccakAir.FastKernel
public import CompStark.Stark.Fingerprint
public import CompStark.Stark.Fast
public import CompStark.KoalaBear.Fast
public import CompStark.Plonky3.Prover
public import CompStark.Mont32.Json
public import CompStark.KoalaBear.Poseidon2
public import CompPoly.Univariate.NTTFast.Packed.Instances

/-! # The keccak-air showcase: evidence and benchmark

The commands of `lake exe keccak_showcase`, on the Poseidon2 instances `I` of Plonky3's example
(`KeccakShowcase.Main`).

`lake exe keccak_showcase kat` checks the known answers CompStark's tests keep from Plonky3: the
fingerprint, the trace of five permutations, and the proof of Plonky3's example on `2 ^ 6` rows.

`lake exe keccak_showcase check L RUST` checks, on `2 ^ L` rows, that the CompStark AIR of Clean's
keccak-air component (`toAir`) is Plonky3's `KeccakAir`, against Plonky3's side `RUST` (the binary
of `rust/`, Plonky3 `a4982ec`):

* fingerprint: the AIR's fingerprint report and digest are those of Plonky3's `KeccakAir`
  (CompStark's `tests/data/fingerprint/keccak_4.json`, from Plonky3's symbolic constraints);
* trace: Clean's fast trace (`KeccakAir.koalaBearTrace`) is Plonky3's `generate_trace_rows` on the
  example's inputs, row by row;
* the example's configuration (caps of height 3, the example's Poseidon2 constants, FRI with
  arity up to 8 and 87 queries): CompStark's fast prover, from the Clean AIR and the Clean trace,
  produces Plonky3's proof byte for byte, and CompStark's verifier accepts Plonky3's proof;
* the proven configuration of the end-to-end theorem (`keccak_soundness_ro`, the example's with
  `188` queries and `2`, `24` and `12` bits of grinding before `ζ`, the batching challenge and each
  fold): Plonky3's verifier accepts CompStark's proof and rejects it with an opened value
  changed, CompStark's verifier accepts Plonky3's proof, and the two are byte for byte the same.

`lake exe keccak_showcase bench CONFIG L REPS` times trace generation, the proof, both together
and the proof's verification by CompStark's fast verifier (`verifyFast`, Plonky3's verifier by
`verifyFast_eq`) in Lean on `2 ^ L` rows, `CONFIG` `example` or `proven`; `rust/`'s `bench` times
Plonky3's.
-/

@[expose] public section

namespace KeccakShowcase
open CompStark CompStark.Stark CleanCompStark

/-- The configuration of Plonky3's example `prove_prime_field_31`, `87` queries
(`CleanCompStark.KeccakShowcase.params`). -/
def exampleParams : Fri.Params := CleanCompStark.KeccakShowcase.params 87

/-- The configuration of `keccak_soundness_ro`, the example's with `203` queries. -/
def provenParams : Fri.Params := CleanCompStark.KeccakShowcase.params 203

/-- The configurations by name. -/
def params : String → IO Fri.Params
  | "example" => pure exampleParams
  | "proven" => pure provenParams
  | name => throw (IO.userError s!"unknown configuration {name}: example or proven")

/-- The Clean trace of the inputs, in row chunks of CompStark's fast prover. -/
def trace (logN : ℕ) (inputs : Array KeccakAir.State) : Except String (Array ByteArray) :=
  KeccakAir.koalaBearTrace inputs (min logN 6)

variable (I : CompStark.KoalaBear.Instances)

/-- CompStark's fast prover with the Poseidon2 instances `I`. -/
def prove (P : Fri.Params) (logN : ℕ) (chunks : Array ByteArray) : Proof F EF :=
  let A := air logN
  let B := I.backendFor [QuotientKernel.kernel] P.logBlowup [(logN, A.logQuotientChunks logN)]
  proveWith B P A logN chunks []

/-- CompStark's verifier with the Poseidon2 instances `I`. -/
def verifyProof (P : Fri.Params) (logN : ℕ) (proof : Proof F EF) : Except String Unit :=
  letI := I.field
  let A := air logN
  verify P A (setup P A logN) proof []

/-- Run Plonky3's side, single-threaded so that its grinding witnesses are the smallest. -/
def rust (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := bin, args, env := #[("RAYON_NUM_THREADS", some "1")] }
  unless out.exitCode = 0 do
    throw (IO.userError s!"{bin} {" ".intercalate args.toList} failed:\n{out.stdout}{out.stderr}")
  return out.stdout

def readInputs (file : String) : IO (Array KeccakAir.State) := do
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.filter (· ≠ "")
  lines.toArray.mapM fun line => do
    let lanes := (line.splitOn " ").toArray.map (·.toNat!.toUInt64)
    if h : lanes.size = 25 then return ⟨lanes, h⟩
    else throw (IO.userError s!"an input of {lanes.size} lanes")

/-- The FNV-1a hash of the canonical values of every row of a trace in row chunks. -/
def rowHashes (chunks : Array ByteArray) : Array UInt64 := Id.run do
  let w := traceWidth (CleanCompStark.KeccakAir.component 0)
  let mut out := #[]
  for chunk in chunks do
    for r in [0:chunk.size / (4 * w)] do
      let mut hash : UInt64 := 0xcbf29ce484222325
      for c in [0:w] do
        let word := chunk.getUInt32LE! (4 * (r * w + c))
        let value : UInt64 := if h : word.toNat < _root_.KoalaBear.fieldSize then
          (Montgomery.Native32.FastField.toUInt32 (⟨word, h⟩ : F)).toUInt64 else 0
        hash := (hash ^^^ value) * 0x100000001b3
      out := out.push hash
  return out

/-- A proof from Plonky3's JSON. -/
def parseProof (text : String) : IO (Proof F EF) :=
  IO.ofExcept (Json.parse (p := _root_.KoalaBear.fieldSize) text)

/-- The first line where two texts differ. -/
def firstDifference (a b : String) : Option (ℕ × String × String) :=
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  ((la.zip lb).zipIdx.find? fun ((x, y), _) => x != y).map (fun ((x, y), i) => (i + 1, x, y)) <|>
    if la.length = lb.length then none else some (min la.length lb.length, "", "")

/-- The quotient kernel's constraints are the AIR's on `2 ^ logN` rows and its code is their
program, so that the fast backend runs it. -/
def kernelApplies (logN : ℕ) : IO Unit := do
  let K := QuotientKernel.kernel
  unless K.kernel.code == K.prog.code && decide (K.cs = (air logN).constraints) do
    throw (IO.userError s!"the quotient kernel is not the AIR's program on 2^{logN} rows")
  IO.println s!"quotient kernel: the {K.kernel.code.size} instructions of the generated kernel \
    are the program of the AIR's constraints on 2^{logN} rows"

/-- CompStark's known answers from Plonky3. -/
def data : String := ".lake/packages/CompStark/tests/data"

/-- The AIR's fingerprint is Plonky3's `KeccakAir`'s. -/
def fingerprint : IO Unit := do
  let expected ← IO.FS.readFile s!"{data}/fingerprint/keccak_4.json"
  let (digest, report) := (air 4).fingerprint EF 4
  if let some (line, ours, theirs) := firstDifference report expected then
    throw (IO.userError
      s!"fingerprint differs at line {line}:\n  clean   {ours}\n  plonky3 {theirs}")
  IO.println s!"fingerprint: the {(air 4).constraints.length} constraints of the Clean AIR are \
    Plonky3's KeccakAir's (digest {digest.toList.map (·.1)})"

/-- The known answers of CompStark's tests, without Plonky3 at hand: the fingerprint, Plonky3's
trace of five permutations and a truncated padding one (each row's Poseidon2 digest), and the
proof of Plonky3's example on `2 ^ 6` rows. -/
def kat : IO Unit := do
  fingerprint
  kernelApplies 6
  let expected := (← IO.FS.readFile s!"{data}/keccak_trace_5.txt").splitOn "\n" |>.filter (· ≠ "")
  let inputs : Array KeccakAir.State := (Array.range 5).map fun k =>
    Vector.ofFn fun i => (25 * k + i.val + 1).toUInt64 * 0x9e3779b97f4a7c15
  let chunks ← IO.ofExcept (trace 7 inputs)
  let words := chunks.foldl (· ++ ·) .empty
  let w := (air 7).width
  unless words.size = 4 * w * 128 ∧ expected.length = 128 do
    throw (IO.userError s!"trace: {words.size / (4 * w)} rows")
  for (line, r) in expected.zipIdx do
    let row : List F := (List.range w).map fun j =>
      CompPoly.CPolynomial.NTTFast.Packed.ofWord _
        (CompPoly.CPolynomial.NTTFast.Packed.Native.read words (r * w + j))
    let digest := (Hash.Poseidon2.hash F row).toList.map
      fun x => toString (CompPoly.CanonicalNat.toNat x)
    unless " ".intercalate digest = line do
      throw (IO.userError s!"trace differs from Plonky3's at row {r}")
  IO.println "trace: the 128 rows of Clean's fast trace of 5 permutations are Plonky3's"
  let chunks ← IO.ofExcept (trace 6 (← readInputs s!"{data}/keccak_example_6_inputs.txt"))
  let theirsText ← IO.FS.readFile s!"{data}/keccak_example_6.json"
  let theirsProof ← parseProof theirsText
  let oursProof := prove I exampleParams 6 chunks
  unless oursProof == theirsProof ∧ Json.proof oursProof == theirsText do
    throw (IO.userError "example: the proof differs from Plonky3's")
  IO.ofExcept (verifyProof I exampleParams 6 theirsProof)
  IO.println "example: CompStark's proof from the Clean AIR and trace is Plonky3's byte for byte, \
    and CompStark's verifier accepts Plonky3's proof"

def check (logN : ℕ) (bin : String) : IO Unit := do
  let dir := ".lake/showcase"
  IO.FS.createDirAll dir
  fingerprint
  kernelApplies logN
  -- The trace is Plonky3's.
  let inputsFile := s!"{dir}/inputs_{logN}.txt"
  let _ ← rust bin #["inputs", toString logN, inputsFile]
  let inputs ← readInputs inputsFile
  let chunks ← IO.ofExcept (trace logN inputs)
  let ours := rowHashes chunks
  let theirs := ((← rust bin #["trace", toString logN]).splitOn "\n").filter (· ≠ "")
  unless ours.size = 2 ^ logN ∧ theirs.length = 2 ^ logN do
    throw (IO.userError s!"trace: {ours.size} rows, Plonky3 {theirs.length}")
  for (h, i) in ours.zipIdx do
    let hex := String.ofList (Nat.toDigits 16 h.toNat)
    unless "".pushn '0' (16 - hex.length) ++ hex = theirs[i]! do
      throw (IO.userError s!"trace: row {i} differs from Plonky3's")
  IO.println s!"trace: the {2 ^ logN} rows of Clean's fast trace of {inputs.size} permutations \
    are Plonky3's generate_trace_rows"
  -- Plonky3's example: the same proof.
  let exampleFile := s!"{dir}/example_{logN}.json"
  let _ ← rust bin #["prove", "example", toString logN, exampleFile]
  let theirsText ← IO.FS.readFile exampleFile
  let theirsProof ← parseProof theirsText
  let oursProof := prove I exampleParams logN chunks
  unless oursProof == theirsProof ∧ Json.proof oursProof == theirsText do
    throw (IO.userError "example: the proof differs from Plonky3's")
  IO.ofExcept (verifyProof I exampleParams logN theirsProof)
  IO.println s!"example: CompStark's proof from the Clean AIR and trace is Plonky3's byte for \
    byte ({theirsText.length} bytes of JSON), and CompStark's verifier accepts Plonky3's proof"
  -- The proven configuration: each side accepts the other's proof.
  let P := provenParams
  let oursProof := prove I P logN chunks
  let oursFile := s!"{dir}/proven_{logN}_lean.json"
  IO.FS.writeFile oursFile (Json.proof oursProof)
  let verdict ← rust bin #["verify", "proven", toString logN, oursFile]
  let opened := oursProof.opened
  let opened := { opened with traceLocal := opened.traceLocal.modify 0 (· + 1) }
  let tampered := { oursProof with opened := opened }
  IO.FS.writeFile s!"{dir}/proven_{logN}_tampered.json" (Json.proof tampered)
  let tamperedArgs := #["verify", "proven", toString logN, s!"{dir}/proven_{logN}_tampered.json"]
  let out ← IO.Process.output { cmd := bin, args := tamperedArgs }
  unless out.exitCode ≠ 0 do throw (IO.userError "proven: Plonky3 accepts a tampered proof")
  let theirsFile := s!"{dir}/proven_{logN}_plonky3.json"
  let _ ← rust bin #["prove", "proven", toString logN, theirsFile]
  let theirsText ← IO.FS.readFile theirsFile
  let theirsProof ← parseProof theirsText
  IO.ofExcept (verifyProof I P logN theirsProof)
  unless oursProof == theirsProof ∧ Json.proof oursProof == theirsText do
    throw (IO.userError "proven: the proof differs from Plonky3's")
  IO.println s!"proven: Plonky3's verifier {verdict.trimAscii} CompStark's proof and rejects it \
    with an opened value changed, CompStark's verifier accepts Plonky3's proof, and the two \
    are byte for byte the same ({theirsText.length} bytes of JSON)"

/-- Run `f`, its result forced, and the nanoseconds it took. -/
def timeNs {α : Type} (f : Unit → α) : IO (ℕ × α) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (t1 - t0, a)

/-- The benchmark: the AIR, the prover's backend (its extension plans and quotient tables) and
the verifying key are made once, as Plonky3's side makes its configuration once. -/
def bench (name : String) (logN reps : ℕ) : IO Unit := do
  let P ← params name
  let inputs ← readInputs s!".lake/showcase/inputs_{logN}.txt"
  let A := air logN
  let B := I.backendFor [QuotientKernel.kernel] P.logBlowup [(logN, A.logQuotientChunks logN)]
  let vk := letI := I.field; setup P A logN
  let mut samples : Array (Array ℕ) := #[#[], #[], #[], #[]]
  for _ in [0:reps] do
    let (t0, chunks) ← timeNs fun _ => trace logN inputs
    let chunks ← IO.ofExcept chunks
    let (t1, proof) ← timeNs fun _ => proveWith B P A logN chunks []
    let (t2, verdict) ← timeNs fun _ => I.verifyFast P A vk proof []
    IO.ofExcept verdict
    samples := (samples.zip #[t0, t1, t0 + t1, t2]).map fun (s, t) => s.push t
  let median (s : Array ℕ) : String :=
    let m := (s.qsort (· < ·))[s.size / 2]!
    s!"{m / 1000000}.{(m / 100000) % 10}"
  IO.println s!"lean {name} 2^{logN} tracegen {median samples[0]!} prove {median samples[1]!} \
    total {median samples[2]!} verify {median samples[3]!} ms"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["kat"] => kat I
  | ["check", logN, bin] => check I logN.toNat! bin
  | ["bench", name, logN, reps] => bench I name logN.toNat! reps.toNat!
  | _ =>
    IO.eprintln "usage: keccak_showcase kat | check L RUST | bench CONFIG L REPS"
    return 1
  return 0

end KeccakShowcase
