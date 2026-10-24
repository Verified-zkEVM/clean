/-
`keccak_air_trace bench GENERATOR LOG_ROWS REPS LOG_CHUNKS`: the median time of generating the trace
of Plonky3's Keccak AIR over KoalaBear for `2 ^ LOG_ROWS` rows of pseudorandom permutations, in
`2 ^ LOG_CHUNKS` chunks, by the compiled kernel (`compiled`, `koalaBearTrace`) or the interpreter
(`interpreted`, `fastTrace`); the number of threads is Lean's (`LEAN_NUM_THREADS`).
`keccak_air_trace kat GENERATOR PERMUTATIONS`: the height, width and per-row FNV-1a hashes of the
canonical values of the trace of `PERMUTATIONS` pseudorandom permutations.
Lane `i` of permutation `k` is SplitMix64 of `25 k + i`.
-/
module

public import Clean.Examples.KeccakAir.FastKernel
public import CompPoly.Fields.KoalaBear.Fast

@[expose] public section

namespace KeccakAir.Bench
open Montgomery.Native32

abbrev p := KoalaBear.fieldSize

def splitMix (seed : UInt64) : UInt64 :=
  let z := seed + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def inputs (n : ℕ) : Array Trace.State :=
  (Array.range n).map fun k => Vector.ofFn fun i => splitMix (25 * k + i.val).toUInt64

/-- The canonical value of a Montgomery word. -/
def canonical (w : UInt32) : UInt64 :=
  if h : w.toNat < p then (FastField.toUInt32 (⟨w, h⟩ : FastField p)).toUInt64 else 0

def generate (generator : String) (inputs : Array Trace.State) (logChunks : ℕ) :
    Except String (Array ByteArray) :=
  if generator = "compiled" then koalaBearTrace inputs logChunks
  else fastTrace (p := p) inputs logChunks

def kat (generator : String) (n : ℕ) : IO UInt32 := do
  let .ok chunks := generate generator (inputs n) 0 | return 1
  let rows := chunks[0]!
  let width := 2633
  let height := rows.size / (4 * width)
  IO.println s!"{height} {width}"
  for r in [0:height] do
    let mut h : UInt64 := 0xcbf29ce484222325
    for c in [0:width] do
      h := (h ^^^ canonical (rows.getUInt32LE! (4 * (r * width + c)))) * 0x100000001b3
    let digits := String.ofList (Nat.toDigits 16 h.toNat)
    IO.println s!"0x{String.ofList (List.replicate (16 - digits.length) '0')}{digits}"
  return 0

def bench (generator : String) (logRows reps logChunks : ℕ) : IO UInt32 := do
  let ins := inputs (2 ^ logRows / 24)
  let mut times := #[]
  for _ in [0:reps] do
    let start ← IO.monoNanosNow
    let .ok chunks := generate generator ins logChunks | return 1
    let stop ← IO.monoNanosNow
    -- the chunks are freed after the measurement
    let size : ℕ := chunks.foldl (· + ·.size) 0
    unless size = 4 * 2633 * 2 ^ logRows do return 1
    times := times.push ((stop - start).toFloat / 1e6)
  let sorted := times.qsort fun a b => decide (a < b)
  IO.println s!"lean {generator} tracegen 2^{logRows} chunks 2^{logChunks} median \
    {sorted[reps / 2]!} ms min {sorted[0]!} ms"
  return 0

end KeccakAir.Bench

open KeccakAir.Bench in
public def main (args : List String) : IO UInt32 :=
  match args with
  | ["kat", generator, n] => kat generator n.toNat!
  | ["bench", generator, logRows, reps, logChunks] =>
      bench generator logRows.toNat! reps.toNat! logChunks.toNat!
  | _ => do
      IO.eprintln "usage: keccak_air_trace (kat GENERATOR N | bench GENERATOR LOG_ROWS REPS \
        LOG_CHUNKS)"
      return 2
