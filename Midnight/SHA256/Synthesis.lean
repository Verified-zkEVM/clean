import Midnight.SHA256.Tables
import Midnight.SHA256.Constants
import Midnight.Chips.Synthesis

/-!
Source-derived key-generation schedule for `ShaPreImageCircuit` (24 input bytes).

This is a port of Rust synthesis with advice *values* erased: they cannot affect this
circuit's key generation. It preserves advice allocation sites, fixed assignments,
selector enables, and ordered copy constraints. It does not provide a SHA witness
generator or a SHA soundness/completeness theorem. The small schedule below is lowered
to actual Clean operations by `toOperations`, with activations supplied by configure.
No captured trace, matrix, placement, or permutation is an input to this program.
-/

namespace Midnight.SHA256.Synthesis
open Halo2

export Midnight.Chips.Synthesis (Instruction Step BuildState Build Region
  putInstr advice fixed enable equal copyAdvice region constant custom linearAux linearCombination)

def sa (index row : Nat) : Region Cell := advice shaAdvice[index]! row
def scopy (source : Cell) (index row : Nat) : Region Cell :=
  copyAdvice source shaAdvice[index]! row

structure PlainSpread where
  plain : Cell
  spread : Cell
  deriving Inhabited

structure Word where
  combined : PlainSpread
  limbs : Array Cell
  deriving Inhabited

structure Compression where
  a : Word
  b : PlainSpread
  c : PlainSpread
  d : Cell
  e : Word
  f : PlainSpread
  g : PlainSpread
  h : Cell

def plainState (s : Compression) : Array Cell :=
  #[s.a.combined.plain, s.b.plain, s.c.plain, s.d,
    s.e.combined.plain, s.f.plain, s.g.plain, s.h]

def constantPair (n : Nat) : Build PlainSpread := do
  let plain ← constant n
  let expanded ← constant (SHA256.spread n)
  return ⟨plain, expanded⟩

/-- Rust `u32_in_be_limbs`, followed by the fixed spreaded-limb assignments. -/
def constantWord (n : Nat) (widths : Array Nat) : Build Word := do
  let pair ← constantPair n
  let mut remaining := 32
  let mut limbs := #[]
  for width in widths do
    remaining := remaining - width
    limbs := limbs.push (← constant (SHA256.spread ((n / 2^remaining) % 2^width)))
  return ⟨pair, limbs⟩

def initialState : Build Compression := do
  let a ← constantWord iv[0]! #[10,9,11,2]
  let b ← constantPair iv[1]!
  let c ← constantPair iv[2]!
  let d ← constant iv[3]!
  let e ← constantWord iv[4]! #[7,12,2,5,6]
  let f ← constantPair iv[5]!
  let g ← constantPair iv[6]!
  let h ← constant iv[7]!
  return ⟨a,b,c,d,e,f,g,h⟩

def assignBytes : Build (Array Cell) := do
  let mut bytes := #[]
  for _ in [:24] do
    bytes := bytes.push (← region "assign_many_small" do
      enable 3 0
      let _ ← fixed 10 0 8
      advice 1 0)
  return bytes

/-- The pinned example has exactly 24 bytes; its SHA length suffix is 192 bits. -/
def pad (bytes : Array Cell) : Build (Array Cell) := do
  let one ← constant 128
  let zero ← constant 0
  let mut output := bytes.push one ++ Array.replicate 31 zero
  for byte in #[0,0,0,0,0,0,0,192] do output := output.push (← constant byte)
  return output

def blockFromBytes (bytes : Array Cell) : Build (Array Cell) := do
  let mut words := #[]
  for word in [:16] do
    let terms := (Array.range 4).map fun i => (((256^i : Nat) : F), bytes[word*4+3-i]!)
    words := words.push (← linearCombination terms)
  return words

def plainAndSpread (width offset index : Nat) : Region PlainSpread := do
  enable 4 offset
  let _ ← fixed index offset (width : F)
  let plain ← sa (2*index) offset
  let expanded ← sa (2*index+1) offset
  return ⟨plain, expanded⟩

/-- The source chip supports at most seven summands; all callers below obey this. -/
private def addMod (summands : Array Cell) (zero : Cell) : Region Cell := do
  enable 15 1
  let terms := summands ++ Array.replicate (7-summands.size) zero
  let targets := #[(5,0),(6,0),(5,1),(6,1),(4,2),(5,2),(6,2)]
  for i in [:7] do let _ ← scopy terms[i]! targets[i]!.1 targets[i]!.2
  let _ ← plainAndSpread 3 2 1
  sa 4 0

def prepare (name : String) (selector : Nat) (widths : Array Nat)
    (summands : Array Cell) : Build Word := do
  let zero ← constant 0
  region name do
    enable selector 1
    let plain ← addMod summands zero
    let expanded ← sa 4 1
    let mut limbs := #[]
    for i in [:widths.size] do
      limbs := limbs.push (← plainAndSpread widths[i]! (i/2) (i%2)).spread
    return ⟨⟨plain, expanded⟩, limbs⟩

def prepareA (summands : Array Cell) : Build Word :=
  prepare "decompose A in 10-9-11-2" 12 #[10,9,11,2,0] summands
def prepareE (summands : Array Cell) : Build Word :=
  prepare "decompose E in 7-12-2-5-6" 13 #[7,12,2,5,6] summands

def prepareMessage (summands : Array Cell) : Build Word := do
  let zero ← constant 0
  region "prepare message word" do
    enable 14 1
    let plain ← addMod summands zero
    let w12 ← plainAndSpread 12 0 0
    let w07 ← plainAndSpread 7 0 1
    let w3a ← plainAndSpread 3 1 0
    let w04 ← plainAndSpread 4 1 1
    let w3b ← plainAndSpread 3 2 0
    let w1a ← sa 7 0
    let w1b ← sa 7 1
    let w1c ← sa 7 2
    return ⟨⟨plain, plain⟩, #[w12.spread,w1a,w1b,w1c,w07.spread,w3a.spread,w04.spread,w3b.spread]⟩

/-- Parity changes assignment order but not the target limbs or output address. -/
def spread111110 (odd : Bool) (offset : Nat) : Region Cell := do
  enable 11 (offset+1)
  let index := if odd then 1 else 0
  for i in [:3] do let _ ← plainAndSpread (if i < 2 then 11 else 10) (offset+i) index
  for i in [:3] do let _ ← plainAndSpread (if i < 2 then 11 else 10) (offset+i) (1-index)
  sa 4 offset

def sigma (name : String) (selector : Nat) (word : Word)
    (targets : Array (Nat × Nat)) : Build Cell :=
  region name do
    enable selector 1
    for i in [:targets.size] do let _ ← scopy word.limbs[i]! targets[i]!.1 targets[i]!.2
    spread111110 false 0

def sigma0 (w : Word) : Build Cell :=
  sigma "σ₀(W)" 9 w #[(5,0),(6,0),(4,1),(5,1),(6,1),(4,2),(5,2),(6,2)]
def sigma1 (w : Word) : Build Cell :=
  sigma "σ₁(W)" 10 w #[(5,0),(6,0),(4,1),(5,1),(6,1),(4,2),(5,2),(6,2)]
def bigSigma0 (w : Word) : Build Cell :=
  sigma "Σ₀(A)" 7 w #[(5,0),(6,0),(5,1),(6,1)]
def bigSigma1 (w : Word) : Build Cell :=
  sigma "Σ₁(E)" 8 w #[(5,0),(6,0),(5,1),(6,1),(5,2)]

def messageSchedule (block : Array Cell) : Build (Array Cell) := do
  let mut words : Array Word := #[]
  for i in [:16] do words := words.push (← prepareMessage #[block[i]!])
  for i in [16:64] do
    let s0 ← sigma0 words[i-15]!
    let s1 ← sigma1 words[i-2]!
    words := words.push (← prepareMessage #[words[i-16]!.combined.plain,
      words[i-7]!.combined.plain,s0,s1])
  return words.map (·.combined.plain)

def majority (a b c : Cell) : Build Cell :=
  region "Maj(A, B, C)" do
    enable 5 1
    let _ ← scopy a 5 0
    let _ ← scopy b 6 0
    let _ ← scopy c 5 1
    spread111110 true 0

def choice (e f g : Cell) : Build Cell := do
  let mask ← constant 0x5555555555555555
  region "Ch(E, F, G)" do
    enable 6 1
    enable 6 4
    let _ ← scopy e 5 0
    let _ ← scopy e 4 4
    let _ ← scopy f 6 0
    let _ ← scopy g 6 3
    let ne ← sa 5 3
    let _ ← scopy ne 5 4
    let _ ← scopy mask 6 4
    let ef ← spread111110 true 0
    let _ ← scopy ef 4 1
    let neg ← spread111110 true 3
    let _ ← scopy neg 5 1
    sa 6 1

def compressionRound (state : Compression) (k : Nat) (w : Cell) : Build Compression := do
  let kcell ← constant k
  let s0 ← bigSigma0 state.a
  let maj ← majority state.a.combined.spread state.b.spread state.c.spread
  let s1 ← bigSigma1 state.e
  let ch ← choice state.e.combined.spread state.f.spread state.g.spread
  let a ← prepareA #[state.h,s1,ch,kcell,w,s0,maj]
  let e ← prepareE #[state.d,state.h,s1,ch,kcell,w]
  return ⟨a,state.a.combined,state.b,state.c.plain,e,state.e.combined,state.f,state.g.plain⟩

def addStates (initial final : Compression) : Build (Array Cell) := do
  let a := plainState initial
  let b := plainState final
  let mut result := #[]
  for i in [:8] do
    let w ← if i < 4 then prepareA #[a[i]!,b[i]!] else prepareE #[a[i]!,b[i]!]
    result := result.push w.combined.plain
  return result

def wordToBytes (word : Cell) : Build (Array Cell) := do
  let (result, limbs) ← region "decompose core" do
    let pair ← linearAux #[1,256,65536,16777216] 1
    for row in #[3,2,1,0] do
      enable 3 row
      let _ ← fixed 10 row 8
    return pair
  region "copy" (equal word result)
  return limbs.reverse

def synthesize : Build Unit := do
  let bytes ← assignBytes
  let initial ← initialState
  let padded ← pad bytes
  let block ← blockFromBytes padded
  let words ← messageSchedule block
  let mut state := initial
  for i in [:64] do state ← compressionRound state roundConstants[i]! words[i]!
  let digest ← addStates initial state
  let mut outputs := #[]
  for word in digest do outputs := outputs ++ (← wordToBytes word)
  for i in [:outputs.size] do
    modify fun st => { st with steps := st.steps.push (.publicInput outputs[i]! i) }

/-- Keep the source-state projection behind a generic application so kernel
proofs can share it without normalizing the entire closed synthesis program. -/
def runSteps {α : Type} (action : Build α) : Array Step :=
  (action.run {}).2.steps

def schedule : Array Step := runSteps synthesize

/-- Source schedule lowered to real Clean operations; advice witness values erased. -/
def toOperations (activate : Nat → Nat → List (RegionOperation F)) : Operations F :=
  Midnight.Chips.Synthesis.scheduleToOperations schedule activate

end Midnight.SHA256.Synthesis
