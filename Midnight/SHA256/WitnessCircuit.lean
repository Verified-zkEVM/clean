import Midnight.SHA256.WitnessIR
import Midnight.SHA256.Configure
import Midnight.SHA256.Constants

/-!
Input-driven port of the pinned 24-byte Midnight SHA synthesis in Clean's actual
Halo2 DSL. Advice uses serializable witness expressions, copies use `copyAdvice`,
and selectors carry the configured gates/lookups. Native source ordering and
constant-cache shortcuts are preserved. This is the witness-bearing circuit;
semantic soundness/completeness is supplied separately, not asserted here.

Source: `circuits/src/hash/sha256/sha256_chip.rs`, native/native_chip.rs and
field/decomposition/chip.rs (Midnight Foundation, Apache-2.0).
-/
namespace Midnight.SHA256.WitnessCircuit
open Halo2

abbrev Cell := AssignedCell F
abbrev Cache := List (Nat × Cell)
/-- Fixed native architecture and source-internal helper preconditions apply:
linearAux has nonempty terms and colsUsed ∈ {1,4}; addMod has at most seven
summands; words/blocks have the limb/word counts produced by this module. The
closed public synthesize entry constructs every such argument internally. -/
abbrev Build := StateT Cache (Circuit F)
abbrev Region := RegionCircuit F

def region {α : Type} (name : String) (body : Region α) : Build α :=
  liftM (assignRegion name body)

/-- Uses the source-configured real gate and lookup operations. -/
def enable (selector row : Nat) : Region Unit :=
  fun _ => ((), SHA256.activation selector row)

def sa (index row : Nat) (value : U64Expr F) : Region Cell :=
  assignAdvice ⟨Synthesis.shaAdvice[index]!⟩ row (WitnessIR.program value)
def scopy (source : Cell) (index row : Nat) : Region Cell :=
  copyAdvice source ⟨Synthesis.shaAdvice[index]!⟩ row

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

/-- Canonical-value cache shared with the native arithmetic operations. -/
def constant (n : Nat) : Build Cell := do
  let key := (n : F).val
  if let some (_, cell) := (← get).find? (fun entry => entry.1 == key) then return cell
  let cell ← region "Assign fixed" (assignFixed ⟨9⟩ 0 (n : F))
  modify ((key, cell) :: ·)
  return cell

def constantPair (n : Nat) : Build PlainSpread := do
  let plain ← constant n
  let expanded ← constant (SHA256.spread n)
  return ⟨plain, expanded⟩

def constantWord (n : Nat) (widths : Array Nat) : Build Word := do
  let pair ← constantPair n
  let mut remaining := 32
  let mut limbs := #[]
  for width in widths do
    remaining := remaining - width
    limbs := limbs.push (← constant (SHA256.spread ((n / 2^remaining) % 2^width)))
  return ⟨pair, limbs⟩

def initialState : Build Compression := do
  let a ← constantWord Synthesis.iv[0]! #[10,9,11,2]
  let b ← constantPair Synthesis.iv[1]!
  let c ← constantPair Synthesis.iv[2]!
  let d ← constant Synthesis.iv[3]!
  let e ← constantWord Synthesis.iv[4]! #[7,12,2,5,6]
  let f ← constantPair Synthesis.iv[5]!
  let g ← constantPair Synthesis.iv[6]!
  let h ← constant Synthesis.iv[7]!
  return ⟨a,b,c,d,e,f,g,h⟩

def custom (coeffs : Array F) (next : F) (row : Nat) : Region Unit := do
  enable 0 row
  for i in [:5] do let _ ← assignFixed ⟨4+i⟩ row coeffs[i]!
  let _ ← assignFixed ⟨0⟩ row next
  for col in [1,2,3] do let _ ← assignFixed ⟨col⟩ row 0

/-- Native auxiliary for the nonempty calls using one or four columns below. The next-row
witness is the source recurrence `result - sum(current chunk)`, in the field. -/
def linearAux (terms : Array (F × FExpr F)) (initial : FExpr F)
    (colsUsed : Nat) : Region (Cell × Array Cell) := do
  let mut assigned := #[]
  let mut output := default
  let mut resultValue := initial
  let rows := (terms.size + colsUsed - 1) / colsUsed
  for row in [:rows] do
    let result ← assignAdvice ⟨0⟩ row (.ofFExpr resultValue)
    if row == 0 then output := result
    let mut coeffs : Array F := #[-1,0,0,0,0]
    let mut chunk : FExpr F := .const 0
    let count := min colsUsed (terms.size - row*colsUsed)
    for i in [:count] do
      let (coefficient, value) := terms[row*colsUsed+i]!
      assigned := assigned.push (← assignAdvice ⟨i+1⟩ row (.ofFExpr value))
      coeffs := coeffs.set! (i+1) coefficient
      chunk := chunk + .const coefficient * value
    custom coeffs (if row+1 < rows then 1 else 0) row
    resultValue := resultValue - chunk
  return (output, assigned)

def linearCombination (input : Array (F × Cell)) : Build Cell := do
  let zero ← constant 0
  let terms := input.filter fun (coeff, cell) => coeff != 0 && cell != zero
  if terms.isEmpty then return zero
  if terms.size == 1 && terms[0]!.1 == 1 then return terms[0]!.2
  region "Linear combination" do
    let values := terms.map fun (coefficient, cell) => (coefficient, (.expr cell : FExpr F))
    let resultValue := values.foldl (fun acc (coeff, value) => acc + .const coeff * value)
      (.const 0)
    let (result, assigned) ← linearAux values resultValue 4
    for i in [:terms.size] do constrainEqual assigned[i]! terms[i]!.2
    return result

def assignBytes (input : Vector (WitgenIR F 1) 24) : Build (Array Cell) := do
  let mut bytes := #[]
  for program in input.toArray do
    bytes := bytes.push (← region "assign_many_small" do
      enable 3 0
      let _ ← assignFixed ⟨10⟩ 0 8
      assignAdvice ⟨1⟩ 0 program)
  return bytes

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

/-- Source plain/spread assignment, with the lookup tag fixed by the circuit.
The spread program reads the plain cell just assigned, sharing the computed value
through the real witness environment instead of repeating its integer expression. -/
def plainAndSpread (width offset index : Nat) (value : U64Expr F) : Region PlainSpread := do
  enable 4 offset
  let _ ← assignFixed ⟨index⟩ offset (width : F)
  let plain ← sa (2*index) offset value
  let expanded ← sa (2*index+1) offset (WitnessIR.spread32 (WitnessIR.readNat plain))
  return ⟨plain, expanded⟩

def addMod (summands : Array Cell) (zero : Cell) : Region Cell := do
  enable 15 1
  let terms := summands ++ Array.replicate (7-summands.size) zero
  let values := terms.toList.map WitnessIR.readNat
  let targets := #[(5,0),(6,0),(5,1),(6,1),(4,2),(5,2),(6,2)]
  for i in [:7] do let _ ← scopy terms[i]! targets[i]!.1 targets[i]!.2
  let _ ← plainAndSpread 3 2 1 (WitnessIR.carry32 values)
  sa 4 0 (WitnessIR.sum32 values)

/-- The source preparation region itself, shared by synthesis and its semantic
contracts. Constant-cache handling stays in `prepare`. -/
def prepareRegion (selector : Nat) (widths : Array Nat)
    (summands : Array Cell) (zero : Cell) : Region Word := do
  enable selector 1
  let plain ← addMod summands zero
  let value := WitnessIR.readNat plain
  let expanded ← sa 4 1 (WitnessIR.spread32 value)
  let mut limbs := #[]
  let mut remaining := 32
  for i in [:widths.size] do
    remaining := remaining - widths[i]!
    let limbValue := WitnessIR.limb value (remaining, widths[i]!)
    limbs := limbs.push (← plainAndSpread widths[i]! (i/2) (i%2) limbValue).spread
  return ⟨⟨plain, expanded⟩, limbs⟩

def prepare (name : String) (selector : Nat) (widths : Array Nat)
    (summands : Array Cell) : Build Word := do
  let zero ← constant 0
  region name (prepareRegion selector widths summands zero)

def prepareA (summands : Array Cell) : Build Word :=
  prepare "decompose A in 10-9-11-2" 12 #[10,9,11,2,0] summands
def prepareE (summands : Array Cell) : Build Word :=
  prepare "decompose E in 7-12-2-5-6" 13 #[7,12,2,5,6] summands

/-- The source message preparation region, with no separate proof-side circuit. -/
def prepareMessageRegion (summands : Array Cell) (zero : Cell) : Region Word := do
  enable 14 1
  let plain ← addMod summands zero
  let values := WitnessIR.limbs Witness.messageLayout (WitnessIR.readNat plain)
  let w12 ← plainAndSpread 12 0 0 values[0]
  let w07 ← plainAndSpread 7 0 1 values[4]
  let w3a ← plainAndSpread 3 1 0 values[5]
  let w04 ← plainAndSpread 4 1 1 values[6]
  let w3b ← plainAndSpread 3 2 0 values[7]
  let w1a ← sa 7 0 values[1]
  let w1b ← sa 7 1 values[2]
  let w1c ← sa 7 2 values[3]
  return ⟨⟨plain, plain⟩, #[w12.spread,w1a,w1b,w1c,w07.spread,w3a.spread,w04.spread,w3b.spread]⟩

def prepareMessage (summands : Array Cell) : Build Word := do
  let zero ← constant 0
  region "prepare message word" (prepareMessageRegion summands zero)

/-- Even limbs are assigned first, even when the returned parity is odd. -/
def spread111110 (odd : Bool) (offset : Nat) (value : U64Expr F) : Region Cell := do
  enable 11 (offset+1)
  let index := if odd then 1 else 0
  let evens := WitnessIR.limbs Witness.parityLayout (WitnessIR.evenBits value)
  let odds := WitnessIR.limbs Witness.parityLayout (WitnessIR.oddBits value)
  for i in [:3] do
    let _ ← plainAndSpread (if i < 2 then 11 else 10) (offset+i) index evens[i]!
  for i in [:3] do
    let _ ← plainAndSpread (if i < 2 then 11 else 10) (offset+i) (1-index) odds[i]!
  sa 4 offset (if odd then WitnessIR.oddBits value else WitnessIR.evenBits value)

def sigma {n : Nat} (name : String) (selector : Nat) (word : Word)
    (targets : Vector (Nat × Nat) n) (recipe : Witness.Recipe n) : Build Cell :=
  region name do
    enable selector 1
    for i in [:n] do let _ ← scopy word.limbs[i]! targets[i]!.1 targets[i]!.2
    let values := Vector.ofFn fun i : Fin n => WitnessIR.readNat word.limbs[i.val]!
    spread111110 false 0 (WitnessIR.weighted recipe values)

def sigma0 (w : Word) : Build Cell :=
  sigma "σ₀(W)" 9 w #v[(5,0),(6,0),(4,1),(5,1),(6,1),(4,2),(5,2),(6,2)] Witness.sigma0Recipe
def sigma1 (w : Word) : Build Cell :=
  sigma "σ₁(W)" 10 w #v[(5,0),(6,0),(4,1),(5,1),(6,1),(4,2),(5,2),(6,2)] Witness.sigma1Recipe
def bigSigma0 (w : Word) : Build Cell :=
  sigma "Σ₀(A)" 7 w #v[(5,0),(6,0),(5,1),(6,1)] Witness.bigSigma0Recipe
def bigSigma1 (w : Word) : Build Cell :=
  sigma "Σ₁(E)" 8 w #v[(5,0),(6,0),(5,1),(6,1),(5,2)] Witness.bigSigma1Recipe

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
    spread111110 true 0 (.add (.add (WitnessIR.readNat a) (WitnessIR.readNat b))
      (WitnessIR.readNat c))

def choice (e f g : Cell) : Build Cell := do
  let mask ← constant 0x5555555555555555
  region "Ch(E, F, G)" do
    enable 6 1
    enable 6 4
    let _ ← scopy e 5 0
    let _ ← scopy e 4 4
    let _ ← scopy f 6 0
    let _ ← scopy g 6 3
    let ne ← sa 5 3 (WitnessIR.negateSpread (WitnessIR.readNat e))
    let _ ← scopy ne 5 4
    let _ ← scopy mask 6 4
    let ef ← spread111110 true 0 (.add (WitnessIR.readNat e) (WitnessIR.readNat f))
    let _ ← scopy ef 4 1
    let neg ← spread111110 true 3 (.add (WitnessIR.readNat ne) (WitnessIR.readNat g))
    let _ ← scopy neg 5 1
    sa 6 1 (.add (WitnessIR.readNat ef) (WitnessIR.readNat neg))

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

def wordToBytesRegion (word : Cell) : Region (Cell × Array Cell) := do
  let terms := (Array.range 4).map fun i =>
    (((256^i : Nat) : F), (.ofU64 (WitnessIR.limb (WitnessIR.readNat word) (8*i,8)) : FExpr F))
  let pair ← linearAux terms (.expr word) 1
  for row in #[3,2,1,0] do
    enable 3 row
    let _ ← assignFixed ⟨10⟩ row 8
  return pair

def wordToBytes (word : Cell) : Build (Array Cell) := do
  let (result, limbs) ← region "decompose core" (wordToBytesRegion word)
  region "copy" (constrainEqual word result)
  return limbs.reverse

def body (input : Vector (WitgenIR F 1) 24) : Build (Array Cell) := do
  let bytes ← assignBytes input
  let initial ← initialState
  let padded ← pad bytes
  let block ← blockFromBytes padded
  let words ← messageSchedule block
  let mut state := initial
  for i in [:64] do state ← compressionRound state Synthesis.roundConstants[i]! words[i]!
  let digest ← addStates initial state
  let mut outputs := #[]
  for word in digest do outputs := outputs ++ (← wordToBytes word)
  return outputs

/-- Full SHA data path. Its output array contains the 32 big-endian digest cells.
The input programs must produce bytes; range lookups enforce this requirement. -/
def synthesize (input : Vector (WitgenIR F 1) 24) : Circuit F (Array Cell) := do
  let (output, _) ← (body input).run []
  return output

/-- The exact preimage-example boundary, including public digest copies and tables. -/
def preimageCircuit (input : Vector (WitgenIR F 1) 24) : Circuit F (Array Cell) := do
  let outputs ← synthesize input
  for i in [:outputs.size] do constrainInstance outputs[i]! ⟨1⟩ i
  shaTables
  return outputs

end Midnight.SHA256.WitnessCircuit
