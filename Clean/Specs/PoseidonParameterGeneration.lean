/-
Deterministic generation of the BN254 Poseidon parameters used by circomlib.

This module implements the Grain-LFSR parameter generation from the Poseidon
reference script and the optimized constant/matrix transformation from
circomlibjs. It intentionally targets circomlib's fixed widths 2 through 17;
it is not a general-purpose security parameter selection tool.
-/
module

public import Mathlib.Data.Int.GCD

@[expose] public section

namespace Specs.Poseidon.ParameterGeneration

def prime : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def fieldSize : ℕ := 254

def nRoundsF : ℕ := 8

def nRoundsP : Vector ℕ 16 :=
  #v[56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]

abbrev Matrix := Array (Array ℕ)

structure BaseParameters where
  constants : Array ℕ
  matrix : Matrix

structure OptimizedParameters where
  C : Array ℕ
  M : Matrix
  P : Matrix
  S : Array ℕ
deriving DecidableEq, Inhabited

/-- Statically sized form consumed by the optimized Poseidon specification.
The executable generator first produces `OptimizedParameters`; alternative
integration strategies differ only in how they construct this structure. -/
structure GeneratedVectors (width nPartial : ℕ) where
  C : Vector ℕ (nRoundsF * width + nPartial)
  M : Vector (Vector ℕ width) width
  P : Vector (Vector ℕ width) width
  S : Vector ℕ (nPartial * (2 * width - 1))
deriving DecidableEq

def fixedBits (value width : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin width =>
    if value.testBit (width - 1 - i.val) then 1 else 0

structure Grain where
  state : Array ℕ

def Grain.step (grain : Grain) : ℕ × Grain :=
  let bit := grain.state[62]! ^^^ grain.state[51]! ^^^ grain.state[38]! ^^^
    grain.state[23]! ^^^ grain.state[13]! ^^^ grain.state[0]!
  (bit, ⟨(grain.state.extract 1 grain.state.size).push bit⟩)

def Grain.warmup (grain : Grain) : Grain := Id.run do
  let mut current := grain
  for _ in [0:160] do
    current := current.step.2
  return current

def Grain.init (width nPartial : ℕ) : Grain :=
  Grain.warmup ⟨
    fixedBits 1 2 ++
    fixedBits 0 4 ++
    fixedBits fieldSize 12 ++
    fixedBits width 12 ++
    fixedBits nRoundsF 10 ++
    fixedBits nPartial 10 ++
    Array.replicate 30 1⟩

partial def Grain.nextBit (grain : Grain) : ℕ × Grain :=
  let (selector, afterSelector) := grain.step
  let (candidate, afterCandidate) := afterSelector.step
  if selector = 1 then
    (candidate, afterCandidate)
  else
    Grain.nextBit afterCandidate

def Grain.randomInt (grain : Grain) (nBits : ℕ := fieldSize) : ℕ × Grain := Id.run do
  let mut value := 0
  let mut current := grain
  for _ in [0:nBits] do
    let (bit, next) := current.nextBit
    value := 2 * value + bit
    current := next
  return (value, current)

partial def Grain.nextFieldElement (grain : Grain) : ℕ × Grain :=
  let (value, next) := grain.randomInt
  if value < prime then
    (value, next)
  else
    Grain.nextFieldElement next

def modAdd (a b : ℕ) : ℕ :=
  (a + b) % prime

def modSub (a b : ℕ) : ℕ :=
  (a + prime - b) % prime

def modMul (a b : ℕ) : ℕ :=
  (a * b) % prime

def modInv (a : ℕ) : ℕ :=
  ((Nat.gcdA a prime) % (prime : ℤ)).toNat

def hasDuplicate (values : Array ℕ) : Bool := Id.run do
  for i in [0:values.size] do
    for j in [i + 1:values.size] do
      if values[i]! = values[j]! then
        return true
  return false

def hasZeroCrossSum (values : Array ℕ) (width : ℕ) : Bool := Id.run do
  for i in [0:width] do
    for j in [0:width] do
      if modAdd values[i]! values[width + j]! = 0 then
        return true
  return false

partial def generateMatrix (grain : Grain) (width : ℕ) : Matrix × Grain :=
  let (coordinates, next) := Id.run do
    let mut values := #[]
    let mut current := grain
    for _ in [0:2 * width] do
      let (value, after) := current.randomInt
      values := values.push (value % prime)
      current := after
    return (values, current)
  if hasDuplicate coordinates || hasZeroCrossSum coordinates width then
    generateMatrix next width
  else
    let matrix := Array.ofFn fun i : Fin width =>
      Array.ofFn fun j : Fin width =>
        modInv (modAdd coordinates[i.val]! coordinates[width + j.val]!)
    (matrix, next)

def generateBase (width nPartial : ℕ) : BaseParameters := Id.run do
  let mut grain := Grain.init width nPartial
  let mut constants := #[]
  for _ in [0:(nRoundsF + nPartial) * width] do
    let (value, next) := grain.nextFieldElement
    constants := constants.push value
    grain := next
  let (matrix, _) := generateMatrix grain width
  return { constants, matrix }

def transpose (matrix : Matrix) : Matrix :=
  Array.ofFn fun i : Fin matrix.size =>
    Array.ofFn fun j : Fin matrix.size => matrix[j.val]![i.val]!

def matrixInverse (matrix : Matrix) : Matrix := Id.run do
  let size := matrix.size
  let mut augmented := Array.ofFn fun i : Fin size =>
    matrix[i.val]! ++ Array.ofFn fun j : Fin size => if i.val = j.val then 1 else 0
  for column in [0:size] do
    let mut pivot := column
    while pivot < size && augmented[pivot]![column]! = 0 do
      pivot := pivot + 1
    if pivot = size then
      panic! "Poseidon parameter generation encountered a singular matrix"
    let columnRow := augmented[column]!
    augmented := augmented.set! column augmented[pivot]!
    augmented := augmented.set! pivot columnRow
    let scale := modInv augmented[column]![column]!
    augmented := augmented.set! column (augmented[column]!.map (modMul scale))
    for row in [0:size] do
      if row != column then
        let factor := augmented[row]![column]!
        if factor != 0 then
          let reduced := Array.zipWith
            (fun left right => modSub left (modMul factor right))
            augmented[row]! augmented[column]!
          augmented := augmented.set! row reduced
  return augmented.map fun row => row.extract size (2 * size)

def vectorTimesMatrix (vector : Array ℕ) (matrix : Matrix) : Array ℕ :=
  Array.ofFn fun column : Fin vector.size =>
    (List.range vector.size).foldl
      (fun acc row => modAdd acc (modMul vector[row]! matrix[row]![column.val]!)) 0

def matrixTimesVector (matrix : Matrix) (vector : Array ℕ) : Array ℕ :=
  matrix.map fun row =>
    (List.range vector.size).foldl
      (fun acc column => modAdd acc (modMul row[column]! vector[column]!)) 0

def matrixMultiply (left right : Matrix) : Matrix :=
  let rightT := transpose right
  left.map fun row =>
    rightT.map fun column =>
      (List.range row.size).foldl
        (fun acc i => modAdd acc (modMul row[i]! column[i]!)) 0

def compressConstants (width nPartial : ℕ)
    (constants : Array ℕ) (matrix : Matrix) : Array ℕ := Id.run do
  let matrixInv := matrixInverse matrix
  let mut result := constants.extract 0 width

  for round in [0:nRoundsF / 2 - 1] do
    let start := (round + 1) * width
    result := result ++ vectorTimesMatrix (constants.extract start (start + width)) matrixInv

  let start := (nRoundsF / 2 + nPartial) * width
  let mut accumulator := constants.extract start (start + width)
  let mut partialConstants := #[]
  for step in [0:nPartial] do
    let round := nRoundsF / 2 + nPartial - 1 - step
    let mut transformed := vectorTimesMatrix accumulator matrixInv
    partialConstants := partialConstants.push transformed[0]!
    transformed := transformed.set! 0 0
    let roundStart := round * width
    accumulator := Array.zipWith modAdd transformed
      (constants.extract roundStart (roundStart + width))

  result := result ++ vectorTimesMatrix accumulator matrixInv
  result := result ++ partialConstants.reverse

  for round in [nRoundsF / 2 + nPartial:nRoundsF + nPartial - 1] do
    let roundStart := (round + 1) * width
    result := result ++ vectorTimesMatrix
      (constants.extract roundStart (roundStart + width)) matrixInv
  return result

def sparseFactorize (matrix : Matrix) : Matrix × Array ℕ :=
  let width := matrix.size
  let mHat := (matrix.extract 1 width).map fun row => row.extract 1 width
  let mPrime := Array.ofFn fun i : Fin width =>
    Array.ofFn fun j : Fin width =>
      if i.val > 0 && j.val > 0 then matrix[i.val]![j.val]!
      else if i.val = 0 && j.val = 0 then 1 else 0
  let w := Array.ofFn fun i : Fin (width - 1) => matrix[i.val + 1]![0]!
  let wPrime := matrixTimesVector (matrixInverse mHat) w
  let sparse := (#[matrix[0]![0]!] ++ wPrime) ++ matrix[0]!.extract 1 width
  (mPrime, sparse)

def calculateSparse (nPartial : ℕ) (matrix : Matrix) : Matrix × Array ℕ := Id.run do
  let mut current := matrix
  let mut sparseMatrices := #[]
  for _ in [0:nPartial] do
    let (mPrime, sparse) := sparseFactorize current
    sparseMatrices := sparseMatrices.push sparse
    current := matrixMultiply matrix mPrime
  let mut sparse := #[]
  for values in sparseMatrices.reverse do
    sparse := sparse ++ values
  return (current, sparse)

def reproduce (width nPartial : ℕ) : OptimizedParameters :=
  let base := generateBase width nPartial
  let matrix := transpose base.matrix
  let constants := compressConstants width nPartial base.constants matrix
  let (preSparse, sparse) := calculateSparse nPartial matrix
  { C := constants, M := matrix, P := preSparse, S := sparse }

end Specs.Poseidon.ParameterGeneration
