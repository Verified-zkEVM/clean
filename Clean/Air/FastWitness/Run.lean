module

public import Clean.Air.FastWitness.Compile
public import CompPoly.Data.ByteArray.Packed

@[expose] public section

/-!
# Running register programs

Runs the kernels of `Clean.Air.FastWitness.Compile`: a trace is generated in chunks of consecutive
rows, one task per chunk, each writing its rows as packed Montgomery words into one `ByteArray`. A
row is computed in a buffer of two rows, after the previous row, and appended to its chunk; a chunk
that starts within a segment first computes the segment's earlier rows.

The interpreter's registers are a `ByteArray` of 64-bit words, so that it runs on unboxed words.
Kernels compiled to native code by `fast_witness_kernel` (`Clean.Air.FastWitness.Codegen`) run the
same way, without the interpreter.
-/

namespace Air.Flat.FastWitness
open Montgomery.Native32

/-! ### Words

Branch-free operations on 64-bit words, shared by the interpreter and the kernels that
`Clean.Air.FastWitness.Codegen` generates. Field words are canonical Montgomery words below `p`. -/

/-- Montgomery reduction of `x < p · 2^32`, for `p < 2^31` given as `p64`, and `negInv` the
negated inverse of `p` modulo `2^32`. -/
@[inline] def reduceWord (p64 negInv x : UInt64) : UInt64 :=
  let m := (x.toUInt32 * negInv.toUInt32).toUInt64
  let u := (x + m * p64) >>> 32
  let t := u - p64
  t + (p64 &&& ((0 : UInt64) - (t >>> 63)))

/-- The sum of two field words. -/
@[inline] def addWord (p64 a b : UInt64) : UInt64 :=
  let t := a + b - p64
  t + (p64 &&& ((0 : UInt64) - (t >>> 63)))

/-- `1` if `a = b`, else `0`. -/
@[inline] def eqWord (a b : UInt64) : UInt64 :=
  let d := a ^^^ b
  ((d ||| ((0 : UInt64) - d)) >>> 63) ^^^ 1

/-- `1` if `a < b`, else `0`. -/
@[inline] def ltWord (a b : UInt64) : UInt64 :=
  ((~~~a &&& b) ||| (~~~(a ^^^ b) &&& (a - b))) >>> 63

/-- `yes` if `condition = 1`, `no` if `condition = 0`. -/
@[inline] def selectWord (condition yes no : UInt64) : UInt64 :=
  no ^^^ ((yes ^^^ no) &&& ((0 : UInt64) - condition))

/-- The word of bit `shift` of `value`: `0` or the word of one, `one`. -/
@[inline] def bitWord (one : UInt32) (value shift : UInt64) : UInt32 :=
  one * ((value >>> shift) &&& 1).toUInt32

/-- `words[index]`, or `0` out of range. -/
def tableWord (words : @& Array UInt64) (index : UInt64) : UInt64 := words.getD index.toNat 0

/-- Column `column` of row `row` of a table of rows of `width` words, or `0` out of range. -/
def hintWord (hints : @& Array ByteArray) (table width : ℕ) (row : UInt64) (column : ℕ) :
    UInt64 :=
  let words := hints[table]!
  if row.toNat < words.size / (4 * width) then
    (words.getUInt32LE! (4 * (row.toNat * width + column))).toUInt64
  else 0

/-- A buffer of `n` bytes. -/
abbrev Rows (n : ℕ) := {rows : ByteArray // rows.size = n}

/-- A buffer as a buffer of its size. -/
@[inline] def Rows.of (rows : ByteArray) : Rows rows.size := ⟨rows, rfl⟩

@[inline] def Rows.buffer {n : ℕ} (rows : Rows n) : ByteArray := rows.1

/-- Whether a buffer of `n` bytes has room for `width` words from byte offset `base`. -/
def Room (n width : ℕ) (base : USize) : Prop :=
  base.toNat + 4 * width ≤ n ∧ base.toNat + 4 * width < USize.size

instance (n width : ℕ) (base : USize) : Decidable (Room n width base) := by
  unfold Room
  infer_instance

theorem Room.word {n width : ℕ} {base : USize} (room : Room n width base) {k : ℕ}
    (hk : k < width) : (base + (4 * k).toUSize).toNat + 4 ≤ n := by
  obtain ⟨h1, h2⟩ := room
  have hsize : (2 : ℕ) ^ System.Platform.numBits = USize.size := rfl
  have h4 : (4 * k).toUSize.toNat = 4 * k := USize.toNat_ofNat_of_lt' (by omega)
  rw [USize.toNat_add, h4, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Store `value` as word `k` from byte offset `base`. -/
@[inline] def storeAt {n width : ℕ} (rows : Rows n) (base : USize) (room : Room n width base)
    (k : ℕ) (hk : k < width) (value : UInt32) : Rows n :=
  ⟨rows.1.usetUInt32LE (base + (4 * k).toUSize) value (by rw [rows.2]; exact room.word hk),
    by rw [ByteArray.size_usetUInt32LE, rows.2]⟩

/-- Word `k` from byte offset `base`. -/
@[inline] def loadAt {n width : ℕ} (rows : @& Rows n) (base : USize) (room : Room n width base)
    (k : ℕ) (hk : k < width) : UInt32 :=
  rows.1.ugetUInt32LE (base + (4 * k).toUSize) (by rw [rows.2]; exact room.word hk)

variable {p : ℕ} [P : Mont32Field p]

/-- The field word of the inverse of a field word, `0` for `0`. -/
def inverseWord (a : UInt64) : UInt64 :=
  if h : a.toUInt32.toNat < p then (inv (⟨a.toUInt32, h⟩ : FastField p)).val.toUInt64 else 0

/-- The constants of `p` that the word operations take: `p`, the negated inverse of `p` modulo
`2^32`, `2^64 mod p` and the word of one. -/
def fieldConstants : UInt64 × UInt64 × UInt64 × UInt32 :=
  (P.modulus64, P.montgomeryNegInv.toUInt64, P.r2ModModulus, P.rModModulus)

@[inline] def reduce (x : UInt64) : UInt64 := reduceWord P.modulus64 P.montgomeryNegInv.toUInt64 x

@[inline] def binary (op : BinaryOp) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b
  | .mul => a * b
  | .div => a / b
  | .mod => a % b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shiftLeft => a <<< b
  | .shiftRight => a >>> b
  | .eq => eqWord a b
  | .lt => ltWord a b
  | .fieldAdd => addWord P.modulus64 a b
  | .fieldMul => reduce (p := p) (a * b)

/-! ### The interpreter -/

@[inline] def getRegister (registers : @& ByteArray) (r : ℕ) : UInt64 :=
  (registers.getUInt32LE! (8 * r)).toUInt64 ||| (registers.getUInt32LE! (8 * r + 4)).toUInt64 <<< 32

@[inline] def setRegister (registers : ByteArray) (r : ℕ) (v : UInt64) : ByteArray :=
  (registers.setUInt32LE! (8 * r) v.toUInt32).setUInt32LE! (8 * r + 4) (v >>> 32).toUInt32

/-- The registers and the rows that a task writes. -/
structure Machine where
  registers : ByteArray
  rows : ByteArray

/-- Where a row is in the rows buffer, in words. -/
structure Position where
  current : ℕ
  previous : ℕ

/-- Store bits `shift, …, shift + count - 1` of `value`. -/
def storeBits (one : UInt32) (value : UInt64) (rows : ByteArray) (offset : ℕ) (shift : UInt64) :
    ℕ → ByteArray
  | 0 => rows
  | count + 1 =>
      let rows := rows.setUInt32LE! offset (bitWord one value shift)
      storeBits one value rows (offset + 4) (shift + 1) count

/-- Copy `count` words from byte offset `source` to `target`. -/
def copyWords (rows : ByteArray) (source target : ℕ) : ℕ → ByteArray
  | 0 => rows
  | count + 1 =>
      let rows := rows.setUInt32LE! target (rows.getUInt32LE! source)
      copyWords rows (source + 4) (target + 4) count

mutual

/-- Run instructions `i, …` of `code` on the row at `position`. -/
partial def exec (hints : @& Array ByteArray) (position : Position) (code : @& Array Instr)
    (i : ℕ) (m : Machine) : Machine :=
  if h : i < code.size then
    exec hints position code (i + 1) (step hints position code[i] m)
  else m

partial def step (hints : @& Array ByteArray) (position : Position) (instr : @& Instr)
    (m : Machine) : Machine :=
  match m with
  | ⟨registers, rows⟩ =>
  match instr with
  | .binary op dest left right =>
      { registers := setRegister registers dest
          (binary (p := p) op (getRegister registers left) (getRegister registers right)), rows }
  | .select dest condition yes no =>
      { registers := setRegister registers dest (selectWord (getRegister registers condition)
          (getRegister registers yes) (getRegister registers no)), rows }
  | .value dest source =>
      { registers := setRegister registers dest (reduce (p := p) (getRegister registers source)),
        rows }
  | .ofU64 dest source =>
      { registers := setRegister registers dest
          (reduce (p := p) ((getRegister registers source % P.modulus64) * P.r2ModModulus)), rows }
  | .ofSmall dest source =>
      { registers := setRegister registers dest
          (reduce (p := p) (getRegister registers source * P.r2ModModulus)), rows }
  | .inverse dest source =>
      { registers := setRegister registers dest
          (inverseWord (p := p) (getRegister registers source)), rows }
  | .table dest index words =>
      { registers := setRegister registers dest (tableWord words (getRegister registers index)),
        rows }
  | .pick dest index sources =>
      { registers := setRegister registers dest
          (tableWord (sources.map (getRegister registers)) (getRegister registers index)), rows }
  | .previous dest column =>
      { registers := setRegister registers dest
          (rows.getUInt32LE! (4 * (position.previous + column))).toUInt64, rows }
  | .current dest column =>
      { registers := setRegister registers dest
          (rows.getUInt32LE! (4 * (position.current + column))).toUInt64, rows }
  | .hint dest table width row column =>
      { registers := setRegister registers dest
          (hintWord hints table width (getRegister registers row) column), rows }
  | .store column source =>
      { registers, rows := rows.setUInt32LE! (4 * (position.current + column))
          (getRegister registers source).toUInt32 }
  | .storeBits column source shift count =>
      { registers, rows := storeBits P.rModModulus (getRegister registers source) rows
          (4 * (position.current + column)) shift.toUInt64 count }
  | .copy column previousColumn count =>
      { registers, rows := copyWords rows (4 * (position.previous + previousColumn))
          (4 * (position.current + column)) count }
  | .loop count index result column body =>
      loop hints position body index result column count 0 ⟨registers, rows⟩

/-- Iterations `k, …, count - 1` of a loop. -/
partial def loop (hints : @& Array ByteArray) (position : Position) (body : @& Array Instr)
    (index result column count k : ℕ) (m : Machine) : Machine :=
  if k < count then
    match exec hints position body 0 ⟨setRegister m.registers index k.toUInt64, m.rows⟩ with
    | ⟨registers, rows⟩ =>
      loop hints position body index result column count (k + 1)
        ⟨registers, rows.setUInt32LE! (4 * (position.current + column + k))
          (getRegister registers result).toUInt32⟩
  else m

end

/-- How a task computes rows into its buffer: `run state rows row position` writes row `row` at
`position` of `rows`, reading the previous row there unless the row starts a segment, and threads a
state through the rows of the task. -/
structure RowRunner (σ : Type) where
  init : σ
  run : σ → ByteArray → ℕ → Position → σ × ByteArray

/-- Rows `start, …, start + count - 1` of a trace with rows of `width` words in segments of
`length`, as packed words. Each row is computed in a buffer of two rows, after the previous row,
and appended; a chunk that starts within a segment first computes the segment's earlier rows. -/
def chunk {σ : Type} (runner : RowRunner σ) (width length start count : ℕ) : ByteArray := Id.run do
  let segmentStart := if length = 0 then 0 else start - start % length
  let mut state := runner.init
  let mut scratch := ByteArray.zeros (8 * width)
  let mut rows := ByteArray.emptyWithCapacity (4 * count * width)
  for row in [segmentStart:start + count] do
    let slot := (row - segmentStart) % 2
    (state, scratch) := runner.run state scratch row
      { current := slot * width, previous := (1 - slot) * width }
    if start ≤ row then
      rows := scratch.copySlice (4 * slot * width) rows rows.size (4 * width)
  return rows

/-- The `height` rows of a trace in `chunks` chunks of consecutive rows, one task each. -/
def chunks {σ : Type} (runner : RowRunner σ) (width length height chunks : ℕ) :
    Array ByteArray :=
  let rows := height / chunks
  let tasks := (Array.range chunks).map fun c =>
    Task.spawn fun _ => chunk runner width length (c * rows) rows
  tasks.map Task.get

/-- Whether row `row` starts a segment of `length`. -/
@[inline] def startsSegment (length row : ℕ) : Bool :=
  if length = 0 then row = 0 else row % length = 0

/-- The interpreter of a kernel, whose state is its registers. -/
def Kernel.runner (kernel : Kernel) (hints : Array ByteArray) : RowRunner ByteArray where
  init := kernel.constants.foldl (fun registers (r, v) => setRegister registers r v)
    (ByteArray.zeros (8 * kernel.registers))
  run registers rows row position :=
    let code := if startsSegment kernel.length row then kernel.first else kernel.next
    let m := exec (p := p) hints position code 0
      ⟨setRegister registers kernel.index row.toUInt64, rows⟩
    (m.registers, m.rows)

/-- The trace of a segment-generated component, each row's cells but the fixed and the window
cells, as packed Montgomery words in `2 ^ logChunks` chunks of consecutive rows: CompStark's chunks
of packed rows (`rowChunks`). `hints` are the hint tables that its programs read, by key and width,
as packed words, row after row. -/
def segmentTrace (component : Component (F p)) (hints : Array (String × ℕ × ByteArray))
    (logChunks : ℕ) : Except String (Array ByteArray) := do
  let kernel ← compileSegments component (hints.map fun (key, width, _) => (key, width))
  let height := (component.fixedColumns.map (·.height.toNat)).getD 0
  unless 2 ^ logChunks ∣ height do
    throw s!"{2 ^ logChunks} chunks don't divide {height} rows"
  return chunks (kernel.runner (p := p) (hints.map (·.2.2))) kernel.width kernel.length height
    (2 ^ logChunks)

/-- A kernel compiled to native code by `fast_witness_kernel`: the functions writing a row that
starts a segment and another row, from the rows buffer, the hint tables, the word offsets of the
row and the previous row, and the row's index. -/
structure CompiledKernel where
  width : ℕ
  length : ℕ
  first : ByteArray → Array ByteArray → ℕ → ℕ → UInt64 → ByteArray
  next : ByteArray → Array ByteArray → ℕ → ℕ → UInt64 → ByteArray

/-- A compiled kernel's rows. -/
def CompiledKernel.runner (kernel : CompiledKernel) (hints : Array ByteArray) : RowRunner Unit where
  init := ()
  run _ rows row position :=
    let run := if startsSegment kernel.length row then kernel.first else kernel.next
    ((), run rows hints position.current position.previous row.toUInt64)

/-- A compiled kernel's trace of `height` rows in `2 ^ logChunks` chunks. -/
def CompiledKernel.trace (kernel : CompiledKernel) (hints : Array ByteArray)
    (height logChunks : ℕ) :
    Except String (Array ByteArray) := do
  unless 2 ^ logChunks ∣ height do
    throw s!"{2 ^ logChunks} chunks don't divide {height} rows"
  return chunks (kernel.runner hints) kernel.width kernel.length height (2 ^ logChunks)

end Air.Flat.FastWitness
