module

public import Clean.Air.FlatEnsemble
public import Clean.Air.WitnessGeneration.Kernel
public import CompPoly.Data.ByteArray.Packed

@[expose] public section

/-!
# Packed traces

The trace of a segment-generated component over a field `K`, as a backend commits it: each row's
cells but the window cells, in the layout of `CompPoly.PackedRepr K`, rows one after the other, in
`2 ^ k` chunks of consecutive rows (CompStark's `rowChunks`). One task computes each chunk, running
the component's kernel (`Clean.Air.WitnessGeneration.Kernel`). A row is computed in a buffer of two
rows, after the previous row, and appended to its chunk; a chunk that starts within a segment first
computes the segment's earlier rows.

The interpreter keeps its registers in buffers too, field registers in `PackedRepr K` layout and
word registers as 64-bit words, so that it runs on unboxed values. Kernels compiled to native code
by `witness_kernel` (`Clean.Air.WitnessGeneration.Codegen`) run the same way, without the
interpreter.
-/

namespace Air.Flat.WitnessGeneration
open CompPoly

variable {K : Type} [FiniteField K] [WordField K] [PackedRepr K]

/-! ### Elements in buffers -/

/-- Element `j` of a buffer, or `0` past its end. -/
@[inline] def loadElement (b : @& ByteArray) (j : ℕ) : K :=
  if h : j < b.size / PackedRepr.width K ∧ b.size < USize.size then
    PackedRepr.getAt b j.toUSize (by
      rw [USize.toNat_ofNat_of_lt' (by have := Nat.div_le_self b.size (PackedRepr.width K); omega)]
      exact h.1) h.2
  else 0

/-- A buffer with element `j` overwritten, unchanged past its end. -/
@[inline] def storeElement (b : ByteArray) (j : ℕ) (x : K) : ByteArray :=
  if h : j < b.size / PackedRepr.width K ∧ b.size < USize.size then
    PackedRepr.setAt b j.toUSize x (by
      rw [USize.toNat_ofNat_of_lt' (by have := Nat.div_le_self b.size (PackedRepr.width K); omega)]
      exact h.1) h.2
  else b

/-- The keys and widths of hint tables, as kernels name them (`compileSegments`). -/
def hintKeys (tables : List HintTable) : Array (String × ℕ) :=
  tables.toArray.map fun table => (table.key, table.width)

variable (K) in
/-- The hint tables cut from the packed private input of an ensemble, as `prepareHint` cuts them
from its elements. -/
def packedHints (tables : List HintTable) (input : ByteArray) : Array ByteArray :=
  tables.toArray.map fun table =>
    input.extract (PackedRepr.width K * table.offset)
      (PackedRepr.width K * (table.offset + table.rows * table.width))

/-- `values[index]`, or `0` out of range. -/
@[inline] def tableElement (values : @& Array K) (index : UInt64) : K := values.getD index.toNat 0

/-- Column `column` of row `row` of a table of rows of `width` elements, or `0` out of range. -/
@[inline] def hintElement (hints : @& Array ByteArray) (table width : ℕ) (row : UInt64)
    (column : ℕ) : K :=
  let rows := hints[table]!
  if row.toNat < rows.size / (PackedRepr.width K * width) then
    loadElement rows (row.toNat * width + column)
  else 0

/-! ### Operations -/

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

@[inline] def wordOp (op : WordOp) (a b : UInt64) : UInt64 :=
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

@[inline] def fieldOp (op : FieldOp) (a b : K) : K :=
  match op with
  | .add => a + b
  | .mul => a * b

/-- `1` if `a = b`, else `0`. -/
@[inline] def eqField (a b : K) : UInt64 := if a = b then 1 else 0

/-- `yes` if `condition ≠ 0`, else `no`. -/
@[inline] def selectField (condition : UInt64) (yes no : K) : K := if condition = 0 then no else yes

/-- Bit `shift` of `value`, as the element `bits[0]` or `bits[1]`. -/
@[inline] def bitElement (bits : Vector K 2) (value shift : UInt64) : K :=
  bits[((value >>> shift) &&& 1).toNat]'(by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

/-! ### The interpreter -/

@[inline] def getWord (words : @& ByteArray) (r : ℕ) : UInt64 :=
  (words.getUInt32LE! (8 * r)).toUInt64 ||| (words.getUInt32LE! (8 * r + 4)).toUInt64 <<< 32

@[inline] def setWord (words : ByteArray) (r : ℕ) (v : UInt64) : ByteArray :=
  (words.setUInt32LE! (8 * r) v.toUInt32).setUInt32LE! (8 * r + 4) (v >>> 32).toUInt32

/-- The registers and the rows that a task writes. -/
structure Machine where
  fields : ByteArray
  words : ByteArray
  rows : ByteArray

/-- Where a row is in the rows buffer, in elements. -/
structure Position where
  current : ℕ
  previous : ℕ

/-- Store bits `shift, …, shift + count - 1` of `value` in elements `j, …`. -/
def storeBits (value : UInt64) (rows : ByteArray) (j : ℕ) (shift : UInt64) : ℕ → ByteArray
  | 0 => rows
  | count + 1 =>
      storeBits value (storeElement rows j (bitElement #v[0, 1] value shift : K)) (j + 1)
        (shift + 1) count

/-- Copy `count` elements from `source` to `target`. -/
def copyElements (rows : ByteArray) (source target : ℕ) : ℕ → ByteArray
  | 0 => rows
  | count + 1 =>
      copyElements (storeElement rows target (loadElement rows source : K)) (source + 1)
        (target + 1) count

variable (K) in
mutual

/-- Run instructions `i, …` of `code` on the row at `position`. -/
partial def exec (hints : @& Array ByteArray) (position : Position) (code : @& Array (Instr K))
    (i : ℕ) (m : Machine) : Machine :=
  if h : i < code.size then
    exec hints position code (i + 1) (step hints position code[i] m)
  else m

partial def step (hints : @& Array ByteArray) (position : Position) (instr : @& Instr K)
    (m : Machine) : Machine :=
  match m with
  | ⟨fields, words, rows⟩ =>
  let field (r : ℕ) : K := loadElement fields r
  let word (r : ℕ) : UInt64 := getWord words r
  let setField (r : ℕ) (x : K) : Machine := ⟨storeElement fields r x, words, rows⟩
  let setWord' (r : ℕ) (v : UInt64) : Machine := ⟨fields, setWord words r v, rows⟩
  match instr with
  | .word op dest left right => setWord' dest (wordOp op (word left) (word right))
  | .field op dest left right => setField dest (fieldOp op (field left) (field right))
  | .fieldEq dest left right => setWord' dest (eqField (field left) (field right))
  | .selectWord dest condition yes no =>
      setWord' dest (selectWord (word condition) (word yes) (word no))
  | .selectField dest condition yes no =>
      setField dest (selectField (word condition) (field yes) (field no))
  | .value dest source => setWord' dest (WordField.toWord (field source))
  | .ofWord dest source => setField dest (WordField.ofWord (word source))
  | .ofSmallWord dest source => setField dest (WordField.ofSmallWord (word source))
  | .inverse dest source => setField dest (field source)⁻¹
  | .table dest index values => setField dest (tableElement values (word index))
  | .pick dest index sources =>
      setField dest (tableElement (sources.map field) (word index))
  | .previous dest column => setField dest (loadElement rows (position.previous + column))
  | .current dest column => setField dest (loadElement rows (position.current + column))
  | .hint dest table width row column =>
      setField dest (hintElement hints table width (word row) column)
  | .store column source => ⟨fields, words, storeElement rows (position.current + column)
      (field source)⟩
  | .storeBits column source shift count =>
      ⟨fields, words, storeBits (K := K) (word source) rows (position.current + column)
        shift.toUInt64 count⟩
  | .copy column previousColumn count =>
      ⟨fields, words, copyElements (K := K) rows (position.previous + previousColumn)
        (position.current + column) count⟩
  | .loop count index result column body =>
      loop hints position body index result column count 0 m

/-- Iterations `k, …, count - 1` of a loop. -/
partial def loop (hints : @& Array ByteArray) (position : Position) (body : @& Array (Instr K))
    (index result column count k : ℕ) (m : Machine) : Machine :=
  if k < count then
    match exec hints position body 0 { m with words := setWord m.words index k.toUInt64 } with
    | ⟨fields, words, rows⟩ =>
      loop hints position body index result column count (k + 1)
        ⟨fields, words, storeElement rows (position.current + column + k)
          (loadElement fields result : K)⟩
  else m

end

/-! ### Traces -/

/-- How a task computes rows into its buffer: `run state rows row position` writes row `row` at
`position` of `rows`, reading the previous row there unless the row starts a segment, and threads a
state through the rows of the task. -/
structure RowRunner (σ : Type) where
  init : σ
  run : σ → ByteArray → ℕ → Position → σ × ByteArray

variable (K) in
/-- Rows `start, …, start + count - 1` of a trace with rows of `width` elements in segments of
`length`. Each row is computed in a buffer of two rows, after the previous row, and appended; a
chunk that starts within a segment first computes the segment's earlier rows. -/
def chunk {σ : Type} (runner : RowRunner σ) (width length start count : ℕ) : ByteArray := Id.run do
  let rowBytes := PackedRepr.width K * width
  let segmentStart := if length = 0 then 0 else start - start % length
  let mut state := runner.init
  let mut scratch := ByteArray.zeros (2 * rowBytes)
  let mut rows := ByteArray.emptyWithCapacity (count * rowBytes)
  for row in [segmentStart:start + count] do
    let slot := (row - segmentStart) % 2
    (state, scratch) := runner.run state scratch row
      { current := slot * width, previous := (1 - slot) * width }
    if start ≤ row then
      rows := scratch.copySlice (slot * rowBytes) rows rows.size rowBytes
  return rows

/-- Whether row `row` starts a segment of `length`. -/
@[inline] def startsSegment (length row : ℕ) : Bool :=
  if length = 0 then row = 0 else row % length = 0

variable (K) in
/-- The `height` rows of a trace in `2 ^ logChunks` chunks of consecutive rows, one task each. -/
def trace {σ : Type} (runner : RowRunner σ) (width length height logChunks : ℕ) :
    Except String (Array ByteArray) := do
  let chunks := 2 ^ logChunks
  unless chunks ∣ height do
    throw s!"{chunks} chunks don't divide {height} rows"
  let rows := height / chunks
  let tasks := (Array.range chunks).map fun c =>
    Task.spawn fun _ => chunk K runner width length (c * rows) rows
  return tasks.map Task.get

/-- The interpreter of a kernel, whose state is its registers. -/
def Kernel.runner (kernel : Kernel K) (hints : Array ByteArray) :
    RowRunner (ByteArray × ByteArray) where
  init :=
    (kernel.fieldConstants.foldl (fun fields (r, x) => storeElement fields r x)
      (ByteArray.zeros (PackedRepr.width K * kernel.fieldRegisters)),
    kernel.wordConstants.foldl (fun words (r, v) => setWord words r v)
      (ByteArray.zeros (8 * kernel.wordRegisters)))
  run registers rows row position :=
    let code := if startsSegment kernel.length row then kernel.first else kernel.next
    let m := exec K hints position code 0
      ⟨registers.1, setWord registers.2 kernel.index row.toUInt64, rows⟩
    ((m.fields, m.words), m.rows)

/-- The packed trace of `height` rows of a kernel, interpreted, in `2 ^ logChunks` chunks, reading
the hint tables `hints` (`packedHints`). -/
def Kernel.trace (kernel : Kernel K) (hints : Array ByteArray) (height logChunks : ℕ) :
    Except String (Array ByteArray) :=
  WitnessGeneration.trace K (kernel.runner hints) kernel.width kernel.length height logChunks

/-! ### Compiled kernels -/

/-- A buffer of `n` bytes. -/
abbrev Rows (n : ℕ) := {rows : ByteArray // rows.size = n}

/-- A buffer as a buffer of its size. -/
@[inline] def Rows.of (rows : ByteArray) : Rows rows.size := ⟨rows, rfl⟩

@[inline] def Rows.buffer {n : ℕ} (rows : Rows n) : ByteArray := rows.1

variable (K) in
/-- Whether a buffer of `n` bytes has room for `width` elements from element `base`. -/
def Room (n width : ℕ) (base : USize) : Prop :=
  base.toNat + width ≤ n / PackedRepr.width K ∧ n < USize.size

instance (n width : ℕ) (base : USize) : Decidable (Room K n width base) := by
  unfold Room
  infer_instance

omit [FiniteField K] [WordField K] in
theorem Room.element {n width : ℕ} {base : USize} (room : Room K n width base) {k : ℕ}
    (hk : k < width) : (base + k.toUSize).toNat < n / PackedRepr.width K := by
  obtain ⟨h1, h2⟩ := room
  have hsize : (2 : ℕ) ^ System.Platform.numBits = USize.size := rfl
  have hdiv := Nat.div_le_self n (PackedRepr.width K)
  have hk' : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  rw [USize.toNat_add, hk', hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Store `value` as element `k` from element `base`. -/
@[inline] def storeAt {n width : ℕ} (rows : Rows n) (base : USize) (room : Room K n width base)
    (k : ℕ) (hk : k < width) (value : K) : Rows n :=
  ⟨PackedRepr.setAt rows.1 (base + k.toUSize) value (by rw [rows.2]; exact room.element hk)
      (by rw [rows.2]; exact room.2),
    by rw [PackedRepr.size_setAt, rows.2]⟩

/-- Element `k` from element `base`. -/
@[inline] def loadAt {n width : ℕ} (rows : @& Rows n) (base : USize) (room : Room K n width base)
    (k : ℕ) (hk : k < width) : K :=
  PackedRepr.getAt rows.1 (base + k.toUSize) (by rw [rows.2]; exact room.element hk)
    (by rw [rows.2]; exact room.2)

/-- A kernel over `K` compiled to native code by `witness_kernel`: the functions writing a row that
starts a segment and another row, from the rows buffer, the hint tables, the element offsets of the
row and the previous row, and the row's index. -/
structure CompiledKernel (K : Type) where
  width : ℕ
  length : ℕ
  first : ByteArray → Array ByteArray → ℕ → ℕ → UInt64 → ByteArray
  next : ByteArray → Array ByteArray → ℕ → ℕ → UInt64 → ByteArray

/-- A compiled kernel's rows. -/
def CompiledKernel.runner (kernel : CompiledKernel K) (hints : Array ByteArray) :
    RowRunner Unit where
  init := ()
  run _ rows row position :=
    let run := if startsSegment kernel.length row then kernel.first else kernel.next
    ((), run rows hints position.current position.previous row.toUInt64)

/-- The packed trace of `height` rows of a compiled kernel, in `2 ^ logChunks` chunks, reading the
hint tables `hints` (`packRows`). -/
def CompiledKernel.trace (kernel : CompiledKernel K) (hints : Array ByteArray)
    (height logChunks : ℕ) : Except String (Array ByteArray) :=
  WitnessGeneration.trace K (kernel.runner hints) kernel.width kernel.length height logChunks

end Air.Flat.WitnessGeneration
