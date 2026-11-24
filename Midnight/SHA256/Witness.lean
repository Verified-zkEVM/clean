import Midnight.SHA256.Tables

/-! Pure advice computations ported from Midnight's SHA chip.

Source: `circuits/src/hash/utils.rs`, `hash/sha256/utils.rs` and the advice
callbacks in `hash/sha256/sha256_chip.rs` (Midnight Foundation, Apache-2.0).
These functions compute witness values from their inputs. They do not assert
that a circuit constrains those values; semantic gadget proofs supply that link.
Natural numbers make intermediate integer sums explicit. The source's `u32`
and `u64` domains are represented by stated range hypotheses where needed.
-/

namespace Midnight.SHA256.Witness

def wordModulus : Nat := 2 ^ 32
def evenMask : Nat := 0x5555555555555555

/-- Rust `spread`: only the low 32 input bits participate. -/
def spread32 (value : Nat) : Nat :=
  (List.range 32).foldl (fun acc i =>
    acc ||| (((value >>> i) &&& 1) <<< (2 * i))) 0

/-- Exact mask/shift compaction from Rust `compact_even`. The first mask also
truncates any bits above the source u64 domain. -/
def compactEven (value : Nat) : Nat :=
  let x := value &&& evenMask
  let x := (x ||| (x >>> 1)) &&& 0x3333333333333333
  let x := (x ||| (x >>> 2)) &&& 0x0f0f0f0f0f0f0f0f
  let x := (x ||| (x >>> 4)) &&& 0x00ff00ff00ff00ff
  let x := (x ||| (x >>> 8)) &&& 0x0000ffff0000ffff
  (x ||| (x >>> 16)) &&& 0x00000000ffffffff

def evenBits (value : Nat) : Nat := compactEven value
def oddBits (value : Nat) : Nat := compactEven (value >>> 1)
def negateSpread (value : Nat) : Nat := value ^^^ evenMask

/-- A big-endian word decomposition represented by its low-bit offsets and widths. -/
abbrev Slice := Nat × Nat

def limb (value : Nat) (slice : Slice) : Nat :=
  (value >>> slice.1) % 2 ^ slice.2

def parityLayout : Vector Slice 3 := #v[(21,11),(10,11),(0,10)]
def messageLayout : Vector Slice 8 :=
  #v[(20,12),(19,1),(18,1),(17,1),(10,7),(7,3),(3,4),(0,3)]

theorem limb_lt (value : Nat) (slice : Slice) : limb value slice < 2 ^ slice.2 :=
  Nat.mod_lt _ (by positivity)

/-- Each term names an exponent of four and an in-bounds source limb. -/
abbrev Recipe (n : Nat) := List (Nat × Fin n)

def weighted {n : Nat} (recipe : Recipe n) (values : Vector Nat n) : Nat :=
  recipe.foldr (fun (exponent, index) acc => 4 ^ exponent * values[index] + acc) 0

-- The three rotation/shift sums are kept in the same term order as Rust.
def bigSigma0Recipe : Recipe 4 :=
  [(30,3),(20,0),(11,1),(0,2),
   (21,2),(19,3),(9,0),(0,1),
   (23,1),(12,2),(10,3),(0,0)]

def bigSigma1Recipe : Recipe 5 :=
  [(26,4),(19,0),(7,1),(5,2),(0,3),
   (27,3),(21,4),(14,0),(2,1),(0,2),
   (20,1),(18,2),(13,3),(7,4),(0,0)]

def sigma0Recipe : Recipe 8 :=
  [(17,0),(16,1),(15,2),(14,3),(7,4),(4,5),(0,6),
   (28,6),(25,7),(13,0),(12,1),(11,2),(10,3),(3,4),(0,5),
   (31,3),(24,4),(21,5),(17,6),(14,7),(2,0),(1,1),(0,2)]

def sigma1Recipe : Recipe 8 :=
  [(10,0),(9,1),(8,2),(7,3),(0,4),
   (25,4),(22,5),(18,6),(15,7),(3,0),(2,1),(1,2),(0,3),
   (31,2),(30,3),(23,4),(20,5),(16,6),(13,7),(1,0),(0,1)]

def spreadedBigSigma0 (values : Vector Nat 4) : Nat := weighted bigSigma0Recipe values
def spreadedBigSigma1 (values : Vector Nat 5) : Nat := weighted bigSigma1Recipe values
def spreadedSigma0 (values : Vector Nat 8) : Nat := weighted sigma0Recipe values
def spreadedSigma1 (values : Vector Nat 8) : Nat := weighted sigma1Recipe values

def sum32 (values : List Nat) : Nat := values.sum % wordModulus
def carry32 (values : List Nat) : Nat := values.sum / wordModulus

theorem sum32_lt (values : List Nat) : sum32 values < wordModulus :=
  Nat.mod_lt _ (by decide)

private theorem sum_le_length_mul (values : List Nat) (bound : Nat)
    (h : ∀ value ∈ values, value ≤ bound) : values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have hv := h value (by simp)
    have hr := ih (fun v hm => h v (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Seven 32-bit inputs fit in the source chip's three-bit carry lookup. -/
theorem carry32_lt_eight (values : List Nat) (hcount : values.length ≤ 7)
    (hvalues : ∀ value ∈ values, value < wordModulus) : carry32 values < 8 := by
  have hsum := sum_le_length_mul values (wordModulus - 1) (fun v hv => by
    have := hvalues v hv
    omega)
  dsimp [carry32, wordModulus] at *
  omega

end Midnight.SHA256.Witness
