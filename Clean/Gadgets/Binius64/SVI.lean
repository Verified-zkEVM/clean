import Mathlib.Data.ZMod.Basic
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Utils.Vector

namespace Gadgets.Binius64

/--
Structured representation of a Binius shifted vector index (SVI).

The wire is encoded using the `fields 64` provable type, while the shift
metadata lives directly in the base field.
-/
structure SVIData (F : Type) where
  wire : (fields 64) F
  shiftType : F
  shiftAmount : F
deriving Repr

@[reducible]
def SVI : TypeMap := SVIData

instance : ProvableStruct SVI where
  components := [fields 64, field, field]
  toComponents := fun { wire, shiftType, shiftAmount } =>
    .cons wire (.cons shiftType (.cons shiftAmount .nil))
  fromComponents := fun
    | .cons wire (.cons shiftType (.cons shiftAmount .nil)) =>
        { wire, shiftType, shiftAmount }

/-- Enumeration of supported shift kinds. -/
inductive ShiftKind
  | sll
  | srl
  | sra
  deriving DecidableEq, Repr

namespace ShiftKind

/-- Encode a shift kind as a natural number. -/
def toNat : ShiftKind → ℕ
  | .sll => 0
  | .srl => 1
  | .sra => 2

/-- Decode a shift kind from a natural number. Values wrap modulo 3. -/
def fromNat (n : ℕ) : ShiftKind :=
  match n % 3 with
  | 0 => .sll
  | 1 => .srl
  | _ => .sra

end ShiftKind

/-- Restrict a shift amount to the `0 ≤ amount < 64` range. -/
def normalizeShiftAmount (n : ℕ) : ℕ :=
  n % 64

/-- Decode a shift kind from a field element. -/
def decodeShiftKind {p : ℕ} [Fact p.Prime] (x : F p) : ShiftKind :=
  ShiftKind.fromNat x.val

/-- Decode (and normalise) a shift amount from a field element. -/
def decodeShiftAmount {p : ℕ} [Fact p.Prime] (x : F p) : ℕ :=
  normalizeShiftAmount x.val

lemma decodeShiftAmount_lt {p : ℕ} [Fact p.Prime] (x : F p) :
    decodeShiftAmount x < 64 := by
  unfold decodeShiftAmount normalizeShiftAmount
  exact Nat.mod_lt _ (by decide)

section ShiftOperations
variable {p : ℕ} [Fact p.Prime]

/-- Logical shift left -/
def shiftLeftLogical (wire : Vector (F p) 64)
    (amount : ℕ) : Vector (F p) 64 :=
  if hZero : amount = 0 then
    wire
  else
    Vector.ofFn fun i : Fin 64 =>
      if hLe : amount ≤ i.val then
        let idxVal := i.val - amount
        -- idxVal < 64 because idxVal ≤ i.val and i.val < 64
        have hIdx : idxVal < 64 := by
          have : idxVal ≤ i.val := Nat.sub_le _ _
          exact lt_of_le_of_lt this i.isLt
        let idx : Fin 64 := ⟨idxVal, hIdx⟩
        wire[idx]
      else
        (0 : F p)


/-- Logical shift right -/
def shiftRightLogical (wire : Vector (F p) 64) (amount : ℕ) : Vector (F p) 64 :=
  Vector.ofFn fun i : Fin 64 =>
    let src := i.val + amount
    if hSrc : src < 64 then
      let idx : Fin 64 := ⟨src, hSrc⟩
      wire[idx]
    else
      (0 : F p)

/-- Arithmetic shift right -/
def shiftRightArithmetic (wire : Vector (F p) 64) (amount : ℕ) : Vector (F p) 64 :=
  let msbIdx : Fin 64 := Fin.last 63
  let msb := wire[msbIdx]
  Vector.ofFn fun i : Fin 64 =>
    let src := i.val + amount
    if hSrc : src < 64 then
      let idx : Fin 64 := ⟨src, hSrc⟩
      wire[idx]
    else
      msb


/-- Apply a shift described by kind and amount. -/
def applyShiftVec (wire : Vector (F p) 64) (kind : ShiftKind)
    (amount : ℕ) : Vector (F p) 64 :=
  match kind with
  | .sll => shiftLeftLogical wire amount
  | .srl => shiftRightLogical wire amount
  | .sra => shiftRightArithmetic wire amount

end ShiftOperations

section Evaluation
variable {p : ℕ} [Fact p.Prime]

/-- Apply the shift metadata of an `SVIData` to its wire. -/
def applyShift (x : SVIData (F p)) : Vector (F p) 64 :=
  let kind := decodeShiftKind x.shiftType
  let amount := decodeShiftAmount x.shiftAmount
  applyShiftVec x.wire kind amount

end Evaluation

end Gadgets.Binius64
