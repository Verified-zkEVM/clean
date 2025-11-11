import Mathlib.Data.ZMod.Basic
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Utils.Vector
import Clean.Circuit.Basic

namespace Gadgets.Binius64

/-- Enumeration of supported shift kinds. -/
inductive ShiftKind
  | sll
  | srl
  | sra
  deriving DecidableEq, Repr

/--
Structured representation of a Binius shifted vector index (SVI).

The wire is encoded using the `fields 64` provable type, while the shift
metadata lives directly in the base field.
-/
structure SVIData (shiftKind: ShiftKind) (shiftAmount: Fin 64) (F : Type) where
  wire : (fields 64) F
deriving Repr

@[reducible]
def SVI := SVIData

instance (k: ShiftKind) (a: Fin 64) : ProvableStruct (SVI k a) where
  components := [fields 64]
  toComponents := fun svi => .cons svi.wire .nil
  fromComponents := fun | .cons wire .nil => { wire }

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

section ShiftOperations
variable {p : ℕ} [Fact p.Prime]

/-- Logical shift left -/
def shiftLeftLogical {F : Type} [Zero F] (wire : Vector F 64)
    (amount : Fin 64) : Vector F 64 :=
  if hZero : amount = 0 then
    wire
  else
    Vector.ofFn fun i : Fin 64 =>
      if hLe : amount.val ≤ i.val then
        let idxVal := i.val - amount.val
        -- idxVal < 64 because idxVal ≤ i.val and i.val < 64
        have hIdx : idxVal < 64 := by
          have : idxVal ≤ i.val := Nat.sub_le _ _
          exact lt_of_le_of_lt this i.isLt
        let idx : Fin 64 := ⟨idxVal, hIdx⟩
        wire[idx]
      else
        (0 : F)

/-- Logical shift right -/
def shiftRightLogical {F : Type} [Zero F] (wire : Vector F 64) (amount : Fin 64) : Vector F 64 :=
  Vector.ofFn fun i : Fin 64 =>
    let src := i.val + amount.val
    if hSrc : src < 64 then
      let idx : Fin 64 := ⟨src, hSrc⟩
      wire[idx]
    else
      (0 : F)

/-- Arithmetic shift right -/
def shiftRightArithmetic {F : Type} [Zero F] (wire : Vector F 64) (amount : Fin 64) : Vector F 64 :=
  let msbIdx : Fin 64 := Fin.last 63
  let msb := wire[msbIdx]
  Vector.ofFn fun i : Fin 64 =>
    let src := i.val + amount.val
    if hSrc : src < 64 then
      let idx : Fin 64 := ⟨src, hSrc⟩
      wire[idx]
    else
      msb

/-- Apply a shift described by kind and amount. -/
def applyShiftVec {F: Type} [Zero F] (wire : Vector F 64) (kind : ShiftKind)
    (amount : Fin 64) : Vector F 64 :=
  match kind with
  | .sll => shiftLeftLogical wire amount
  | .srl => shiftRightLogical wire amount
  | .sra => shiftRightArithmetic wire amount

end ShiftOperations

section Evaluation
variable {p : ℕ} [Fact p.Prime]
variable {k: ShiftKind} {a: Fin 64}

/-- Apply the shift metadata of an `SVIData` to its wire. -/
def applyShift (x : SVIData k a (F p)) : Vector (F p) 64 :=
  applyShiftVec x.wire k a

private def evalShiftedWire
    (x : SVIData k a (Expression (F p)))
    (env : Environment (F p)) : Vector (F p) 64 :=
  let wireVals := Vector.map (Expression.eval env) x.wire
  applyShiftVec wireVals k a

def applyShiftExpr (x : SVIData k a (Expression (F p))) :
    Circuit (F p) (Vector (Expression (F p)) 64) :=
  return applyShiftVec x.wire k a

-- TODO can remove
@[simp] lemma applyShiftExpr_localLength
    (x : SVIData k a (Expression (F p))) (offset : ℕ) :
    (applyShiftExpr x).localLength offset = 0 := by
  simp_all [circuit_norm, applyShiftExpr]

end Evaluation

end Gadgets.Binius64
