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
metadata lives as type parameters.
-/
structure SVI (shiftKind: ShiftKind) (shiftAmount: Fin 64) (F : Type) where
  wire : (fields 64) F
deriving Repr

instance (k: ShiftKind) (a: Fin 64) : ProvableStruct (SVI k a) where
  components := [fields 64]
  toComponents := fun svi => .cons svi.wire .nil
  fromComponents := fun | .cons wire .nil => { wire }

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

/-- Apply the shift metadata of an `SVI` to its wire. -/
def applyShift (x : SVI k a (F p)) : Vector (F p) 64 :=
  applyShiftVec x.wire k a

private def evalShiftedWire
    (x : SVI k a (Expression (F p)))
    (env : Environment (F p)) : Vector (F p) 64 :=
  let wireVals := Vector.map (Expression.eval env) x.wire
  applyShiftVec wireVals k a

def applyShiftExpr (x : SVI k a (Expression (F p))) :
    Circuit (F p) (Vector (Expression (F p)) 64) :=
  return applyShiftVec x.wire k a

@[simp] lemma applyShiftExpr_localLength
    (x : SVI k a (Expression (F p))) (offset : ℕ) :
    (applyShiftExpr x).localLength offset = 0 := by
  simp_all [circuit_norm, applyShiftExpr]

@[simp] lemma applyShiftExpr_subcircuitsConsistent
    (x : SVI k a (Expression (F p))) (offset : ℕ) :
    ((applyShiftExpr x).operations offset).SubcircuitsConsistent offset := by
  simp [applyShiftExpr, Operations.SubcircuitsConsistent,
    Operations.forAll, Circuit.pure_def, Circuit.operations]

@[simp] lemma map_eval_applyShiftVec
    (env : Environment (F p))
    (wire : Vector (Expression (F p)) 64)
    (kind : ShiftKind) (amount : Fin 64) :
    Vector.map (Expression.eval env) (applyShiftVec wire kind amount) =
      applyShiftVec (Vector.map (Expression.eval env) wire) kind amount := by
  classical
  cases kind with
  | sll =>
      by_cases hZero : amount = 0
      · simp [applyShiftVec, shiftLeftLogical, hZero]
      · ext i
        rename_i hi
        by_cases hLe : amount ≤ (⟨i, hi⟩ : Fin 64)
        · simp [applyShiftVec, shiftLeftLogical, hZero, hLe]
        · simp [applyShiftVec, shiftLeftLogical, hZero, hLe]
  | srl =>
      ext i
      rename_i hi
      by_cases hSrc : i + amount.val < 64
      · simp [applyShiftVec, shiftRightLogical, hSrc]
      · simp [applyShiftVec, shiftRightLogical, hSrc]
  | sra =>
      ext i
      rename_i hi
      by_cases hSrc : i + amount.val < 64
      · simp [applyShiftVec, shiftRightArithmetic, hSrc]
      · simp [applyShiftVec, shiftRightArithmetic, hSrc]

end Evaluation

end Gadgets.Binius64
