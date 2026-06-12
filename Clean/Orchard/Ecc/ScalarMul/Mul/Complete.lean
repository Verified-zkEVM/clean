import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/complete.rs`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Complete

structure Row (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.zNext - 2 * row.zPrev

def ySwitch {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def SelectedCompleteBitPointNegation (row : Row Fp) : Prop :=
  ∀ baseX : Fp,
    (bit row = 0 →
      (baseX, row.yP) =
        CompElliptic.CurveForms.ShortWeierstrass.neg (baseX, row.baseY)) ∧
      (bit row = 1 →
        (baseX, row.yP) = (baseX, row.baseY))

def Spec (row : Row Fp) : Prop :=
  IsBool (bit row) ∧ SelectedCompleteBitPointNegation row

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (ySwitch row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Decompose scalar for complete bits of variable-base mul"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPointNegation,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hSwitch⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool)
    · intro x
      constructor
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          linear_combination hSwitch' + (2 * input_yP) * hBit
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          have hBitNorm : input_zNext + -(2 * input_zPrev) = 1 := by
            linear_combination hBit
          have hCoeff : 1 + (2 * input_zPrev + -input_zNext) = 0 := by
            linear_combination -hBitNorm
          have hDiff : input_baseY + -input_yP = 0 := by
            linear_combination hSwitch' - (input_baseY + -input_yP) * hBitNorm -
              (input_baseY + input_yP) * hCoeff
          linear_combination -hDiff
  completeness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPointNegation,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool
    · rcases hBool with hBit | hBit
      · exact by
          have hPoint := (hSelect 0).1 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          simpa [sub_eq_add_neg] using hBit
      · exact by
          have hPoint := (hSelect 0).2 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          linear_combination -hBit

/-!
### `complete.rs::Config::assign_region`

The three complete-addition bits `k_3, k_2, k_1` of variable-base scalar mul. Each bit
extends the running sum, conditionally negates the base y-coordinate (checked by the
decomposition gate above), and performs two complete additions:
`acc ← acc + (acc + U)` with `U = (base.x, ±base.y)`.
-/

namespace AssignRegion

open CompElliptic.Curves.Pasta
open Incomplete.DoubleAndAdd (BitsHint zRunValue)

/-- Inputs: the base point, the accumulator cells from incomplete addition, the
running-sum cell, and the prover-side complete-range bits (indexed `0..2`). -/
structure Input (F : Type) where
  base : Ecc.Point F
  xA : F
  yA : F
  z : F
  bits : Unconstrained BitsHint F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, xA := default, yA := default,
     z := default, bits := fun _ => default }⟩

structure Output (F : Type) where
  acc : Ecc.Point F
  zs : Vector F 3
deriving ProvableStruct

/-- One complete-addition step on coordinate pairs:
`acc + (U + acc)` with `U = (base.x, ±base.y)`. -/
def stepValue (baseX baseY : Fp) (acc : Fp × Fp) (bit : Bool) : Fp × Fp :=
  Pallas.add acc (Pallas.add (baseX, if bit then baseY else -baseY) acc)

/-- The accumulator after the first `b` complete-addition steps. -/
def accValue (baseX baseY : Fp) (acc : Fp × Fp) (bits : ℕ → Bool) : ℕ → Fp × Fp
  | 0 => acc
  | b + 1 => stepValue baseX baseY (accValue baseX baseY acc bits b) (bits b)

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- copy the running sum from incomplete addition
  let z₀ <== input.z
  -- the interstitial running-sum cells of the three complete bits
  let zs ← witnessVector 3 fun env =>
    .ofFn fun (b : Fin 3) => zRunValue (env input.z) (input.bits env) b.val
  let zsAll := Vector.cast (Nat.add_comm 1 3) ((#v[z₀] : Vector (Expression Fp) 1) ++ zs)
  let acc₀ : Var Ecc.Point Fp := { x := input.xA, y := input.yA }
  let accFinal ← Circuit.foldlRange 3 acc₀ fun acc i => do
    -- copy base.y for the decomposition gate, witness the conditionally-negated y_p
    let baseY <== input.base.y
    let yP ← witnessField fun env =>
      if input.bits env i.val then env input.base.y else -(env input.base.y)
    Complete.circuit {
      zPrev := zsAll[i.val]'(by have := i.isLt; omega),
      zNext := zsAll[i.val + 1]'(by have := i.isLt; omega),
      baseY, yP }
    -- U = (base.x, y_p); acc + U, then acc + (acc + U)
    let tmp ← Add.circuit { p := { x := input.base.x, y := yP }, q := acc }
    Add.circuit { p := acc, q := tmp }
  return { acc := accFinal, zs }

instance elaborated : ElaboratedCircuit Fp Input Output main := by
  elaborate_circuit

def Spec (input : Value Input Fp) (output : Output Fp) (_ : ProverData Fp) : Prop :=
  ∃ bits : ℕ → Bool,
    (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
      ∀ b : Fin 2, output.zs[b.val + 1] =
        2 * output.zs[b.val]'(by have := b.isLt; omega) +
          (if bits (b.val + 1) then 1 else 0)) ∧
    (Pallas.Valid (input.xA, input.yA) → Pallas.Valid input.base.coords →
      Pallas.Valid output.acc.coords ∧
        output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) bits 3)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  Pallas.Valid (input.xA, input.yA) ∧ Pallas.Valid input.base.coords

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  (∀ b : Fin 3, output.zs[b.val] = zRunValue input.z input.bits b.val) ∧
  output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) input.bits 3

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  sorry

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  sorry

/-- `complete.rs::Config::assign_region`: the complete-addition bits of variable-base
scalar multiplication. -/
def circuit : GeneralFormalCircuit.WithHint Fp Input Output where
  main
  Spec
  ProverAssumptions
  ProverSpec
  soundness
  completeness

end AssignRegion

end Orchard.Ecc.ScalarMul.Mul.Complete
