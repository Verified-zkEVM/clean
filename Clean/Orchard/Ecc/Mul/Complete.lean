import Clean.Orchard.Ecc.Defs
import Clean.Orchard.Ecc.Mul.Incomplete
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/complete.rs`.
-/

namespace Orchard.Ecc.Mul.Complete

structure Input (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Input K) : K :=
  row.zNext - 2 * row.zPrev

def ySwitch {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Input K) : K :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def SelectedCompleteBitPointNegation (row : Input Fp) : Prop :=
  ∀ baseX : Fp,
    (bit row = 0 →
      (baseX, row.yP) =
        CompElliptic.CurveForms.ShortWeierstrass.neg (baseX, row.baseY)) ∧
      (bit row = 1 →
        (baseX, row.yP) = (baseX, row.baseY))

def Spec (row : Input Fp) : Prop :=
  IsBool (bit row) ∧ SelectedCompleteBitPointNegation row

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertBool (bit row)
  assertZero (ySwitch row)

def circuit : FormalAssertion Fp Input where
  name := "GATE Decompose scalar for complete bits of variable-base mul"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPointNegation,
      bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hSwitch⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · simpa [sub_eq_add_neg] using hBool
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
      bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · simpa [sub_eq_add_neg] using hBool
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
  base : Point F
  xA : F
  yA : F
  z : F
  bits : UnconstrainedNative BitsHint F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ base := { x := default, y := default }, xA := default, yA := default,
     z := default, bits := fun _ => default }⟩

structure Output (F : Type) where
  acc : Point F
  zs : Vector F 3
deriving ProvableStruct

/-- One complete-addition step on coordinate pairs:
`acc + (U + acc)` with `U = (base.x, ±base.y)`. -/
def stepValue (baseX baseY : Fp) (acc : Fp × Fp) (bit : Bool) : Fp × Fp :=
  CompElliptic.CurveForms.ShortWeierstrass.add pallasA acc
    (CompElliptic.CurveForms.ShortWeierstrass.add pallasA
      (baseX, if bit then baseY else -baseY) acc)

/-- The accumulator after the first `b` complete-addition steps. -/
def accValue (baseX baseY : Fp) (acc : Fp × Fp) (bits : ℕ → Bool) : ℕ → Fp × Fp
  | 0 => acc
  | b + 1 => stepValue baseX baseY (accValue baseX baseY acc bits b) (bits b)

private def accValuePoint (baseX baseY xA yA : Fp) (bits : ℕ → Bool) :
    ℕ → Point Fp
  | 0 => { x := xA, y := yA }
  | b + 1 =>
      let acc := accValuePoint baseX baseY xA yA bits b
      acc + ({ x := baseX, y := if bits b then baseY else -baseY } + acc)

private theorem accValuePoint_coords
    (baseX baseY xA yA : Fp) (bits : ℕ → Bool) :
    (accValuePoint baseX baseY xA yA bits 3).coords
      = accValue baseX baseY (xA, yA) bits 3 := by
  simp only [accValuePoint, accValue, stepValue, Point.coords_add]
  simp [Point.coords]

def main (input : Var Input Fp) : Circuit Fp (Var Output Fp) := do
  -- copy the running sum from incomplete addition
  let z₀ <== input.z
  -- the interstitial running-sum cells of the three complete bits
  let zs ← witnessVectorNative 3 fun env =>
    Vector.ofFn fun (b : Fin 3) => zRunValue (env input.z) (input.bits env) b.val
  let zsAll := Vector.cast (Nat.add_comm 1 3) ((#v[z₀] : Vector (Expression Fp) 1) ++ zs)
  let acc₀ : Var Point Fp := { x := input.xA, y := input.yA }
  let accFinal ← Circuit.foldlRange 3 acc₀ fun acc i => do
    -- copy base.y for the decomposition gate, witness the conditionally-negated y_p
    let baseY <== input.base.y
    let yP ← witnessNative fun env =>
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
    (({ x := input.xA, y := input.yA } : Point Fp).Valid → input.base.Valid →
      output.acc.Valid ∧
        output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) bits 3)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  ({ x := input.xA, y := input.yA } : Point Fp).Valid ∧ input.base.Valid

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  (∀ b : Fin 3, output.zs[b.val] = zRunValue input.z input.bits b.val) ∧
  output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) input.bits 3

/-- The evaluations of the prepended running-sum cells, by computation. Stating this
over an abstract `v` (pinned by `hv`) lets the `getElem`s elaborate; the concrete
append term would not. -/
private theorem eval_z (env : Environment Fp) (i₀ : ℕ) (v : Vector (Expression Fp) 4)
    (hv : v = (#v[var { index := i₀ }] : Vector (Expression Fp) 1) ++
      (Vector.mapRange 3 fun i => var { index := i₀ + 1 + i } :
        Vector (Expression Fp) 3)) :
    Expression.eval env v[0] = env.get i₀ ∧
    Expression.eval env v[1] = env.get (i₀ + 1) ∧
    Expression.eval env v[2] = env.get (i₀ + 1 + 1) ∧
    Expression.eval env v[3] = env.get (i₀ + 1 + 2) := by
  subst hv
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- One complete bit: the decomposition gate facts pin the running-sum step and the
conditionally-negated `y_p` in terms of the decidable bit `z' = 2z + 1`. -/
private theorem bit_facts {zP zN bY yP : Fp}
    (hbool : IsBool (Complete.bit { zPrev := zP, zNext := zN, baseY := bY, yP := yP }))
    (hsel : SelectedCompleteBitPointNegation
      { zPrev := zP, zNext := zN, baseY := bY, yP := yP }) :
    (zN = 2 * zP + if zN = 2 * zP + 1 then 1 else 0) ∧
      yP = if zN = 2 * zP + 1 then bY else -bY := by
  rcases hbool with h | h
  · have hz : zN = 2 * zP := by
      simp only [Complete.bit] at h
      linear_combination h
    have hcond : ¬(zN = 2 * zP + 1) := by
      rw [hz]
      intro hc
      exact one_ne_zero (by linear_combination -hc)
    have hy := (hsel 0).1 h
    simp only [CompElliptic.CurveForms.ShortWeierstrass.neg, Prod.mk.injEq] at hy
    rw [if_neg hcond, if_neg hcond]
    exact ⟨by rw [hz]; ring, hy.2⟩
  · have hz : zN = 2 * zP + 1 := by
      simp only [Complete.bit] at h
      linear_combination h
    have hy := (hsel 0).2 h
    simp only [Prod.mk.injEq] at hy
    rw [if_pos hz, if_pos hz]
    exact ⟨hz, hy.2⟩

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True) Spec := by
  circuit_proof_start [main, Spec, Complete.circuit, Complete.Spec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_z0, h_loop⟩ := h_holds
  have h0 := h_loop ⟨0, by norm_num⟩
  have h1 := h_loop ⟨1, by norm_num⟩
  have h2 := h_loop ⟨2, by norm_num⟩
  clear h_loop
  simp only [Nat.reduceAdd, Nat.reduceMul,
    Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk,
    Fin.foldl_const, Fin.val_last, circuit_norm] at h0 h1 h2
  norm_num at h0 h1 h2
  obtain ⟨hz0e, hz1e, hz2e, hz3e⟩ := eval_z env i₀ _ rfl
  rw [hz0e, hz1e] at h0
  rw [hz1e, hz2e] at h1
  rw [hz2e, hz3e] at h2
  obtain ⟨hby0, ⟨hbool0, hsel0⟩, hAddA0, hAddB0⟩ := h0
  obtain ⟨hby1, ⟨hbool1, hsel1⟩, hAddA1, hAddB1⟩ := h1
  obtain ⟨hby2, ⟨hbool2, hsel2⟩, hAddA2, hAddB2⟩ := h2
  obtain ⟨hchain0, hyP0⟩ := bit_facts hbool0 hsel0
  obtain ⟨hchain1, hyP1⟩ := bit_facts hbool1 hsel1
  obtain ⟨hchain2, hyP2⟩ := bit_facts hbool2 hsel2
  -- the bit values, decidably read off the running-sum cells
  refine ⟨fun b =>
    decide (env.get (i₀ + 1 + b) =
      2 * (if b = 0 then env.get i₀ else env.get (i₀ + b)) + 1), ⟨?_, ?_⟩, ?_⟩
  · rw [← h_z0]
    simpa using hchain0
  · intro b
    rcases b with ⟨_ | _ | _, hb⟩
    · simpa using hchain1
    · simpa using hchain2
    · omega
  · intro hAccV hBaseV
    obtain ⟨hbx, hby⟩ : Expression.eval env input_var.base.x = input_base.x ∧
        Expression.eval env input_var.base.y = input_base.y := by
      have h := h_input.1
      rw [← h]
      exact ⟨rfl, rfl⟩
    rw [h_input.2.1, h_input.2.2.1] at hAddA0 hAddB0
    rw [hbx] at hAddA0 hAddA1 hAddA2
    rw [hby] at hby0 hby1 hby2
    rw [hby0] at hyP0
    rw [hby1] at hyP1
    rw [hby2] at hyP2
    -- the conditionally-negated points are valid
    have hU0V :
        ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 1) } : Point Fp).Valid := by
      rw [hyP0]
      split
      · exact hBaseV
      · exact Point.valid_neg hBaseV
    have hU1V :
        ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 24 + 1) } : Point Fp).Valid := by
      rw [hyP1]
      split
      · exact hBaseV
      · exact Point.valid_neg hBaseV
    have hU2V :
        ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 48 + 1) } : Point Fp).Valid := by
      rw [hyP2]
      split
      · exact hBaseV
      · exact Point.valid_neg hBaseV
    -- chain the six complete additions
    have hT0 := hAddA0 hU0V hAccV
    have hA1 := hAddB0 hAccV hT0.1
    have hT1 := hAddA1 hU1V hA1.1
    have hA2 := hAddB1 hA1.1 hT1.1
    have hT2 := hAddA2 hU2V hA2.1
    have hA3 := hAddB2 hA2.1 hT2.1
    simp only [Fin.foldl_const, Fin.val_last]
    refine ⟨hA3.1, ?_⟩
    rw [show i₀ + 1 + 3 + 2 * 24 + 2 + 11 + 2 + 2
        = i₀ + 1 + 3 + 48 + 1 + 1 + 11 + 2 + 2 from by omega]
    rw [hA3.2, hT2.2, hA2.2, hT1.2, hA1.2, hT0.2, hyP0, hyP1, hyP2]
    simpa [accValuePoint, Point.coords] using
      accValuePoint_coords input_base.x input_base.y input_xA input_yA
        (fun b => decide (env.get (i₀ + 1 + b) =
          2 * (if b = 0 then env.get i₀ else env.get (i₀ + b)) + 1))

/-- The honest assignment of one complete bit satisfies the decomposition gate. -/
private theorem bit_facts_complete (zP bY : Fp) (b : Bool) :
    IsBool (Complete.bit
      { zPrev := zP, zNext := 2 * zP + (if b = true then 1 else 0), baseY := bY,
        yP := if b = true then bY else -bY }) ∧
    SelectedCompleteBitPointNegation
      { zPrev := zP, zNext := 2 * zP + (if b = true then 1 else 0), baseY := bY,
        yP := if b = true then bY else -bY } := by
  constructor
  · cases b <;> simp [Complete.bit, IsBool]
  · intro baseX
    cases b
    · refine ⟨fun _ => ?_, fun h => ?_⟩
      · simp [CompElliptic.CurveForms.ShortWeierstrass.neg]
      · simp [Complete.bit] at h
    · refine ⟨fun h => ?_, fun _ => by simp⟩
      simp [Complete.bit] at h

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness Fp main ProverAssumptions ProverSpec := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions, Complete.circuit, Complete.Spec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_z0w, h_zsw, h_loop⟩ := h_env
  obtain ⟨hbx, hby⟩ : Expression.eval env.toEnvironment input_var.base.x = input_base.x ∧
      Expression.eval env.toEnvironment input_var.base.y = input_base.y := by
    have h := h_input.1
    rw [← h]
    exact ⟨rfl, rfl⟩
  have hz1 := h_zsw ⟨0, by norm_num⟩
  have hz2 := h_zsw ⟨1, by norm_num⟩
  have hz3 := h_zsw ⟨2, by norm_num⟩
  norm_num at hz1 hz2 hz3
  have hl0 := h_loop ⟨0, by norm_num⟩
  have hl1 := h_loop ⟨1, by norm_num⟩
  have hl2 := h_loop ⟨2, by norm_num⟩
  clear h_loop h_zsw
  simp only [Nat.reduceAdd, Nat.reduceMul,
    Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk,
    Fin.foldl_const, Fin.val_last, circuit_norm] at hl0 hl1 hl2
  norm_num at hl0 hl1 hl2
  obtain ⟨hby0, hyP0, hAdds0⟩ := hl0
  obtain ⟨hby1, hyP1, hAdds1⟩ := hl1
  obtain ⟨hby2, hyP2, hAdds2⟩ := hl2
  obtain ⟨hz0e, hz1e, hz2e, hz3e⟩ := eval_z env.toEnvironment i₀ _ rfl
  obtain ⟨hAccV, hBaseV⟩ := h_assumptions
  rw [hby] at hby0 hby1 hby2 hyP0 hyP1 hyP2
  rw [hbx] at hAdds0 hAdds1 hAdds2
  rw [h_input.2.1, h_input.2.2.1] at hAdds0
  -- the honest running-sum steps
  have hz1' : env.get (i₀ + 1) = 2 * input_z + (if input_bits 0 = true then 1 else 0) := by
    rw [hz1]
    rfl
  have hz2' : env.get (i₀ + 1 + 1)
      = 2 * env.get (i₀ + 1) + (if input_bits 1 = true then 1 else 0) := by
    rw [hz2, hz1]
    rfl
  have hz3' : env.get (i₀ + 1 + 2)
      = 2 * env.get (i₀ + 1 + 1) + (if input_bits 2 = true then 1 else 0) := by
    rw [hz3, hz2]
    rfl
  -- the conditionally-negated points are valid
  have hU0V :
      ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 1) } : Point Fp).Valid := by
    rw [hyP0]
    split
    · exact hBaseV
    · exact Point.valid_neg hBaseV
  have hU1V :
      ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 24 + 1) } : Point Fp).Valid := by
    rw [hyP1]
    split
    · exact hBaseV
    · exact Point.valid_neg hBaseV
  have hU2V :
      ({ x := input_base.x, y := env.get (i₀ + 1 + 3 + 48 + 1) } : Point Fp).Valid := by
    rw [hyP2]
    split
    · exact hBaseV
    · exact Point.valid_neg hBaseV
  -- chain the six complete additions
  have hT0 := hAdds0.1 hU0V hAccV
  have hA1 := hAdds0.2 hAccV hT0.1
  have hT1 := hAdds1.1 hU1V hA1.1
  have hA2 := hAdds1.2 hA1.1 hT1.1
  have hT2 := hAdds2.1 hU2V hA2.1
  have hA3 := hAdds2.2 hA2.1 hT2.1
  refine ⟨⟨h_z0w, fun i => ?_⟩, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := i
    simp only [Nat.reduceAdd,
      Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.val_mk,
      Fin.foldl_const, circuit_norm]
    rcases b with _ | _ | _ | n
    · rw [hbx, hby, hz0e, hz1e, h_z0w, hz1', hby0, hyP0, h_input.2.1, h_input.2.2.1]
      exact ⟨hby0 ▸ rfl, bit_facts_complete input_z input_base.y (input_bits 0),
        ⟨hyP0 ▸ hU0V, hAccV⟩, hAccV, hT0.1⟩
    · rw [hbx, hby, hz1e, hz2e, hz1', hz2', hby1, hyP1]
      exact ⟨rfl, by rw [← hz1']; exact bit_facts_complete _ input_base.y (input_bits 1),
        ⟨hyP1 ▸ hU1V, hA1.1⟩, hA1.1, hT1.1⟩
    · rw [hbx, hby, hz2e, hz3e, hz2', hz3', hby2, hyP2]
      exact ⟨rfl, by rw [← hz2']; exact bit_facts_complete _ input_base.y (input_bits 2),
        ⟨hyP2 ▸ hU2V, hA2.1⟩, hA2.1, hT2.1⟩
    · omega
  · intro b
    rcases b with ⟨_ | _ | _ | n, hb⟩
    · simpa using hz1
    · simpa using hz2
    · simpa using hz3
    · omega
  · simp only [Fin.foldl_const, Fin.val_last]
    rw [show i₀ + 1 + 3 + 2 * 24 + 2 + 11 + 2 + 2
        = i₀ + 1 + 3 + 48 + 1 + 1 + 11 + 2 + 2 from by omega]
    rw [hA3.2, hT2.2, hA2.2, hT1.2, hA1.2, hT0.2, hyP0, hyP1, hyP2]
    simpa [accValuePoint, Point.coords] using
      accValuePoint_coords input_base.x input_base.y input_xA input_yA input_bits

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

end Orchard.Ecc.Mul.Complete
